from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field, replace
from typing import TextIO

from .ambiguity import ambiguity_bounds
from .interfaces import Checker, PromptRenderer, QuestionFamily, Sampler
from .models import (
    AnalysisParameters,
    BoundaryEstimate,
    ChainReport,
    ChainSpec,
    CheckerResult,
    DetectorReport,
    SampleTrace,
    SamplingMode,
    SliceEstimate,
    SliceSpec,
    TaskSpec,
)
from .policy import (
    boundary_estimates_from_slices,
    chain_effective_route,
    classify_chain,
    detector_state_summary,
    effective_success_hats,
    global_obstructions,
    summarize_task_partition,
    witness_pairs_from_boundaries,
)
from .stats import enough_precision, event_delta, slice_bounds


@dataclass
class _SliceRunState:
    samples: int = 0
    successes: int = 0
    traces: list[SampleTrace] = field(default_factory=list)


class SafeSliceDetector:
    """Orchestrates witness-side and ambiguity-side safe-slice analysis."""

    def __init__(
        self,
        *,
        sampler: Sampler,
        checker: Checker,
        prompt_renderer: PromptRenderer,
        question_family: QuestionFamily | None = None,
        example_limit: int = 3,
        progress_stream: TextIO | None = None,
    ) -> None:
        self.sampler = sampler
        self.checker = checker
        self.prompt_renderer = prompt_renderer
        self.question_family = question_family
        self.example_limit = example_limit
        self.progress_stream = progress_stream
        self._progress_uses_carriage = bool(
            progress_stream
            and hasattr(progress_stream, "isatty")
            and progress_stream.isatty()
        )
        self._progress_line_open = False

    def _progress_message(
        self,
        *,
        chain_index: int,
        chain_count: int,
        chain: ChainSpec,
        slice_index: int,
        sample_count: int,
        sample_limit: int,
        successes: int,
        status: str,
    ) -> str:
        return (
            f"[safe_slice] chain {chain_index + 1}/{chain_count} {chain.chain_id} "
            f"slice {slice_index + 1}/{len(chain.slices)} {chain.slices[slice_index].slice_id} "
            f"prompt {sample_count}/{sample_limit} success={successes} {status}"
        )

    def _emit_progress(self, message: str, *, transient: bool) -> None:
        if self.progress_stream is None:
            return
        if transient and self._progress_uses_carriage:
            self.progress_stream.write("\r" + message.ljust(160))
            self.progress_stream.flush()
            self._progress_line_open = True
            return
        if self._progress_line_open and self._progress_uses_carriage:
            self.progress_stream.write("\n")
            self._progress_line_open = False
        self.progress_stream.write(message + "\n")
        self.progress_stream.flush()

    def _maybe_report_sample_progress(
        self,
        *,
        chain_index: int,
        chain_count: int,
        chain: ChainSpec,
        slice_index: int,
        samples: int,
        sample_limit: int,
        successes: int,
    ) -> None:
        if self.progress_stream is None:
            return
        transient = self._progress_uses_carriage
        if not transient:
            report_every = max(1, sample_limit // 8)
            if samples not in {1, sample_limit} and samples % report_every != 0:
                return
        self._emit_progress(
            self._progress_message(
                chain_index=chain_index,
                chain_count=chain_count,
                chain=chain,
                slice_index=slice_index,
                sample_count=samples,
                sample_limit=sample_limit,
                successes=successes,
                status="running",
            ),
            transient=transient,
        )

    def _time_uniform_horizon(self, task: TaskSpec) -> int | None:
        if str(task.thresholds.sampling_mode) == SamplingMode.ADAPTIVE.value:
            return int(task.thresholds.max_samples)
        return None

    def _finalize_slice_estimate(
        self,
        *,
        slice_spec: SliceSpec,
        state: _SliceRunState,
        thresholds,
        delta_event: float,
        time_uniform_horizon: int | None,
    ) -> SliceEstimate:
        success_rate_hat, sample_radius, total_radius, lower_bound, upper_bound = slice_bounds(
            state.successes,
            state.samples,
            oracle_error=thresholds.oracle_error,
            delta_event=delta_event,
            bound_method=thresholds.bound_method,
            time_uniform_horizon=time_uniform_horizon,
        )
        return SliceEstimate(
            slice_id=slice_spec.slice_id,
            premises=slice_spec.premises,
            samples=state.samples,
            successes=state.successes,
            success_rate_hat=success_rate_hat,
            sample_radius=sample_radius,
            total_radius=total_radius,
            success_lower_bound=lower_bound,
            success_upper_bound=upper_bound,
            meets_safe_success=lower_bound >= thresholds.safe_success,
            reached_evidence_threshold=enough_precision(total_radius, thresholds.ci_half_width),
            traces=tuple(state.traces),
        )

    def _attach_smoothed_hats(
        self,
        slices: tuple[SliceEstimate, ...],
        *,
        thresholds,
    ) -> tuple[SliceEstimate, ...]:
        smoothed = effective_success_hats(
            slices,
            boundary_mode=str(thresholds.boundary_mode),
        )
        return tuple(
            replace(slice_estimate, smoothed_success_rate_hat=smoothed[index])
            for index, slice_estimate in enumerate(slices)
        )

    def _is_slice_resolved(self, slice_estimate: SliceEstimate, thresholds) -> bool:
        if slice_estimate.samples < thresholds.min_samples:
            return False
        if slice_estimate.meets_safe_success:
            return True
        if slice_estimate.success_upper_bound < thresholds.safe_success:
            return True
        return enough_precision(slice_estimate.total_radius, thresholds.ci_half_width)

    def _sample_selected_indices(
        self,
        *,
        chain: ChainSpec,
        selected_indices: tuple[int, ...],
        prompts: tuple[str, ...],
        states: list[_SliceRunState],
        chain_index: int,
        chain_count: int,
        thresholds,
    ) -> None:
        if not selected_indices:
            return

        def run_one(slice_index: int):
            slice_spec = chain.slices[slice_index]
            prompt = prompts[slice_index]
            checker_details: dict[str, object]
            try:
                output_text = self.sampler.sample(chain, slice_spec, prompt)
                checker_result = self.checker.check(output_text, chain, slice_spec)
                checker_details = dict(checker_result.details)
            except Exception as exc:
                output_text = str(getattr(exc, "output_text", "") or "")
                checker_result = CheckerResult(
                    success=False,
                    details={
                        "error": str(exc),
                        "error_type": type(exc).__name__,
                    },
                )
                checker_details = dict(checker_result.details)
                extra_details = getattr(exc, "details", None)
                if isinstance(extra_details, dict):
                    checker_details.update(extra_details)
            return slice_index, output_text, checker_result, checker_details

        max_workers = max(1, min(thresholds.parallel_samples, len(selected_indices)))
        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            futures = [executor.submit(run_one, slice_index) for slice_index in selected_indices]
            for future in as_completed(futures):
                slice_index, output_text, checker_result, checker_details = future.result()
                state = states[slice_index]
                state.samples += 1
                state.successes += 1 if checker_result.success else 0
                if len(state.traces) < self.example_limit:
                    state.traces.append(
                        SampleTrace(
                            sample_index=state.samples,
                            success=checker_result.success,
                            output_text=output_text,
                            checker_details=checker_details,
                        )
                    )
                self._maybe_report_sample_progress(
                    chain_index=chain_index,
                    chain_count=chain_count,
                    chain=chain,
                    slice_index=slice_index,
                    samples=state.samples,
                    sample_limit=thresholds.max_samples,
                    successes=state.successes,
                )

    def estimate_slice(
        self,
        task: TaskSpec,
        chain: ChainSpec,
        slice_index: int,
        delta_event: float,
        *,
        chain_index: int,
        chain_count: int,
    ) -> SliceEstimate:
        slice_spec = chain.slices[slice_index]
        thresholds = task.thresholds
        prompt = self.prompt_renderer.render(chain, slice_spec)
        state = _SliceRunState()
        time_uniform_horizon = self._time_uniform_horizon(task)

        self._emit_progress(
            self._progress_message(
                chain_index=chain_index,
                chain_count=chain_count,
                chain=chain,
                slice_index=slice_index,
                sample_count=0,
                sample_limit=thresholds.max_samples,
                successes=0,
                status="start",
            ),
            transient=False,
        )

        while state.samples < thresholds.max_samples:
            checker_details: dict[str, object]
            try:
                output_text = self.sampler.sample(chain, slice_spec, prompt)
                checker_result = self.checker.check(output_text, chain, slice_spec)
                checker_details = dict(checker_result.details)
            except Exception as exc:
                output_text = str(getattr(exc, "output_text", "") or "")
                checker_result = CheckerResult(
                    success=False,
                    details={
                        "error": str(exc),
                        "error_type": type(exc).__name__,
                    },
                )
                checker_details = dict(checker_result.details)
                extra_details = getattr(exc, "details", None)
                if isinstance(extra_details, dict):
                    checker_details.update(extra_details)

            state.samples += 1
            state.successes += 1 if checker_result.success else 0
            if len(state.traces) < self.example_limit:
                state.traces.append(
                    SampleTrace(
                        sample_index=state.samples,
                        success=checker_result.success,
                        output_text=output_text,
                        checker_details=checker_details,
                    )
                )
            self._maybe_report_sample_progress(
                chain_index=chain_index,
                chain_count=chain_count,
                chain=chain,
                slice_index=slice_index,
                samples=state.samples,
                sample_limit=thresholds.max_samples,
                successes=state.successes,
            )
            estimate = self._finalize_slice_estimate(
                slice_spec=slice_spec,
                state=state,
                thresholds=thresholds,
                delta_event=delta_event,
                time_uniform_horizon=time_uniform_horizon,
            )
            if self._is_slice_resolved(estimate, thresholds):
                break

        estimate = self._finalize_slice_estimate(
            slice_spec=slice_spec,
            state=state,
            thresholds=thresholds,
            delta_event=delta_event,
            time_uniform_horizon=time_uniform_horizon,
        )
        self._emit_progress(
            self._progress_message(
                chain_index=chain_index,
                chain_count=chain_count,
                chain=chain,
                slice_index=slice_index,
                sample_count=state.samples,
                sample_limit=thresholds.max_samples,
                successes=state.successes,
                status=f"done hat={estimate.success_rate_hat:.3f}",
            ),
            transient=False,
        )
        return estimate

    def _analyze_chain_uniform(
        self,
        task: TaskSpec,
        chain: ChainSpec,
        delta_event: float,
        *,
        chain_index: int,
        chain_count: int,
    ) -> ChainReport:
        slice_estimates = tuple(
            self.estimate_slice(
                task,
                chain,
                index,
                delta_event,
                chain_index=chain_index,
                chain_count=chain_count,
            )
            for index in range(len(chain.slices))
        )
        slice_estimates = self._attach_smoothed_hats(
            slice_estimates,
            thresholds=task.thresholds,
        )
        boundary_estimates = boundary_estimates_from_slices(
            slice_estimates,
            task.thresholds,
        )
        witness_pairs = witness_pairs_from_boundaries(chain.chain_id, boundary_estimates)
        local_partition = classify_chain(slice_estimates, boundary_estimates, task.thresholds)
        chain_detector_state = detector_state_summary(
            scope="chain",
            witness_family_scope="detected witness pairs in chain",
            witness_pairs=witness_pairs,
            detector_state_budget=task.thresholds.detector_state_budget,
        )
        return ChainReport(
            chain_id=chain.chain_id,
            slice_estimates=slice_estimates,
            boundary_estimates=boundary_estimates,
            witness_pairs=witness_pairs,
            local_partition=local_partition,
            detector_state=chain_detector_state,
            global_obstructions=(),
            effective_route=local_partition.route,
        )

    def _analyze_chain_adaptive(
        self,
        task: TaskSpec,
        chain: ChainSpec,
        delta_event: float,
        *,
        chain_index: int,
        chain_count: int,
    ) -> ChainReport:
        thresholds = task.thresholds
        prompts = tuple(
            self.prompt_renderer.render(chain, slice_spec)
            for slice_spec in chain.slices
        )
        states = [_SliceRunState() for _ in chain.slices]
        time_uniform_horizon = self._time_uniform_horizon(task)

        for slice_index, slice_spec in enumerate(chain.slices):
            self._emit_progress(
                self._progress_message(
                    chain_index=chain_index,
                    chain_count=chain_count,
                    chain=chain,
                    slice_index=slice_index,
                    sample_count=0,
                    sample_limit=thresholds.max_samples,
                    successes=0,
                    status="start",
                ),
                transient=False,
            )

        warmup_target = min(
            thresholds.max_samples,
            max(1, thresholds.adaptive_warmup_samples),
        )

        while True:
            warmup_indices = tuple(
                index
                for index, state in enumerate(states)
                if state.samples < warmup_target
            )
            if not warmup_indices:
                break
            selected = warmup_indices[: max(1, thresholds.parallel_samples)]
            self._sample_selected_indices(
                chain=chain,
                selected_indices=selected,
                prompts=prompts,
                states=states,
                chain_index=chain_index,
                chain_count=chain_count,
                thresholds=thresholds,
            )

        while True:
            slice_estimates = tuple(
                self._finalize_slice_estimate(
                    slice_spec=slice_spec,
                    state=states[index],
                    thresholds=thresholds,
                    delta_event=delta_event,
                    time_uniform_horizon=time_uniform_horizon,
                )
                for index, slice_spec in enumerate(chain.slices)
            )
            slice_estimates = self._attach_smoothed_hats(
                slice_estimates,
                thresholds=thresholds,
            )
            boundary_estimates = boundary_estimates_from_slices(
                slice_estimates,
                thresholds,
            )
            local_partition = classify_chain(slice_estimates, boundary_estimates, thresholds)
            slice_index_by_id = {
                slice_estimate.slice_id: index
                for index, slice_estimate in enumerate(slice_estimates)
            }
            relevant_last_index = (
                len(slice_estimates) - 1
                if local_partition.stopping_slice_id is None
                else slice_index_by_id[local_partition.stopping_slice_id]
            )

            candidate_scores: list[tuple[float, int]] = []
            for index in range(relevant_last_index + 1):
                state = states[index]
                estimate = slice_estimates[index]
                if state.samples >= thresholds.max_samples:
                    continue

                if state.samples < thresholds.min_samples:
                    priority = 1000.0 + (thresholds.min_samples - state.samples)
                    candidate_scores.append((priority, index))
                    continue

                own_uncertainty = estimate.total_radius
                left_boundary_radius = (
                    boundary_estimates[index - 1].drop_radius if index > 0 else 0.0
                )
                right_boundary_radius = (
                    boundary_estimates[index].drop_radius
                    if index < len(boundary_estimates)
                    else 0.0
                )
                boundary_uncertainty = max(left_boundary_radius, right_boundary_radius)

                if self._is_slice_resolved(estimate, thresholds) and boundary_uncertainty <= thresholds.drop_threshold:
                    continue

                priority = own_uncertainty + (0.5 * boundary_uncertainty)
                if local_partition.stopping_slice_id == estimate.slice_id:
                    priority += thresholds.drop_threshold
                candidate_scores.append((priority, index))

            if not candidate_scores:
                break

            candidate_scores.sort(key=lambda item: (-item[0], item[1]))
            selected = tuple(
                index for _, index in candidate_scores[: max(1, thresholds.parallel_samples)]
            )
            self._sample_selected_indices(
                chain=chain,
                selected_indices=selected,
                prompts=prompts,
                states=states,
                chain_index=chain_index,
                chain_count=chain_count,
                thresholds=thresholds,
            )

        slice_estimates = tuple(
            self._finalize_slice_estimate(
                slice_spec=slice_spec,
                state=states[index],
                thresholds=thresholds,
                delta_event=delta_event,
                time_uniform_horizon=time_uniform_horizon,
            )
            for index, slice_spec in enumerate(chain.slices)
        )
        slice_estimates = self._attach_smoothed_hats(
            slice_estimates,
            thresholds=thresholds,
        )
        for index, estimate in enumerate(slice_estimates):
            self._emit_progress(
                self._progress_message(
                    chain_index=chain_index,
                    chain_count=chain_count,
                    chain=chain,
                    slice_index=index,
                    sample_count=estimate.samples,
                    sample_limit=thresholds.max_samples,
                    successes=estimate.successes,
                    status=f"done hat={estimate.success_rate_hat:.3f}",
                ),
                transient=False,
            )

        boundary_estimates = boundary_estimates_from_slices(
            slice_estimates,
            thresholds,
        )
        witness_pairs = witness_pairs_from_boundaries(chain.chain_id, boundary_estimates)
        local_partition = classify_chain(slice_estimates, boundary_estimates, thresholds)
        chain_detector_state = detector_state_summary(
            scope="chain",
            witness_family_scope="detected witness pairs in chain",
            witness_pairs=witness_pairs,
            detector_state_budget=thresholds.detector_state_budget,
        )
        return ChainReport(
            chain_id=chain.chain_id,
            slice_estimates=slice_estimates,
            boundary_estimates=boundary_estimates,
            witness_pairs=witness_pairs,
            local_partition=local_partition,
            detector_state=chain_detector_state,
            global_obstructions=(),
            effective_route=local_partition.route,
        )

    def analyze_chain(
        self,
        task: TaskSpec,
        chain: ChainSpec,
        delta_event: float,
        *,
        chain_index: int,
        chain_count: int,
    ) -> ChainReport:
        if str(task.thresholds.sampling_mode) == SamplingMode.ADAPTIVE.value:
            return self._analyze_chain_adaptive(
                task,
                chain,
                delta_event,
                chain_index=chain_index,
                chain_count=chain_count,
            )
        return self._analyze_chain_uniform(
            task,
            chain,
            delta_event,
            chain_index=chain_index,
            chain_count=chain_count,
        )

    def run(self, task: TaskSpec) -> DetectorReport:
        num_slices = sum(len(chain.slices) for chain in task.chains)
        num_boundaries = sum(max(0, len(chain.slices) - 1) for chain in task.chains)
        delta_event = event_delta(task.thresholds.confidence, num_slices, num_boundaries)

        chain_reports = tuple(
            self.analyze_chain(
                task,
                chain,
                delta_event,
                chain_index=index,
                chain_count=len(task.chains),
            )
            for index, chain in enumerate(task.chains)
        )
        all_witness_pairs = tuple(pair for report in chain_reports for pair in report.witness_pairs)
        task_detector_state = detector_state_summary(
            scope="task",
            witness_family_scope="all detected witness pairs across detector run",
            witness_pairs=all_witness_pairs,
            detector_state_budget=task.thresholds.detector_state_budget,
        )

        ambiguity = None
        if task.ambiguity is not None:
            ambiguity = ambiguity_bounds(
                task.ambiguity,
                question_family=self.question_family,
            )

        global_obstructions_for_task = global_obstructions(
            detector_state=task_detector_state,
            ambiguity=ambiguity,
        )

        adjusted_reports = tuple(
            replace(
                report,
                global_obstructions=global_obstructions_for_task,
                effective_route=chain_effective_route(report.local_partition, global_obstructions_for_task),
            )
            for report in chain_reports
        )
        task_partition = summarize_task_partition(
            adjusted_reports,
            global_obstructions_for_task=global_obstructions_for_task,
        )
        analysis_parameters = AnalysisParameters(
            confidence=task.thresholds.confidence,
            delta_event=delta_event,
            safe_success=task.thresholds.safe_success,
            drop_threshold=task.thresholds.drop_threshold,
            oracle_error=task.thresholds.oracle_error,
            ci_half_width=task.thresholds.ci_half_width,
            min_samples=task.thresholds.min_samples,
            max_samples=task.thresholds.max_samples,
            bound_method=str(task.thresholds.bound_method),
            sampling_mode=str(task.thresholds.sampling_mode),
            boundary_mode=str(task.thresholds.boundary_mode),
            detector_state_budget=task.thresholds.detector_state_budget,
        )

        return DetectorReport(
            task_id=task.task_id,
            analysis_parameters=analysis_parameters,
            chains=adjusted_reports,
            witness_pairs=all_witness_pairs,
            task_partition=task_partition,
            detector_state=task_detector_state,
            ambiguity=ambiguity,
            global_obstructions=global_obstructions_for_task,
        )
