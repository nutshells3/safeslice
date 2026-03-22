from __future__ import annotations

from itertools import combinations

from .models import (
    AmbiguityReport,
    BoundaryMode,
    BoundaryEstimate,
    ChainLocalPartition,
    ChainReport,
    DetectorStateSummary,
    GlobalObstruction,
    GlobalObstructionKind,
    LocalUnsafeReason,
    RouteLabel,
    SliceEstimate,
    TaskPartition,
    ThresholdSpec,
    WitnessPair,
)
from .stats import drop_bounds


def witness_pairs_from_boundaries(
    chain_id: str, boundaries: tuple[BoundaryEstimate, ...]
) -> tuple[WitnessPair, ...]:
    pairs = []
    for boundary in boundaries:
        if not boundary.significant_witness_cliff:
            continue
        pairs.append(
            WitnessPair(
                chain_id=chain_id,
                from_slice_id=boundary.from_slice_id,
                to_slice_id=boundary.to_slice_id,
                lower_premises=boundary.lower_premises,
                upper_premises=boundary.upper_premises,
                drop_hat=boundary.drop_hat,
                drop_lower_bound=boundary.drop_lower_bound,
            )
        )
    return tuple(pairs)


def empirical_medim_lower_bound(witness_pairs: tuple[WitnessPair, ...]) -> int:
    if not witness_pairs:
        return 0

    def upper(pair: WitnessPair) -> frozenset[str]:
        return frozenset(pair.upper_premises)

    def incomparable(left: WitnessPair, right: WitnessPair) -> bool:
        left_upper = upper(left)
        right_upper = upper(right)
        return not (left_upper <= right_upper or right_upper <= left_upper)

    if len(witness_pairs) <= 20:
        best = 1
        for size in range(2, len(witness_pairs) + 1):
            for combo in combinations(witness_pairs, size):
                if all(incomparable(x, y) for x, y in combinations(combo, 2)):
                    best = size
        return best

    selected: list[WitnessPair] = []
    for pair in sorted(witness_pairs, key=lambda item: len(item.upper_premises)):
        if all(incomparable(pair, chosen) for chosen in selected):
            selected.append(pair)
    return len(selected)


def detector_state_summary(
    *,
    scope: str,
    witness_family_scope: str,
    witness_pairs: tuple[WitnessPair, ...],
    detector_state_budget: int | None,
) -> DetectorStateSummary:
    medim_lower_bound = empirical_medim_lower_bound(witness_pairs)
    return DetectorStateSummary(
        scope=scope,
        witness_family_scope=witness_family_scope,
        witness_pair_count=len(witness_pairs),
        medim_lower_bound=medim_lower_bound,
        detector_state_budget=detector_state_budget,
        budget_exceeded=(
            medim_lower_bound > detector_state_budget
            if detector_state_budget is not None
            else None
        ),
    )


def isotonic_nonincreasing(values: tuple[float, ...], weights: tuple[float, ...]) -> tuple[float, ...]:
    if len(values) != len(weights):
        raise ValueError("values and weights must have the same length")
    if not values:
        return ()

    blocks: list[dict[str, float | int]] = []
    for index, (value, weight) in enumerate(zip(values, weights)):
        block = {
            "start": index,
            "end": index,
            "weight": max(float(weight), 1.0),
            "mean": float(value),
        }
        blocks.append(block)
        while len(blocks) >= 2 and float(blocks[-2]["mean"]) < float(blocks[-1]["mean"]):
            right = blocks.pop()
            left = blocks.pop()
            total_weight = float(left["weight"]) + float(right["weight"])
            merged = {
                "start": int(left["start"]),
                "end": int(right["end"]),
                "weight": total_weight,
                "mean": (
                    float(left["mean"]) * float(left["weight"])
                    + float(right["mean"]) * float(right["weight"])
                )
                / total_weight,
            }
            blocks.append(merged)

    fitted = [0.0] * len(values)
    for block in blocks:
        start = int(block["start"])
        end = int(block["end"])
        mean = float(block["mean"])
        for index in range(start, end + 1):
            fitted[index] = mean
    return tuple(fitted)


def effective_success_hats(
    slices: tuple[SliceEstimate, ...],
    *,
    boundary_mode: str,
) -> tuple[float, ...]:
    if boundary_mode == BoundaryMode.ISOTONIC.value:
        return isotonic_nonincreasing(
            tuple(slice_estimate.success_rate_hat for slice_estimate in slices),
            tuple(max(1.0, float(slice_estimate.samples)) for slice_estimate in slices),
        )
    return tuple(slice_estimate.success_rate_hat for slice_estimate in slices)


def boundary_estimates_from_slices(
    slices: tuple[SliceEstimate, ...],
    thresholds: ThresholdSpec,
) -> tuple[BoundaryEstimate, ...]:
    effective_hats = effective_success_hats(
        slices,
        boundary_mode=str(thresholds.boundary_mode),
    )
    boundaries: list[BoundaryEstimate] = []
    for index in range(len(slices) - 1):
        left = slices[index]
        right = slices[index + 1]
        left_hat = effective_hats[index]
        right_hat = effective_hats[index + 1]
        drop_hat, drop_radius, drop_lower_bound, drop_upper_bound = drop_bounds(
            left_hat,
            right_hat,
            left_lower_bound=left.success_lower_bound,
            left_upper_bound=left.success_upper_bound,
            right_lower_bound=right.success_lower_bound,
            right_upper_bound=right.success_upper_bound,
        )
        boundaries.append(
            BoundaryEstimate(
                from_slice_id=left.slice_id,
                to_slice_id=right.slice_id,
                lower_premises=left.premises,
                upper_premises=right.premises,
                drop_hat=drop_hat,
                drop_radius=drop_radius,
                drop_lower_bound=drop_lower_bound,
                drop_upper_bound=drop_upper_bound,
                significant_witness_cliff=drop_lower_bound >= thresholds.drop_threshold,
                boundary_mode=str(thresholds.boundary_mode),
                left_effective_success_rate=left_hat,
                right_effective_success_rate=right_hat,
            )
        )
    return tuple(boundaries)


def classify_chain(
    slices: tuple[SliceEstimate, ...],
    boundaries: tuple[BoundaryEstimate, ...],
    thresholds: ThresholdSpec,
) -> ChainLocalPartition:
    safe_prefix_length = 0
    stopping_slice_id = None
    local_reason = None
    local_reason_details: dict[str, object] = {}

    for index, slice_estimate in enumerate(slices):
        if index > 0 and boundaries[index - 1].significant_witness_cliff:
            boundary = boundaries[index - 1]
            stopping_slice_id = slice_estimate.slice_id
            local_reason = LocalUnsafeReason.WITNESS_CLIFF
            local_reason_details = {
                "from_slice_id": boundary.from_slice_id,
                "to_slice_id": boundary.to_slice_id,
                "drop_lower_bound": boundary.drop_lower_bound,
                "drop_threshold": thresholds.drop_threshold,
            }
            break

        if slice_estimate.meets_safe_success:
            safe_prefix_length += 1
            continue

        if slice_estimate.success_upper_bound >= thresholds.safe_success:
            stopping_slice_id = slice_estimate.slice_id
            local_reason = LocalUnsafeReason.INSUFFICIENT_EVIDENCE
            local_reason_details = {
                "slice_id": slice_estimate.slice_id,
                "success_lower_bound": slice_estimate.success_lower_bound,
                "success_upper_bound": slice_estimate.success_upper_bound,
                "safe_success": thresholds.safe_success,
                "total_radius": slice_estimate.total_radius,
                "ci_half_width": thresholds.ci_half_width,
                "reached_evidence_threshold": slice_estimate.reached_evidence_threshold,
            }
            break

        stopping_slice_id = slice_estimate.slice_id
        local_reason = LocalUnsafeReason.LOW_SUCCESS
        local_reason_details = {
            "slice_id": slice_estimate.slice_id,
            "success_lower_bound": slice_estimate.success_lower_bound,
            "success_upper_bound": slice_estimate.success_upper_bound,
            "safe_success": thresholds.safe_success,
        }
        break

    safe_slice_ids = tuple(slice_estimate.slice_id for slice_estimate in slices[:safe_prefix_length])
    unsafe_slice_ids = tuple(slice_estimate.slice_id for slice_estimate in slices[safe_prefix_length:])
    route = RouteLabel.SAFE if safe_prefix_length == len(slices) else RouteLabel.UNSAFE
    return ChainLocalPartition(
        route=route,
        safe_prefix_length=safe_prefix_length,
        safe_slice_ids=safe_slice_ids,
        unsafe_slice_ids=unsafe_slice_ids,
        stopping_slice_id=stopping_slice_id,
        local_reason=local_reason,
        local_reason_details=local_reason_details,
    )


def global_obstructions(
    *,
    detector_state: DetectorStateSummary,
    ambiguity: AmbiguityReport | None,
) -> tuple[GlobalObstruction, ...]:
    obstructions: list[GlobalObstruction] = []

    if detector_state.budget_exceeded:
        obstructions.append(
            GlobalObstruction(
                kind=GlobalObstructionKind.STATE_BUDGET_EXCEEDED,
                details={
                    "scope": detector_state.scope,
                    "medim_lower_bound": detector_state.medim_lower_bound,
                    "detector_state_budget": detector_state.detector_state_budget,
                    "witness_family_scope": detector_state.witness_family_scope,
                },
            )
        )

    if ambiguity is not None and ambiguity.routing.clarification_required:
        obstructions.append(
            GlobalObstruction(
                kind=GlobalObstructionKind.CLARIFICATION_REQUIRED,
                details={
                    "routing_status": ambiguity.routing.status,
                    "question_budget": ambiguity.routing.question_budget,
                    "necessary_binary_clarifications": ambiguity.routing.necessary_binary_clarifications,
                    "single_shot_success_upper_bound": ambiguity.single_shot_success_upper_bound,
                    "target_success": ambiguity.target_success,
                },
            )
        )

    return tuple(obstructions)


def chain_effective_route(
    local_partition: ChainLocalPartition,
    global_obstructions_for_task: tuple[GlobalObstruction, ...],
) -> RouteLabel:
    if local_partition.route == RouteLabel.UNSAFE:
        return RouteLabel.UNSAFE
    if global_obstructions_for_task:
        return RouteLabel.UNSAFE
    return RouteLabel.SAFE


def summarize_task_partition(
    chain_reports: tuple[ChainReport, ...],
    *,
    global_obstructions_for_task: tuple[GlobalObstruction, ...],
) -> TaskPartition:
    locally_safe_chain_ids = tuple(
        report.chain_id for report in chain_reports if report.local_partition.route == RouteLabel.SAFE
    )
    locally_unsafe_chain_ids = tuple(
        report.chain_id for report in chain_reports if report.local_partition.route == RouteLabel.UNSAFE
    )
    safe_chain_ids = tuple(report.chain_id for report in chain_reports if report.effective_route == RouteLabel.SAFE)
    unsafe_chain_ids = tuple(
        report.chain_id for report in chain_reports if report.effective_route == RouteLabel.UNSAFE
    )
    globally_blocked_chain_ids = tuple(
        report.chain_id
        for report in chain_reports
        if report.local_partition.route == RouteLabel.SAFE and report.effective_route == RouteLabel.UNSAFE
    )
    route = (
        RouteLabel.SAFE
        if not global_obstructions_for_task
        and all(report.local_partition.route == RouteLabel.SAFE for report in chain_reports)
        else RouteLabel.UNSAFE
    )
    global_obstruction_routing_statuses = tuple(
        getattr(obstruction.details["routing_status"], "value", str(obstruction.details["routing_status"]))
        for obstruction in global_obstructions_for_task
        if "routing_status" in obstruction.details
    )
    return TaskPartition(
        route=route,
        safe_chain_ids=safe_chain_ids,
        unsafe_chain_ids=unsafe_chain_ids,
        locally_safe_chain_ids=locally_safe_chain_ids,
        locally_unsafe_chain_ids=locally_unsafe_chain_ids,
        globally_blocked_chain_ids=globally_blocked_chain_ids,
        global_obstruction_kinds=tuple(obstruction.kind for obstruction in global_obstructions_for_task),
        global_obstruction_routing_statuses=global_obstruction_routing_statuses,
    )
