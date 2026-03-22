from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Mapping


class RouteLabel(str, Enum):
    SAFE = "safe"
    UNSAFE = "unsafe"


class BoundMethod(str, Enum):
    HOEFFDING = "hoeffding"
    WILSON = "wilson"
    JEFFREYS = "jeffreys"
    CLOPPER_PEARSON = "clopper_pearson"
    AGRESTI_COULL = "agresti_coull"
    EMPIRICAL_BERNSTEIN = "empirical_bernstein"


class SamplingMode(str, Enum):
    UNIFORM = "uniform"
    ADAPTIVE = "adaptive"


class BoundaryMode(str, Enum):
    ADJACENT = "adjacent"
    ISOTONIC = "isotonic"


class LocalUnsafeReason(str, Enum):
    WITNESS_CLIFF = "witness_cliff"
    LOW_SUCCESS = "low_success"
    INSUFFICIENT_EVIDENCE = "insufficient_evidence"


class GlobalObstructionKind(str, Enum):
    STATE_BUDGET_EXCEEDED = "state_budget_exceeded"
    CLARIFICATION_REQUIRED = "clarification_required"


class AmbiguityRoutingStatus(str, Enum):
    SINGLE_SHOT_SAFE = "single_shot_safe"
    SINGLE_SHOT_UNSAFE = "single_shot_unsafe"
    CLARIFIABLE_UNDER_BUDGET = "clarifiable_under_budget"
    CLARIFICATION_BUDGET_EXCEEDED = "clarification_budget_exceeded"
    UNKNOWN_NEEDS_BETTER_QUESTION_FAMILY = "unknown_needs_better_question_family"


class RestrictedQuestionFamilyStatus(str, Enum):
    NOT_REQUESTED = "not_requested"
    NOT_AVAILABLE = "not_available"
    SUPPORT_TOO_LARGE = "support_too_large"
    DEPTH_TOO_LARGE = "depth_too_large"
    COMPUTED = "computed"


@dataclass(frozen=True)
class ThresholdSpec:
    safe_success: float = 0.95
    drop_threshold: float = 0.20
    oracle_error: float = 0.00
    confidence: float = 0.95
    min_samples: int = 32
    max_samples: int = 128
    ci_half_width: float = 0.05
    bound_method: str = BoundMethod.HOEFFDING.value
    sampling_mode: str = SamplingMode.UNIFORM.value
    boundary_mode: str = BoundaryMode.ADJACENT.value
    adaptive_warmup_samples: int = 4
    detector_state_budget: int | None = None
    parallel_samples: int = 1


@dataclass(frozen=True)
class SliceSpec:
    slice_id: str
    premises: tuple[str, ...]
    label: str | None = None
    metadata: Mapping[str, Any] = field(default_factory=dict)


@dataclass(frozen=True)
class ChainSpec:
    chain_id: str
    question: str
    context: str
    slices: tuple[SliceSpec, ...]
    label: str | None = None
    conclusion: str | None = None
    metadata: Mapping[str, Any] = field(default_factory=dict)


@dataclass(frozen=True)
class AmbiguitySpec:
    prior: Mapping[str, float]
    target_success: float = 0.95
    channel_capacity_bits: float = 1.0
    question_budget: int = 0
    restricted_question_budget: int | None = None
    max_exact_support_size: int = 32
    max_exact_depth: int = 8


@dataclass(frozen=True)
class TaskSpec:
    task_id: str
    chains: tuple[ChainSpec, ...]
    thresholds: ThresholdSpec
    ambiguity: AmbiguitySpec | None = None


@dataclass(frozen=True)
class CheckerResult:
    success: bool
    details: Mapping[str, Any] = field(default_factory=dict)


@dataclass(frozen=True)
class SampleTrace:
    sample_index: int
    success: bool
    output_text: str
    checker_details: Mapping[str, Any] = field(default_factory=dict)


@dataclass(frozen=True)
class AnalysisParameters:
    confidence: float
    delta_event: float
    safe_success: float
    drop_threshold: float
    oracle_error: float
    ci_half_width: float
    min_samples: int
    max_samples: int
    bound_method: str
    sampling_mode: str
    boundary_mode: str
    detector_state_budget: int | None


@dataclass(frozen=True)
class SliceEstimate:
    slice_id: str
    premises: tuple[str, ...]
    samples: int
    successes: int
    success_rate_hat: float
    sample_radius: float
    total_radius: float
    success_lower_bound: float
    success_upper_bound: float
    meets_safe_success: bool
    reached_evidence_threshold: bool
    smoothed_success_rate_hat: float | None = None
    traces: tuple[SampleTrace, ...] = ()


@dataclass(frozen=True)
class BoundaryEstimate:
    from_slice_id: str
    to_slice_id: str
    lower_premises: tuple[str, ...]
    upper_premises: tuple[str, ...]
    drop_hat: float
    drop_radius: float
    drop_lower_bound: float
    drop_upper_bound: float
    significant_witness_cliff: bool
    boundary_mode: str = BoundaryMode.ADJACENT.value
    left_effective_success_rate: float | None = None
    right_effective_success_rate: float | None = None


@dataclass(frozen=True)
class WitnessPair:
    chain_id: str
    from_slice_id: str
    to_slice_id: str
    lower_premises: tuple[str, ...]
    upper_premises: tuple[str, ...]
    drop_hat: float
    drop_lower_bound: float


@dataclass(frozen=True)
class ChainLocalPartition:
    route: RouteLabel
    safe_prefix_length: int
    safe_slice_ids: tuple[str, ...]
    unsafe_slice_ids: tuple[str, ...]
    stopping_slice_id: str | None = None
    local_reason: LocalUnsafeReason | None = None
    local_reason_details: Mapping[str, Any] = field(default_factory=dict)


@dataclass(frozen=True)
class DetectorStateSummary:
    scope: str
    witness_family_scope: str
    witness_pair_count: int
    medim_lower_bound: int
    detector_state_budget: int | None
    budget_exceeded: bool | None


@dataclass(frozen=True)
class GlobalObstruction:
    kind: GlobalObstructionKind
    details: Mapping[str, Any] = field(default_factory=dict)


@dataclass(frozen=True)
class RestrictedQuestionFamilyReport:
    question_budget: int
    status: RestrictedQuestionFamilyStatus
    success_upper_bound: float | None
    details: Mapping[str, Any] = field(default_factory=dict)


@dataclass(frozen=True)
class AmbiguityRoutingInterpretation:
    status: AmbiguityRoutingStatus
    automation_safe: bool
    clarification_required: bool
    question_budget: int
    necessary_binary_clarifications: int
    details: Mapping[str, Any] = field(default_factory=dict)


@dataclass(frozen=True)
class AmbiguityReport:
    support_size: int
    target_success: float
    channel_capacity_bits: float
    question_budget: int
    single_shot_success_upper_bound: float
    unrestricted_success_upper_bound_at_question_budget: float
    necessary_binary_clarifications: int
    exact_identification_clarifications: int
    fano_lower_bound_rounds: int
    restricted_question_family: RestrictedQuestionFamilyReport
    routing: AmbiguityRoutingInterpretation


@dataclass(frozen=True)
class ChainReport:
    chain_id: str
    slice_estimates: tuple[SliceEstimate, ...]
    boundary_estimates: tuple[BoundaryEstimate, ...]
    witness_pairs: tuple[WitnessPair, ...]
    local_partition: ChainLocalPartition
    detector_state: DetectorStateSummary
    global_obstructions: tuple[GlobalObstruction, ...]
    effective_route: RouteLabel


@dataclass(frozen=True)
class TaskPartition:
    route: RouteLabel
    safe_chain_ids: tuple[str, ...]
    unsafe_chain_ids: tuple[str, ...]
    locally_safe_chain_ids: tuple[str, ...]
    locally_unsafe_chain_ids: tuple[str, ...]
    globally_blocked_chain_ids: tuple[str, ...]
    global_obstruction_kinds: tuple[GlobalObstructionKind, ...]
    global_obstruction_routing_statuses: tuple[str, ...]


@dataclass(frozen=True)
class DetectorReport:
    task_id: str
    analysis_parameters: AnalysisParameters
    chains: tuple[ChainReport, ...]
    witness_pairs: tuple[WitnessPair, ...]
    task_partition: TaskPartition
    detector_state: DetectorStateSummary
    ambiguity: AmbiguityReport | None
    global_obstructions: tuple[GlobalObstruction, ...]
