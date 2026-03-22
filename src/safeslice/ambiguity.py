from __future__ import annotations

import math
from functools import lru_cache
from typing import FrozenSet, Mapping

from .interfaces import QuestionFamily
from .models import (
    AmbiguityReport,
    AmbiguityRoutingInterpretation,
    AmbiguityRoutingStatus,
    AmbiguitySpec,
    RestrictedQuestionFamilyReport,
    RestrictedQuestionFamilyStatus,
)


def normalize_prior(prior: Mapping[str, float]) -> dict[str, float]:
    total = sum(float(value) for value in prior.values())
    if total <= 0.0:
        raise ValueError("ambiguity prior must have positive total mass")
    return {key: float(value) / total for key, value in prior.items() if float(value) > 0.0}


def binary_entropy(probability: float) -> float:
    if probability <= 0.0 or probability >= 1.0:
        return 0.0
    return -(probability * math.log2(probability) + (1.0 - probability) * math.log2(1.0 - probability))


def entropy(prior: Mapping[str, float]) -> float:
    return -sum(probability * math.log2(probability) for probability in prior.values() if probability > 0.0)


def single_shot_upper_bound(prior: Mapping[str, float]) -> float:
    normalized = normalize_prior(prior)
    return max(normalized.values(), default=0.0)


def succ_questions_unrestricted(prior: Mapping[str, float], questions: int) -> float:
    normalized = normalize_prior(prior)
    slots = 2**questions
    top_masses = sorted(normalized.values(), reverse=True)[:slots]
    return min(1.0, sum(top_masses))


def necessary_rounds_partition_bound(
    prior: Mapping[str, float],
    target_success: float,
    *,
    channel_capacity_bits: float = 1.0,
) -> int:
    if target_success <= 0.0:
        return 0
    if channel_capacity_bits <= 0.0:
        raise ValueError("channel_capacity_bits must be positive")
    max_mass = single_shot_upper_bound(prior)
    return max(0, math.ceil(math.log2(target_success / max_mass) / channel_capacity_bits))


def exact_identification_rounds(
    prior: Mapping[str, float], *, channel_capacity_bits: float = 1.0
) -> int:
    support_size = len(normalize_prior(prior))
    if support_size <= 1:
        return 0
    if channel_capacity_bits <= 0.0:
        raise ValueError("channel_capacity_bits must be positive")
    return math.ceil(math.log2(support_size) / channel_capacity_bits)


def fano_lower_bound_rounds(
    prior: Mapping[str, float],
    target_success: float,
    *,
    channel_capacity_bits: float = 1.0,
) -> int:
    normalized = normalize_prior(prior)
    support_size = len(normalized)
    if support_size <= 1:
        return 0
    if channel_capacity_bits <= 0.0:
        raise ValueError("channel_capacity_bits must be positive")
    epsilon = max(0.0, min(1.0, 1.0 - target_success))
    numerator = entropy(normalized) - binary_entropy(epsilon) - epsilon * math.log2(support_size - 1)
    return max(0, math.ceil(numerator / channel_capacity_bits))


def restricted_success_upper_bound(
    prior: Mapping[str, float], family: QuestionFamily, questions: int
) -> float:
    normalized = normalize_prior(prior)
    support = frozenset(normalized)

    @lru_cache(maxsize=None)
    def recurse(active_keys: FrozenSet[str], depth: int) -> float:
        if not active_keys:
            return 0.0

        leaf_value = max(normalized[key] for key in active_keys)
        if depth == 0:
            return leaf_value

        best = leaf_value
        for question_id in family.questions(active_keys):
            false_keys, true_keys = family.split(active_keys, question_id)
            if false_keys == active_keys or true_keys == active_keys:
                continue
            candidate = recurse(false_keys, depth - 1) + recurse(true_keys, depth - 1)
            if candidate > best:
                best = candidate
        return min(1.0, best)

    return recurse(support, questions)


def restricted_question_family_report(
    spec: AmbiguitySpec,
    support_size: int,
    *,
    question_family: QuestionFamily | None,
    normalized_prior: Mapping[str, float],
) -> RestrictedQuestionFamilyReport:
    budget = spec.restricted_question_budget
    if budget is None:
        return RestrictedQuestionFamilyReport(
            question_budget=spec.question_budget,
            status=RestrictedQuestionFamilyStatus.NOT_REQUESTED,
            success_upper_bound=None,
            details={},
        )

    if question_family is None:
        return RestrictedQuestionFamilyReport(
            question_budget=budget,
            status=RestrictedQuestionFamilyStatus.NOT_AVAILABLE,
            success_upper_bound=None,
            details={},
        )

    if support_size > spec.max_exact_support_size:
        return RestrictedQuestionFamilyReport(
            question_budget=budget,
            status=RestrictedQuestionFamilyStatus.SUPPORT_TOO_LARGE,
            success_upper_bound=None,
            details={
                "support_size": support_size,
                "max_exact_support_size": spec.max_exact_support_size,
            },
        )

    if budget > spec.max_exact_depth:
        return RestrictedQuestionFamilyReport(
            question_budget=budget,
            status=RestrictedQuestionFamilyStatus.DEPTH_TOO_LARGE,
            success_upper_bound=None,
            details={
                "question_budget": budget,
                "max_exact_depth": spec.max_exact_depth,
            },
        )

    return RestrictedQuestionFamilyReport(
        question_budget=budget,
        status=RestrictedQuestionFamilyStatus.COMPUTED,
        success_upper_bound=restricted_success_upper_bound(normalized_prior, question_family, budget),
        details={},
    )


def ambiguity_routing_interpretation(
    *,
    spec: AmbiguitySpec,
    single_shot: float,
    necessary_binary_clarifications: int,
    unrestricted_upper_bound: float,
    restricted_report: RestrictedQuestionFamilyReport,
) -> AmbiguityRoutingInterpretation:
    if single_shot >= spec.target_success:
        status = AmbiguityRoutingStatus.SINGLE_SHOT_SAFE
    elif spec.question_budget <= 0:
        status = AmbiguityRoutingStatus.SINGLE_SHOT_UNSAFE
    elif necessary_binary_clarifications > spec.question_budget:
        status = AmbiguityRoutingStatus.CLARIFICATION_BUDGET_EXCEEDED
    elif (
        restricted_report.status == RestrictedQuestionFamilyStatus.COMPUTED
        and restricted_report.success_upper_bound is not None
        and restricted_report.success_upper_bound < spec.target_success
    ):
        status = AmbiguityRoutingStatus.UNKNOWN_NEEDS_BETTER_QUESTION_FAMILY
    else:
        status = AmbiguityRoutingStatus.CLARIFIABLE_UNDER_BUDGET

    return AmbiguityRoutingInterpretation(
        status=status,
        automation_safe=status == AmbiguityRoutingStatus.SINGLE_SHOT_SAFE,
        clarification_required=status != AmbiguityRoutingStatus.SINGLE_SHOT_SAFE,
        question_budget=spec.question_budget,
        necessary_binary_clarifications=necessary_binary_clarifications,
        details={
            "target_success": spec.target_success,
            "single_shot_success_upper_bound": single_shot,
            "unrestricted_success_upper_bound_at_question_budget": unrestricted_upper_bound,
            "restricted_question_family_status": restricted_report.status,
            "restricted_success_upper_bound": restricted_report.success_upper_bound,
        },
    )


def ambiguity_bounds(
    spec: AmbiguitySpec,
    *,
    question_family: QuestionFamily | None = None,
) -> AmbiguityReport:
    normalized = normalize_prior(spec.prior)
    support_size = len(normalized)
    single_shot = single_shot_upper_bound(normalized)
    unrestricted = succ_questions_unrestricted(normalized, spec.question_budget)
    necessary_binary_clarifications = necessary_rounds_partition_bound(
        normalized,
        spec.target_success,
        channel_capacity_bits=spec.channel_capacity_bits,
    )
    restricted_report = restricted_question_family_report(
        spec,
        support_size,
        question_family=question_family,
        normalized_prior=normalized,
    )
    routing = ambiguity_routing_interpretation(
        spec=spec,
        single_shot=single_shot,
        necessary_binary_clarifications=necessary_binary_clarifications,
        unrestricted_upper_bound=unrestricted,
        restricted_report=restricted_report,
    )
    return AmbiguityReport(
        support_size=support_size,
        target_success=spec.target_success,
        channel_capacity_bits=spec.channel_capacity_bits,
        question_budget=spec.question_budget,
        single_shot_success_upper_bound=single_shot,
        unrestricted_success_upper_bound_at_question_budget=unrestricted,
        necessary_binary_clarifications=necessary_binary_clarifications,
        exact_identification_clarifications=exact_identification_rounds(
            normalized,
            channel_capacity_bits=spec.channel_capacity_bits,
        ),
        fano_lower_bound_rounds=fano_lower_bound_rounds(
            normalized,
            spec.target_success,
            channel_capacity_bits=spec.channel_capacity_bits,
        ),
        restricted_question_family=restricted_report,
        routing=routing,
    )
