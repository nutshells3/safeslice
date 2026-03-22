from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Iterable, Mapping, Sequence

from .models import AmbiguitySpec, ChainSpec, SliceSpec, TaskSpec, ThresholdSpec


DEFAULT_RELATION_TYPES = (
    "depends_on",
    "decomposes_into",
    "refines",
    "specializes",
)

ACTIVE_RELATION_STATUSES = {"active", "provisional"}


@dataclass(frozen=True)
class ClaimGraphAdapterConfig:
    relation_types: tuple[str, ...] = DEFAULT_RELATION_TYPES
    include_baseline_slice: bool = True
    include_scope_conditions_in_context: bool = True
    include_semantics_guard_in_context: bool = True


def _claim_index(claim_graph: Mapping[str, Any]) -> dict[str, Mapping[str, Any]]:
    claims = claim_graph.get("claims") or []
    return {
        str(claim.get("claim_id") or ""): claim
        for claim in claims
        if str(claim.get("claim_id") or "")
    }


def _active_dependency_edges(
    claim_graph: Mapping[str, Any],
    *,
    relation_types: Iterable[str],
) -> tuple[dict[str, list[str]], dict[tuple[str, str], list[str]]]:
    allowed_types = {str(item) for item in relation_types}
    outgoing: dict[str, list[str]] = {}
    relation_ids: dict[tuple[str, str], list[str]] = {}
    for relation in claim_graph.get("relations") or []:
        relation_type = str(relation.get("relation_type") or "")
        status = str(relation.get("status") or "active")
        if relation_type not in allowed_types or status not in ACTIVE_RELATION_STATUSES:
            continue
        source_id = str(relation.get("from_claim_id") or "")
        target_id = str(relation.get("to_claim_id") or "")
        relation_id = str(relation.get("relation_id") or "")
        if not source_id or not target_id:
            continue
        outgoing.setdefault(source_id, []).append(target_id)
        relation_ids.setdefault((source_id, target_id), []).append(relation_id)
    for key in outgoing:
        outgoing[key] = sorted(set(outgoing[key]))
    for key in relation_ids:
        relation_ids[key] = sorted(set(relation_ids[key]))
    return outgoing, relation_ids


def _target_claim_ids(
    claim_graph: Mapping[str, Any],
    *,
    explicit_target_claim_ids: Sequence[str] | None,
) -> tuple[str, ...]:
    if explicit_target_claim_ids:
        return tuple(str(item) for item in explicit_target_claim_ids if str(item))
    roots = tuple(str(item) for item in list(claim_graph.get("root_claim_ids") or []) if str(item))
    if roots:
        return roots
    return ()


def _claim_statement(claim: Mapping[str, Any]) -> str:
    for key in ("normalized_statement", "nl_statement", "title"):
        value = str(claim.get(key) or "").strip()
        if value:
            return value
    return "unlabeled claim"


def _claim_premise_text(claim: Mapping[str, Any]) -> str:
    claim_id = str(claim.get("claim_id") or "")
    title = str(claim.get("title") or claim_id or "claim")
    statement = _claim_statement(claim)
    return f"{claim_id} | {title} | {statement}"


def _context_lines_for_claim(
    claim_graph: Mapping[str, Any],
    claim: Mapping[str, Any],
    *,
    include_scope_conditions: bool,
    include_semantics_guard: bool,
) -> list[str]:
    lines = []
    graph_description = str(claim_graph.get("description") or "").strip()
    if graph_description:
        lines.append(f"graph: {graph_description}")

    title = str(claim.get("title") or "").strip()
    if title:
        lines.append(f"target: {title}")

    intent_gloss = str(claim.get("intent_gloss") or "").strip()
    if intent_gloss:
        lines.append(f"intent: {intent_gloss}")

    scope = dict(claim.get("scope") or {})
    domain = str(scope.get("domain") or "").strip()
    modality = str(scope.get("modality") or "").strip()
    if domain or modality:
        lines.append(f"scope: domain={domain or 'unknown'} modality={modality or 'unknown'}")

    if include_scope_conditions:
        included = [str(item) for item in list(scope.get("included_conditions") or []) if str(item)]
        excluded = [str(item) for item in list(scope.get("excluded_conditions") or []) if str(item)]
        if included:
            lines.append("included_conditions: " + "; ".join(included))
        if excluded:
            lines.append("excluded_conditions: " + "; ".join(excluded))

    if include_semantics_guard:
        guard = dict(claim.get("semantics_guard") or {})
        must_preserve = [str(item) for item in list(guard.get("must_preserve") or []) if str(item)]
        forbidden_weakenings = [str(item) for item in list(guard.get("forbidden_weakenings") or []) if str(item)]
        if must_preserve:
            lines.append("must_preserve: " + "; ".join(must_preserve))
        if forbidden_weakenings:
            lines.append("forbidden_weakenings: " + "; ".join(forbidden_weakenings))
    return lines


def _dependency_layers(
    target_claim_id: str,
    *,
    outgoing_edges: Mapping[str, list[str]],
) -> tuple[tuple[str, ...], ...]:
    seen: set[str] = set()
    layers: list[tuple[str, ...]] = []
    frontier = tuple(outgoing_edges.get(target_claim_id, []))
    while frontier:
        layer = tuple(claim_id for claim_id in frontier if claim_id not in seen)
        if not layer:
            break
        layers.append(tuple(sorted(layer)))
        seen.update(layer)
        next_frontier: list[str] = []
        for claim_id in layer:
            next_frontier.extend(outgoing_edges.get(claim_id, []))
        frontier = tuple(sorted(set(next_frontier)))
    return tuple(layers)


def chain_from_claim_graph(
    claim_graph: Mapping[str, Any],
    *,
    target_claim_id: str,
    config: ClaimGraphAdapterConfig | None = None,
) -> ChainSpec:
    adapter_config = config or ClaimGraphAdapterConfig()
    claims = _claim_index(claim_graph)
    claim = claims.get(target_claim_id)
    if claim is None:
        raise KeyError(f"Unknown target claim_id: {target_claim_id}")

    outgoing_edges, relation_ids = _active_dependency_edges(
        claim_graph,
        relation_types=adapter_config.relation_types,
    )
    layers = _dependency_layers(
        target_claim_id,
        outgoing_edges=outgoing_edges,
    )

    slices: list[SliceSpec] = []
    cumulative_claim_ids: list[str] = []

    if adapter_config.include_baseline_slice:
        slices.append(
            SliceSpec(
                slice_id=f"{target_claim_id}.n0",
                premises=(),
                label="baseline",
                metadata={
                    "claim_graph_graph_id": str(claim_graph.get("graph_id") or ""),
                    "claim_graph_project_id": str(claim_graph.get("project_id") or ""),
                    "target_claim_id": target_claim_id,
                    "layer_index": 0,
                    "dependency_claim_ids": (),
                    "dependency_relation_ids": (),
                },
            )
        )

    for layer_index, layer_claim_ids in enumerate(layers, start=1):
        cumulative_claim_ids.extend(layer_claim_ids)
        premise_texts = tuple(
            _claim_premise_text(claims[claim_id])
            for claim_id in cumulative_claim_ids
            if claim_id in claims
        )
        dependency_relation_ids = tuple(
            relation_id
            for source_id in ([target_claim_id] + cumulative_claim_ids)
            for dependency_id in outgoing_edges.get(source_id, [])
            if dependency_id in cumulative_claim_ids
            for relation_id in relation_ids.get((source_id, dependency_id), [])
        )
        slices.append(
            SliceSpec(
                slice_id=f"{target_claim_id}.n{layer_index}",
                premises=premise_texts,
                label=f"dependency_layer_{layer_index}",
                metadata={
                    "claim_graph_graph_id": str(claim_graph.get("graph_id") or ""),
                    "claim_graph_project_id": str(claim_graph.get("project_id") or ""),
                    "target_claim_id": target_claim_id,
                    "layer_index": layer_index,
                    "dependency_claim_ids": tuple(cumulative_claim_ids),
                    "dependency_relation_ids": dependency_relation_ids,
                },
            )
        )

    context = "\n".join(
        _context_lines_for_claim(
            claim_graph,
            claim,
            include_scope_conditions=adapter_config.include_scope_conditions_in_context,
            include_semantics_guard=adapter_config.include_semantics_guard_in_context,
        )
    )

    if not slices:
        slices.append(
            SliceSpec(
                slice_id=f"{target_claim_id}.n0",
                premises=(),
                label="baseline",
                metadata={
                    "claim_graph_graph_id": str(claim_graph.get("graph_id") or ""),
                    "claim_graph_project_id": str(claim_graph.get("project_id") or ""),
                    "target_claim_id": target_claim_id,
                    "layer_index": 0,
                    "dependency_claim_ids": (),
                    "dependency_relation_ids": (),
                },
            )
        )

    return ChainSpec(
        chain_id=f"claim_graph::{target_claim_id}",
        question=_claim_statement(claim),
        context=context,
        slices=tuple(slices),
        label=str(claim.get("title") or target_claim_id),
        conclusion=target_claim_id,
        metadata={
            "adapter": "orchestration_claim_graph",
            "graph_id": str(claim_graph.get("graph_id") or ""),
            "project_id": str(claim_graph.get("project_id") or ""),
            "target_claim_id": target_claim_id,
            "root_claim_ids": tuple(str(item) for item in list(claim_graph.get("root_claim_ids") or [])),
            "relation_types": tuple(adapter_config.relation_types),
        },
    )


def task_from_claim_graph(
    claim_graph: Mapping[str, Any],
    *,
    thresholds: ThresholdSpec | None = None,
    ambiguity: AmbiguitySpec | None = None,
    target_claim_ids: Sequence[str] | None = None,
    config: ClaimGraphAdapterConfig | None = None,
) -> TaskSpec:
    adapter_config = config or ClaimGraphAdapterConfig()
    targets = _target_claim_ids(
        claim_graph,
        explicit_target_claim_ids=target_claim_ids,
    )
    if not targets:
        raise ValueError("Claim graph has no root_claim_ids and no explicit target_claim_ids were provided.")

    chains = tuple(
        chain_from_claim_graph(
            claim_graph,
            target_claim_id=target_claim_id,
            config=adapter_config,
        )
        for target_claim_id in targets
    )
    task_id = str(claim_graph.get("graph_id") or claim_graph.get("project_id") or "claim_graph_task")
    return TaskSpec(
        task_id=f"claim_graph::{task_id}",
        chains=chains,
        thresholds=thresholds or ThresholdSpec(),
        ambiguity=ambiguity,
    )
