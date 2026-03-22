# safeslice

`safeslice` is a theorem-backed core library for safe-slice detection.

This repository contains only the detector algorithm, the data model it
operates on, and the abstract interfaces needed to plug in a sampler, checker,
and optional clarification-question family.

It is intended as a theorem-driven engineering primitive. The core quantities
are not arbitrary heuristics; they are the computational counterparts of the
Lean results in `lean/Problem1.lean` and `lean/Problem2.lean`, turned into a
benchmark-grounded robustness certificate for claim decompositions and other
natural-language verification tasks.

The integration direction is now fixed: the main adapter surface should consume
`orchestration-assurance-engine` claim decompositions directly.

## What It Does

Given:

- a task made of premise-expansion chains
- per-run thresholds
- a sampler that produces outputs for each slice
- a checker that marks outputs as success/failure
- optional ambiguity metadata and a restricted question family

the library computes:

- per-slice success estimates with confidence bounds
- significant witness cliffs between adjacent slices
- safe vs unsafe chain partitions
- detector-state budget pressure
- ambiguity routing / clarification feasibility
- a task-level safe/unsafe partition

## Lean Correspondence

The folder `lean/` carries the theorem source this implementation is based on.

- `Problem1.lean`: witness-transition and detector-basis lower-bound results
- `Problem2.lean`: clarification-budget benchmark and restricted-family upper bounds

The code mirrors those roles:

- `policy.py`: witness-pair extraction, empirical MEDIM lower bound, local/global obstruction logic
- `ambiguity.py`: clarification-budget bounds, unrestricted benchmark, restricted-family upper bounds
- `pipeline.py`: detector pass that composes the two sides into one report

So the intended semantics are:

- Lean proves the exact structural theorems
- Python computes the theorem-shaped quantities on finite sampled runs

## Engineering Interpretation

The intended engineering use is benchmark-grounded verification, not abstract
truth-oracle access.

Suppose:

- `n = 0` is the unsliced or baseline version of a claim/question
- `y*(x) in {0, 1}` is a ground-truth benchmark label for instance `x`
- `A_{m,i}^{(n)}` is the `i`-th sampled answer from model `m` on slice level `n`
- `C_n(A)` is the checker result for that answer at slice level `n`

Then the core quantity is the slice success probability

```text
p_{m,n} = Pr[C_n(A_{m}^{(n)}) = 1]
```

For the benchmark-grounded baseline `n = 0`, this becomes the empirical
correctness rate of a model against known answers:

```text
p_{m,0} = Pr[C_0(A_{m}^{(0)}) = y*(x)]
```

or equivalently a deviation/error rate

```text
e_{m,0} = 1 - p_{m,0}.
```

So yes: in the engineering setting this lets you quantify how far different LLM
families drift from the `n = 0` benchmark baseline, with confidence bounds over
that success/error quantity.

Once you have slice levels `n = 0, 1, 2, ...`, the detector also estimates the
drop between adjacent slices:

```text
Delta_{m,n} = p_{m,n} - p_{m,n+1}.
```

If the lower confidence bound on `Delta_{m,n}` exceeds the configured threshold,
that boundary is treated as a witness cliff.

In other words, the library is not just saying "model accuracy is X". It is
saying:

- how well the baseline claim or task matches benchmark truth
- how much that success degrades as premises are removed, hidden, or re-routed
- where a decomposition or clarification structure becomes operationally unsafe

## Why This Matters For Orchestration

This gives a direct engineering interpretation for
`orchestration-assurance-engine`.

If the engine decomposes a natural-language claim into structured subclaims or
premise slices, then `safeslice` can be used as a statistical certificate over
that decomposition:

- if `p_{m,0}` is high across benchmarked instances, the baseline claim framing is operationally aligned with ground truth
- if the safe prefix remains long, the decomposition is stable under premise removal or restriction
- if a witness cliff appears early, the decomposition is hiding a brittle dependency
- if ambiguity routing says clarification is required, then the decomposition is not safely automatable under the given question budget

So the engineering claim is:

```text
the decomposition is statistically robust with respect to a benchmarked
ground-truth task family
```

not:

```text
the decomposition is mathematically true in all interpretations
```

That distinction matters, but the engineering certificate is still highly
useful. It turns claim decomposition, legal reasoning chains, policy workflows,
and other natural-language verification problems into something that can be
benchmarked, stress-tested, and certified with explicit failure boundaries.

## Cross-Domain Use

Under that benchmark-grounded interpretation, the same machinery can be reused
far beyond one theorem benchmark.

- mathematics: benchmark theorem statements against known yes/no theorem labels or proof-check outcomes
- law: benchmark legal holdings against known case outcomes or expert labels
- policy/compliance: benchmark decisions against approved determinations
- general natural-language verification: benchmark claim families against curated truth labels or adjudicated outcomes

The common structure is always the same:

```text
ground truth at n = 0
-> sampled model behavior
-> confidence-bounded slice success
-> witness-cliff / ambiguity certificate
```

That is the main reason this detector is useful as a reusable engineering
component rather than a one-off experiment.

## Core Modules

```text
src/safeslice/
  ambiguity.py
  interfaces.py
  models.py
  pipeline.py
  policy.py
  stats.py
  __init__.py
lean/
  Problem1.lean
  Problem2.lean
```

Module roles:

- `pipeline.py`: orchestrates the detector run
- `stats.py`: confidence intervals and drop bounds
- `policy.py`: witness-pair extraction, local/global obstruction logic, final routing
- `ambiguity.py`: ambiguity and clarification bounds
- `models.py`: immutable input/output data structures
- `interfaces.py`: sampler/checker/question-family protocols

## Current Algorithm

The current detector is simple and explicit:

1. For each slice, sample outputs until either:
   - the configured precision target is met, or
   - `max_samples` is reached.
2. Estimate each slice success rate using a chosen confidence scheme.
3. Compare adjacent slices using lower/upper drop bounds.
4. Mark a boundary as a witness cliff when the lower drop bound exceeds the
   configured threshold.
5. Build local chain partitions from:
   - witness cliffs,
   - low success,
   - insufficient evidence.
6. Add global obstructions from:
   - detector-state budget pressure, and
   - ambiguity clarification requirements.

## Bound Methods

The interval method is selectable through `ThresholdSpec(bound_method=...)`.

Supported values:

- `"hoeffding"`: fully distribution-free and conservative
- `"wilson"`: strong default Bernoulli interval for many finite-sample settings
- `"jeffreys"`: exact Bayesian Beta(1/2, 1/2) interval
- `"clopper_pearson"`: exact binomial inversion interval
- `"agresti_coull"`: adjusted-score interval
- `"empirical_bernstein"`: usually sharper when slice variance is low

Example:

```python
from safeslice import ThresholdSpec

thresholds = ThresholdSpec(
    safe_success=0.95,
    drop_threshold=0.20,
    confidence=0.95,
    bound_method="empirical_bernstein",
    sampling_mode="adaptive",
    boundary_mode="isotonic",
)
```

The addition of `jeffreys`, `clopper_pearson`, `agresti_coull`, and
`empirical_bernstein` means the detector is no longer locked to just Hoeffding
or Wilson.

## Sampling And Boundary Modes

`ThresholdSpec` also supports:

- `sampling_mode = "uniform" | "adaptive"`
- `boundary_mode = "adjacent" | "isotonic"`

Interpretation:

- `uniform`: estimate each slice independently until its own stopping rule fires
- `adaptive`: spend more samples on the current decision frontier and uncertain boundaries
- `adjacent`: use raw adjacent slice estimates for boundary drops
- `isotonic`: first project slice success estimates onto a monotone nonincreasing sequence, then compute boundary drops from the smoothed sequence

The adaptive mode uses time-uniform delta splitting over the finite sampling
horizon so that optional stopping does not silently invalidate the interval
interpretation.

## Minimal Usage

The library is intentionally backend-agnostic. Callers implement the protocols
in `interfaces.py`, then run the detector:

```python
from safeslice import SafeSliceDetector, TaskSpec

detector = SafeSliceDetector(
    sampler=my_sampler,
    checker=my_checker,
    prompt_renderer=my_prompt_renderer,
    question_family=my_question_family,
)

report = detector.run(task_spec)
```

The public surface is pure Python and centered on `TaskSpec`,
`SafeSliceDetector`, and `DetectorReport`.

## Claim Graph Adapter

The preferred integration path is to adapt
`orchestration-assurance-engine` `ClaimGraph` payloads directly into detector
tasks.

Public entrypoints:

- `ClaimGraphAdapterConfig`
- `chain_from_claim_graph(...)`
- `task_from_claim_graph(...)`

The default adapter behavior is:

- use `root_claim_ids` as target chains
- treat active `depends_on`, `decomposes_into`, `refines`, and `specializes`
  relations as dependency edges
- build `n = 0` as the baseline target claim
- build later slices as cumulative dependency layers

That gives a direct way to ask whether a claim decomposition produced by
`orchestration-assurance-engine` is benchmark-robust or whether it hides early
witness cliffs and clarification bottlenecks.

## If You Want A Better Algorithm

Even after adding more interval methods, adaptive sampling, and isotonic
boundary localization, there are stronger next-step
algorithms than the current uniform slice-by-slice estimator.

The most promising upgrade path is:

- adaptive sample allocation instead of uniform sampling
- monotone / isotonic boundary localization across slices
- anytime confidence sequences instead of fixed-time stopping

That combination would usually beat the current implementation on sample
efficiency while preserving explicit certificates. The current version still
favors theorem correspondence, clarity, and inspectability over maximum
statistical efficiency.
