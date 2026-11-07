# Arithmetic Abel continuation

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Objective:** Construct and formalize an arithmetic mechanism crossing the shared sign/precision/reflection barrier. A new receiver or isolated obstruction does not meet this objective.

## Open source estimate

The damped Euler logarithm admits an arithmetic continuation estimate retaining its holomorphic normalization and controlling mollifier budgets. The required estimate must be proved from the source, without zero-freeness or a sign assumption.

## Distinction requiring audit

For finite curve data, write `P(v)=∏(1−βᵢv)`. The candidate implication

`mean |P(v)/P(ρv)|² → 1` ⇒ near-extremal Abel mollifiers

fails: the quotient limit holds for every finite datum, whereas the golden datum's Abel budgets are at least `φ²>1`. The Euler-log series cannot be identified with the reciprocal beyond its convergence domain.

**Paper argument.** For `|β|≤1`, each quotient factor is bounded by 2. For `|β|>1`, eventually `ρ|β|−1≥(|β|−1)/2`, so its quotient factor is bounded by `2(1+|β|)/(|β|−1)`. A finite product gives uniform eventual domination. Away from the finite zero set of `P` on the circle, the quotient tends to 1; dominated convergence gives the mean limit. No purity hypothesis enters.

**Positive survivor, Lean verified:** explicit eventual domination and the quotient limit for every finite datum. For the golden datum the budget minus quotient mean is eventually at least `(φ²−1)/2`, uniformly in truncation degree. See [the closed surrogate](../5-failed/boundary-quotient-convergence-as-an-abel-mechanism.md). This isolates holomorphic Euler-log continuation from boundary quotient control; it supplies no new arithmetic upper bound.

## Next mathematical gate

Determine whether a source-defined approximation can retain holomorphic normalization beyond the initial Euler-log convergence disc. Track its complete budget, including contributions lost by replacing the holomorphic mollifier with a meromorphic reciprocal. No mechanism is established yet.

## Existing inputs

- `ArithmeticInnerFunctionTheory/CastelnuovoConstructsTheMollifierOfACurve.lean`: Abel family, quotient, domination under purity, golden budget floor.
- `ArithmeticInnerFunctionTheory/TheCurveChainOfTheInnerFactor.lean`: exact Szegő infimum and golden inner mass.
- Frontier: `docs/reports/review-0611/route-unification-ledger.md`, classes C37 and C50.
