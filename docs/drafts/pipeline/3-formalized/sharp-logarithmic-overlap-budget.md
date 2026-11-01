# Explicit logarithmic-profile positivity and its spectral-budget ceiling

- **ID:** sharp-logarithmic-overlap-budget
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** `docs/reports/review-0111/obstacles-summary.md`, A2.
- **Statement:** The absolute reciprocal-floor budget `exp(Bc/log²c)≤(log N)^α`
  admits every `e≤c≤(α/B)L(log L)²`, eventually, where `L=loglog N`.
  Every fixed multiple `K>α/B` eventually fails that same budget.

## Proof [PROVED HERE]

For `c²≤L`, `Bc/log²c≤B√L≤αL` eventually. For `√L<c≤L`,
`log c≥(log L)/2`, so the exponent is at most `4BL/log²L≤αL`.
For `L<c≤(α/B)L(log L)²`, use `log c≥log L` directly.
This improves the earlier overlap coefficient `α/(4B)` by four.

At `c=KL(log L)²`,
`log c/log L=1+(log K+2loglog L)/log L→1`.
Consequently `(Bc/log²c)/L→BK`; when `BK>α`, the budget fails eventually.
This is an exact ceiling for the specified reciprocal-floor budget, not an
upper bound on positivity or on all possible absolute estimates.

For the zero-free logarithmic profile, `B=808(8π/3+3000)`.
The existing conductor argument uses `α=1/256`. Its stated auxiliary bounds
also permit `α=1/128`, `q=1/8`, `k=8`, `ν=1/1000`:
`4α−q/2≤−ν`, `5q+19α+1/k−1≤−ν`, and `q/4>α`.
Thus the resulting explicit coefficient is `1/[103424(8π/3+3000)]`.
For the exact sinc critical scale, divide by `96e` using the proved scale comparison.

The coefficient also optimizes the current absolute-budget system: existence
of an exponent `0<α≤1/128` paying every overlap through `K·dcScale N`
is equivalent to `K≤1/[103424(8π/3+3000)]`. Sufficiency uses `α=1/128`.
For necessity, a larger `K` exceeds `α/B` for every allowed exponent;
the exact asymptotic above contradicts its budget at `c=K·dcScale N`.
This last classification is awaiting its direct Lean audit.

## Gates

- [x] Dependency-closed paper proof.
- [x] Direct checks of both Lean leaves; umbrella import present.

## Lean

`TransMetzlerWeilPositivity/ReceiverRate/SharpLogarithmicOverlapBudget.lean` proves
`eventually_logarithmicSpectralControl_le_log_rpow_sharp`,
`tendsto_logarithmicExponent_critical_ratio`, and
`eventually_log_rpow_lt_logarithmicSpectralControl`.

`TheLogarithmicProfileIsPositiveBelowCriticalOverlap.lean` proves
`zeroFreeLogProfile_completeWeilMatrix_posDef_explicit_critical_overlap`,
its exact-sinc counterpart, and
`zeroFreeLogProfile_spectral_budget_fails_above_explicit_multiple`.
Both direct `lake --old env lean` checks pass. All audited declarations
depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## Remaining A2 question

Optimality over every possible absolute estimate is not established.
The sharp ceiling proved here concerns the specified reciprocal-floor budget.
