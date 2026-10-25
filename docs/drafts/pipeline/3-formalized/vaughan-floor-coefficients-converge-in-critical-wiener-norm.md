# Vaughan floor coefficients converge in critical Wiener norm

- **ID:** vaughan-floor-coefficients-converge-in-critical-wiener-norm
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** vaughan-admission-phase-transition-at-half-damping.md
- **Lean:** `BezoutValuationIncidence/TheVaughanFloorCoefficientsConvergeInCriticalWienerNorm.lean`
- **Verification:** Final direct Lean check passed. All three public targets depend only on `propext`, `Classical.choice`, and `Quot.sound`. Umbrella import present.

For `ε>1/2`, write `‖a‖_W=Σ_d |a(d)|d^(-1/2)`. As `U→∞`,
the coefficient `μ_{≤U}(d)d^(-ε)` converges in this norm to
`μ(d)d^(-ε)`. This covers either small Vaughan leg. As both cutoffs diverge,
the signed small-small coefficient
`−(μ_{≤U}⋆μ_{≤V}⋆1)(d)d^(-ε)` converges to `−μ(d)d^(-ε)`.

At each `d≤U,V`, the convolution is exactly `μ(d)`: the truncated
Möbius-zeta defect vanishes on every divisor of `d`. The common divisor-square
majorant has finite critical Wiener mass; twice that majorant dominates the
coefficient differences. Dominated convergence proves both norm limits.

Exact declarations:

- `pmPronicVaughanSmallSmallCoeff_eq_moebius_of_le`
- `tendsto_criticalWiener_truncatedMoebius_sub_moebius`
- `tendsto_criticalWiener_neg_vaughanSmallSmall_sub_neg_moebius`

These coefficient statements do not assert receiver admission below half damping.
