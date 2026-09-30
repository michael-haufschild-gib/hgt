# Actual first-atom Gaussian score envelope

- **ID:** PA-THETA-GAUSSIAN-SCORE-FLOOR
- **Stage:** 3-formalized
- **Type:** THEOREM; unconditional actual-source bound
- **Parent:** [literal-mass score-floor obstruction](../2-fully-proven/li-mass-calibrated-score-floor-obstruction.md)

For every `x≥0`, in the installed Born–Witten normalization,

`πψ_1(x)²(x−1)² ≤ (110843/111104) [243/(100√(2π))] exp(−18x²)(1+177x²)`.

Multiplier is strictly below one. This gives the exact positive survivor of the literal-mass floor obstruction; it does not establish the complete analytic Gaussian–Hermite countermodel in Lean, any actual cumulant sign, or RH.

## Dependency-closed proof

The first-atom identity is `ψ_1²=4(πe^(2x)−3/2)exp(5x/2−πe^(2x))`. Split at `x=1/3`. On the compact side, exponential monotonicity, a finite Taylor upper bound and a completed-square polynomial certificate preserve the strict rational surplus. On the tail, fourth/fifth Taylor lower bounds and a positive Bernstein identity prove `πe^(2x)≥18x²+(9/2)x`; `(x−1)²≤(2/93)(1+177x²)` and rational π/square-root bounds close the scalar comparison. These are exact proof certificates, with no sampled or numerical experiment.

## Lean status

- `PrimeArchThetaGaussianScoreEnvelopeCertificates.lean`: nine public certificate lemmas.
- `PrimeArchThetaGaussianScoreFloorEnvelope.lean`: actual amplitude normalization, two regional bounds and `thetaCuspFirstAtom_gaussianScoreEnvelope`.
- Named `lake build --old` completed: both leaves, 8975 jobs; own leaf times 21s and 29s.
- Final exact `lake env lean` checks: exit zero, empty logs.
- All 13 public declaration axioms: only `propext`, `Classical.choice`, `Quot.sound`.
- Both leaves imported by `RHTower.lean`. Global index/lint refresh pending; previous authoritative lint had 13 unrelated unreachable modules.

Evidence: `/tmp/hgt-theta-envelope-build.log`, `/tmp/hgt-theta-envelope-axioms.log`, `/tmp/hgt-theta-envelope-cert-direct.log`, `/tmp/hgt-theta-envelope-floor-direct.log`.

## Limits and next burden

Literal raw mass plus this complete prescribed polynomial floor admits a paper countermodel with a negative normalized cumulant determinant. Gaussian characteristic has order two; theta lattice, exact Euler membership and full source moments remain unmatched. Separate order-one derivative-packet compatibility is under audit. No actual-source route is retired.
