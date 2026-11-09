# Positive Laplace sources admit finite positive translation repair

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)

## Statement

Let `f:ℝ→ℝ` be globally Lipschitz, with `exp(c|x|)|f(x)|` integrable for
every real `c`. Suppose `f` is strictly positive outside a compact interval
and `∫f(x)exp(sx)dx>0` for every real `s`.

For every `δ>0` there are `0<h<δ` and positive real numbers `r₁,…,rₙ`
such that, with `Q(X)=∏(X+rᵢ)` and `τ_h f(x)=f(x-h)`,

`Q(τ_h)f(x)≥0` for every real `x`.

All coefficients of `Q` are nonnegative. Its zeros are strictly negative real.
The repaired source retains all absolute exponential moments. Any prescribed
nonzero complex Laplace value can also be retained: choose
`h |Im w|<π/2`, so `Q(exp(hw))≠0`.

## Proof

Fix a compact interval containing the negative part and positive unit bands
strictly beyond it on both sides. Their positive contributions dominate the
bounded negative part under sufficiently large positive or negative Laplace
tilts. This threshold is independent of subsequent truncation and mesh.

On the remaining compact tilt interval, dominated continuity gives a positive
minimum of the Laplace transform. One stronger exponential moment makes the
discarded tail uniformly small. On a sufficiently fine symmetric grid, use
the left value minus the Lipschitz constant times the mesh, and zero outside.
This lower step loses at most twice that mesh error per cell. It preserves the
outer bands, every real Laplace sign, and a positive first coefficient.

The step equals `P(τ_h)b` for one nonnegative interval indicator `b`.
Its Laplace transform is a positive factor times `P(exp(hs))`; the first
coefficient supplies positivity at zero. Thus `P>0` on `[0,∞)`.
Real factorization and quadratic binomial repair yield a negative-root product
`Q` with `PQ` coefficientwise nonnegative. Consequently
`0≤(PQ)(τ_h)b=Q(τ_h)P(τ_h)b≤Q(τ_h)f`.

## Lean

Namespace `GaloisForLFunctions.HTGeometry.PositiveTranslationRepair`:

- `PositiveLaplaceRepair.lean`: `exists_positive_lower_grid`,
  `exists_positive_average_of_laplace_positive`.
- `PolynomialPulses.lean`: `polynomialAverage_gridPolynomial`,
  `gridPolynomial_eval_pos_of_laplace_pos`.
- `LaplaceBounds.lean`: `laplace_pos_of_outer_bands`,
  `laplace_sub_le_of_compact_error`, `exists_laplace_margin`.
- `PolynomialAverages.lean`: `exists_positive_average_of_polynomial_lower_bound`.
- `SpectralPreservation.lean`: `polynomialAverage_abs_moment`,
  `exists_positive_average_preserving_character`.
- `PolynomialTransforms.lean`: `integral_polynomialAverage_cexp`,
  `negativeRootMultiplier_eval₂_exp_ne_zero`.

Polynomial factor repair:
`ArithmeticLocalDivisorGeometry/PositiveMultipliers.lean`,
`exists_negativeRootMultiplier_repair` and
`negativeRootMultiplier_eval₂_ne_zero`.

Capstone axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`.
No raised limits or trusted computation shortcuts.

This is an independent positive-repair theorem. The zeta localization route
can instead use the existing `ThetaSeedTransferQuartet.quartet_seed_transfer`
directly. No arithmetic B130 bound follows from this theorem alone.
