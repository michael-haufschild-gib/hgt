# Nonstationary Gaussian type-II energy

- **Obstacle:** B13.
- **Stage:** 3-formalized
- **Type:** THEOREM

## Arithmetic improvement

Let `S` be the literal Gaussian Vaughan type-II sum on
`[D,2D)×[M,2M)`, retaining `A≤dm<B`, the actual coefficients
`typeIILong U d`, `typeIIShort V m`, and weight
`(dm)^(−σ) exp(−α(dm)²+i(ξ(dm)²−t log(dm)))`.
Put `Wσ=DM D^(−σ) M^(−σ)` and `θ=ξD²M²`.
For `σ,α≥0`, `ξ>0`, positive integer endpoints, and `16ξDM²≤π`,

`|S|² ≤ C Wσ² log(2D)(1+H_{2M}³) exp(−2αD²M²)`
`  × [1/M+2π(1+log(2M))/θ]`,

where `H_N=Σ_{1≤n≤N}1/n`. The constant is uniform in all parameters,
including the Vaughan cutoffs `U,V`; no zero-location assumption enters.

If additionally `t>0`, `t≤32θ`, and `t≤M`, then

`|S|² ≤ C Wσ² (1+log(2D))(1+log(2M))⁴ exp(−2αD²M²)/t`.

Thus the norm gains `t^(−1/2)` up to logarithms. Every rectangle containing
an integer quadratic stationary point satisfies `t=2ξ(dm)²≤32θ`.
The first-band condition and `M≥t` remain separate requirements.
At the exact scale `θ=t`, the first-band condition becomes `16t≤πD`.

## Proof

For `u≠0`, `P≥1`, and `|u|Q/π≤1/2`, the derivative of
`ux²/(2π)` stays in the first nonresonant band. Kuzmin–Landau gives
`|Σ_{P≤n<Q} exp(iun²)|≤2π/(|u|P)`; conjugation handles negative `u`.
Every prefix obeys the same bound. Abel summation retains the factor
`exp(−vP²)` for `v≥0`.

Pairing the height phases leaves a constant unit scalar. For distinct
`m,n∈[M,2M)`, `|m²−n²|≥2M|m−n|`; the first-band assumption bounds
each masked correlation by
`exp(−2αD²M²) π/(ξDM|m−n|)`. Both product cutoffs intersect to an
interval inside `[D,2D)`, so neither cutoff is discarded. The diagonal
costs `D exp(−2αD²M²)`. The harmonic row sum is at most

`D+2π(1+log(2M))/(ξDM)`.

Cauchy–Schwarz and the symmetric Schur bound give
`|S|²≤E_a E_b exp(−2αD²M²)` times this row bound. Chebyshev bounds the
long coefficient energy by `C D log(2D)`; the divisor second moment
bounds the short energy by `4M(1+H_{2M}³)`. Decreasing abscissa weights
cost `D^(−2σ)` and `M^(−2σ)`, proving the envelope.

Finally, `H_{2M}≤1+log(2M)`, `1/M≤1/t`, and `1/θ≤32/t` give the
logarithmic height bound. A stationary point has `t=2ξ(dm)²`; the dyadic
inequality `dm≤4DM` proves the stated stationary-scale inclusion.

## Direct comparison with the previous correlation bound

Write `λ=|u|/π` and `N=Q−P`. Under the first-band condition, if also
`P√λ≥1` and `N√λ≥12`, the Gaussian norm is at most
`exp(−vP²) quadraticSumBound(N,u)/6`.
Indeed `λP≥√λ` bounds the new factor by `2/√λ`; both branches of the
previous minimum `min(N,8N√λ+12/√λ)` are at least `12/√λ`.
This comparison is formalized separately and retains identical damping.

## Scope

The controlling scale is `θ`, since logarithmic height cancels from pair
correlations. Rectangles with `θ<t/32`, rectangles outside the first band,
and those with `M<t` need separate estimates before global summation.
Infinite tails, pole cancellation and contracting filter factors remain.
No improved asymptotic bound for the complete filtered current or B13
conclusion follows yet.

## Lean declarations and audit

All declarations are in `GaloisForLFunctions.ExceptionalLayerTheory`.

- `NonstationaryGaussianCorrelations.lean`:
  `norm_sum_quadratic_first_derivative_le`,
  `norm_sum_gaussian_quadratic_first_derivative_le`,
  `norm_gaussian_correlation_first_derivative_le`,
  `norm_sum_gaussian_quadratic_le_sixth_curvature_bound`.
- `NonstationaryGaussianTypeII.lean`:
  `norm_maskedGaussian_dyadic_correlation_le`,
  `sum_gaussianDyadicCorrelationKernel_le`,
  `norm_maskedGaussian_dyadic_nonstationary_sq_le`,
  `norm_gaussianVaughan_dyadic_nonstationary_sq_le`,
  `gaussianDyadicRowBound_normalized`.
- `GaussianVaughanDyadicSaving.lean`:
  `exists_gaussianVaughan_dyadic_envelope_bound`,
  `exists_gaussianVaughan_dyadic_height_saving`,
  `exists_gaussianVaughan_dyadic_log_height_saving`,
  `gaussian_stationary_height_le_dyadic_scale`.

All three modules pass direct `lake --old env lean` source audits without
warnings and are imported by `ExceptionalLayerTheory.lean`. Thirteen
transitive axiom lists contain only `propext`, `Classical.choice`, and
`Quot.sound`.
