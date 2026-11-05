# Gaussian cone coupling as an arithmetic heat average

- **ID:** gaussian-cone-coupling-arithmetic-heat-identity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** review-0411, §2.1, A12.

## Statement

For `τ > 0`, put `gτ(y) = exp(−y²/(4τ))/sqrt(4πτ)` and let
`B` be the existing cubic spline. Define the arithmetic profile

`P(t) = WeilFullFunctional_Λ(weilTest(B, B(·+t)))`.

Prove, for the existing Gaussian-damped cone kernel and coupling,

`Kτ(t) = ∫ gτ(y) P(t+y) dy`,

`Cτ(a,b;m,n) = ∫ gτ(y)[P(ma+nb+y)−P(ma+y)−P(nb+y)+P(y)] dy`.

This expresses the damped zero sum using the actual prime, archimedean and pole
functional. No boundedness or positivity of the coupling is asserted.

## Proof

[PROVED HERE] The mixed compact-test explicit formula identifies `P(t)` with
`Σρ exp(t zρ)wρ`, where `zρ = ρ−1/2`. For `b>0`, the complex Gaussian integral is

`∫ exp(−by²+zy) dy = sqrt(π/b) exp(z²/(4b))`.

On `|Re z|≤1/2`, the integrand's norm is bounded by
`E_b(y)=exp(−by²+y/2)+exp(−by²−y/2)`, an integrable function. Hence the sum of
the integrals of the term norms is bounded by
`exp(|t|/2)(∫E_b) Σρ|wρ|`, finite by absolute summability of the spline weights.
Bochner sum–integral interchange gives

`∫ exp(−by²)P(t+y) dy = sqrt(π/b) K_{1/(4b)}(t)`.

Set `b=1/(4τ)` and divide by `sqrt(4πτ)>0`. This proves the kernel formula.
Each of the four integrands is absolutely integrable by the same estimate.
The existing spectral mixed-difference identity and linearity of the integral
therefore prove the coupling formula.

## Lean inputs

- `ConeCoupling.summable_norm_wt`, `W_shiftTest_shiftTest`.
- `RHTower.zeta_W_eq_weilFullFunctional_mixed`.
- `gaussianConeCoupling_eq_kernel_difference`.
- Mathlib Gaussian integral and summable-integral interchange.

## Lean certification

Module: `ArithmeticCouplingTheory.ConeBoundary.TheGaussianCouplingIsAnArithmeticHeatAverage`.

- `arithmeticSplineProfile_eq_tsum`.
- `integrable_gaussian_arithmeticSplineProfile`.
- `integral_gaussian_arithmeticSplineProfile`.
- `gaussianConeKernel_eq_arithmetic_heatAverage`.
- `gaussianConeCoupling_eq_arithmetic_heatAverage`.

Direct `lake --old env lean` check passed. All five transitive axiom reports contain
only `propext`, `Classical.choice`, and `Quot.sound`. Imported by the owning umbrella.
