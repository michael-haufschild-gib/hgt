# Joint continuity of actual Hecke theta

- **ID:** hecke-theta-joint-continuity-on-positive-parameters
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Hecke and class-field programme](../1-in-progress/hecke-l-functions-and-class-field-theory-2026-10-28.md), HL7
- **Statement:** Physical and finite-Fourier dual Hecke theta are jointly continuous in place profile and positive Gaussian parameter.

## Dependency-closed proof

For `t ≥ δ > 0`, parameter monotonicity bounds the parity kernel by its value
at `δ`. The fixed-parameter parity majorant bounds that value by a half-rate
Gaussian. When every place profile satisfies `y_v ≤ M`, the proved scaled
norm inequality replaces this by one unscaled Gaussian of positive rate
`(δ/2)*exp(-M)^2`. This is summable on every integral ideal and every actual
nonzero fractional ideal.

Actual finite weights have norm at most one; actual finite Fourier coefficients
have norm at most the finite modulus norm. Thus both weighted theta series
admit summable majorants uniform on bounded profile neighborhoods and positive
parameter strips. `continuousOn_tsum` gives the claimed joint continuity.
No uniform convergence or coefficient bound is assumed in an actual theorem.

## Lean and verification

[HeckeThetaIsJointlyContinuous.lean](../../../../formal/GaloisForLFunctions/HeckeLFunctions/HeckeThetaIsJointlyContinuous.lean)
contains:

- `numberFieldMixedPlaceScale_zero`
- `exists_uniform_mixedParityGaussian_majorant`
- `summable_integralIdeal_gaussian`, `summable_fractionalIdeal_gaussian`
- `exists_uniform_heckeThetaKernel_majorant`
- `exists_uniform_heckeDualThetaKernel_majorant`
- `continuousOn_heckeIdealTheta_joint`
- `continuousOn_heckeDualIdealTheta_joint`

The final direct `lake --old env lean` audit passes without warnings. Both
main transitive axiom audits, checked through the built module, contain only
`propext`, `Classical.choice`, and `Quot.sound`. No proof limits were raised;
explicit subtype annotations resolve the ideal-element elaboration. The module
is wired into the Hecke umbrella, its required olean is built for the written
unit-average consumer, and the completed scratch is removed.

Actual unit averaging, Gamma/ideal-series unfolding, primitive Gauss evaluation,
and full Hecke continuation remain separate open work.
