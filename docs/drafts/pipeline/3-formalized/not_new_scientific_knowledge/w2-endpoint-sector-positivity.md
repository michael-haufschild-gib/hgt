# Endpoint exterior coefficients are PF₂₀₀

- **ID:** w2-endpoint-sector-positivity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Arithmetic symmetric-group characters](../../1-in-progress/w2-representation-construction.md)
- **Statement:** Every Toeplitz minor of order at most 200 of
  `n ↦ Re(xiEndpointExteriorCoefficient n)` is nonnegative.

## Proof

Write `t_q=xiSpectralPoint q`, `M=xiEndpointColorMass>0`, and `D_q=M(1/4+t_q²)`. If
`cos(π/(k+1)) |t_q²| ≤ Re(t_q²)`, then adding the positive real number `1/4` preserves this
sector inequality: for `0≤c≤1` and `a≥0`,
`c|a+z|≤ca+c|z|≤a+Re z`. Positive dilation by `M` also preserves the cone.

For a conjugate pair with denominator `D`, the even factor is
`(1+x²/D)(1+x²/conj D) = (x⁴+2 Re(D)x²+|D|²)/|D|²`.
Set `A=(|D|+Re D)/2` and `C=(|D|−Re D)/2`. The corpus quadratic cone theorem applies directly.
Conjugation-fixed factors have nonnegative linear coefficients in `x²`.
Products over `S ∪ conj(S)` are conjugation-stable and form a cofinal net. Genus-zero local
uniform convergence is supplied by
`HTGeometry.canonicalWeightProduct_hasProdLocallyUniformlyOn` in `GeneralPrimaryFactor.lean`.
The `PFTaylorAtZero` closure theorem applies to `x↦E(x²)`, where
`E(z)=G(1/4+z/M)²/G(1/4)²` and `G=xiCentreLift`. Its even Taylor coefficients are exactly the real exterior
coefficients by the squared-variable lift and `xiEndpointExteriorCoefficient_eq_deriv`.

For order 200, `HadamardBudget.rhVerifiedThrough_sixtySeven` puts every divisor point of
height at most 67 on the critical line. Above that height, the strict strip bound together
with `cone_of_distance` and `half_le_sq_mul_one_sub_cos` supplies the required cone.
Thus no zero-location hypothesis remains in the conclusion.

## Lean

`RHTower/Representation/EndpointSectorPositivity.lean` proves the unconditional theorem
`xiEndpointExteriorCoefficient_pfSeq_twoHundred`. It uses the exact endpoint product from
`EndpointExteriorProduct.lean` and the existing finite-order quadratic cone criterion.
Its direct leaf check passes, and its `RHTower` umbrella import is present.

## Scope

This transfers an existing finite-order criterion; no novelty is claimed. Identifying these
Toeplitz minors with mixed Young projections remains open. Fixed finite order does not
establish full arithmetic character positivity or RH.
