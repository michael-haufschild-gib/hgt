# Quartic cross-load reserve from scale seven

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Wall:** Σ6
- **Result:** For `q=π exp(2x)≥7`, the complete native matrix satisfies
  `H(x)−(3/20)K(x)q⁴B ≻ 0`, where `K=4q² exp(x−2q)` and
  `B=loadMapᵀ paidSevenSchur loadMap`. The truncated quartic weighted source
  is positive definite whenever `a>0` and `π exp(r)≥7`.

## Proof

Put `u=q/7−1≥0` and `z=exp(−3q)(q/7)¹⁵`. The exponential tangent bound gives
`0≤z≤exp(−21)≤1/1300000000`. Multiply the normalized Gaussian comparison,
minus its actual quartic cross-load and `147/4000` identity reserve, by
`(1+u)²³`. The result is a degree-25 matrix polynomial, affine in `z`.

All 26 coefficient matrices at `z=0` and the first 19 at the upper endpoint
have exact positive Schur certificates. Coefficients 19–25 are independent
of `z`. Affine interpolation makes every coefficient positive definite;
the nonnegative powers of `u` preserve positivity, including `u=0` through
the constant coefficient.

The complete-source comparison bounds all omitted terms below by the
subtracted `147/4000` reserve. Inverse Gaussian congruence therefore gives
the native quartic reserve with every theta atom retained.

Before the profile zero, the complete scalar correction satisfies
`G_P>−(3/20)Kq⁴`. Adding its remaining nonnegative cross-load gives strict
positivity. The literal aperture-dependent source adds another nonnegative
load to `r sinh(ar)` times this matrix. Beyond the double zero `r=√2`,
truncation leaves the native source, already positive there.

## Lean

- [FifthEvenQuarticRayModel.lean](../../../../formal/GaloisForLFunctions/ThetaCuspSections/FifthEvenQuarticRayModel.lean):
  `QuarticRayCertificate.model_quartic_reserve_from_seven_posDef`.
- [FifthEvenQuarticRay.lean](../../../../formal/GaloisForLFunctions/ThetaCuspSections/FifthEvenQuarticRay.lean):
  `QuarticRayCertificate.native_quartic_reserve_from_seven_posDef`.
- [FifthEvenTruncatedQuarticUpperRay.lean](../../../../formal/GaloisForLFunctions/ThetaCuspSections/FifthEvenTruncatedQuarticUpperRay.lean):
  `FifthPolynomialCross.repair_compact_from_seven_posDef`,
  `FifthPolynomialCross.weightedRepair_compact_from_seven_posDef`,
  `FifthTruncatedCross.weightedRepair_from_seven_posDef`.

Dependency audits use only `propext`, `Classical.choice`, and `Quot.sound`.
The compact matrix sign below scale seven and rank-nine integrated sign
remain open.
