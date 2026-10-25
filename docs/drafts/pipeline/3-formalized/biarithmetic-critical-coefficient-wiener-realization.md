# Actual Wiener realization of the critical coefficient domain

- **ID:** biarithmetic-critical-coefficient-wiener-realization
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [One-prime Fredholm phase](../1-in-progress/biarithmetic-one-prime-payment-fredholm-phase.md)
- **Statement:** Complex `ell1` maps linearly and isometrically onto the critical Wiener kernels supported on powers of five, by `k(5^r)=sqrt(5)^r g_r`. Normalized restriction is its inverse. Actual critical golden payment pulls back exactly to square summability of coefficient partial sums.

The checked complex lift supplies the coefficient formulas, linearity, and
norm identity. Restricting the actual Wiener norm series along the injective
five-power map proves summability of inverse coordinates. Support and
coordinate identities prove both inverses and the exact range. The checked
critical golden payment criterion supplies the source-domain equality.

Lean: `BiarithmeticGeometry/CriticalCoefficientWienerRealization.lean`.
Audited declarations: `criticalCoefficientLift`,
`summable_norm_criticalNormalizedCoefficients`,
`criticalNormalizedCoefficients_lift`,
`criticalCoefficientLift_normalizedCoefficients`,
`mem_range_criticalCoefficientLift_iff`, and
`criticalCoefficientLift_mem_golden_paidIdeal_iff`.

- [x] Direct check: `lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/CriticalCoefficientWienerRealization.lean`.
- [x] All six transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Default proof limits; umbrella import wired; umbrella not compiled.

The isometric range is the prime-five supported subspace. This statement
does not identify the full Wiener algebra with a one-prime coefficient space.
