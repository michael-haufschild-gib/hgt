# Actual critical golden payment has continuum-dimensional defect

- **ID:** biarithmetic-critical-golden-continuum-defect
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Critical continuum defect](../1-in-progress/biarithmetic-critical-payment-has-continuum-defect.md)
- **Statement:** The full actual critical golden payment quotient and the quotient of its Wiener closure by payment both have complex Hamel dimension exactly continuum. An independent family in each quotient consists of actual norm-two kernels supported on powers of five.

Index the checked power-tail kernels by `0<α<1/2`. A finite relation in
the actual quotient is an actually paid kernel. Its exact normalized
coefficients have square-summable partial sums, so power-tail independence
forces every scalar coefficient to vanish. Each kernel also belongs to
the actual paid closure. The canonical map from the closure defect to the
full quotient carries its classes to the independent family. The real
interval supplies the continuum lower bound, matching the ambient Wiener
cardinality upper bounds.

Lean: `BiarithmeticGeometry/CriticalGoldenContinuumDefect.lean`.
Audited declarations: `criticalGoldenPowerClass_linearIndependent`,
`criticalGoldenPowerDefectClass_linearIndependent`,
`rank_criticalGoldenPaymentQuotient_eq_continuum`, and
`rank_criticalGoldenPaymentClosureDefect_eq_continuum`.

- [x] Direct check: `lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/CriticalGoldenContinuumDefect.lean`.
- [x] All four transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Umbrella import wired; umbrella not compiled.

This is the ordinary-floor golden source. The intrinsic receiver transfer
and the separate coefficient-space quotient comparison remain obligations.
