# Zero evaluation gives actual critical golden closure classes

- **ID:** biarithmetic-critical-golden-closure-inclusion
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Critical continuum defect](../1-in-progress/biarithmetic-critical-payment-has-continuum-defect.md)
- **Statement:** Every absolutely summable complex one-prime coefficient sequence with zero total sum lifts into the closure of the actual critical golden paid ideal.

Retain coefficients through `N`, subtract their partial sum from the last
retained coefficient, and set later coefficients to zero. Each corrected
finite sequence has eventually zero partial sums, so its actual Wiener lift
pays the critical golden source. The exact lift isometry identifies its
Wiener error with the coefficient error, which tends to the absolute total
sum. Zero evaluation therefore gives norm convergence inside the actual
paid ideal.

Lean: `BiarithmeticGeometry/CriticalGoldenClosure.lean`.
Audited declarations: `criticalCorrectedWiener_mem_paidIdeal`,
`criticalCorrectedWiener_norm_error_tendsto`, `criticalCorrectedWiener_tendsto`,
and `fiveComplexCriticalWienerLift_mem_closure_paidIdeal`.

- [x] Direct check: `lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/CriticalGoldenClosure.lean`.
- [x] All four transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Umbrella import wired; umbrella not compiled.

This proves a closure inclusion for the one-prime lift. It does not assert
the converse or identify the closure of the full Wiener ideal.
