# The power-tail family in the actual critical golden Wiener ideal

- **ID:** biarithmetic-power-tail-wiener-family
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Critical continuum defect](../1-in-progress/biarithmetic-critical-payment-has-continuum-defect.md)
- **Statement:** Every positive exponent `α` gives an actual critical Wiener kernel, supported on powers of five, with norm two. It pays the critical golden source exactly when `α>1/2`. Every member belongs to the closure of the full actual paid ideal.

Lift the real power-difference coefficients through the checked complex
one-prime isometry. Its exact coefficient and norm formulas retain the
norm-two normalization. The actual source payment criterion reads the
square-partial-sum threshold. Total evaluation is zero, so corrected finite
paid kernels approximate every member in Wiener norm.

Lean: `BiarithmeticGeometry/PowerTailWienerFamily.lean`.
Audited declarations: `powerTailWiener_pow`, `norm_powerTailWiener`,
`powerTailWiener_mem_paidIdeal_iff`, and
`powerTailWiener_mem_closure_paidIdeal`.

- [x] Direct check: `lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/PowerTailWienerFamily.lean`.
- [x] All four transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Umbrella import wired; umbrella not compiled.

Independence of the actual quotient classes and its exact dimension remain
the next separate proof obligation.
