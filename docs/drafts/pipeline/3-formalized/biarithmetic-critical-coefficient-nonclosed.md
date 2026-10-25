# The actual critical coefficient domain is not closed

- **ID:** biarithmetic-critical-coefficient-nonclosed
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [One-prime Fredholm phase](../1-in-progress/biarithmetic-one-prime-payment-fredholm-phase.md)
- **Statement:** The actual complex `ell1` domain of square-summable partial sums is not closed. An explicit norm-two vector has total evaluation zero and divergent response energy, while paid finite cores converge to it.

The inverse-square-root-tail differences embed in the complex coefficient
space without changing their absolute sum or partial-sum square energy.
The checked closure theorem puts this unpaid vector in the evaluation
kernel, and the corrected finite-core theorem gives its paid approximants.

Lean: `BiarithmeticGeometry/CriticalCoefficientNonclosed.lean`.
Audited declarations: `norm_criticalUnpaidCoefficientVector`,
`criticalUnpaidCoefficientVector_not_mem`,
`criticalUnpaidCoefficientVector_finiteCore_tendsto`, and
`not_isClosed_criticalCoefficientDomain`.

- [x] Direct check: `lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/CriticalCoefficientNonclosed.lean`.
- [x] All four transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Default proof limits; umbrella import wired; umbrella not compiled.
