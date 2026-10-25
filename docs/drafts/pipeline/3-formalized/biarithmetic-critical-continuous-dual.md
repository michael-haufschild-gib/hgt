# Continuous dual of the unreduced critical coefficient quotient

- **ID:** biarithmetic-critical-continuous-dual
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [One-prime Fredholm phase](../1-in-progress/biarithmetic-one-prime-payment-fredholm-phase.md)
- **Statement:** The continuous complex dual of the actual unreduced critical coefficient quotient is linearly equivalent to `C`, with dimension one. Every continuous functional is a scalar multiple of total evaluation and vanishes on every closure-defect class.

The actual quotient map is continuous even though its denominator is not
closed. Pulling a continuous functional back to complex `ell1` gives an
annihilator of the payment domain. The checked annihilator classification
then gives the unique scalar total evaluation. Evaluation on the unit
coefficient class supplies the inverse linear equivalence.

Lean: `BiarithmeticGeometry/CriticalContinuousDual.lean`.
Audited declarations: `criticalQuotientTotalEvaluation`,
`criticalUnreducedContinuousDual_classification`,
`criticalUnreducedContinuousDualEquiv`,
`finrank_criticalUnreducedContinuousDual`, and
`criticalUnreducedContinuousDual_vanishes_on_closure`.

- [x] Direct check: `lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/CriticalContinuousDual.lean`.
- [x] All five transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Default proof limits; umbrella import wired; umbrella not compiled.

No closedness instance is imposed on the paid submodule. This result concerns
continuous functionals on the unreduced quotient itself.
