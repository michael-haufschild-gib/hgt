# Critical coefficient payment has continuum-dimensional defect

- **ID:** biarithmetic-critical-coefficient-continuum-defect
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [One-prime Fredholm phase](../1-in-progress/biarithmetic-one-prime-payment-fredholm-phase.md)
- **Statement:** Both the unreduced critical coefficient quotient and the quotient of its closure by payment have complex Hamel dimension exactly continuum.

Normalize the actual power-tail Wiener kernels to complex `ell1` coefficient
vectors. Their classes map to the independent classes in the actual golden
quotient, so they are independent already in the coefficient quotient.
Total evaluation vanishes on every vector, placing the same independent
family inside the closure defect. The interval of exponents `(0,1/2)`
provides the continuum lower bound. The coefficient lift and quotient
surjections give matching cardinality upper bounds.

Lean: `BiarithmeticGeometry/CriticalCoefficientContinuumDefect.lean`.
Audited declarations: `criticalPowerCoefficientClass_linearIndependent`,
`criticalPowerCoefficientDefectClass_linearIndependent`,
`rank_criticalCoefficientPaymentQuotient_eq_continuum`, and
`rank_criticalCoefficientClosureDefect_eq_continuum`.

- [x] Direct check: `lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/CriticalCoefficientContinuumDefect.lean`.
- [x] All four transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Default proof limits; umbrella import wired; umbrella not compiled.

These are algebraic quotient dimensions. Their reduced topological quotient
and continuous dual have dimension one, as established by separate leaves.
