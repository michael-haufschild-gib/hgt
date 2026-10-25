# Exact closure and continuous annihilator of critical coefficient payment

- **ID:** biarithmetic-critical-coefficient-domain
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [One-prime Fredholm phase](../1-in-progress/biarithmetic-one-prime-payment-fredholm-phase.md)
- **Statement:** In complex `ell1`, coefficients with square-summable inclusive partial sums form a submodule. Its closure is exactly the zero-total-evaluation hyperplane. Distance to that hyperplane is attained and equals the modulus of total evaluation. Every continuous functional vanishing on payment is a scalar total evaluation.

Finite square energy forces partial sums to tend to zero, while absolute
summability makes them tend to total evaluation. Corrected finite cores
approximate every zero-total vector in coefficient norm. Subtracting the
total evaluation at coordinate zero gives a minimum-distance representative.
The existing continuous augmentation annihilator theorem then gives the
complete functional classification.

Lean: `BiarithmeticGeometry/CriticalCoefficientDomain.lean`.
Audited declarations: `criticalCoefficientDomain`,
`criticalFiniteCoefficientCore_tendsto`, `closure_criticalCoefficientDomain`,
`criticalTotalEvaluation_minimum_distance`, and
`criticalCoefficientDomain_continuous_annihilator`.

- [x] Direct check: `lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/CriticalCoefficientDomain.lean`.
- [x] All five transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Default proof limits; umbrella import wired; umbrella not compiled.

The actual Wiener isometry, reduced quotient isometry, and quotient-dual
dimension have separate formalization obligations.
