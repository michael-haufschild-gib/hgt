# The critical reduced coefficient cokernel is isometrically the complex line

- **ID:** biarithmetic-critical-reduced-cokernel
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [One-prime Fredholm phase](../1-in-progress/biarithmetic-one-prime-payment-fredholm-phase.md)
- **Statement:** The quotient of complex `ell1` by the closure of its square-partial-sum domain is linearly isometric to `C`. The quotient norm of a coefficient class is exactly the modulus of its total evaluation, and its complex dimension is one.

The checked closure theorem identifies the denominator with the total-evaluation
kernel. Its attained minimum-distance theorem supplies the upper quotient-norm
bound. Every nearly minimal representative has the same total evaluation,
which supplies the reverse bound. The surjective evaluation then induces
the stated linear isometry.

Lean: `BiarithmeticGeometry/CriticalReducedCokernel.lean`.
Audited declarations: `norm_criticalEvaluation_quotient_mk`,
`criticalEvaluationQuotientIsometry`, `criticalReducedCoefficientCokernelIsometry`,
and `finrank_criticalReducedCoefficientCokernel`.

- [x] Direct check: `lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/CriticalReducedCokernel.lean`.
- [x] All four transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Default proof limits; umbrella import wired; umbrella not compiled.

This is the normalized coefficient quotient. Actual source graph comparisons
remain separate obligations; the [unreduced continuous-dual classification](biarithmetic-critical-continuous-dual.md)
is also formalized.
