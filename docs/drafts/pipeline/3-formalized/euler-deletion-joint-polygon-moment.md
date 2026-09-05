# Exact polynomial moments of coprime deletion polygons

**Stage:** 3-formalized. **RH implication:** none. **Novelty:** not certified.

For positive coprime integers `P,Q`, join the literal prefix points `(n mod P,n mod Q)` by
straight segments, for `n=0,...,P*Q`. Each velocity is
`(1-P[P divides n+1],1-Q[Q divides n+1])`.

Lean proves the path closes, all polynomial one-forms of coefficient degree at most three
integrate to zero, and

`integral x*y^3 dx = P*(P-1)*Q*(Q-1)*(Q-2)/120`.

The proof uses exact CRT factorization of the segment integrand, symbolic finite power-sum
identities, and ordinary integration of polynomials. The closed moduli-2-and-3 theorem combines
both families of low-degree tests with the surviving value `1/10`. No numerical experiment or
external computation certificate enters any proof.

Module: `formal/GaloisForLFunctions/RHTower/EulerDeletionJointPolygonMoment.lean`.
Namespace: `RHTower.DeletionJointPolygon`; its parameters `p,q` represent actual moduli `p+1,q+1`.
Main declarations: `integrand_factorization`, `circulation_one_three`, `circulation_low_degree`,
`circulation_eq_segment_sum`, `moduli_two_three_closed_low_degree_nonzero`.

Foreground scratch checks and the narrow leaf build passed. Eight axiom-audited endpoint,
factorization, integral, and capstone theorems use only `propext`, `Classical.choice`, `Quot.sound`.
The module is wired into `RHTower.lean`; no umbrella build ran. Scoped whitespace check passed.
Global lint failed on concurrent unwired modules `EulerDeletionBalancedPeriodCurvatureNoGo` and
`EulerDeletionCurvatureCriticalBoundary`, with no error reported for this module.

[Full construction, proof, literature boundary, and continuing infinite-product
candidate](../1-in-progress/euler-deletion-joint-polygon-moment.md).
The finite statement does not supply any cancellation at a zeta zero. General signature and
polynomial-moment methods are published; the arithmetic specialization has no global novelty
certificate.
