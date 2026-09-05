# Fifth-order remainder of the actual joint deletion block

**Stage:** 3-formalized. **RH implication:** none. **Novelty:** not certified.

For arbitrary `X,Y` in any complete complex normed algebra, form the chronological six-factor
block from the actual moduli-2-and-3 deletion coefficients. Lean verifies its derivatives at
zero of orders one through four all vanish and proves

`B(z)-1 = O(||z||^5)` as `z -> 0`.

The source is the original coefficient function `blockDeletionCoefficient`, with a proved
identification of its six velocities. Integer-normalized coefficients satisfy the exact
Leibniz convolution. Their cancellation is a universal noncommutative ring identity; a
separate theorem identifies them with the actual exponential word's derivatives. Analytic
Taylor remainder then supplies the bound. No signature theorem, numerical experiment,
external computation certificate, or assumed vanishing enters the proof.

Module: `formal/GaloisForLFunctions/RHTower/EulerDeletionJointExponentialRemainder.lean`.
Namespace: `RHTower.DeletionJointExponential`.
Capstones: `twoThreeVelocities_eq_source`, `iteratedDeriv_exponentialWord_zero`,
`twoThree_exponentialWord_first_four`, `twoThreeSourceBlock_remainder`.

Scratch `lake env lean /tmp/hgt-joint-polygon-17TZsg/RemainderAudit.lean` passed. Five
axiom checks report only `propext`, `Classical.choice`, and `Quot.sound`. The narrow final
`lake build GaloisForLFunctions.RHTower.EulerDeletionJointExponentialRemainder` passed.
The umbrella import is wired; no umbrella build ran. Global lint returned exit 1 solely for the
concurrent unwired `EulerDeletionBalancedPeriodCurvatureNoGo` module. No lint error was reported
for this new module.

[Continuing full-product proof and exact remaining Lean
obligations](../2-fully-proven/euler-deletion-joint-product-one-fifth.md).
A local fifth-order bound alone does not prove convergence of the product with weights varying
inside each block. Nor does convergence force the resulting unit to be the identity at a zero.
