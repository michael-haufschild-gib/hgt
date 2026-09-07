# EDQ blanket nonnegativity of the completed arithmetic half

Stage: 5-failed. Scope: only global or eventual high-strip nonnegativity of the
literal completed half. The EDQ route remains active; RH remains open.

## Exact obstruction

Let `A_p` be the genuine completed arithmetic half. For every nontrivial
modulus and every real height threshold T, there exists an off-line source
point s in the open critical strip with `T<Im(s)` and `Re(A_p(s))<0`.
Thus neither global strip nonnegativity nor nonnegativity above some height
can follow from this source's holomorphy and critical-line positive energy.
These negative source points are not asserted to be off-line zeta zeros.

The proof uses actual simple critical zeros supplied unconditionally above
every height, the exact reflected identity for the literal half, and analytic
factorization at the full zero multiplicity. No numerical census is substituted
for the corpus theorem.

## Strongest positive survivor

At any critical-line center and `0<d<1/2`, the complete reflected real pair is
exactly `Re(xi(rho+d)^2)`, independently of every nontrivial deletion modulus.
At an actual critical zero of full multiplicity m, its quotient by `d^(2*m)`
tends to `(-1)^m*B` for one `B>0`. One positive neighborhood, also independent
of the modulus, gives a lower bound `B*d^(2*m)/2` for even m and an upper bound
`-B*d^(2*m)/2` for odd m. This classifies the nonzero contact and preserves both
horizontal sides, full multiplicity, and the actual completed arithmetic source.

The second pass through the obstruction strengthens pointwise-in-modulus
limits to a common magnitude and common sign neighborhood for every nontrivial
modulus, using the exact finite pair identity. Changing the modulus cannot
repair the common negative pair. Which individual side is negative may change.

Paper status: dependency-closed proof in the
[completed horizontal contact card](../3-formalized/edq-completed-horizontal-contact.md).
Lean status: all eight public theorems and the definition in
`EulerDeletionHorizontalContact.lean` verified by scratch, a targeted leaf build,
and a new-only axiom audit using only standard Lean axioms.
The obstruction is `not_eventually_nonnegative_completedSplit`; the survivor
is `exists_horizontal_contact` together with `horizontalPair_channel_independent`,
`odd_contact_negative`, and `even_contact_positive`.

A viable interior comparison must accommodate these negative neighborhoods
and still constrain values at actual zeros. Universal vanishing of the retained
oriented current is not proved by the contact law.
