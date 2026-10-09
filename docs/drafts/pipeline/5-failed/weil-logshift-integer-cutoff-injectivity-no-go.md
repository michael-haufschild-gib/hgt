# Integer-cutoff first-probe data do not reconstruct coefficients

Status: RETIRED — exact obstruction and replacement sampling law formalized.

## Obstruction

`RHTower.exists_integer_firstProbe_collision_detected_by_recovery_mesh` gives
two coefficient systems with identical m=2 probe values at every positive
integer cutoff, but distinct values at a coefficient-recovery cutoff. Thus
integer-cutoff history is not injective even after ignoring coefficients zero
and one. One system can be von Mangoldt; the other comes from the preceding
nonsummable-history construction.

## Strongest positive survivor

Use L_n=(log(n+1)-log 2)/2. No atom above n is visible, and the diagonal response
to atom n is strictly positive. `weilLogShiftRecoveryProbe_sub` gives the exact
finite triangular transform. `weilLogShiftRecoveryProbe_prefix_iff` identifies
each finite coefficient head from the matching sample head.
`weilLogShiftRecoveryProbe_eq_iff` and `real_cutoff_firstProbe_eq_iff` identify
all coefficients at n>=2 from the countable mesh or full positive real-cutoff
history, respectively. No growth, summability, sign, or RH premise is needed.

Paper proof: dependency-closed from our Lean corpus. Lean status: all three
definitions and ten theorems compile, with axiom sets exactly
`[propext, Classical.choice, Quot.sound]`. Umbrella/API wired; global lint passes.
Source: `formal/GaloisForLFunctions/RHTower/WeilLogShiftCutoffReconstruction.lean`.
Full record: `../3-formalized/weil-logshift-cutoff-reconstruction.md`.

Second-pass audit extracted finite-prefix and full-history reconstruction as
the exact replacement law. The follow-up `WeilLogShiftRecoveryHomeomorphism.lean`
also proves fine-mesh surjectivity, unique zero-head realization, and continuity
of both directions in the product topology. That homeomorphism is formalized;
see `../3-formalized/weil-logshift-recovery-homeomorphism.md`.
No claim of uniform-norm stability, external novelty, or an RH proof.
