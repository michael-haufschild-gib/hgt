# First-order Clifford interpolation law — Lean certificate

- **ID:** `first-order-clifford-interpolation-law-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `first-order-clifford-interpolation-law.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Capstones

- `GaloisForLFunctions.HTGeometry.twoInvolutionQuarterTurnOddDifferenceIdentity` — the card's `(1)`,
  over an arbitrary ring.  Axiom audit: `[propext, Quot.sound]` — no choice.
- `GaloisForLFunctions.HTGeometry.finiteTwoReplicaSingleSiteCollectiveCommutator_eq_cliffordDifference_of_relativeOdd`
  — the card's `(2)`, for every finite qubit register.
- `GaloisForLFunctions.HTGeometry.firstDefectCollectiveCommutator_mem_canonicalObstruction` — the
  frontier consequence, with no hypothesis.

## What was already closed

`HTGeometry/TwoReplicaFirstOrderCliffordInterpolation.lean` proved both displayed identities and
both containment statements.  The card's emphasis is worth repeating: `(1)` is a ring identity
between commuting involutions, so nothing continuous, no differentiation of a finite group action,
and no fourth-moment inference enters.  Its Lean proof is choice-free.

`(2)` specialises it with `A = P ⊗ I`, `B = I ⊗ P`, `J = i`, and the strict quarter turns, and
holds exactly on the odd paired-Pauli sector — the card's hostile audit is respected in the
statement's hypothesis `hodd`.

## What the assembly needed

The umbrella build, and the discharge of the greatest-maximizer premise.  Both containment theorems
were stated for a subspace `U` assumed greatest; the card describes `U_*` as *the* canonical
obstruction.  With `canonicalTwoReplicaQLocalObstruction` a named subspace,
`HTGeometry/FirstOrderCliffordInterpolationCanonical.lean` restates them there:

- `finiteTwoReplicaSingleSiteCollectiveCommutator_mem_canonicalObstruction_of_relativeOdd`;
- `firstDefectCollectiveCommutator_mem_canonicalObstruction`.

No new mathematics — the invariance argument is unchanged; what changes is that the subject is a
term rather than a hypothesis.

## Why this matters downstream

The card notes that `(2)` is "stronger than the previous square identity, which only proved
preservation after applying the commutator twice".  That strength is what
`nonzero-pauli-internal-reproduction-law` consumes: internal reproduction needs the *first* image
back inside the obstruction, not the second.
