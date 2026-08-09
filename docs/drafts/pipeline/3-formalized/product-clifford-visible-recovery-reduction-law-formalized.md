# Product-Clifford visible-recovery reduction law — Lean certificate

- **ID:** `product-clifford-visible-recovery-reduction-law-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `product-clifford-visible-recovery-reduction-law.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Capstones

- `GaloisForLFunctions.HTGeometry.finiteProductCliffordTwoReplicaTwirl_collectiveCommutator_eq_zero_of_mem_range`
  — the card's `(1)`: the twirl kills every collective commutator image of its own range.
- `GaloisForLFunctions.HTGeometry.finiteTwoReplicaQLocal_shadow_le_productCliffordTwirl_ker_of_le_range`
  — the card's `(2)`.
- `GaloisForLFunctions.HTGeometry.canonicalTwoReplicaObstruction_finrank_mod_synchronized_of_zeroTwirl_reproduced`
  — the card's `(4)` at the canonical obstruction, with `(3)` as its only premise.
- `GaloisForLFunctions.HTGeometry.canonicalTwoReplicaObstruction_finrank_le_shadow_add_two_of_zeroTwirl_reproduced`
  — the same with the constant `2` in place of `dim(U_S ∩ N)`.

Axiom audit: `[propext, Classical.choice, Quot.sound]`.

## On `(3)`

The card states `(4)` as a conditional: *if* `(3)`, then `(4)`.  Its hostile audit says so plainly —
"Condition (3) remains unproved for the complete canonical zero-twirl layer".  So `(3)` appearing as
a Lean hypothesis is the card's own statement, not a shortfall of the formalization.  Everything the
card claims to *prove* is proved.

## What was already closed

`HTGeometry/TwoReplicaProductCliffordVisibleRecovery.lean` had `(1)`, `(2)`, the physical detector
wrapper `(4)`, and the reduction to `(3)` for a greatest maximizer.

The proof of `(1)` is exactly the card's finite-group character separation: a nonidentity Pauli word
admits a paired Pauli whose conjugation sign is `-1`, the twirl is unchanged by paired-Pauli
conjugation, so `T(A_P X) = -T(A_P X)`.  No Haar or continuous-symmetry step appears anywhere, which
is what the hostile audit demands.

## What the assembly needed

`HTGeometry/ProductCliffordVisibleRecoveryCanonical.lean`:

1. **The greatest-maximizer premise, discharged.**  The reduction is restated at
   `canonicalTwoReplicaQLocalObstruction`, whose two summands are the
   `canonicalTwoReplicaVisibleSource` and `canonicalTwoReplicaHiddenLayer` shared across this
   family.  The card says the split "automatically supplies `U_S`, `U_W`, disjointness, paired-Pauli
   invariance, detector hidden-kernel classification, visible quotient rank, and connected graph
   recovery" — all seven are now available at a named subspace, so `(3)` reads as a single inclusion
   about a named object.

2. **The correction term bounded.**  The card identifies `N` as "exactly the span of global identity
   and global replica swap".  That sector is two-dimensional
   (`finrank_finiteTwoReplicaGlobalSynchronizedSubmodule`, from the graph edge-Casimir card), so the
   inequality holds with the constant `2`.  This is the form a Hall argument uses: the correction is
   an absolute constant, independent of the register.

## `(3)` is discharged

The card lists `(3)` as unproved, and it was when the card was written.  It is proved for the
canonical obstruction in `HTGeometry/TwoReplicaSingleSiteZeroTwirlRecovery.lean`: the one-site
collective family has a Hilbert–Schmidt energy identity, its squared sum is injective on the
zero-twirl sector, and so the zero-twirl layer lies in its own one-step shadow.  The route is *not*
nonzero-character Hall — the card is right that that would not suffice — but the one-site quadratic
return, which sees the anisotropic directions too.

`canonicalTwoReplicaObstruction_zeroTwirl_reproduced` states it at the canonical obstruction, and
`canonicalTwoReplicaObstruction_finrank_le_shadow_add_two` is the resulting unconditional
inequality.  See `visible-kernel-recovery-hall-law-formalized.md`.

## Not claimed

The card's remaining limits stand: nothing about anti-concentration, complexity growth, plateau, or
recurrence follows from these dimension counts.
