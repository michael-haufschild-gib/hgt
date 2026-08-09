# Visible-kernel recovery Hall law — Lean certificate

- **ID:** `visible-kernel-recovery-hall-law-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `visible-kernel-recovery-hall-law.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Capstone

`GaloisForLFunctions.HTGeometry.canonicalTwoReplicaObstruction_finrank_le_shadow_add_two` — for
every nonempty finite register, every `q ≥ 2`, and every preconnected simple interaction graph,

    dim U_*  ≤  dim (weight-≤q collective Pauli shadow of U_*)  +  2 ,

where `U_*` is the canonical greatest maximum-defect subspace of the weight-at-most-`q` two-replica
collective Pauli family.  No further hypothesis.

Axiom audit: `[propext, Classical.choice, Quot.sound]`.

## The four items the card left open

The card's hostile audit ended: "Remaining formal work is the product-local lift of those results,
identity `(5a)` and `K_1` injectivity, quotient detector `(7)`, and physical edge-Casimir
restriction."  All four are formalized.

| Item | Where |
|---|---|
| product-local lift | `global-product-clifford-twirl-range-law` — `ran T_V = S_V`, `T_V² = T_V`, `dim S_V = 2^{\|V\|}`, and the direct split of `U_*` |
| identity `(5a)` | `finiteTwoReplicaSingleSiteCollectiveCommutator_square_groupAlgebra` |
| `K_1` injectivity | `finiteTwoReplicaSingleSiteCollectiveSquare_injective_on_productCliffordTwirl_ker`, from the Hilbert–Schmidt energy identity for the one-site family |
| quotient detector `(7)` | `aggregate-pauli-visible-quotient-detector-law` |
| physical edge-Casimir restriction | `two-replica-global-physical-edge-casimir-law`, `positive-graph-edge-casimir-kernel-law` |

## What the assembly needed

`HTGeometry/TwoReplicaHallSaturationCanonical.lean`.

The universal theorem and every physical ingredient were already proved, but each was stated for a
subspace *assumed* to be the greatest defect maximizer.  With
`canonicalTwoReplicaQLocalObstruction` a named subspace (see
`nonzero-pauli-internal-reproduction-law-formalized.md`), the premise is discharged and three
statements follow:

- `canonicalTwoReplicaObstruction_zeroTwirl_reproduced` — the zero-twirl layer lies in its own
  one-step shadow.  This is the condition that
  `product-clifford-visible-recovery-reduction-law` isolates as its last premise; it is *proved*,
  by the one-site quadratic return, not assumed.  The card's warning that nonzero-character Hall
  alone would not give it is respected — the proof does not go that way.
- `canonicalTwoReplicaObstruction_finrank_mod_synchronized` — the mixed inequality with the exact
  correction `dim(U_S ⊓ N)`.
- `canonicalTwoReplicaObstruction_finrank_le_shadow_add_two` — the same with the constant `2`, since
  `N` is two-dimensional.

## Why the correction cannot be removed

The card's parent audit is right that unreduced all-subspaces Hall is false: the global identity and
the global replica swap are annihilated by every collective commutator, so any subspace containing
either has strictly smaller shadow.  `N` is exactly two-dimensional
(`finrank_finiteTwoReplicaGlobalSynchronizedSubmodule`), so `+2` is the sharp constant, and it does
not grow with the register.

## Not claimed

This is a dimension count on the two-replica operator algebra.  Nothing about circuit
anti-concentration, complexity growth, plateau measure, or recurrence scale follows from it, and the
card says so.
