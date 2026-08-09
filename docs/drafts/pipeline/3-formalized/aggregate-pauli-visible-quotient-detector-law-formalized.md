# Aggregate Pauli visible-quotient detector law — Lean certificate

- **ID:** `aggregate-pauli-visible-quotient-detector-law-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `aggregate-pauli-visible-quotient-detector-law.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Capstone

`GaloisForLFunctions.HTGeometry.finiteTwoReplicaPauliVisibleQuotientDetector_canonical_mem_ker_iff`
— the card's `(2)` at the card's own concrete layer, with no hypotheses, on any finite qubit
register and for every locality cutoff `q`:

    D(s) = 0  ↔  ∀ P, A_P s ∈ U_* ⊓ ker T_V ,

for `s` in `U_* ⊓ range (swap-invariant embedding)`.

Axiom audit: `[propext, Classical.choice, Quot.sound]`.

## What was already closed

`HTGeometry/TwoReplicaPauliVisibleQuotientDetector.lean` had the whole abstract layer, and had it
in the *general* form — for an arbitrary zero-character source `Uₛ` and an arbitrary paired-Pauli
invariant target `W`:

- `finiteTwoReplicaPauliVisibleQuotientDetector` — the card's `(1)`.
- `finiteTwoReplicaPauliVisibleQuotientDetector_mem_ker_iff` — the card's `(2)`.
- `finiteTwoReplicaPauliVisibleRangeInclusion_injective` — the detector already takes values in the
  actual quotient, so the range inclusion is a subtype map and injectivity is `Subtype.val_injective`.
  The card's "no separate direct-sum codomain, dimension comparison, or choice of grade
  representatives is needed" is literally what the proof shows.
- `finiteTwoReplicaPauliVisibleRangeInclusion_range_le` — the embedded range lies in the quotient of
  the one-step weight-at-most-`q` output.

These are stronger than the canonical instance, so the concrete layer needs no restatement of them.

## What the assembly needed

The card's "Concrete canonical layer" asserts that `U_W = U_* ∩ ker T_V` satisfies the
invariant-subspace premise of `(2)` **unconditionally**.  In Lean it did not: the invariance theorem
carried

    hgreatest : ∀ W, linearFamilyDefect A W = linearFamilyDefect A U → W ≤ U

because nothing in the corpus turned the card's definite description "the canonical greatest
two-replica Hall obstruction" into a term.

`HTGeometry/CanonicalTwoReplicaObstruction.lean` supplies it.  Existence *and* uniqueness of the
greatest defect maximizer were already proved from supermodularity, so the subspace is a function of
the family; `canonicalTwoReplicaQLocalObstruction` names it and
`le_canonicalTwoReplicaQLocalObstruction` is exactly the discharged premise.

`HTGeometry/PauliVisibleQuotientDetectorCanonical.lean` names both sides of the card's concrete
layer and closes it:

1. `canonicalTwoReplicaHiddenLayer` = `U_* ⊓ ker T_V`, with
   `canonicalTwoReplicaHiddenLayer_pairedPauli_invariant` — product-Clifford covariance fixes `U_*`
   under every paired-Pauli conjugation, and the strict half-turn identity makes the twirl kernel
   invariant.  Both were already proved; only the premise was in the way.
2. `canonicalTwoReplicaVisibleSource` = `U_* ⊓ range (swap-invariant embedding)`, with
   `canonicalTwoReplicaVisibleSource_le_zeroCharacter`.  This one was *already* unconditional in the
   corpus: the swap sector of **any** subspace has exact zero paired-Pauli character, because the
   swap-invariant range coincides with the product-Clifford twirl range and every twirled vector is
   fixed by every paired-Pauli half-turn.  The card's "for the canonical greatest obstruction" is
   more restrictive than what the proof needs.
3. The capstone, obtained by feeding 1 and 2 to the general `(2)`.

## Relation to the sibling card

`CanonicalTwoReplicaObstruction.lean` is shared with
`nonzero-pauli-internal-reproduction-law-formalized.md`, which introduced the general
`linearFamilyGreatestMaximizer` layer.  Eleven further two-replica modules still carry the same
premise; each can be restated at `canonicalTwoReplicaQLocalObstruction` by supplying
`le_canonicalTwoReplicaQLocalObstruction`, with no new mathematics.
