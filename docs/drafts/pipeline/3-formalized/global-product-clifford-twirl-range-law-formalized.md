# Global product-Clifford twirl range law — Lean certificate

- **ID:** `global-product-clifford-twirl-range-law-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `global-product-clifford-twirl-range-law.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Capstones

- `GaloisForLFunctions.HTGeometry.finiteProductCliffordTwoReplicaTwirl_range_eq` — `ran T_V = S_V`.
- `GaloisForLFunctions.HTGeometry.finiteProductCliffordTwoReplicaTwirl_idempotent` — `T_V² = T_V`.
- `GaloisForLFunctions.HTGeometry.finrank_finiteProductCliffordTwoReplicaTwirl_range` —
  `dim_ℂ S_V = 2^{|V|}`.
- `GaloisForLFunctions.HTGeometry.canonicalTwoReplicaQLocalObstruction_twirl_split` and
  `..._twirl_disjoint` — the card's `U_* = (U_* ∩ S_V) ⊕ (U_* ∩ ker T_V)`, with no hypothesis.

Axiom audit: `[propext, Classical.choice, Quot.sound]`.

## What was already closed

`HTGeometry/TwoReplicaGlobalCliffordTwirlRange.lean` had the range and idempotence.  The card's
proof factorises `T_V` as `⨂_v T_v` and then diagonalises in a tensor basis; the Lean proof does not
need the second step.  `finiteProductCliffordTwoReplicaTwirl_localMatrix` gives the sitewise action
on a pure local tensor, and `finiteTwoReplicaMatrix_eq_sum_localUnits` says every global matrix is a
sum of local matrix units, so the range is determined by what happens on those — no choice of a
basis of `ran T_v` extended by a basis of `ker T_v`, and no induced tensor-product basis.

Injectivity of the swap-coefficient embedding (`finiteTwoReplicaSwapInvariantEmbed_injective`) was
also already proved, from the explicit Möbius extractor the card cites.

## What the assembly needed

1. **The dimension.**  The card asserts `dim_ℂ S_V = 2^{|V|}` from linear independence of the swap
   words.  In Lean that independence *is* injectivity of the coefficient embedding, so the dimension
   is `finrank ℂ ((V → Bool) → ℂ)` transported along `LinearMap.finrank_range_of_inj`.

2. **The empty register.**  The card says both sides are then the one-dimensional scalar algebra.
   Recorded as `finrank_finiteProductCliffordTwoReplicaTwirl_range_empty`; it is the instance
   `2^0 = 1` of the general dimension formula, not a separate argument.

3. **The split, unconditionally.**  The existing splitting theorem carried the greatest-maximizer
   premise.  With `canonicalTwoReplicaQLocalObstruction` a named subspace it is discharged, and the
   two summands are exactly the `canonicalTwoReplicaVisibleSource` and
   `canonicalTwoReplicaHiddenLayer` already used by the detector and zero-twirl cards.

4. **Directness.**  The corpus theorem gives the join; the card writes `⊕`.  The disjointness needs
   nothing about the obstruction at all — the range and kernel of an idempotent meet in zero, so any
   two subspaces contained in them do.  That is `canonicalTwoReplicaQLocalObstruction_twirl_disjoint`.

## Position in the two-replica chain

This card supplies the fact that the visible source and the hidden layer *exhaust* the canonical
obstruction and meet only in zero.  `paired-pauli-zero-twirl-invariance-law` supplies their
paired-Pauli invariance, and `aggregate-pauli-visible-quotient-detector-law` consumes both.
