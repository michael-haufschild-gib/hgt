# Nonzero Pauli internal-reproduction law — Lean certificate

- **ID:** `nonzero-pauli-internal-reproduction-law-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `nonzero-pauli-internal-reproduction-law.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Capstone

`GaloisForLFunctions.HTGeometry.finiteTwoReplicaNonzeroPauliResolvedSubspace_canonical_le_shadow`
— the card's `(1)`, with no hypotheses, on any finite linearly ordered qubit register and for
every `q`:

    U_{≠0} ≤ linearFamilyShadow (weight-one collective Pauli family) U_{≠0} ,

where `U_{≠0} = finiteTwoReplicaNonzeroPauliResolvedSubspace (canonicalTwoReplicaQLocalObstruction V q)`.

Axiom audit: `[propext, Classical.choice, Quot.sound]`.

## What was already closed

`HTGeometry/TwoReplicaNonzeroPauliInternalReproduction.lean` proved the general mechanism —
`gradedInjectiveSelector_subspace_le_shadow_of_internal`: a collision-free injective graded
selector whose images land back inside the resolved input reproduces that input inside its own
one-step shadow, because the images are independent, dimension-preserving, and therefore assemble
to a subspace of equal dimension.  It then instantiated `(1)` for any `U` satisfying the
greatest-maximizer condition.

## What the assembly needed

The instantiation carried a premise:

    hgreatest : ∀ W, linearFamilyDefect A W = linearFamilyDefect A U → W ≤ U

The card does not state this as an assumption — it says "let `U_*` be **the** canonical greatest
maximum-defect subspace", which is a definition.  Nothing in the corpus turned that definite
description into a term, so every one of the thirteen `TwoReplica*` modules restated the condition
as a hypothesis instead.

`HTGeometry/LinearFamilyGreatestMaximizer.lean` closes the gap.  The existence *and* uniqueness of
the greatest defect maximizer was already proved from supermodularity
(`existsUnique_linearFamilyDefect_greatestMaximizer`), so the subspace is a function of the family
and can be named outright:

- `linearFamilyGreatestMaximizer` — the subspace itself.
- `linearFamilyDefect_le_greatestMaximizer` — it maximizes.
- `le_linearFamilyGreatestMaximizer` — it is greatest; this is exactly the discharged premise.
- `eq_linearFamilyGreatestMaximizer` — no other subspace has both properties, so the name is
  unambiguous and matches the card's "canonical".
- `linearFamilyHall_iff_greatestMaximizer_defect_eq_zero` — the all-subspaces Hall condition is the
  vanishing of this one subspace's deficiency, with no maximality side condition to supply.

`HTGeometry/NonzeroPauliInternalReproductionCanonical.lean` names the card's `U_*` as
`canonicalTwoReplicaQLocalObstruction` and applies the conditional capstone to it.

## Note for the rest of the two-replica layer

The same premise appears in twelve further modules —
`TwoReplicaFirstOrderCliffordInterpolation`, `TwoReplicaTwoScaleLocalCommutatorClosure`,
`TwoReplicaGlobalCliffordTwirlRange`, `TwoReplicaRationalLocalRotationCovariance`,
`TwoReplicaGlobalPauliHallSymmetryReduction`, `TwoReplicaPauliHallSymmetryReduction`,
`TwoReplicaProductCliffordVisibleRecovery`, `TwoReplicaSingleSiteZeroTwirlRecovery`,
`TwoReplicaPauliVisibleQuotientDetector`, `TwoReplicaGlobalCliffordHallSymmetryReduction`,
`TwoReplicaCliffordTwirlHallSymmetryReduction`, and `PauliCharacterFirstDefectHallExpansion`.
Each of their capstones can now be restated at `canonicalTwoReplicaQLocalObstruction` by supplying
`le_linearFamilyGreatestMaximizer`, with no new mathematics.  Those restatements belong to their own
cards.
