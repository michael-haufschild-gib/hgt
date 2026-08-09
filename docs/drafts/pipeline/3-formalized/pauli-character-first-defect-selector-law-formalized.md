# Pauli-character first-defect selector law — Lean certificate

- **ID:** `pauli-character-first-defect-selector-law-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `pauli-character-first-defect-selector-law.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Capstone

`GaloisForLFunctions.HTGeometry.invariantSubspace_inf_nonzeroCharacter_finrank_le_shadow` — for a
subspace stable under every paired-Pauli conjugation, the intersection with the sum of the nonzero
character subspaces expands under the literal weight-one collective Pauli family.  This is the
card's `(4)` in the card's own terms.

## What was already closed

`PauliCharacterFirstDefectSelector.lean`, `FinitePauliConjugationLaw.lean`,
`TwoReplicaGlobalPauliHallSymmetryReduction.lean`,
`FiniteCommutingInvolutionParityDecomposition.lean`,
`PauliCharacterFirstDefectCovariance.lean`, `PauliCharacterFirstDefectHallExpansion.lean` — the
first-defect permutation, the weight-one selector and its exact anticommutation, arbitrary-string
Pauli conjugation, paired commutation and covariance, span preservation, canonical invariance,
character injectivity, independence of the character subspaces, and the Hall expansion for the
*resolved* nonzero-character part.

## What the assembly needed

The existing capstone is stated for `⨆_{δ≠0}(U ⊓ X_δ)`.  The card states `(4)` for
`U ∩ ⊕_{δ≠0} X_δ`.  They agree exactly when `U` is graded by the character decomposition — the
card's step `(5)`, which the paper proof obtains from character averaging.  Five modules close it.

1. **`SimultaneousParityGrading.lean`.**  A subspace stable under a finite family of commuting
   involutions is the sum of its simultaneous parity components, indexed by sign patterns on the
   family.  The induction peels one involution at a time and records its sign by updating the
   pattern at that index.  No averaging projector and no character orthogonality appears — the paper
   proof uses both.  The same module proves `inf_biSup_eq_biSup_inf_of_graded`: a subspace graded by
   an independent family meets every partial sum of that family gradewise, from the modular law and
   disjointness of complementary partial sums.

2. **`FiniteQubitPauliComplexBasis.lean`.**  The literal Pauli strings are a *complex* basis of the
   qubit matrix algebra.  The corpus already had their complex linear independence and a real basis
   of the Hermitian matrices; the real basis is not enough here, because the two-replica space
   contains non-Hermitian directions.

3. **`TwoReplicaPauliCharacterCompleteness.lean`.**  The character subspaces exhaust the two-replica
   space.  The phase-free Pauli labels carry a product (`pauliLabelMul`) and the conjugation sign is
   multiplicative in it — a finite table, decided rather than computed, since the label arithmetic is
   decidable even though the signs live in `ℂ`.  Hence a Kronecker product of two Pauli strings lies
   in the character subspace of the product label.  And Kronecker products of Pauli strings span the
   doubled algebra: a standard basis matrix on a product index is a Kronecker product of standard
   basis matrices, so the bilinear Kronecker image of the two full factors is everything.

4. **`JointEigenspaceExhaustion.lean`.**  If an independent family of subspaces exhausts the module
   and each member is a simultaneous eigenspace for a family of operators, then a scalar pattern
   realized by no member carries no joint eigenvector.  The proof is a finite induction along the
   partial sums: a joint eigenvector inside a partial sum meets the operator separating its pattern
   from the leading component's character, which forces that component into the smaller partial sum,
   and independence removes it.  The finiteness is free — the partial sums over finite index sets
   are directed.  No projector and no `DirectSum` machinery.

5. **`PauliCharacterGradedAssembly.lean`.**  The assembly.  Character subspaces are joint
   eigenspaces of the paired conjugations; parity subspaces are joint eigenspaces at `±1` patterns;
   patterns realized by no Pauli word vanish by (4).  Hence `U = ⨆_P (U ⊓ X_P)` for invariant `U` —
   the card's `(5)` — and then `inf_biSup_eq_biSup_inf_of_graded` gives
   `U ⊓ (⨆_{P≠0} X_P) = finiteTwoReplicaNonzeroPauliResolvedSubspace U`, so the existing Hall
   expansion is the capstone.

## Design note

The paper proof of `(5)` runs through finite character averaging: the projector onto each character
subspace is a combination of the conjugations, so it preserves any invariant subspace.  That route
needs the group law on Pauli words and character orthogonality.  The Lean proof avoids both.  It
splits parity one involution at a time, which is elementary, and then repairs the mismatch between
sign patterns and Pauli-word characters by showing the unrealized patterns are empty — which needs
only independence and completeness of the character family, both of which are wanted anyway.

## Verification

- `lake env lean` on each of the five modules — clean, no warnings.
- `lake build GaloisForLFunctions.HTGeometry.PauliCharacterGradedAssembly` — succeeds.
- `#print axioms` on every declaration in the five modules:
  `[propext, Classical.choice, Quot.sound]` only.
