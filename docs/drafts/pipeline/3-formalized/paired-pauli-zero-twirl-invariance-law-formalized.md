# Paired-Pauli zero-twirl invariance law — Lean certificate

- **ID:** `paired-pauli-zero-twirl-invariance-law-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `paired-pauli-zero-twirl-invariance-law.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Capstones

The card's `(1)`, both halves, on every finite qubit register:

- `GaloisForLFunctions.HTGeometry.finiteProductCliffordTwoReplicaTwirl_comp_pairedPauli` —
  `T_V ∘ C_Q = T_V` as an identity of linear maps.
- `GaloisForLFunctions.HTGeometry.finiteProductCliffordTwoReplicaTwirl_ker_pairedPauli_invariant` —
  `C_Q (ker T_V) ⊆ ker T_V`.

Axiom audit: `[propext, Classical.choice, Quot.sound]`.

## What was already closed

`HTGeometry/TwoReplicaGlobalCliffordTwirlRange.lean` had the mathematical content:
`finiteProductCliffordTwoReplicaTwirl_pairedPauli_input` (`T_V (C_Q X) = T_V X`) and the kernel
half.  The card's `(2)` — right-translation of the averaging index — is
`finiteProductCliffordTwoReplicaTwirl_conjugated_input`, and the card's `(3)`/`(4)` — realizing
paired-Pauli conjugation inside the strict product-Clifford code — is
`finiteProductCliffordDoubledConjugation_pauliHalfTurn`.

That last step is where the card's hostile audit puts the risk ("not from the false assertion that
projective Pauli matrices literally belong to `SU(2)` without phases"), and the Lean proof never
tracks `η_Q` at all: the half-turn code is a genuine group element, and conjugation by it cancels
the scalar against its conjugate before any phase can appear.

`HTGeometry/FinitePauliCharacterProjector.lean` had the projector and the fact that it preserves any
paired-Pauli invariant subspace, plus graded extraction from a member sum.

## What the assembly needed

Three things, in `HTGeometry/PairedPauliZeroTwirlInvariance.lean`.

1. **The operator form.**  The card states `(1)` as `T_V C_Q = T_V`, an equation between operators;
   the corpus had it pointwise.  `LinearMap.ext` closes the gap, but the card's statement is the one
   downstream users compose with, so it is recorded.

2. **The empty register.**  The card calls this out explicitly.  Nothing in the development assumes
   the register is nonempty or ordered — the hypotheses are `[Fintype V] [DecidableEq V]` — so the
   empty register is an instance rather than a separate case, recorded as
   `finiteProductCliffordTwoReplicaTwirl_comp_pairedPauli_empty`.

3. **The frontier consequence, unconditionally.**  The card asserts that
   `U_W = U_* ∩ ker T_V` is paired-Pauli invariant "because both factors are invariant", hence that
   the exact character projectors preserve `U_W`.  Invariance of the first factor was previously
   conditioned on a greatest-maximizer premise; with the canonical obstruction now a named subspace
   (`CanonicalTwoReplicaObstruction.lean`), `canonicalTwoReplicaHiddenLayer_pairedPauli_invariant`
   is hypothesis-free, and the two consequences follow:

   - `finiteTwoReplicaPauliCharacterProjector_mem_canonicalHiddenLayer`;
   - `finiteTwoReplicaPauliCharacter_component_mem_canonicalHiddenLayer` — if a sum of exact
     character components lies in `U_W`, each component does.  This is the card's "the aggregate
     visible detector can recover every hidden character component modulo `U_W`", and it is the
     hypothesis consumed by `aggregate-pauli-visible-quotient-detector-law`.
