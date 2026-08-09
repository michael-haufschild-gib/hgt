# Finite Pauli-character projector extraction law — Lean certificate

- **ID:** `finite-pauli-character-projector-extraction-law-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `finite-pauli-character-projector-extraction-law.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Capstones

- `GaloisForLFunctions.HTGeometry.finitePauliConjugationSign_orthogonality` — the card's `(1)`.
- `GaloisForLFunctions.HTGeometry.finiteTwoReplicaPauliCharacterProjector_apply_grade` — the card's
  `(3)`.
- `GaloisForLFunctions.HTGeometry.finiteTwoReplicaPauliCharacter_component_mem_of_sum_mem` — the
  card's `(4)`, the extraction step.
- `GaloisForLFunctions.HTGeometry.finiteTwoReplicaPauliCharacterProjector_of_isEmpty` — the empty
  register: the projector is the identity map.

Axiom audit: `[propext, Classical.choice, Quot.sound]`.

## What was already closed

`HTGeometry/FinitePauliCharacterProjector.lean` had the one-site sign orthogonality `(5)`, its
factorisation into the global statement `(1)`, the normalized projector `(2)`, its exact action on a
grade `(3)`, the fact that it preserves any paired-Pauli invariant subspace, and the graded
extraction `(4)`.

The card's proof of `(1)` factors `∑_Q ∏_v` into `∏_v ∑_q` by finite distributivity; that is what
the Lean proof does, so the argument is the card's, not a substitute.

## What the assembly needed

Two statements the card makes and the corpus did not carry, both in
`HTGeometry/PauliCharacterProjectorExtraction.lean`.

1. **The empty register.**  The card says "there is one character and its projector is the
   identity".  The route is `finitePauliMatrix_const_none`: the all-identity Pauli string is the
   identity matrix, so `finiteTwoReplicaPairedPauliConjugationLinear_const_none` says conjugation by
   the trivial paired label does nothing.  On an empty register that is the only label, the
   normalization `4^0` is one, and the sign is an empty product, so
   `finiteTwoReplicaPauliCharacterProjector_of_isEmpty` gives `LinearMap.id` with no orthogonality
   argument left to make.  `card_pauliLabel_of_isEmpty` records the count.

   The trivial-label conjugation lemma is stated for an arbitrary register, not just the empty one —
   it is the general fact that the all-identity label acts trivially, which is worth having on its
   own.

2. **`Π_P(U) ≤ U` as an inclusion.**  The corpus proved the memberwise form; the card writes the
   submodule inequality, which is what a downstream invariance argument composes with.

## Frontier obligations

The card lists four.  Three are now closed on sibling cards: the paired-Pauli invariance of the
product-Clifford zero-twirl canonical layer and the aggregate quotient detector with its
hidden-kernel law (`paired-pauli-zero-twirl-invariance-law`,
`aggregate-pauli-visible-quotient-detector-law`), and the identification and count of the global
identity/global-swap kernel (`positive-graph-edge-casimir-kernel-law`).

The fourth — reproducing the nonsinglet layer by the one-site central-Casimir family — remains open
and belongs to `visible-kernel-recovery-hall-law`.
