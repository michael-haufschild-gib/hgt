# Elliptic unipotent coordinates identify the actual restricted group

- **Stage:** 2-fully-proven
- **Parent:** [Elliptic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** Completed unipotent matrices over the actual adele ring,
  with one common finite exceptional-place set for all coefficients, map
  bijectively to the positive unipotent subgroup of the actual restricted
  central loop group.

## Proof

Evaluate every matrix coefficient in each completion and use the canonical
positive-loop embedding. Its full integral-loop intersection is exactly
coefficient integrality. Thus uniform integrality makes these local loops
an element of the restricted carrier. Evaluation and the positive embedding
are group homomorphisms. Their product is injective: local embeddings are
injective, the free stream commutes with evaluation, and all evaluations
together distinguish actual adeles.

Conversely, lift each local positive unipotent loop uniquely to its actual
power-series matrix. Outside the single finite exceptional set of the given
restricted loop, every coefficient of every local matrix is integral. For
each stream index, assemble its local values into an adele. The exceptional
set is independent of that index. Decode this adele stream. Naturality and
the stream bijection identify every local evaluation with the chosen local
matrix. Hence decoding gives the required uniformly integral preimage.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticUnipotentCarrier.lean`:
`adelicUnipotentEmbedding_injective`, `adelicUnipotentEmbedding_surjective`.
Direct check pending.
