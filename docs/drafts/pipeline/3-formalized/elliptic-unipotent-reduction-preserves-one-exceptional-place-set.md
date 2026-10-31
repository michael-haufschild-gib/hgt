# Elliptic unipotent reduction preserves one exceptional-place set

- **Stage:** 3-formalized
- **Parent:** [Elliptic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** If every coefficient of a completed adelic unipotent
  matrix is integral outside one finite set of places, its canonical
  rational correction has the same property, with the same exceptional set.
  The reduced matrix is integral at every finite place.

## Proof

Fix a finite place and let `Aᵥ` be the subring of adeles integral there.
Assume every original stream coefficient belongs to `Aᵥ`. Induct on the
correction index. Earlier diagonal corrections belong to `Aᵥ` by induction,
so subring preservation of the triangular correction puts its next input
in `Aᵥ`. The proved additive rational projection preserves integrality at
this place; negation does too. This proves the claim at every index.

Apply this argument separately at each place outside the original finite
exceptional set. No union over coefficient indices is taken. Every reduced
coefficient belongs to the additive gap domain, which is integral at all
finite places. Subring descent identifies free-stream integrality with
integrality of all matrix entries. The previously proved uniqueness
therefore restricts to the groups with a common finite exceptional set.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticUnipotentIntegrality.lean`:
`adeleUnipotentCorrectionStream_integral_at`,
`adeleUnipotentRationalCorrection_uniform`,
`existsUnique_uniformlyIntegralUnipotentCorrection`. Direct Lean check passed; all three axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
