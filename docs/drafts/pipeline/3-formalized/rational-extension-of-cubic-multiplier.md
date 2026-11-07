# Rational extension of the cubic multiplier

- **ID:** rational-extension-of-cubic-multiplier
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [metaplectic Möbius descent](../1-in-progress/metaplectic-mobius-descent.md)
- **Statement:** Extend the actual cubic character from `Γ(3)` to `Γ(3)·SL₂(ℤ)`, trivially on rational matrices; prove that this larger group normalizes the metaplectic kernel.

Conjugation by rational generators `S,T` preserves the multiplier. For `S`,
use the inverse and upper-right symbol formulas; for `T`, reciprocity turns
the denominator shift into numerator congruence.

The character is trivial on `Γ(3)∩SL₂(ℤ)`. For rational coprime arguments,
remove powers of three using the different's supplementary law and apply
reciprocal Euclidean reduction. These facts make `κ(nr)=κ(n)` independent
of the product decomposition and prove multiplicativity. The extended
character then gives invariance of the original kernel under conjugation.

Source: external OpenAI `Reciprocity/KubotaCharacter.lean`.
Lean: `MetaplecticMobiusDescent/TheCubicMultiplierExtendsOverRationalMatrices.lean`.
Endpoints: `CubicKubota.value_conjugate_rational`,
`CubicJacobi.rational_symbol_eq_one`, `CubicKubota.extendedComplexCharacter_restrict`,
`extendedComplexCharacter_rational`, `extendedComplexCharacter_cube`,
`globalKubotaKernel_conjugate`, `kernelInRationalExtension_finiteIndex`, and
`kernelInRationalExtension_normal`. Direct Lean check passes; all eight
transitive audits use only `propext`, `Classical.choice`, and `Quot.sound`.

The cubic theta transformation remains a separate analytic obligation.
