# Rotated elliptic Eisenstein series descends to the actual unipotent quotient

- **Stage:** 3-formalized
- **Parent:** [Elliptic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** The arithmetic coset series with an actual idele rotation
  is well-defined on arithmetic Borel cosets and invariant under rotated
  right arithmetic translation. Its unipotent restriction descends to the
  literal arithmetic quotient. This independently defines its constant-term
  integral against the audited quotient probability.

## Proof

Compose the actual arithmetic embedding with the idele rotation. If two
rational loops differ on the right by an arithmetic Borel element, their
rotated images differ by its Borel rotation. The proved character invariance
and arithmetic character triviality give equal Iwasawa summands. Therefore
the summand descends to the arithmetic coset quotient.

Left multiplication by a restricted rational loop permutes those cosets.
Reindexing the independently defined sum gives right invariance under its
rotated arithmetic image. For two actual unipotent representatives with
`u⁻¹v ∈ Γ`, choose its actual restricted rational preimage. Multiplicativity
of rotation and the preceding invariance identify the two values. This
proves descent to `U_A/(U_A∩Γ)`, so its integral uses the actual quotient
probability and no Weyl-sum definition.

These are algebraic descent identities and definitions. Summability,
measurability, integrability, and the unfolding identity remain separate
unproved assertions.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticRotatedEisenstein.lean`.
`rotatedIwasawaSection_arithmetic_coset`,
`ellipticRotatedEisensteinSeries_right_arithmetic`,
`ellipticEisensteinOnUnipotentQuotient`, and
`ellipticEisensteinConstantTerm` passed direct Lean and transitive axiom audits;
only `propext`, `Classical.choice`, and `Quot.sound` occur.
