# Affine polynomial cell heads are unique

- **Stage:** 3-formalized
- **Parent:** [Arithmetic cell coordinates](../1-in-progress/affine-a1-bruhat-cells-have-one-polynomial-root-coordinate.md).
- **Statement:** The polynomial heads in all four monomial cell families
  are unique modulo the right Iwahori. Matrix right-coset factorizations
  lift modulo the actual positive Borel.

## Proof

Equality of right cosets puts the conjugated difference of the two root
parameters in the Iwahori. Upper parameters must be integral; lower
parameters must be strictly integral. For upper and lower translations,
these conditions force `p-q` to be divisible by `X^(2n)`. For upper and
lower reflections they force divisibility by `X^(2n+1)`.

For a strictly integral power series, the constant coefficient vanishes,
so one first factors out `X`. All coefficients below the indicated power
then vanish. All later coefficients vanish by the degree bounds on both
heads. Thus `p=q`.

If `projection(g)=projection(r)j` with `j` in the Iwahori, then
`projection(r⁻¹g)=j`. The audited Borel preimage identity gives
`r⁻¹g∈B`, hence `g=r(r⁻¹g)`. This absorbs central discrepancies without
claiming that the residual Borel character is trivial.

## Lean

`HTGeometry/LoopEisenstein/AffinePolynomialCellUniqueness.lean`: `upper_polynomial_translation_unique`,
`lower_polynomial_translation_unique`, `upper_polynomial_reflection_unique`,
`lower_polynomial_reflection_unique`, and
`LoopSL2.exists_right_borel_of_projection_factor` passed direct Lean and
transitive axiom audits. Only `propext`, `Classical.choice`, and `Quot.sound` occur.
