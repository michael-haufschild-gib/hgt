# Hecke characters split into finite characters and real parities

- **ID:** hecke-character-components
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Hecke L-functions and class field theory](../1-in-progress/hecke-l-functions-and-class-field-theory-2026-10-28.md), HL7
- **Statement:** Every ray class character has a finite residue character and independent real-place parities. Their product evaluates the character on principal ideals and equals one on global units.

## Paper proof

Surjectivity of `rayHom` identifies its range with the full product of invertible finite
residues and real signs. The existing principal ray-class map on that range therefore
defines `fullRayResidueClass` on the full product. Compose it with the given character `ψ`.

Restrict this composite to `(ρ,1)` and `(1,σ)`. Since `(ρ,σ) = (ρ,1)(1,σ)`, the composite
is the product of these two characters. Its defining principal-ideal identity gives
`ψ((α)) = χ_fin(reduce α) χ_inf(sign α)` for every element prime to the modulus.

For a real place `w`, the coordinate sign supported at `w` has order dividing two. Its
complex character value therefore has square one, hence is `1` or `−1`. Set `ε_w = 0`
in the first case and `ε_w = 1` in the second. Every sign vector is the finite product
of its coordinate signs, so `χ_inf(σ) = ∏_w σ_w^ε_w`.

A global unit generates the unit fractional ideal. It is therefore prime to every
finite modulus and has trivial principal ray class. Substituting it into the preceding
identity proves `χ_fin(u) ∏_w sign(w(u))^ε_w = 1`.

All ingredients are proved for the actual ray-class characters; no compatibility condition
or character decomposition is assumed.

## Lean declarations

In [HeckeCharactersSplitIntoFiniteCharactersAndRealParities.lean](../../../../formal/GaloisForLFunctions/HeckeLFunctions/HeckeCharactersSplitIntoFiniteCharactersAndRealParities.lean):

- `fullRayResidueClass`, `fullRayResidueClass_rayHom`
- `rayResidueCharacter`, `finiteResidueCharacter`, `infiniteSignCharacter`
- `rayResidueCharacter_eq_mul`, `character_rayClassOfElt_eq`
- `toPrincipalIdeal_globalUnit`, `globalUnitPrimeTo`, `rayClassOfElt_globalUnit`
- `finite_mul_infinite_globalUnit`
- `heckeParity`, `heckeParity_le_one`, `infiniteSignCharacter_eq_prod`
- `finite_character_mul_parities_globalUnit`

## Validation

The principal-ideal identity, parity-product formula, and global-unit parity relation
pass transitive axiom audits using only `propext`, `Classical.choice`, and `Quot.sound`.
The final direct source audit with `lake --old env lean` passes without warnings.
The module is imported by `HeckeLFunctions.lean`; no umbrella is compiled.
No olean is built because no written leaf module yet imports it.

## Remaining use

These are the actual finite coefficients and archimedean parities needed in the Hecke theta
series. Theta inversion, unit-domain integration, full continuation, and the primitive
functional equation remain open.
