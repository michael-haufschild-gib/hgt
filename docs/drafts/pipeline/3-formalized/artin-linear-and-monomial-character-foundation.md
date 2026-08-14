# Artin linear and monomial character foundation

- **ID:** `artin-linear-and-monomial-character-foundation`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Status:** `[LEAN-PROVED] [BRIDGE]`

## Exact claim

For a group `H`, define a concrete complex linear character to be a homomorphism
`lambda : H -> C^x`. It acts on the one-dimensional complex vector space `C` by

```text
rho_lambda(h)(z) = lambda(h) z.
```

Then `rho_lambda` is an actual finite-dimensional representation, its character is exactly the
complex value of `lambda`, and its character at the identity is `1`.

For a subgroup `H <= G` of a finite group, define the monomial genuine and virtual characters
attached to `lambda` as the characters of the actual induced representation
`Ind_H^G(rho_lambda)`. They are concrete elements of the previously formalized genuine- and
virtual-character closures.

Their normalized pairing with any actual `G`-representation character equals the pairing of the
linear character with the restricted representation character on `H`.

## Paper proof

Multiplication by a nonzero complex scalar is complex-linear. The homomorphism laws for `lambda`
give the identity and composition laws for `rho_lambda`, hence an actual representation. On the
one-dimensional space `C`, multiplication by `a` has trace `a`; therefore the representation
character equals `lambda` pointwise and has value `1` at the identity.

The induced representation is actual and finite-dimensional by the induced-representation
foundation. Its character therefore belongs to the `FDRep` generator set, hence defines genuine
and virtual characters.

## Significance boundary

This constructs the exact monomial generators occurring in Brauer induction. It does not yet
prove the degree/index formula, the induced-character coset formula, Brauer decomposition, or
analytic monomial Artin holomorphy.

## Lean target

Build the scalar-multiplication representation from `H ->* C^x`, prove its exact character, and
feed it to `inducedGenuineCharacter` and `inducedVirtualCharacter`. No `sorry`, `admit`, new axiom,
`opaque`, `unsafe`, or target-equivalent proposition interface.

## Lean certificate

- Module: `formal/GaloisForLFunctions/RHTower/ArtinMonomialCharacter.lean`.
- One-dimensional action: `linearCharacterRepresentation`.
- Exact trace theorem: `linearCharacterRepresentation_character`.
- Monomial closures: `monomialGenuineCharacter`, `monomialVirtualCharacter`.
- Multiplicity transport: `monomialCharacter_pairing_eq_restricted`.
- Source check: `lake env lean GaloisForLFunctions/RHTower/ArtinMonomialCharacter.lean`.
- Targeted olean audit: `lake build GaloisForLFunctions.RHTower.ArtinMonomialCharacter`.
- `#print axioms` audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Wired into `GaloisForLFunctions/RHTower.lean`; umbrella deliberately not built.
