# Canonical multiplicities for Artin virtual characters

- **ID:** `artin-character-multiplicity-extraction`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Status:** `[LEAN-PROVED] [BRIDGE]`

## Exact claim

For a finite group `G`, the normalized pairing of two concrete genuine characters has a unique
natural-number value, and the normalized pairing of two concrete virtual characters has a unique
integer value. Define these values as

```text
genuineMultiplicity_G(chi,psi) : N,
virtualMultiplicity_G(theta,eta) : Z.
```

Then:

1. Their complex casts equal the normalized pairings.
2. `virtualMultiplicity` is additive and negation-compatible in both arguments.
3. For genuine characters viewed virtually, `virtualMultiplicity` is the integer cast of
   `genuineMultiplicity`, hence is nonnegative.
4. Multiplicity against a concrete monomial character is additive in the tested virtual character
   and nonnegative for every genuine character.

## Paper proof

Existence is the previously proved natural/integer pairing theorem. Uniqueness follows because the
embeddings `N -> C` and `Z -> C` are injective. Choose the unique values as the definitions.

Additivity and negation follow by casting to `C`, replacing each cast by its pairing, using
biadditivity of the normalized pairing, and applying injectivity of `Z -> C`.

For genuine characters, both extracted values cast to the same complex pairing. Injectivity shows
that the virtual integer value equals the integer cast of the genuine natural value. Its
nonnegativity is immediate.

## Significance boundary

This supplies canonical integer multiplicities needed to state Heilbronn effectivity. It does not
yet construct a complete irreducible-character family, define analytic orders of Artin
L-functions, or prove Heilbronn positivity.

## Lean target

Extract values from the certified pairing-integrality theorems, prove exact cast identities,
biadditivity, and genuine nonnegativity. No `sorry`, `admit`, new axiom, `opaque`, `unsafe`, or
target-equivalent proposition interface.

## Lean certificate

- Module: `formal/GaloisForLFunctions/RHTower/ArtinCharacterMultiplicity.lean`.
- Extractors: `genuineMultiplicity`, `virtualMultiplicity`.
- Exact cast theorems: `genuineMultiplicity_cast`, `virtualMultiplicity_cast`.
- Biadditivity and negation: `virtualMultiplicity_add_left`,
  `virtualMultiplicity_add_right`, `virtualMultiplicity_neg_left`,
  `virtualMultiplicity_neg_right`.
- Genuine compatibility/nonnegativity: `virtualMultiplicity_toVirtual`,
  `virtualMultiplicity_toVirtual_nonneg`.
- Monomial specialization: `monomialMultiplicity`, `monomialMultiplicity_add`,
  `monomialMultiplicity_genuine_nonneg`.
- Source check: `lake env lean GaloisForLFunctions/RHTower/ArtinCharacterMultiplicity.lean`.
- Targeted olean audit: `lake build GaloisForLFunctions.RHTower.ArtinCharacterMultiplicity`.
- `#print axioms` audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Wired into `GaloisForLFunctions/RHTower.lean`; umbrella deliberately not built.
