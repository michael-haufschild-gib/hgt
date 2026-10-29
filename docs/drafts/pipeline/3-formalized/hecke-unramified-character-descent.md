# Unramified character descent and finite-character theta entireness

- **ID:** hecke-unramified-character-descent
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Descent and residue cancellation](hecke-unramified-character-descent-and-residue-cancellation.md)
- **Statement:** Trivial finite weight and zero real parity give an actual ordinary class character with the original Hecke character as pullback; nontrivial finite weight gives an entire actual unit-theta Mellin transform.

## Proof

Zero parity degree forces every selected real parity to vanish. The exact
parity-sign formula therefore makes the infinite character trivial.
Trivial finite weight makes its restriction to residue units trivial.
Every element in the kernel of the ray-to-ordinary class map has a proved
prime-to principal representative, whose character value is now one.
The actual surjective class map therefore admits the descended character.
Its pullback identity preserves nontriviality; ordinary finite-character
orthogonality gives a zero class sum.

For nontrivial finite weight, the finite modulus cannot be the unit ideal,
whose quotient has only one element. The classified physical and dual
theta zero modes both vanish. The actual unit-averaged pair is strong,
so its continued Mellin transform is entire.

## Lean verification

Module: `HeckeLFunctions/UnramifiedHeckeCharactersDescendToIdealClasses.lean`.

- `exists_classCharacter_of_finiteParity_trivial` supplies the actual descent.
- `sum_classCharacter_eq_zero_of_comp` proves ordinary-class orthogonality.
- `heckeUnitThetaMellinPair_isStrong_of_finiteWeight_ne_one` proves zero-mode vanishing.
- `differentiable_heckeUnitThetaMellinContinuation_of_finiteWeight_ne_one`
  proves the resulting entire transform.

Three main transitive axiom audits returned only `propext`, `Classical.choice`,
and `Quot.sound`. Final direct source audit passed without warnings:
`lake --old env lean GaloisForLFunctions/HeckeLFunctions/UnramifiedHeckeCharactersDescendToIdealClasses.lean`.
Wired into the Hecke umbrella; umbrella not compiled.

Normalization and cancellation in the global L-function remain active work.
