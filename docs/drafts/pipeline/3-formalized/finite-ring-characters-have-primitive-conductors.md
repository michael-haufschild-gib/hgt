# Finite-ring characters have unique primitive conductors

- **ID:** finite-ring-characters-have-primitive-conductors
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Primitive Hecke Gauss sums](../1-in-progress/hecke-primitive-gauss-sums-and-arithmetic-dual-character.md)
- **Statement:** Every multiplicative character of a finite commutative ring has a unique greatest quotient-descent ideal, and its unique inducing character on that quotient is primitive.

## Proof

Suppose a unit `u` satisfies `u-1∈I+J`. Write `u-1=x+y` with
`x∈I`, `y∈J`. The image of `1+y` in `R/I × R/J` is `(u,1)`, a
unit. The unit-lifting theorem supplies a unit `w` of `R` with this
same image, even though the ring map need not be surjective. Thus
`w≡1 (mod J)` and `uw⁻¹≡1 (mod I)`. This splits every congruence
unit for `I+J` into a product of congruence units for the two ideals.

By the congruence-kernel descent criterion, if a character descends
through both `I` and `J`, it descends through `I+J`. It also descends
through zero and every smaller ideal than a descent ideal. Since the
ring has finitely many ideals, the sum `C` of all descent ideals is
itself a descent ideal. Consequently descent through `I` is equivalent
to `I≤C`; this proves uniqueness of the greatest descent ideal.

Surjectivity on units gives a unique character on `R/C` inducing the
original character. If this new character descended through an ideal
`J` of `R/C`, its pullback ideal would be a descent ideal of `R` and
hence contained in `C`. Every element of `J` has a lift in that
pullback, whose image is therefore zero. Thus `J=0`, proving primitivity.

The same argument works for any surjective ring map `f:R→S`:
the original character descends to `S` exactly when `ker(f)≤C`, and
the descended character is primitive when `ker(f)=C`. This avoids
dependence on a particular representation of the conductor quotient.

## Lean

Module: `GaloisForLFunctions.HTGeometry.FiniteRingCharactersHavePrimitiveConductors`.
Namespace: `GaloisForLFunctions.FiniteRing`.

- `exists_unit_congruence_decomposition`
- `FactorsThrough.bot`, `FactorsThrough.of_le`, `FactorsThrough.sup`, `FactorsThrough.finset_sup`
- `conductorIdeal`, `factorsThrough_conductorIdeal`
- `factorsThrough_iff_le_conductorIdeal`
- `isPrimitive_iff_conductorIdeal_eq_bot`
- `exists_inflateChar_eq_iff_ker_le_conductorIdeal`
- `isPrimitive_of_ker_eq_conductorIdeal`
- `conductorCharacter`, `inflate_conductorCharacter`, `conductorCharacter_unique`
- `conductorCharacter_isPrimitive`

The congruence decomposition, conductor criterion, primitivity for any
conductor-kernel quotient, and canonical primitive-character theorem
were checked transitively with `#print axioms`: only `propext`,
`Classical.choice`, and `Quot.sound`. Final source audit passed without warnings:

```
lake --old env lean GaloisForLFunctions/HTGeometry/FiniteRingCharactersHavePrimitiveConductors.lean
```

Wired into `HTGeometry.lean`; the umbrella was not compiled. This is a
finite-ring conductor theorem. Application to the actual integral
Hecke conductor and the arithmetic trace pairing is separate work.
