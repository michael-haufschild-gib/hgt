# Artin virtual-character restriction foundation

- **ID:** `artin-virtual-character-restriction-foundation`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Status:** `[LEAN-PROVED] [BRIDGE]`

## Exact claim

For a group `G`, let `CharFD(G)` be the set of character functions of all finite-dimensional
complex representations of `G`. Define

```text
GenuineChar(G) = additive-monoid closure of CharFD(G) in (G -> C),
VirtualChar(G) = additive-group closure of CharFD(G) in (G -> C).
```

Then:

1. `GenuineChar(G)` embeds canonically into `VirtualChar(G)`.
2. Every homomorphism `phi : H -> G` induces restriction maps on both closures by precomposition;
   these maps are obtained from the actual restricted representations.
3. Every virtual character is conjugacy invariant.
4. A genuine character takes a non-negative integer value at `1`; a virtual character takes an
   integer value at `1`.
5. Every finite-dimensional complex representation on a carrier in any universe has a canonical
   coordinate model on `Fin(dim) -> C`; this small model has the same character and therefore its
   character belongs to `CharFD(G)`.

These are concrete closure constructions. No proposition asserting that an arbitrary function is a
character is introduced, and no Artin-holomorphy premise occurs.

## Paper proof

Every finite-dimensional character is a virtual-character generator, so induction over additive
monoid closure gives the canonical inclusion.

Given `phi : H -> G` and a representation `rho` of `G`, `rho o phi` is a finite-dimensional
representation of `H`, and its character is `chi_rho o phi`. Precomposition is additive and
commutes with negation. Induction over the respective closures therefore proves that it maps
genuine characters to genuine characters and virtual characters to virtual characters.

Each generator is conjugacy invariant because trace is cyclic:

```text
tr(rho(hgh^-1)) = tr(rho(h)rho(g)rho(h)^-1) = tr(rho(g)).
```

The property is closed under zero, addition, and negation, hence holds on the virtual-character
group closure.

At the identity, a representation character equals its complex dimension, hence a natural number.
Finite sums remain natural-number-valued. Allowing additive inverses gives an integer value for a
virtual character. Closure induction proves both statements.

For an arbitrary finite-dimensional carrier `V`, choose the canonical finite basis indexed by
`Fin(dim_C V)`. Its coordinate equivalence conjugates the action to an action on
`Fin(dim_C V) -> C`, which lives in the scalar universe and hence bundles as an `FDRep`. Trace is
invariant under this representation equivalence, so the small-model character equals the original
character. This is the universe-safe bridge needed by subgroup induction.

## Significance boundary

This is required representation-theoretic infrastructure, not new scientific knowledge. It does
not yet formalize induction, monomial characters, irreducible decomposition, Heilbronn positivity,
or any Artin L-function.

## Lean target

Formalize exact constructions and all four conclusions from mathlib `FDRep` characters and actual
representation restriction. No `sorry`, `admit`, new axiom, `opaque`, `unsafe`, or target-equivalent
proposition interface.

## Lean certificate

- Module: `formal/GaloisForLFunctions/RHTower/Artin/ArtinVirtualCharacter.lean`
- Concrete carriers: `genuineCharacterMonoid`, `virtualCharacterGroup`.
- Actual representation restriction: `restrictFDRep`.
- Universe-safe carrier reduction: `smallModelRepresentation`, `smallModelEquiv`,
  `smallModelFDRep`, and `representation_character_mem_fdCharacterSet`.
- Closure-preserving maps: `GenuineCharacter.restrict`, `VirtualCharacter.restrict`.
- Structural theorems: `genuineCharacterMonoid_le_virtualCharacterGroup`,
  `VirtualCharacter.conj_invariant`, `GenuineCharacter.one_eq_natCast`, and
  `VirtualCharacter.one_eq_intCast`.
- Source check: `lake env lean GaloisForLFunctions/RHTower/Artin/ArtinVirtualCharacter.lean`.
- Targeted olean audit:
  `lake build GaloisForLFunctions.RHTower.Artin.ArtinVirtualCharacter`.
- `#print axioms` audit of all exported theorems reports only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Wired into `GaloisForLFunctions/RHTower.lean`; umbrella deliberately not built.
