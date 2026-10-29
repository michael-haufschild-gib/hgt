# Finite Hecke characters have primitive conductors

- **ID:** hecke-finite-characters-have-primitive-conductors
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Primitive Hecke Gauss sums](../1-in-progress/hecke-primitive-gauss-sums-and-arithmetic-dual-character.md)
- **Statement:** The actual finite residue character of every Hecke character has a canonical nonzero integral conductor dividing its modulus, and a unique primitive character on the conductor quotient inducing it.

## Proof

Let `χ` be the already constructed finite residue character on
`R=𝓞 K/𝔪₀`. By the [finite-ring conductor theorem](finite-ring-characters-have-primitive-conductors.md),
its quotient-descent ideals have a unique greatest member `C`.
Define `𝔣` to be the inverse image of `C` under `𝓞 K→R`.
Then `𝔪₀⊆𝔣`, so `𝔣` divides `𝔪₀` and is nonzero.

The natural surjection `R→𝓞 K/𝔣` has kernel exactly `C`.
The finite-ring descent and primitivity theorems therefore give a
unique primitive character on `𝓞 K/𝔣` inducing `χ` on units, with
extension by zero at the original level. The equality on units is
proved explicitly. No finite character or conductor is postulated.

The original residue character is primitive exactly when `C=0`,
equivalently `𝔣=𝔪₀`. More generally, for `𝔪₀⊆J`, descent to
`𝓞 K/J` is equivalent to containment of the reduction map's kernel
in `C`, hence to `J⊆𝔣`, or ideal divisibility `𝔣∣J`.

## Lean

Module: `GaloisForLFunctions.HeckeLFunctions.HeckeFiniteCharactersHavePrimitiveConductors`.
Namespace: `GaloisForLFunctions.HeckeLFunctions`.

- `heckeFiniteConductor`
- `modulus_le_heckeFiniteConductor`, `heckeFiniteConductor_dvd_modulus`, `heckeFiniteConductor_ne_bot`
- `heckeConductorReduction`, `heckeConductorReduction_surjective`, `ker_heckeConductorReduction`
- `heckePrimitiveFiniteCharacter`, `inflate_heckePrimitiveFiniteCharacter`
- `heckePrimitiveFiniteCharacter_isPrimitive`, `heckePrimitiveFiniteCharacter_unique`
- `heckePrimitiveFiniteCharacter_unit`
- `finiteHeckeWeight_isPrimitive_iff`, `finiteHeckeWeight_descends_iff`

Conductor divisibility, primitivity of the constructed character,
the original-level primitive criterion, and the exact descent criterion
were checked transitively with `#print axioms`: only `propext`,
`Classical.choice`, and `Quot.sound`. Final direct source audit passed
without warnings:

```
lake --old env lean GaloisForLFunctions/HeckeLFunctions/HeckeFiniteCharactersHavePrimitiveConductors.lean
```

Wired into `HeckeLFunctions.lean`; the umbrella was not compiled.
The actual additive trace character, dual-series arithmetic
identification, and completed functional equation remain separate obligations.
