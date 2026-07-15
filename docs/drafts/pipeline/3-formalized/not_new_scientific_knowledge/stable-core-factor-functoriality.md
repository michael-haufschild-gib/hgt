# Stable cores are functorial under dynamical factor maps

- **ID:** stable-core-factor-functoriality
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), BRIDGE
- **Source:** higher-dimensional HT tail converse program
- **Statement:** If a field embedding intertwines two endomorphisms, the stable core of the
  factor endomorphism maps into the stable core of the ambient endomorphism.

## Goal

Formalize the exact mechanism by which an Albanese, semiabelian, orbifold, or other equivariant
factor contributes persistent observables to a higher-dimensional system.

## Gates

- [x] 0 -> 1 in-progress: commuting-square statement isolated
- [x] 1 -> 2 fully-proven: iterate and preimage proof complete
- [x] 2 -> 3 formalized: targeted build and axiom audit pass
- [ ] 3 -> 4 publication-ready: supporting lemma for converse theory

## Lean certificate

File: `formal/GaloisForLFunctions/HTGeometry/StableCoreFunctoriality.lean`

Declarations:

- `algHom_pow_intertwine`
- `map_stableRangeCore_le_of_intertwine`

Targeted verification:

`lake build GaloisForLFunctions.HTGeometry.StableCoreFunctoriality`

The iterate lemma uses only `propext` and `Quot.sound`; the stable-core theorem additionally uses
`Classical.choice`.

## Mathematical use

If `pi:X->A` is an equivariant factor of an algebraic self-map and `A` is an abelian
multiplication/isogeny factor, the pullback of the Manin horizon of `A` lies in the tail of `X`.
This proves the easy direction of the proposed higher-dimensional converse.  It does not prove
that every tail observable arises from such a factor.

## Log

- 2026-07-15 -- factor functoriality formalized and targeted-build verified.
