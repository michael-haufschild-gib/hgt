# Inversion preserves Hecke conductors and real parities

- **ID:** hecke-conductors-and-parities-are-invariant-under-inversion
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Primitive Hecke dual-character arithmetic](../1-in-progress/hecke-primitive-gauss-sums-and-arithmetic-dual-character.md)
- **Statement:** A finite-order Hecke character and its inverse have the same finite conductor, infinite sign character, real parities, Gamma factor, theta Mellin weight, and affine Mellin argument.

## Proof

Restriction to finite residues commutes with inversion of the actual ray
character. The zero extension to nonunits also commutes with inversion:
on units this is the inverse unit value; on nonunits both sides vanish.
The [finite-ring conductor theorem](finite-ring-conductors-are-invariant-under-inversion.md)
then identifies their greatest descent ideals. Pulling these back to the
ring of integers identifies the actual finite Hecke conductors.

Every real sign has order at most two. A homomorphism on the sign group
therefore equals its own inverse, so inversion does not change the
infinite sign component. The definitions then identify the real,
coordinate, and place parities, hence the Gamma product and both Mellin
normalizations.

## Lean

Module: `GaloisForLFunctions.HeckeLFunctions.HeckeConductorsAndParitiesAreInvariantUnderInversion`.
Namespace: `GaloisForLFunctions.HeckeLFunctions`.

- `finiteResidueCharacter_inv`, `finiteHeckeWeight_inv`
- `heckeFiniteConductor_inv`, `infiniteSignCharacter_inv`
- `heckeParity_inv`, `heckeCoordinateParity_inv`, `heckePlaceParity_inv`
- `heckeGammaFactor_inv`
- `heckeThetaMellinWeight_inv`, `heckeThetaMellinArgument_inv`

Both main transitive axiom audits report only `propext`,
`Classical.choice`, and `Quot.sound`. Final direct source audit passed
without warnings:

```
lake --old env lean GaloisForLFunctions/HeckeLFunctions/HeckeConductorsAndParitiesAreInvariantUnderInversion.lean
```

Wired into `HeckeLFunctions.lean`; the umbrella was not compiled.
