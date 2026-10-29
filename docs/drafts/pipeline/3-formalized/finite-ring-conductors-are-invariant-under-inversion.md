# Inversion preserves finite-ring conductors

- **ID:** finite-ring-conductors-are-invariant-under-inversion
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Primitive Hecke dual-character arithmetic](hecke-primitive-gauss-sums-and-arithmetic-dual-character.md)
- **Statement:** A multiplicative character of a finite commutative ring, valued in a field, and its inverse have exactly the same descent ideals and conductor ideal.

## Proof

The proved descent criterion says that a character descends through an
ideal `J` exactly when it is one on every unit congruent to one modulo
`J`. Since `z⁻¹=1` exactly when `z=1`, inversion preserves this criterion
for each `J`. The conductor is the greatest descent ideal, so the two
conductors contain each other and are equal.

## Lean

Module: `GaloisForLFunctions.HTGeometry.FiniteRingConductorsAreInvariantUnderInversion`.
Namespace: `GaloisForLFunctions.FiniteRing`.

- `factorsThrough_inv_iff`
- `conductorIdeal_inv`

The transitive axiom audit reports only `propext`, `Classical.choice`,
and `Quot.sound`. Final direct source audit passed without warnings:

```
lake --old env lean GaloisForLFunctions/HTGeometry/FiniteRingConductorsAreInvariantUnderInversion.lean
```

Wired into `HTGeometry.lean`; the umbrella was not compiled.
