# Degree rotation preserves positive loop spectral coordinates

- **Stage:** 2-fully-proven
- **Parent:** [Elliptic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** Degree rotation commutes with the canonical positive
  central lift, preserves the actual positive Borel, and fixes both
  intrinsic Borel torus coordinates.

## Proof

On a power series, rotation multiplies coefficient `n` by `qⁿ`. Its Laurent
inclusion therefore agrees coefficientwise with actual Laurent rotation;
negative coefficients vanish on both sides. Entrywise power-series rescaling
commutes with upper and lower root matrices. The proved four-root generation
of the full positive matrix group extends compatibility from root matrices
to the canonical positive central lift.

Rescaling fixes constant coefficients, hence preserves the Iwahori and
its finite torus coordinate. Rotation fixes the central embedding. Apply
uniqueness of central–Iwahori factors to conclude that the two Borel torus
coordinates are unchanged. This statement concerns the positive Borel;
preservation of the full integral loop subgroup is a separate step.

## Lean

`HTGeometry/LoopEisenstein/PositiveLoopRotation.lean`:
`rotation_positiveEmbedding`, `rotation_mem_positiveBorel`,
`borelTorusHom_rotation`. Direct check pending.
