# Ring diagonal rescaling preserves determinant one

- **Stage:** 3-formalized
- **Parent:** [Elliptic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** Over every commutative ring, a unit acts on `SL₂` by
  multiplying the upper-right entry by that unit and the lower-left entry
  by its inverse. This action commutes with ring maps and rescales the two
  elementary root subgroups accordingly.

## Proof

The diagonal entries remain fixed and the product of off-diagonal entries
is unchanged, so the determinant remains one. In matrix multiplication,
the two diagonal cross terms gain the factor `uu⁻¹=1`; each off-diagonal
entry gains its prescribed scalar. This proves multiplicativity.
Replacing the unit by its inverse gives the inverse map. Ring-map
compatibility follows entrywise from preservation of multiplication and
units. Substitution of the two elementary matrices gives the root formulas.

## Lean

`HTGeometry/LoopEisenstein/RingSL2DiagonalRescaling.lean`. `ringSL2Rescale`, `ringSL2Rescale_inverse`, `ringSL2Rescale_map`,
and both root formulas passed direct Lean checking. The homomorphism and
map-compatibility axiom audits contain only `propext`, `Classical.choice`,
and `Quot.sound`.
