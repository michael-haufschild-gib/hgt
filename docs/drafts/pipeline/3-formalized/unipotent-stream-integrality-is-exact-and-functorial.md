# Unipotent stream integrality is exact and functorial

- **Stage:** 3-formalized
- **Parent:** [Elliptic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** A completed unipotent matrix over a commutative ring has
  all coefficients in a subring exactly when its free stream does.
  Every triangular correction commutes with ring maps and preserves subrings.

## Proof

If a stream takes values in a subring, decode that stream over the subring
and map its matrix into the ambient ring. Naturality of the stream
equivalence identifies this matrix with the original one, proving
integrality of every entry, including the determinant-determined fourth
entry. The converse reads the three entries defining the stream.

Zero extension commutes with a ring map. Hence the decoded finite-prefix
matrices commute with the map. Their product and its coefficient defect
also commute with the map, proving naturality of every triangular
correction. Apply this to the subring inclusion to obtain subring closure.

## Lean

`HTGeometry/LoopEisenstein/UnipotentCoefficientSubring.lean`:
`unipotentStream_mem_subring_iff`, `unipotentTriangularCorrection_map`,
`unipotentTriangularCorrection_mem_subring`. Direct `lake --old env lean` check passed. All three transitive axiom audits
contain only `propext`, `Classical.choice`, and `Quot.sound`.
