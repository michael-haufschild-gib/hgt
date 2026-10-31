# Alternating completed vertex words have a nonzero boundary

- **Stage:** 3-formalized
- **Parent:** [Integral loop vertices](../1-in-progress/valued-loop-iwasawa-and-integral-vertices.md).
- **Statement:** A nonempty alternating word in the two full
  power-series vertex embeddings, with every letter outside their
  common Iwahori, is outside the matrix Iwahori.

## Proof

A standard-vertex matrix has no negative Laurent coefficients and
degree-zero coefficient equal to its determinant-one constant
reduction. Its lower-left constant coefficient detects departure
from Iwahori. An adjacent-vertex matrix is the shift
`[[a,X⁻¹b],[Xc,d]]`; its degree-minus-one coefficient is the matrix
whose only possible nonzero entry is the upper-right residue `b(0)`.
It belongs to Iwahori precisely when this residue vanishes.

Boundary matrices multiply when lower degree bounds are added. In an
affine-headed alternating word, each affine letter lowers the boundary
degree by one. Between consecutive affine letters, the finite letter's
nonzero lower-left residue multiplies the boundary. Induction therefore
gives a nonzero top-row coefficient in a negative degree.

A standard-headed word of length one is excluded by its lower-left
residue. For every longer standard-headed word, its invertible constant
reduction multiplies the nonzero negative boundary of the remaining
affine-headed word and cannot annihilate it. Every Iwahori matrix is a
power-series matrix, so every such negative boundary excludes Iwahori.

## Lean

`HTGeometry/LoopEisenstein/FullVertexMatrixWords.lean`:
`affine_vertex_head_boundary`,
`alternating_vertexMatrixWord_not_mem_iwahori`,
`alternating_full_vertex_word_not_mem_iwahori`. Direct Lean check passed;
transitive axioms: `propext`, `Classical.choice`, `Quot.sound`.

The coefficient-integral central vertex intersections remain necessary
to apply this matrix obstruction to Iwasawa character independence.
