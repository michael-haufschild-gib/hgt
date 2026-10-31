# Elliptic unipotent arithmetic intersection is exact

- **Stage:** 3-formalized
- **Parent:** [Elliptic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** Under the actual adelic unipotent embedding, the
  arithmetic intersection is exactly the image of uniformly integral
  completed rational unipotent matrices.

## Proof

Coefficient evaluation commutes with the diagonal field embedding and the
canonical positive central lift. Suppose an actual adelic unipotent equals
the diagonal image of a restricted rational loop. Its infinity component
is positive unipotent. Faithful coefficient-field descent therefore makes
the rational loop itself positive unipotent, with a unique rational
power-series matrix lift. At every finite place and at infinity, its
diagonal matrix has the same local central lift as the original adele
matrix. Joint injectivity of these local lifts proves equality of the
matrices. Uniform integrality then follows from the original matrix.

Conversely, a uniformly integral diagonal rational matrix has local loops
in the full integral subgroup outside one finite set. Its positive central
lift is therefore a restricted rational loop, and local naturality identifies
its actual arithmetic image with the unipotent adelic embedding.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticUnipotentArithmetic.lean`:
`adelicUnipotentEmbedding_mem_arithmetic_iff`. Direct Lean check passed; the axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`.
