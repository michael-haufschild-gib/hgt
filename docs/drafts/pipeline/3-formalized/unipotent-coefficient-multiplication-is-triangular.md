# Unipotent coefficient multiplication is triangular

- **Stage:** 3-formalized
- **Parent:** [Elliptic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** Over every commutative ring, the actual unipotent coefficient
  stream satisfies `(xy)ₙ=xₙ+yₙ+Pₙ(x_{<n},y_{<n})`, where `Pₙ` depends only on
  the two strictly earlier prefixes.

## Proof

Agreement below stream index `N` determines `aₘ` when `3m≤N`, `bₘ` when
`3m<N`, and `cₘ` when `3m≤N+1`. The determinant inverse recursion then
determines `dₘ` when `3m≤N`.

At index `3n`, the upper-right defect is the degree-`n` coefficient of
`(a−1)B+b(D−1)`. Each zero constant removes the only undetermined boundary
coefficient. At index `3n+1`, both factors in each term of
`c(A−1)+(d−1)C` have zero constant, so degree `n+1` uses only degrees at
most `n`. At index `3n+2`, the same reasoning applies to
`(a−1)(A−1)+bC`; the last term needs `cₙ₊₁`, which already precedes `aₙ₊₁`.
The extra constant in the upper-left defect has zero coefficient in degree
`n+1`.

Thus every defect is unchanged when either input is replaced by the matrix
whose stream agrees below the current index and is zero afterwards.
Reading this zero-extended product defines `Pₙ` and proves the identity.

## Lean

`HTGeometry/LoopEisenstein/UnipotentTriangularMultiplication.lean`:
`unipotentStreamDefect_prefix_congr`, `unipotentStream_mul`.
Direct `lake --old env lean` check passed. Both transitive axiom audits
contain only `propext`, `Classical.choice`, and `Quot.sound`.
