# Unipotent Gauss defects use only earlier free coefficients

- **Stage:** 3-formalized
- **Parent:** [Triangular arithmetic-cell unfolding](../1-in-progress/triangular-root-coefficients-unfold-arithmetic-cells.md).
- **Statement:** For a positive unipotent matrix `(a,b;c,d)` over any
  commutative power-series ring, the degree-`n` upper Gauss defect
  `[X^n](b/d-b)` depends on `a,c` through degree `n` and `b` strictly below
  `n`. The lower defect `[X^n](c/a-c)` depends on `a,c` strictly below `n`.

## Proof

All inverses are principal-unit power-series inverses. For the upper
coordinate, `b/d-b=b(d⁻¹-1)`. The second factor has zero constant
coefficient, removing `b_n`. The determinant identity
`d=a⁻¹(1+bc)` and `c₀=0` show that `d` through degree `n` needs only
`a,c` through `n` and `b` below `n`. Power-series inversion preserves
finite coefficient dependence.

For the lower coordinate, `c/a-c=c(a⁻¹-1)`. Both factors have zero
constant coefficient, so both current-degree boundary terms vanish.
Only strictly earlier `a,c` coefficients remain. In the free order
`b₀,c₁,a₁,b₁,…`, both defects therefore precede their selected coordinate.

For a product `gh`, its strict stream prefix depends only on the two strict
input prefixes, by triangular group multiplication. Apply the preceding Gauss
defect law to that product, then add its multiplication defect. Thus the
selected Gauss coefficient is the sum of the two current free coefficients
plus a function of strictly earlier input coordinates. This holds for both
upper and lower Gauss orders.

## Lean

`HTGeometry/LoopEisenstein/UnipotentGaussCoefficients.lean`:
`unipotentUpperGauss_defect_congr`, `unipotentLowerGauss_defect_congr`,
`unipotentUpperGauss_product_defect_prefix`,
`unipotentLowerGauss_product_defect_prefix`.
Direct Lean audit passed. All four transitive axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.
