# Diagonal rescaling lifts to the symbol extension

- **Stage:** 3-formalized
- **Parent:** [Integral loop vertices](../1-in-progress/valued-loop-iwasawa-and-integral-vertices.md).
- **Statement:** For every field unit `r`, diagonal rescaling
  `R_r(g)=diag(r,1)g diag(r,1)⁻¹` lifts to an automorphism of the
  actual Kubota extension by any image of the degree-two Milnor symbol.

## Proof

Let `x(g)=g₂₁` when nonzero and `x(g)=g₂₂` otherwise. Put
`D_r(g)={r,x(g)}` on the upper-triangular chart and zero elsewhere.
The Kubota cocycle is `σ(g,h)={x(gh)/x(g),x(gh)/x(h)}`.
Its rescaling defect is
`σ(R_rg,R_rh)−σ(g,h)=D_r(gh)−D_r(g)−D_r(h)`.

There are five possible triangular-chart patterns. If both factors are
triangular, `x(gh)=x(g)x(h)` and the defect vanishes. If only the left
factor is triangular, the same multiplicative identity gives defect
`−{r,x(g)}`. If only the right factor is triangular,
`x(gh)=x(g)/x(h)` gives defect `−{r,x(h)}`. If neither factor nor their
product is triangular, both ratios in the cocycle are unchanged. In the
remaining case, `x(gh)=−x(g)/x(h)`; bilinearity and
`{r,r}={r,−1}` give defect `{r,x(gh)}`. These identities follow from
the determinant-one relation and the audited symbol laws.

For a symbol homomorphism `τ`, the required lift is
`(g,z)↦(R_rg,z+τ(D_r(g)))`. The defect identity proves multiplicativity.
Rescaling by `r⁻¹` is its inverse, since
`D_{r⁻¹}(R_rg)=−D_r(g)`.

## Lean

`HTGeometry/LoopEisenstein/SymbolDiagonalRescaling.lean`:
`kubotaCocycle_rescale`, `SL2SymbolExtension.diagonalRescale`.
Direct Lean check passed; transitive axioms: `propext`, `Classical.choice`,
`Quot.sound`.
