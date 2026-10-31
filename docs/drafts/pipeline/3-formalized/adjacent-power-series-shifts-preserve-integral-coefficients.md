# Adjacent power-series shifts preserve integral coefficients

- **Stage:** 3-formalized
- **Parent:** [Integral loop vertices](../1-in-progress/valued-loop-iwasawa-and-integral-vertices.md).
- **Statement:** Diagonal rescaling by `X` or `X⁻¹` preserves coefficient
  integrality whenever both matrices are power-series matrices. The corresponding
  residue conditions produce actual integral shifted matrices.

## Proof

For the backward shift `q=R_(X⁻¹)(p)`, the diagonal entries agree and
`Xq₁₂=p₁₂`, `q₂₁=Xp₂₁`. Multiplication by `X` preserves coefficient
integrality in both directions, so all four integral conditions are equivalent.
Apply this equivalence to the inverse rescaling for the forward shift.

If `p₁₂(0)=0`, the audited affine-shift construction produces a positive
Iwahori matrix `q=R_(X⁻¹)(p)`; the equivalence proves its integrality.
If `p` is Iwahori, its inclusion in the adjacent lattice stabilizer produces
a positive matrix `q=R_X(p)`, and the inverse equivalence proves integrality.

## Lean

`HTGeometry/LoopEisenstein/IntegralPowerSeriesRescaling.lean`:
`integralPowerSeriesSL2_rescale_Xinv_iff`,
`exists_integralPowerSeries_affineShift`,
`exists_integralPowerSeries_forwardShift`. Direct Lean check passed; transitive axioms are exactly `propext`, `Classical.choice`, `Quot.sound`.
