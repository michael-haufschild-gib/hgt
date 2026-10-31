# Shifted positive splittings have an exact tame discrepancy

- **Stage:** 3-formalized
- **Parent:** [Integral loop vertices](../1-in-progress/valued-loop-iwasawa-and-integral-vertices.md).
- **Statement:** If positive matrices `p,q` satisfy `q=R_r(p)` and their common
  lower-right entry `d` has nonzero constant coefficient, the lifted diagonal
  rescaling sends `positive(p)` to `central(T(r,d)) positive(q)`.

## Proof

Rescaling preserves the diagonal entries and sends the lower-left entry
`c` to `r⁻¹c`. If `c=0`, both positive section corrections are one, while
rescaling contributes precisely `T(r,d)` by the audited triangular-chart
correction. If `c≠0`, the original and shifted positive section corrections
are respectively `T(c,d)` and `T(r⁻¹c,d)=T(r,d)⁻¹T(c,d)`.
The rescaling chart correction is one in this case. Both cases give the
claimed identity, and the matrix projections agree by construction.

For shifts by `X` or `X⁻¹`, the discrepancy depends only on the constant
coefficient of `d`. Its valuation is one whenever that residue is a
valuation unit; this is the needed central-coordinate compatibility at
adjacent integral vertices.

Rescaling fixes central elements and sends each split root to its scaled
root. The four-root factorization of coefficient-field `SL₂` therefore
identifies the shifted finite splitting with the actual affine splitting.

## Lean

`HTGeometry/LoopEisenstein/ShiftedPositiveSplitting.lean`:
`LoopSL2.diagonalRescale_positiveEmbedding`,
`LoopSL2.diagonalRescale_finiteSL2Embedding`. Direct Lean check passed; transitive axioms are exactly `propext`, `Classical.choice`, `Quot.sound`.
