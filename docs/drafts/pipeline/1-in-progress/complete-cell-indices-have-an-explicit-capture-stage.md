# Complete-cell indices have an explicit capture stage

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** Original obstacle A4: an explicit stage, in source bounds and a
  finite negative spectral margin, after which the literal complete-cell Gram
  matrix carries every negative direction of the source family.

## Route

`CompleteCellLevyTransfer` bounds the jump energy of the cell error by `D/N`.
The difference of the two jump energies is therefore `O(N^(-1/2))` by the
norm-square identity. Mass, both pole moments, and the complete prime term
have `O(1/N)` errors on the same fixed support window.

Polarization gives a finite matrix bound `C/sqrt(N)`. For a negative
compression with margin `δ`, its entrywise coefficient sums turn this into
an explicit quadratic stage in `C/δ`. All source constants and the negative
compression must be supplied by the given compact `C²` family; no convergence
modulus or missing analytic estimate may be assumed.

## Lean status

No new theorem claimed.
