# Columnar absolute-product zero-line/lattice universality law

- **ID:** columnar-absolute-product-zero-line-lattice-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-first closure of absolute-product zero classification and single-column
  zero-line rigidity
- **Statement:** In every vertically invariant region where a carrier is one nonzero-amplitude
  exponential column times a locally nonvanishing absolute product, a carrier zero is equivalent
  to the simultaneous column equation, the exact logarithmic vertical-line coordinate, and the
  full carrier zero lattice.

## Gates

- [x] 0 → 1 in-progress: generated from verified Lean endpoints
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [x] 3 → 4 publication-ready: post-proof literature audit found no exact statement

## Corpus inputs

- `columnarAbsoluteProduct_zero_iff_columnar_and_verticalLattice`
- `singleColumn_zeroLine_and_verticalLattice`

## Proof

`[PROVED HERE]` Specialize the absolute-product classification to the column factor
`q ↦ 1 - A q`.  A carrier zero is then equivalent to the column equation at the base point plus
the full vertical carrier-zero lattice.  Since `A ≠ 0`, single-column rigidity sends the column
equation to the exact line

`Re s = log ‖A‖ / log b`.

This proves all three conclusions.  Conversely, the column equation and carrier lattice are
exactly the two clauses required by the absolute-product classification; the line clause is
compatible extra information.  No computation is used.

## Strict gain over corpus endpoints

The absolute-product theorem leaves the column factor abstract and therefore cannot locate its
zeros horizontally.  The single-column theorem locates and propagates zeros of the isolated
factor but says nothing about a residual product or zeros of the full carrier.  Their closure gives
an exact zero classification for the full carrier, including both geometry and divisor lattice.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.ColumnarAbsoluteProductZeroLineLatticeUniversalityLaw`
- Main theorem:
  `columnarAbsoluteProduct_zero_iff_columnEquation_zeroLine_and_carrierLattice`
- Source:
  `formal/GaloisForLFunctions/RHTower/ColumnarAbsoluteProductZeroLineLatticeUniversalityLaw.lean`
- Exact-file check:
  `lake env lean GaloisForLFunctions/RHTower/ColumnarAbsoluteProductZeroLineLatticeUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty protocol

No literature search occurred before the paper proof or Lean formalization.  Post-proof searches
covered zero sets of combinations of Euler products, vertical arithmetic progressions for
Dirichlet-series values, exponential-polynomial zero lattices, and nonvanishing of absolutely
convergent products.  Righetti studies infinitely many zeros of polynomial combinations of Euler
products ([2014](https://arxiv.org/abs/1412.6331)); Martin--Ng prove that most points in a
vertical arithmetic progression are nonzeros of a Dirichlet L-function
([2011](https://arxiv.org/abs/1109.1788)); Chatterjee--Murty study nonvanishing of Dirichlet
series with periodic coefficients ([2014](https://arxiv.org/abs/1405.6982)).  No source found the
exact local factorization theorem classifying a full carrier zero simultaneously by its explicit
column equation, forced logarithmic line, and complete vertical carrier-zero lattice.

## Log

- 2026-07-23 — Fresh whole-corpus terminal-pair scan exposed the unconsumed abstract-column versus
  explicit-column seam.
- 2026-07-23 — Dependency-closed proof completed from two existing Lean endpoints.
- 2026-07-23 — Exact theorem formalized, checked warning-free, and wired into the RHTower umbrella.
- 2026-07-23 — Post-proof collision audit found adjacent Euler-product and vertical-progression
  work but no exact carrier classification.
