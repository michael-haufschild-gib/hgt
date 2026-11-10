# Landing calibration with the Riemann Gamma factor

- **ID:** landing-calibration-with-the-riemann-gamma-factor
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-1011/obstacles-summary.md`, A68.
- **Statement:** Construct a real, FE-symmetric meromorphic completion with the Riemann Gamma factor, Riemann–von Mangoldt zero counting, and infinitely many off-line zeros approaching the critical line.

## Construction under examination

Project every multiplicity copy of a Riemann Xi zero onto the critical line,
preserving its ordinate. The indexed genus-one product has exactly the
projected divisor. Add quartets at geometrically separated heights with
positive depths tending to zero. These contribute only `O(log T)` zeros,
which preserves the Riemann–von Mangoldt remainder scale. Divide the
resulting symmetric entire function by `s(s−1)Γℝ(s)` to obtain the
uncompleted function.

The corpus proves indexed-product convergence and exact fiber multiplicities
in `HTGeometry/CanonicalProductE1Divisor.lean`, and inverse-square summability
of Xi ordinates in `RHTower/Sieve/InghamUniformDetectorMellinBufferedTail.lean`.
`XiOrderedZeroCopyEnumeration.lean` identifies the positive-copy count with
the actual Xi zero count. Existing approaching models use quadratic heights
and a cosh base; their linear-density count does not settle this target.

## Remaining proof obligations

Projected-product symmetry, exact multiplicity-count transport, sparse-quartet
counting, finite-order growth, Gamma normalization, and the complete landing
counterexample require Lean proofs. No Euler product or Dirichlet-series
representation is claimed for this calibration.
