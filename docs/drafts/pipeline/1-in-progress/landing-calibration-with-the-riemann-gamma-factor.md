# Landing calibration with the Riemann Gamma factor

- **ID:** landing-calibration-with-the-riemann-gamma-factor
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-1011/obstacles-summary.md`, A68.
- **Statement:** Construct a real, FE-symmetric meromorphic completion with the Riemann Gamma factor, Riemann–von Mangoldt zero counting, and infinitely many off-line zeros approaching the critical line.

## Construction under examination

Let `γ₀≤γ₁≤…` be the positive Xi ordinates, with multiplicity. Replace
each adjacent pair by the quartet `1/2±δₙ±iγ₂ₙ₊₁`, where
`δₙ=1/(4(n+1))`. Distinct depths make every new zero simple, even when
the original ordinates repeat. The proposed positive-height count is
exactly `2⌊Nζ(T)/2⌋`: its difference from the actual Xi count is at most
one. Every new zero is off the line, but the depths tend to zero.

Use the indexed genus-one product of these quartets. Divide the resulting
symmetric entire function by `s(s−1)Γℝ(s)` to obtain the uncompleted
function. This pairing construction would give a stronger calibration
than projecting onto the line and adding sparse quartets.

The corpus proves indexed-product convergence and exact fiber multiplicities
in `HTGeometry/CanonicalProductE1Divisor.lean`, and inverse-square summability
of Xi ordinates in `RHTower/Sieve/InghamUniformDetectorMellinBufferedTail.lean`.
`XiOrderedZeroCopyEnumeration.lean` identifies the positive-copy count with
the actual Xi zero count. Existing approaching models use quadratic heights
and a cosh base; their linear-density count does not settle this target.

## Remaining proof obligations

Product symmetry, the exact paired count, order-one growth, Gamma
normalization, and the complete landing counterexample require Lean proofs.
No Euler product or Dirichlet-series representation is claimed for this
calibration.
