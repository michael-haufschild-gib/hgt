# Landing calibration with the Riemann Gamma factor

- **ID:** landing-calibration-with-the-riemann-gamma-factor
- **Stage:** 3-formalized
- **Type:** PROVED
- **Source:** `docs/reports/review-1011/obstacles-summary.md`, A68.
- **Statement:** Construct a real, FE-symmetric meromorphic completion with the Riemann Gamma factor, Riemann–von Mangoldt zero counting, and infinitely many off-line zeros approaching the critical line.

## Construction

Let `γ₀≤γ₁≤…` be the positive Xi ordinates, with multiplicity. Replace
each adjacent pair by the quartet `1/2±δₙ±iγ₂ₙ₊₁`, where
`δₙ=1/(4(n+1))`. Distinct depths make every new zero simple, even when
the original ordinates repeat. The positive-height count is
exactly `2⌊Nζ(T)/2⌋`: its difference from the actual Xi count is at most
one. Every new zero is off the line, but the depths tend to zero.

Let `G` be the indexed genus-one product of these quartets, centered at
`1/2` and normalized by `G(1/2)=1`. Set
`L(s)=G(s)D∞(s)/(2G(1)(s−1))`, using the corpus entire decompletion
`D∞(s)=2/(sΓℝ(s))` away from zero. Thus `L` is holomorphic off `1`,
has residue one there, and has completion
`Γℝ(s)L(s)=G(s)/(G(1)s(s−1))` on the right half-plane away from `1`.

The corpus proves indexed-product convergence and exact fiber multiplicities
in `HTGeometry/CanonicalProductE1Divisor.lean`, and summability of every
reciprocal power above one in
`RHTower/LiEvenCrossInfiniteCriticalAmplitudeSchattenBoundaryNoGo.lean`.
`XiOrderedZeroCopyEnumeration.lean` identifies the positive-copy count with
the actual Xi zero count. Existing approaching models use quadratic heights
and a cosh base; their linear-density count does not settle this target.

## Proof and Lean status

The points have summable reciprocal `p`-powers for every `p>1`, inherited
from the Xi ordinates. Their distinct depths make the divisor injective;
the indexed genus-one product therefore has analytic order one at each
listed point and no other zeros. Sign and conjugation permutations give
the functional equation and reality. The product bound
`|G(s)|≤exp(Cp|s−1/2|^p)`, `1<p≤2`, gives order at most one.
Pairing adjacent ordinates gives the exact count `2⌊Nζ(T)/2⌋`, hence the
Riemann–von Mangoldt remainder. Since `G(1)≠0` and `D∞(1)=2`,
decompletion gives residue one. Depths tend to zero while the right-hand
zero set remains infinite, so the actual analytic divisor fails landing.

Five modules in `InfiniteRankWeilTheory/`, from
`ThePairedXiDivisorApproachesTheLine.lean` through
`TheRiemannGammaFactorDoesNotForceLanding.lean`, passed final direct
`lake --old env lean` checks and transitive audits with only
`propext`, `Classical.choice`, `Quot.sound`.
The capstone is `exists_riemann_gamma_counting_model_without_landing`.
No placeholders or limit overrides occur. The umbrella and README are wired.

The positive survivor is the exact paired-count construction with simple
analytic multiplicities, order at most one, and residue normalization.
No Euler product or Dirichlet-series representation is claimed.
