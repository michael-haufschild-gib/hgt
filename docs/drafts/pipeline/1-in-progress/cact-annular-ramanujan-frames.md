# Two-sided annular frames for growing Ramanujan conductors

Status: in progress. No new theorem claimed before Lean checks.

## Actual object and proposed improvement

For the literal normalized Ramanujan pole profiles, put
`F(n) = Σ_{m≤Q} a_m c_m(n)/sqrt(φ(m)n)` and `C = Σ_{m≤Q} a_m²`.
Seek the simultaneous bound, for every `Q≥2`, shift `A`, length `N`, and real
coefficient vector,

`|Σ_{A<n≤A+N} F(n)² - (H_{A+N}-H_A) C| ≤ Q(Q-1) C/(A+1)`.

On `(A,2A]`, `A≥4Q(Q-1)` should then give frame constants `1/4` and `5/4`.
This supplies both sides on a growing conductor family, unlike the existing
whole-prefix lower frame bound. It does not estimate the completed source or
interactions between distinct annuli.

## Proof mechanism and corpus comparison

The already formalized `abs_ramanujanPacket_window_discrepancy_le` gives the
actual packet's ordinary shifted-prefix discrepancy `Q(Q-1)C`. Existing
`BezoutValuationIncidence.abs_sum_range_mul_antitone_le` transfers that bound
against `1/(A+i+1)` without any sum of pairwise conductor errors. The first
weight is exactly `1/(A+1)`. Dyadic harmonic mass lies between `1/2` and `1`.

Searches142–146 checked weighted windows and actual spectral windows. The latter
are fixed-conductor spectral projections, not these growing annular frames.
The summation-by-parts source and the actual large-sieve packet statement have
been read. No statistical model or unproved analytic premise enters.

## Formalization

Planned module: `CriticalArithmeticCorrelationTheory/AnnularRamanujanFamiliesHaveTwoSidedFrames.lean`.
Depends on the existing packet theorem; its first olean is needed only when
this importing module is checked. No full or umbrella build.
