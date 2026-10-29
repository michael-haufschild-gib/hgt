# Two-sided annular frames for growing Ramanujan conductors

Status: formalized, individually checked, and wired.

## Actual object and improvement

For the literal normalized Ramanujan pole profiles, put
`F(n) = Σ_{m≤Q} a_m c_m(n)/sqrt(φ(m)n)` and `C = Σ_{m≤Q} a_m²`.
The simultaneous bound holds, for every `Q≥2`, shift `A`, length `N`, and real
coefficient vector,

`|Σ_{A<n≤A+N} F(n)² - (H_{A+N}-H_A) C| ≤ Q(Q-1) C/(A+1)`.

On `(A,2A]`, `A≥4Q(Q-1)` give frame constants `1/4` and `5/4`.
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

Module: `CriticalArithmeticCorrelationTheory/AnnularRamanujanFamiliesHaveTwoSidedFrames.lean`.
Final individual check61590 passed clean. All printed capstone dependencies are `propext`, `Classical.choice`, and `Quot.sound` only. The existing packet module's first needed olean39049 passed. The new module is imported by the programme umbrella; no full or umbrella build was run.

The same module proves `weilPrimeKernel_eq_zero_on_dyadic_annulus` and `dyadic_annulus_prime_quadratic_eq_zero`: no two distinct integers in `(A,2A]` divide one another. Thus the literal prime compression to one such annulus is zero. This exact boundary explains why the frame theorem alone gives no localized prime quasimodes; prime transport must cross annular boundaries.
