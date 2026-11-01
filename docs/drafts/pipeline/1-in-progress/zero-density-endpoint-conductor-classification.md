# The zero-density endpoint has positive Euler mass

- **ID:** zero-density-endpoint-conductor-classification
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** review-0111 Γ12; the power-error regime of `TheZeroDensityTwinCarriesTheConductorSeries`.
- **Statement:** The finite-conductor-packet classification extends from `0<κ<1/4` to `0≤κ<1/4`, with the same error condition `0≤α<1−2κ`.

## Endpoint mechanism

At `κ=0`, the existing positive Wirsing lower bound gives
`S_N≥c log N`, `c>0`. Since `H_N≤1+log N`, eventually
`S_N/H_N≥c/2`. The unconditional harmonic-mean limit for arbitrary
prime sets therefore gives Euler mass `δ(P)>0`.

Positive Euler mass already makes the full unnormalized conductor series
summable and classifies every hyperplane gap by its secular sign.
Consequently the maximal gap fails exactly when a finite packet exceeds
`1/s` for some `0<s<2 log 2`. This avoids a singular extension of the
positive-κ fixed-scale argument, whose cutoff uses `1/κ`.

## Scope

The power-error bound is part of the classified regime, not a newly
postulated analytic input. Mere relative logarithmic density zero, with
no quantitative error bound, is not covered by this argument.

## Lean dependencies

`exists_pos_mul_rpow_le_gaugeHarmonicSum_primeSetFlip`,
`primeSetFlip_harmonicCorrelation_tendsto`,
`primeSetFlip_hasHyperplaneGap_iff_secular`,
`hodgeSeparates_primeSetFlip_of_packet`.
