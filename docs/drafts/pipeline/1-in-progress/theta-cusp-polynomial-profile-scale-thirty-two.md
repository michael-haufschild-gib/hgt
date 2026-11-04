# Quartic profile at theta scale thirty-two

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Wall:** Σ6
- **Target:** Exact scalar-load capacities at `x₃₂=log(32/π)/2`, including every
  critical aperture, as the positive survivor of the quartic obstruction.

The last Gaussian coordinate satisfies
`polyModel 32 0 (−216·61²) 1 4 4 < 0`, proved by
`ThirtyTwoCrossData.upper_model_last_negative`.
The complete-source transfer is proved in `FifthEvenPolynomialCrossObstruction`.

Complete-source estimates proved in `ThirtyTwoCrossSource`:

- `9/8≤x₃₂≤6/5` and `F'≤−59F`.
- With `t=2x₃₂²−1`, `49/32≤t≤47/25`, hence
  `G_P=t²G+8x₃₂²tF²≤−280F²`.
- Each normalized even jet through order sixteen differs from its first atom
  by at most `1/10000`. The last Gaussian row has absolute sum below one,
  giving a normalized matrix-entry error below one.

The literal weighted source adds the exact remainder
`P(r)r(ar cosh(ar)−sinh(ar))F(r/2)²`.
For `0<a<1/2` at `r=2x₃₂`, its bound is `12r sinh(ar)F(x₃₂)²`,
leaving the differentiated coefficient at most `−268F(x₃₂)²`.
Thus both the aperture-independent and literal weighted complete sources fail PSD.

The base capacity `0<τ<1`, its exact PD/PSD intervals, and its singular boundary
are formalized by `ThirtyTwoCrossCapacity.exact_scaling_capacity`.
For the literal weighted source, write
`α(a)=[deriv(flux a)(2x₃₂)/(2x₃₂ sinh(2ax₃₂))]/G_P(x₃₂)`.
The aperture capacity is exactly `τ/α(a)`, with `0<α(a)≤1` and
`0<τ≤τ/α(a)<1` throughout `0<a<1/2`.
The coefficient bounds give the stronger targets `τ<27/35` and
`τ/α(a)<54/67`: multiplying `−280·61²` by `27/35`, or `−268·61²`
by `54/67`, reaches the certified negative comparison `−216·61²`.
Existing origin, scale-eight, explicit-interval and cofinal positivity
remain valid; they do not establish the intervening sign.

Relative gain: the same remainder bound gives
`D/w≤G_P+12F²≤(67/70)G_P`, since `G_P≤−280F²`.
Dividing by the negative `G_P` yields `67/70≤α(a)≤1`, hence
`τ≤τ/α(a)≤(70/67)τ`. This sharper comparison is derived; Lean verification pending.
