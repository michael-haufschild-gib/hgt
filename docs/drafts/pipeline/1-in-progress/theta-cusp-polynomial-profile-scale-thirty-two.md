# Quartic profile at theta scale thirty-two

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Σ6
- **Target:** The quartic profiled source has a negative Gaussian-coordinate
  direction at `x₃₂=log(32/π)/2`.

The last Gaussian coordinate satisfies
`polyModel 32 0 (−216·61²) 1 4 4 < 0`, proved by
`ThirtyTwoCrossData.upper_model_last_negative`.
Transferring this exact comparison to the complete source requires the bounds below.

Analytic bounds to discharge:

- `9/8≤x₃₂≤6/5` and `F'≤−59F`.
- With `t=2x₃₂²−1`, `49/32≤t≤47/25`, hence
  `G_P=t²G+8x₃₂²tF²≤−280F²`.
- Each normalized even jet through order sixteen differs from its first atom
  by at most `1/10000`. The last Gaussian row has absolute sum below one,
  giving a normalized matrix-entry error below one.

The literal weighted source adds the exact remainder
`P(r)r(ar cosh(ar)−sinh(ar))F(r/2)²`.
For `0<a<1/2` at `r=2x₃₂`, the proposed bound is `12r sinh(ar)F(x₃₂)²`,
leaving the differentiated coefficient at most `−268F(x₃₂)²`.
No global profile obstruction is established until these complete-source
bounds and the exact negative direction are formalized.

Positive survivor to extract if the obstruction holds: the admissible scalar
load interval at this center, including its positive region and singular
boundary. For the literal weighted source, write
`α(a)=[deriv(flux a)(2x₃₂)/(2x₃₂ sinh(2ax₃₂))]/G_P(x₃₂)`.
The proposed aperture capacity is exactly `τ/α(a)`, with `0<α(a)≤1` and
`0<τ≤τ/α(a)<1` throughout `0<a<1/2`.
Existing origin, scale-eight, explicit-interval and cofinal positivity
remain valid; they do not establish the intervening sign.
