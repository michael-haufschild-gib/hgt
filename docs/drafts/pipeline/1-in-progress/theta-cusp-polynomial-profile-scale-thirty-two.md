# Quartic profile at theta scale thirty-two

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Σ6
- **Target:** The quartic profiled source has a negative Gaussian-coordinate
  direction at `x₃₂=log(32/π)/2`.

Use the last Gaussian basis vector. The proposed complete-source comparison is
`polyModel 32 0 (−216·61²) 1`; its sign is being checked exactly in Lean.
The upper error allowance must include every unequal pair and every higher atom.

Analytic bounds to discharge:

- `9/8≤x₃₂≤6/5` and `F'≤−59F`.
- With `t=2x₃₂²−1`, `49/32≤t≤47/25`, hence
  `G_P=t²G+8x₃₂²tF²≤−280F²`.
- Each normalized even jet through order sixteen differs from its first atom
  by at most `1/10000`. The last Gaussian row has absolute sum below one,
  giving a normalized matrix-entry error below one.

The literal weighted source needs its aperture remainder bounded as well.
No global profile obstruction is established until these complete-source
bounds and the exact negative direction are formalized.

Positive survivor to extract if the obstruction holds: the admissible scalar
load interval at this center, including its positive region and singular
boundary. Existing origin, scale-eight, explicit-interval and cofinal positivity
remain valid; they do not establish the intervening sign.
