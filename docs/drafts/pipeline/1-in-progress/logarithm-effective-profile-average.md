# Effective average of the positive count profile

- **ID:** SPL-effective-profile-average
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** For the continuous norm-four profile `P`, integers `Q≥2`,
  `n≥1`, and every `x>0`,

  `|n⁻¹ Σ_{a<n} P(x/3^a)−1/4|`
  `≤(8 log Q+32 log 4+2/3)/Q + Q·4^Q·log 4/(4n)`.

This would give a uniform error of order `log log n/log n`, including a
starting scale depending on `n`, and an effective remainder in the actual
averaged count asymptotic.

## Proposed modulus

Write `r(y)=dist(y/2,ℤ)²`; it is bounded by `1/4` and has Lipschitz constant
`1/2`. On `1/2≤x≤8`, the finite norm-four count gives

`H(x)/x=x/48+r(x)/x+4r(x/4)/x`.

Truncating the profile correction after exponent `J` leaves a nonnegative
tail at most `1/(6·4^J)`. Each term `r(λx)/(λx)` has Lipschitz constant at
most `1+1/λ` on this interval. Hence, for `x,y` in the interval,

`|P(x)−P(y)|≤(2J+8)|x−y|+1/(3·4^J)`.

For a logarithmic displacement at most `log 4/Q`, period-four normalization
puts one scale in `[1,4]` and the other in `[1/2,8]`; their difference is at
most eight times the displacement. With `J=⌊log Q/log 4⌋`, the resulting
modulus is at most `(16 log Q+64 log 4+4/3)/Q`.

## Pairing and arithmetic input

The [effective half-turn](../3-formalized/logarithm-effective-half-turn.md) provides a shift
`k≤Q·4^Q·log 4/2` approximating the complementary translate. Pairing orbit
sums gives half the modulus plus `k/(2n)`, since `0≤P≤1/2` and shifting
the sum changes only its two boundary blocks.

Required formal inputs: the quantitative half-turn, midpoint Lipschitz bound,
finite profile truncation, logarithmic normalization, and finite pairing
inequality. Qualitative continuity alone supplies none of the displayed
constants. No many-prime all-height saving is claimed.
