# Effective average of the positive count profile

- **ID:** SPL-effective-profile-average
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For the continuous norm-four profile `P`, integers `Q≥2`,
  `n≥1`, and every `x>0`,

  `|n⁻¹ Σ_{a<n} P(x/3^a)−1/4|`
  `≤(8 log Q+32 log 4+2/3)/Q + Q·4^Q·log 4/(4n)`.

Choosing `Q` proportional to `log n` gives a uniform error of order
`log log n/log n`, including a starting scale depending on `n`. The finite
parameter bound also controls the actual averaged count.

## Paper proof: modulus

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

## Actual count remainder

Write `R(Q)=(8 log Q+32 log 4+2/3)/Q` and `B(Q)=Q·4^Q·log 4/4`.
For `x>1`, put `n=⌊log x/log 3⌋+1`. The actual count-profile bridge and
the finite average bound give

`|(x²/2−Riesz(x))/x−n/4|≤5/8+nR(Q)+B(Q)`.

The floor estimate
`0≤n/log x−1/log 3≤1/log x` therefore yields

`|(x²/2−Riesz(x))/(x log x)−1/(4 log 3)|`
`≤R(Q)(1/log 3+1/log x)+(B(Q)+7/8)/log x`.

Here `Riesz(x)=∫₀ˣN(t)dt` is the actual positive-model count average.
All choices `Q≥2` are allowed. The two error terms display the tradeoff
between resolution and return length without an unspecified threshold.

## Parameter choice

Let `Y≥max(256,exp(exp 1))` and `Q=⌊log Y/log 16⌋`. Then `Q≥2`,
`16^Q≤Y`, `Q≤log Y`, and `1/Q≤2 log 16/log Y`. The elementary bound
`Q²≤4^Q` gives `B(Q)/Y≤log 4/Q`. Since `log log Y≥1`,

`R(Q)+B(Q)/Y ≤ C·log log Y/log Y`,

where `C=2 log 16·(8+33 log 4+2/3)`. Taking `Y=n` proves the uniform
profile rate. Taking `Y=log x` in the actual count bound gives a coefficient
error at most `((1/log 3+1)C+7/8)·log log log x/log log x` for
`x≥exp(max(256,exp(exp 1)))`. Indeed `1/Y≤log log Y/log Y` in the chosen
range, and `1/log 3+1/Y≤1/log 3+1`. These are quantitative consequences
of the same finite-parameter estimate.

## Formalization

`EffectiveLogarithmicHalfTurn.lean` proves the arithmetic half-turn.
`PositiveNearCountProfileModulus.lean` proves `midpointRounding_lipschitz`,
`profilePartial_error`, `fourProfile_compact_modulus`, and
`logarithmicProfile_resolution_modulus`. Direct source checks pass; capstone
axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.

`PositiveNearCountEffectiveAverage.lean` proves the finite pairing inequality,
`effective_profile_average`, `effective_riesz_length_error`, and
`effective_integral_count_coefficient_error`. Its direct source check and
capstone axiom audits pass with the same standard axioms.

`PositiveNearCountConvergenceRate.lean` proves
`exists_resolution_for_log_rate`, `profile_log_rate`,
`uniform_profile_log_rate`, and `integral_count_coefficient_log_rate`, with
the constants and cutoffs above. Its direct source check passes; all four
capstones use only `propext`, `Classical.choice`, and `Quot.sound`.

The pointwise count-distance gap and many-prime all-height saving remain open.
