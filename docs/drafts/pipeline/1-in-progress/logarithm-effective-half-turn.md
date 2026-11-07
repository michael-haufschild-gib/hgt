# Effective half-turn of the logarithmic rotation

- **ID:** SPL-effective-half-turn
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** Put `α=log 3/log 4`. For every integer `Q≥2`, there are
  integers `k≥1` and `ℓ` such that
  `k≤Q·4^Q·log 4/2` and `|kα−ℓ−1/2|<1/Q`.

## Arithmetic mechanism

One-dimensional Dirichlet approximation gives `1≤q≤Q` and an integer `m`
with `0<β=|qα−m|<1/Q`. Here `0≤m≤q`. The distinct integers `3^q` and
`4^m` are at most `4^q`, so integer-log separation gives
`β≥1/(4^q log 4)`. Taking `j=⌊1/(2β)⌋` gives `j≥1` and
`0≤1/2−jβ<β`. Thus `k=jq` reaches the half-turn, with either sign of the
Dirichlet error, within the stated bound.

## Scope and remaining work

The target is an explicit bound for the discrete rotation by `log 3/log 4`.
The corpus already gives simultaneous homogeneous returns and effective
inhomogeneous boxes for continuous prime-log flows. The discrete half-turn
would make the complementary-profile averaging argument quantitative once
an explicit modulus of continuity is proved.

Formalize the integer range of `m`, the log-gap bound, and the conversion from
a small return to a half-turn. Then derive an actual averaging error bound.
No many-prime all-height saving or exceptional-zero exclusion is asserted.
