# Effective half-turn of the logarithmic rotation

- **ID:** SPL-effective-half-turn
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Put `α=log 3/log 4`. For every integer `Q≥2`, there are
  integers `k≥1` and `ℓ` such that
  `k≤Q·4^Q·log 4/2` and `|kα−ℓ−1/2|<1/Q`.

## Paper proof

One-dimensional Dirichlet approximation gives `1≤q≤Q` and an integer `m`
with `0<β=|qα−m|<1/Q`. Here `0≤m≤q`. The distinct integers `3^q` and
`4^m` are at most `4^q`, so integer-log separation gives
`β≥1/(4^q log 4)`. Taking `j=⌊1/(2β)⌋` gives `j≥1` and
`0≤1/2−jβ<β`. Thus `k=jq` reaches the half-turn, with either sign of the
Dirichlet error, within the stated bound.

## Scope and remaining work

This is an explicit bound for the discrete rotation by `log 3/log 4`.
The corpus already gives simultaneous homogeneous returns and effective
inhomogeneous boxes for continuous prime-log flows. The discrete half-turn supplies the arithmetic input for quantitative
complementary-profile averaging; an explicit modulus of continuity is the
remaining analytic input.

`EffectiveLogarithmicHalfTurn.lean` formalizes `threeFourRotation_bounds`,
`threeFourRotation_gap`, and `exists_effective_three_four_half_turn`, in
namespace `GaloisForLFunctions.SumProductArithmeticOfTheLogarithm`.
The direct source check passes; the three capstone axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.

An actual profile-averaging error bound remains to be formalized. No many-prime
all-height saving or exceptional-zero exclusion is asserted.
