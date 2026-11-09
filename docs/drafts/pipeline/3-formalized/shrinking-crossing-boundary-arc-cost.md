# A reflected boundary arc forces the three-halves crossing law

- **Obstacles:** B13, B112; arithmetic return bounds and zero transport.
- **Stage:** 3-formalized; dependency-closed paper proof and Lean audit passed.
- **Count:** Contribution 9; all helpers and consequences count together.
- **Target:** Universal `c>0` such that, for `0<δ≤1/8` and `T≥4`,
  the maximum of `|ζ|` on `D=closedBall(3+iT,5/2+δ)` is at least
  `c T^(δ√δ/(32π))`.
- **Consequence:** At a head return `τ`, a bound `|ζ(s+iτ)|≤N^A`
  on the disc centred at `3+iγ`, `γ≥0`, forces
  `δ√δ log(γ+τ)≤32π[A(log1024+6log log τ)+K]`, with universal `K≥0`.
- **Novelty:** The existing crossing-disc theorem has unspecified
  radius-dependent height exponents. Corpus searches found no uniform
  shrinking-depth law. The new bound controls penetration on the
  two-thirds-power logarithmic scale, without assumptions on the zeros.

## Proof

First take `T≥8`. Write `c₀=3+iT`, `R=5/2+δ`, and `f(w)=ζ(c₀−w)`. This function is
analytic near `closedBall(0,R)` because `T≥8>R`; `|f(0)|≥1/2`.
The corpus's analytic zero-set theorem supplies
`5/2−3δ/4<r<5/2−δ/2` with no zero on `|w|=r`.
Thus `F(θ)=log|f(r exp(iθ))|` is continuous.

Put `η=√δ/4`. For `0≤θ≤η`, `θ²≤δ/16` and
`r(1−cosθ)≤rθ²/2≤5δ/64≤δ/8`. For `w=r exp(iθ)` this gives
`r−δ/8≤Re w≤r`, hence
`1/2+δ/2≤Re(c₀−w)≤1/2+7δ/8<1`.
Also `Im(c₀−w)≥T−r≥T/2≥1`.

Reflection of `s=c₀−w` across `Re s=1/2` has squared distance
`25−10 Re w+r²` from `c₀`. It is bounded by
`(5−r)²+5δ/4≤(5/2+3δ/4)²+5δ/4≤R²`.
The already-proved uniform functional-equation estimate therefore gives
`|f(w)|≤C M (T/2)^(-δ/2)` on this arc, where `M=max_D|ζ|` and `C≥1`
is universal. Everywhere on the circle, `|f(w)|≤M`.

Integrating the two logarithmic bounds over `[0,η]` and `[η,2π]`,
and applying Jensen at zero, gives
`log(1/2)≤log M+ω log C−ωδ log(T/2)/2`, with `ω=η/(2π)`.
Since `0≤ω≤1` and `log(T/2)≥log T/2`,
`δ√δ log T/(32π)≤log M+log(2C)`.
Exponentiation gives `c=1/(2C)` for `T≥8`. For `4≤T≤8`,
`δ√δ/(32π)≤1` and the Euler anchor gives `M≥1/2`.
Increasing the logarithmic constant by `log2+log8` proves the full
height range, with `c=1/(32C)`.

For an aligned return `τ`, `N≤1024(log τ)^6` at all sufficiently large
return heights. Translate the source disc by `iτ`; its actual height is
`γ+τ≥τ`. Substitution of `M=N^A`, `A≥0`, gives the stated budget.
No hypothesis on the zero configuration or on RH enters.

## Exact inputs

- `ArithmeticAuxiliaryDynamics.exists_norm_zeta_le_reflect`
- `ArithmeticAuxiliaryDynamics.half_le_norm_zeta`
- `ArithmeticAuxiliaryDynamics.length_le_pow_log_of_isHeadReturn`
- `HTGeometry.log_norm_le_circleAverage_log_norm`
- `Bottcher.exists_radius_avoiding_zeros`
- `HTGeometry.one_sub_cos_le_sq_div_two` in `HyperbolicLevyKhintchine`

## Lean

Owner: `ArithmeticAuxiliaryDynamics`. Module:
`ACrossingArcPaysThreeHalves.lean`. No added analytic premises; the
zero-free boundary radius is proved to exist. Exponent sharpness is not claimed.

Verified capstones:

- `exists_crossing_arc_logarithmic_cost`
- `exists_crossing_arc_rpow_cost`
- `exists_large_zeta_value_on_crossing_arc_disc`
- `exists_aligned_crossing_threeHalves_budget`

Final audit from `formal/`:
`lake --old env lean GaloisForLFunctions/ArithmeticAuxiliaryDynamics/ACrossingArcPaysThreeHalves.lean`.
The logarithmic, actual-source large-value, and aligned-return capstones
depend only on `propext`, `Classical.choice`, and `Quot.sound`.
Imported by `ArithmeticAuxiliaryDynamics.lean`; no umbrella build.
