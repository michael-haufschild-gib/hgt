# The narrow zero-count is vacuous — check the disc reaches the strip

`RHTower.Sieve.exists_zero_count_bound` (`ZetaZeroCount.lean`) bounds the zeros retained by Landau's
lemma at radius `1/4` about `9/8 + iγ`, i.e. those with `‖ρ - (9/8+iγ)‖ ≤ 1/8`. Every such point has

```
Re ρ ≥ 9/8 - 1/8 = 1,
```

and `ζ` has no zero with `Re ≥ 1`. **The retained family is empty; the bound is true and empty.**
Proved: `RHTower/Sieve/ZetaNoZeroNearOne.lean` — `zeta_ne_zero_near_nine_eighths`,
`zeta_narrow_retained_empty`.

It was reported at the time as "the classical `N(t+1) - N(t) = O(log t)`". **That was wrong.** The
classical count is over the critical strip `0 ≤ Re ρ ≤ 1`; a disc of radius `1/8` about `9/8` never
meets it.

## What is sound

`exists_wide_zero_count` (`ZetaZeroCountWide.lean`) uses the wide disc, radius `21/40`, so retained
zeros satisfy `Re ρ ≥ 9/8 - 21/40 = 3/5` (`three_fifths_le_re_of_wide`). Those are not excluded
unconditionally, and this is the lemma the `ζ'/ζ = O(log²)` proof actually consumes. The chain in
`mem:route_e/exponent_one_zeta_toolkit_complete_2026_08_06` is unaffected **except** that its
"zero count `N(t+1)-N(t) = O(log t)`" row should read "zero count on `Re ρ ≥ 3/5`".

## The general lesson

**Before claiming a counting or detection result, check the geometry actually reaches the objects.**
Landau's lemma retains zeros within `R/2` of the centre; with the centre right of `Re s = 1` and `R`
small, that region is provably empty. The test is one subtraction: `centre.re - R/2` versus `1`.

To reach the full critical strip the disc needs radius `≥ 9/8`, so `R ≥ 9/4` and `R₀ > 9/4`, which
puts the disc into `Re w < 0` where the `N = 1` truncation gives no growth bound. A genuine
`N(T+1) - N(T)` count needs the functional equation or a bound left of `Re s = 0`.
