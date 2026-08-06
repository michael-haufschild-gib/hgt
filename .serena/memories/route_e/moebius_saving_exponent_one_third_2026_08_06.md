# The Möbius saving exponent reaches 1/3, and stops there

`RHTower.Sieve.exists_norm_tsum_moebius_smoothWeight_le_saving_two`
(`RHTower/Sieve/MoebiusSavingKappaTwo.lean`) is the κ=2 analogue of
`exists_norm_tsum_moebius_smoothWeight_le_saving`: the left-edge term is `N+H` times

    exp( -log(N+H) / log²K )

in place of the κ=9 chain's `exp( -c₉ log(N+H) / (16 log⁹K) )`.  Unconditional.  Both chains now
terminate at the same layer; nothing downstream consumes either yet.

Helpers: `rpow_leftAbscissaTwo`, `rightAbscissaTwo_sub_leftAbscissaTwo` (the width is *exactly*
`2/log²K`, so the horizontal-edge factor rewrites rather than being bounded).

## The exponent arithmetic

Balancing `log²K` against `exp(-log x / log²K)` gives `log K ≍ (log x)^{1/3}`, hence
`exp(-c (log x)^{1/3})` — against `1/10` from the κ=9 rectangle.  In general the saving exponent is
`1/(w+1)` where `w` is the power of `log K` in the **rectangle half-width** `log^{-w}K`.

## Why 1/3 is the terminus of this route

The half-width is `log^{-2}` because the strip estimate rests on `ζ'/ζ ≪ log²` on the region.
A width `log^{-1-ε}` would need `ζ'/ζ ≪ log^{1+ε}`, which the Landau + Borel–Carathéodory route
cannot supply (already-recorded ceiling: shrinking the Landau radius costs what it gains).
Vinogradov–Korobov would license `log^{-2/3-ε}` and the classical `3/5`, but Vinogradov's mean
value theorem is in neither the corpus nor mathlib.

## Literature benchmark (do not chase)

`arXiv:2603.21490` (Mar 2026) gives `ζ(σ+it) ≠ 0` for `t ≥ 3`, `σ ≥ 1 - 1/(4.896 log t)`.  Same
shape as our `exists_zero_free_region_explicit`; a **constant** improvement only.  The Möbius
exponent depends on the power of `log`, not on the constant, so a better constant buys nothing here.

See `mem:route_e/moebius_kappa_two_contour_proved_2026_08_06`.
