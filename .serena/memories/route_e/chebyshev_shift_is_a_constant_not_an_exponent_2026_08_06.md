# The `Y+1 → Y` shift is a constant, never a factor in the exponent

In the κ=1 Chebyshev chain the truncation height is chosen at `Z = N+H+1` while the left edge's
trivial size is `Y = N+H`.  Bounding `Y^{c(T)}` therefore needs `log Y` from below in terms of
`log Z`.  Two ways:

- **Wrong here:** `Z = Y+1 ≤ Y²` ⟹ `log Y ≥ (log Z)/2` ⟹ the saving halves, `1/80000 → 1/160000`.
- **Right:** `Y + 1 ≤ 2Y` ⟹ `log Y ≥ log Z - log 2`, and the reciprocal logarithm turns the
  difference into `(1/40000)(log 2)/(2√(log Z)) ≤ 1`, so the shift costs the **constant** `e ≤ 3`.

`RHTower/Sieve/ChebyshevPowersAtHeight.lean` now uses the second, with

    chebFactorOne Z = 3 · exp( -√(log Z) / 80000 )

and all three edge powers bounded against it (`rpow_chebLeftTwo_at_shift`,
`rpow_chebLeftTwo_at_le`, `rpow_chebRightTwo_at_le`, the last with an extra `T`).

## Why it mattered

The smoothing's price at `chebRatioOne N = exp(√(log N)/240000)` is `exp(√(log N)/120000)`.  With
the halved exponent, `-1/160000 + 1/120000 = +1/480000 > 0` — the price would have **swamped** the
saving.  With `1/80000` intact, `-1/80000 + 1/120000 = -1/240000` and the plan holds.

**The error is invisible in any single lemma** — the halved bound is perfectly true.  It only
appears when the two exponents are compared.  Whenever a chain's price and saving are of the same
order (`exp(c√(log N))` here), every constant in the exponent has to be tracked.

Contrast: the Möbius chain's `rpow_leftAbscissaTwo_le_shift` *does* halve (`s/9 → s/18`) and that is
harmless, because there the price `exp(2(log N)^{1/6})` is of strictly smaller order than the saving
`exp(-(log N)^{1/3}/18)`.

See `mem:route_e/chebyshev_kappa_one_height_and_width_2026_08_06`.
