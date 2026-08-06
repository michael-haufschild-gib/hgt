# The `1/zeta` bound has its own width ceiling, independent of the zero-free region

Worked out 2026-08-06 while looking for the next consequence of
`mem:route_e/zero_free_region_kappa_one_proved_2026_08_06`. **Record so nobody re-derives it.**

## The mean-value route is capped at width `log^{-9}` — the zero-free region does not help

The classical lower bound `|zeta| >= c/L^7` (PNTPlus `ZetaLowerBnd`) is proved by
`|zeta(s)| >= |zeta(sigma_1+it)| - (sigma_1 - sigma) * sup|zeta'|` with `sigma_1 = 1 + w`. Then

- three-four-one gives `|zeta(sigma_1+it)| >> w^(3/4) L^(-1/4)`;
- `|zeta'| << L^2` (Cauchy at radius `~1/L`).

The step is admissible only when `2 w L^2 <= (1/2) w^(3/4) L^(-1/4)`, i.e. `w <~ L^(-9)`.
**`w ~ L^(-9)` is forced by these two estimates alone** — it has nothing to do with how wide the
zero-free region is. In particular the corpus's `kappa = 1` region does **not** improve it, and
neither does the sharper `zeta'/zeta << L^2` (that route needs `|zeta'|`, and
`|zeta'| = |zeta|·|zeta'/zeta| << L·L^2 = L^3` is *worse* than the direct Cauchy bound `L^2`).

## The logarithmic-derivative route: width `~ log L / L^2`

Integrating `d/du log|zeta(u+it)| = Re(zeta'/zeta)` from `sigma_1 = 1 + L^(-2)` leftwards, with
`|zeta'/zeta| <= A L^2` from `RHTower/Sieve/ZetaLogDerivRegionBound.lean`:

```
log|zeta(sigma+it)| >= log|zeta(sigma_1+it)| - (sigma_1 - sigma) A L^2
                    >= -O(log L)          when  sigma_1 - sigma <~ log L / L^2.
```

Since `sigma_1 - 1 = L^(-2)` and the admissible travel is `~ log L / L^2`, the strip reaches
`sigma >= 1 - (c log L - 1)/L^2` — **left of `1`**, of width `~ log log t / log^2 t`, with
`1/|zeta| << L^K`. That is 7 orders better than PNTPlus's `L^(-9)`, and is the natural next target.

**Not built.** It needs `d/du log|zeta(u+it)| = Re (zeta'/zeta)(u+it)` as a Lean derivative
statement (real variable, complex function, modulus) — the one genuinely new ingredient.

## Also settled: `1/zeta << log t` on the `kappa = 1` region is FALSE by this method

Starting from `sigma_1 = 1 + 1/L`, where `|zeta(sigma_1+it)| >> 1/L`, the admissible travel is only
`~ 1/L^4` (mean value) or `~ log L / L^2` (log-derivative) — both far below the `1/L` needed to
reach the 1-line. So the textbook pairing "`kappa = 1` region + `1/zeta << log t`" does not come
out of the region; it needs a separate argument.

## Done this session

`exists_logDeriv_zeta_bound` now covers `sigma <= 9/8` (was `sigma <= 1`), so it applies on both
sides of the abscissa — needed for any segment argument that starts right of `1`. The `sigma > 1`
case uses `riemannZeta_ne_zero_of_one_le_re` in place of the region.
