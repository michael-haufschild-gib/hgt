# κ = 9 is structural to the mean-value route — and where the 9 comes from

## The arithmetic of the exponent

`RHTower/Sieve/ZeroFreeAssembly.lean` derives the zero-free region from two facts about
`ζ(σ+iγ)` with a zero at `β+iγ`:

- **lower** (three-four-one, `exp_three_four_one_ge`):
  `|ζ(σ+iγ)| >= e^(-11/2) * (δ/2)^(3/4) * B0^(-1/4)`, `δ = σ-1`, `B0` a bound on `|ζ(σ+2iγ)|`;
- **upper** (mean value, `zero_free_inequality`): `|ζ(σ+iγ)| <= M * (σ-β)`, `M` a bound on `|ζ'|`
  on the segment.

The region's width is `δ` itself (`hgap : σ - β <= 2(σ-1)`), so the comparison is
`2 M δ < e^(-11/2)(δ/2)^(3/4) B0^(-1/4)`, i.e.

```
δ  <  C / (B0 * M^4).
```

With `L = log N`, `B0 ≍ L` and `M ≍ L^2` this is `δ ≲ L^(-9)`. **That is exactly the 9:
`1` from `B0`, `8` from `M^4`.** `quarter_comparison` in that file is this computation.

## Why `M ≍ L^2` cannot be improved on this route

`deriv_const_le` bounds `|ζ'|` by Cauchy's estimate on a disc of radius `R` around the segment:
`M ≍ max|ζ| / R ≍ L / R`. The radius cannot be enlarged: the growth bound `|ζ| ≲ log N` holds only
within `≍ 1/log N` of the line `Re s = 1` (further left `ζ` is a power of `t`). So `R ≍ 1/L`, hence
`M ≍ L^2`, hence `κ >= 9`. **Feeding a better growth bound does not help**: with Littlewood's
`|ζ| ≲ L/loglog L` one gets `B0 ≍ L/loglog L` and `M ≍ L^2/loglog L`, so
`δ ≲ (loglog L)^5 / L^9` — the exponent is unchanged.

The same wall is in the vendored `PNTPlus.ZetaBounds`: `Zeta_diff_Bnd` is the same mean-value step,
`ZetaZeroFree` is the same `A/(log|t|)^9`.

## The only exit

Replace the mean value by the **logarithmic derivative**: Landau's lemma
`-Re (f'/f)(z) <= 16M/R - sum_{ρ} Re 1/(z-ρ)` on `|z-c| <= R/4` for `|f/f(c)| <= e^M`, then drop all
zeros but one (each term is `>= 0` for `Re z > 1/2`). Combined with the three-four-one inequality
for `-Re ζ'/ζ` this is de la Vallée Poussin, `κ = 1`; with the Littlewood growth bound it is
`σ >= 1 - c loglog t / log t`, which is what
`mem:zero-free-region-exponent-is-the-mr-wall` licenses.

**Assets already in the corpus** — do not rebuild:
- `RHTower/ArgumentVariation.lean`: `borel_caratheodory` (general, on `ball c R`),
  `exists_analyticOnNhd_exp_eq_ball` (analytic logarithm of a nowhere-zero function on a ball).
- `RHTower/Sieve/ZetaThreeFourOne.lean`: `three_four_one_log_zeta`, `three_four_one_log_zeta_const`.
- `RHTower/Sieve/ZeroFreeAssembly.lean`: the whole κ=9 assembly, including `zeroFreeConst`.
- Littlewood growth: `mem:route_e/littlewood_exponent_proved_2026_08_06`,
  `RHTower/Sieve/ZetaLineRate.lean` (`norm_riemannZeta_line_rate_clean`).

**Missing** (the build): finite zero set in a closed disc + factorisation `f = g * prod (z-ρ)^m`
with `g` zero-free, then Landau's lemma, then the three-four-one for `-Re ζ'/ζ`.
