# Modulus-first vertical integrals cannot save anything for Möbius

- **ID:** modulus-first-no-go
- **Stage:** 5-failed
- **Type:** FALSIFIED (whole family of routes)
- **Statement:** For `1 < σ ≤ 2`, `T ≥ 1`, `x > 0`,
  `∫_{|t| ≤ T} ‖L(μ,σ+it)·x^s/s²‖ dt ≥ x^σ/70`. Hence every route that bounds
  `‖∑_{n ≤ N} μ(n)log(x/n)‖` by `(arithmetic error) + (1/2π)·A` with
  `A ≥ ∫_{|t| ≤ T}‖L(μ,σ+it)x^s/s²‖dt` outputs at least `≍ x^σ`, the trivial size of the sum.

## No-go closure

- **Exact killing theorem/mechanism:** `RHTower/Sieve/MoebiusModulusFirstNoGo.lean`.
  `L(μ,s)·ζ(s) = 1` and `‖ζ(σ+it)‖ ≤ 7` on `1 ≤ σ ≤ 2`, `1/2 ≤ |t| ≤ 1` (from
  `norm_riemannZeta_le_inv_abs_im`), so `‖L(μ,σ+it)‖ ≥ 1/7` there, while the kernel is
  `≥ x^σ/5`. A segment of length `1/2` then forces `A ≥ x^σ/70`
  (`norm_cesaro_integral_moebiusCoeffC_lower`, `le_of_norm_cesaro_integral_moebiusCoeffC_le`).
  The step being killed is `‖∫ F‖ ≤ ∫ ‖F‖`, taken by every Perron/Cesàro/Halász route in the
  folder — *before* any analytic estimate is chosen. So no improvement of the analytic side can
  rescue the family: the deficit is the discarded phase, not a lossy inequality.

- **Strongest positive survivor:** the family's ceiling is `≍ x^σ`, and the best formalized member is
  within one square root of it:
  `∫_{|t| ≤ T} ‖L(f,σ+it)x^s/s²‖ dt ≤ 8x^σ√Q + 12x^σ√κ` for every `|f| ≤ 1`, uniformly in `T`
  (`RHTower/Sieve/CesaroDyadicMeanSquare.integral_symm_norm_cesaro_le_of_meanSquare_dyadic`), giving
  `x^σ√(log N)` for a truncation at `N`, against `x^σ log N` for the pointwise Euler bound. Also
  surviving: the global window law
  (`HalaszGlobalLargeValueWindow.volume_halaszLargeValues_le_window` and
  `HalaszGlobalWindowExplicit.integral_norm_tsum_twistedSummand_le_power_saving`), which repairs a
  vacuous measure bound in the corpus and is the only formalized statement that *locates* the
  exceptional frequency.

- **New insight:** the three analytic mechanisms in the folder — pointwise Euler bound, mean square
  via Cauchy–Schwarz, dyadic blocks with a decaying kernel constant — differ only in the power of
  `log N` they lose, and all of them sit above a common floor `x^σ` that is independent of them.
  Ranking them further is therefore not progress on RH; the next mechanism has to keep the phase.
  Concretely, what must replace `‖∫ F‖ ≤ ∫‖F‖` is an identity: the exact mean value
  `HTGeometry/GeneralizedDirichletMeanValue.genPoly_meanValue` keeps the full off-diagonal
  `∑_{m ≠ n} a_m conj(a_n)·oscInt(log(m/n),T,U)`, and it is the phase-retaining object already
  available in the corpus.

- **Status:** internal; dependency-closed and formalized. `lake build` green, axioms
  `[propext, Classical.choice, Quot.sound]` on every statement above.

## The same cap applies to the unconditional replacement

The mean-square route that replaces the modulus-first estimates is capped in the same way, and by the
same argument rather than by a new one. `norm_sum_Icc_mul_log_div_le_cesaro_dyadic`'s right-hand side —
arithmetic error plus `8x^σ√(5πe(1 + log N)) + 12x^σ√(5π)` — mentions no coefficient, because `Q` and `κ`
are built from `‖a_n‖`. Instantiating at `f ≡ 1` and `x = N`, where the left side is `∑_{n ≤ N}log(N/n)`
and every `n ≤ N/2` contributes at least `log 2`:

`⌊N/2⌋·log 2 ≤ ∑_{n ≤ N}E(σ,T,N/n) + (1/2π)(8N^σ√(5πe(1 + log N)) + 12N^σ√(5π))`

(`CesaroDyadicTrivialCap.trivial_le_cesaro_dyadic_bound`, with `sum_Icc_log_div_ge`). So the chain cannot
assert `o(N)` for any `f`. The `log N → √(log N)` improvements are improvements *within* a capped family;
recording the cap alongside them is what keeps that honest.

## Log
- 2026-08-08 — created; the killing lower bound formalized, and the surviving upper bounds recorded.
- 2026-08-09 — the cap extended to the unconditional mean-square replacement, by instantiation at the
  constant sequence.
