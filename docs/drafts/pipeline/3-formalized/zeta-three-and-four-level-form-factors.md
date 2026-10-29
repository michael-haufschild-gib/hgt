# ζ zeros: the 3- and 4-level form factors below threshold

- **ID:** zeta-higher-form-factors
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-2810/fable.md §7 Q-III (first half); card
  `fable-three-questions-sign-collision-census.md`
- **Statement:** Unconditionally, with complex ordinates, for `S(x,t) = Σ_ρ x^{ρ−1/2}/(1+(t+i(ρ−½))²)`
  (corpus `lorentzZeroSumAll`):
  - **(A, 3-level)** `α, β > 0`, `α + β < 1`:
    `∫_0^T S(T^α,t) S(T^β,t) conj S(T^{α+β},t) dt = o(T log T)`;
  - **(B, 4-level)** `0 < α < β`, `α + β < 1`:
    `∫_0^T |S(T^α,t)|² |S(T^β,t)|² dt ~ (αβ/16) T log² T` (factorization:
    `= (1/T)∫|S(T^α)|² ∫|S(T^β)|² (1+o(1))`, since `∫_0^T|S(x,t)|² ~ (T/4) log x`).

## Goal
The 3- and 4-level correlation sums of Q-III "by the corpus's pair-correlation method": the
height-mean-square method of `MontgomeryPairCorrelationLeadingOrder` (Montgomery's lemma
`Z = −2√x S = P + E`, Montgomery–Vaughan, PNT moments), extended to products of zero sums.

## Paper proof
Notation: `d_x(n) = primeAmp x n = √x Λ(n) n^{−1/2} min(n/x, x/n)`; `K_x(t) = Σ_n d_x(n) e^{−it log n}`;
`P = e^{it log x} K_x` (prime side); `|E(x,t)| ≤ 4x/(1+t²) + x^{−1/2}(C + log(|t|+4)) + 16x^{−2}/(1+|t|)`.

1. **Products of phase series.** For `a, b` with `a₀ = b₀ = 0`, `Σ|a|, Σ|b| < ∞`:
   `K[a]K[b] = K[a ⍟ b]` (Dirichlet convolution; `LSeries_convolution'` at `s = it`).
2. **Mean values.** If also `Σ n|a_n|² < ∞`: `|∫_0^T |K[a]|² − T Σ|a_n|²| ≤ 104 Σ n|a_n|²` (truncation
   of the sharp Montgomery–Vaughan theorem); by polarization
   `|∫_0^T K[a] conj K[b] − T Σ a_n conj b_n| ≤ 208 (Σ n|a_n|² + Σ n|b_n|²)`.
3. **Prime-power pairs.** For prime powers with `uv = u'v'`: `(u',v') = (u,v)`, or `= (v,u)`, or all
   four are powers of one prime. Hence for `c = d₁ ⍟ d₂` (`d_i = d_{x_i}`, supported on prime powers,
   `d_x(p^k) ≤ √x log p · p^{−k/2}`):
   - `Σ_m c(m) d₃(m) ≤ c₀ √(x₁x₂x₃)`, `c₀ = Σ_p log³p/(p−1)²` (only same-prime pairs);
   - `(Σ d₁²)(Σ d₂²) ≤ Σ_m c(m)² ≤ (Σ d₁²)(Σ d₂²) + (Σ d₁d₂)² + c₁ x₁x₂`;
   - `Σ_m m c(m)² ≤ 2 (Σ n d₁²)(Σ n d₂²) + c₂ x₁x₂ (x₁x₂)^{…}` (polylog · `x₁²x₂²`).
4. **(A)** `S₁S₂ conj S₃ = −Z₁Z₂ conj Z₃/(8x₁x₂)` (`x₃ = x₁x₂`), and `P₁P₂ conj P₃ = K₁K₂ conj K₃`
   (phases cancel). By 1–3, `|∫_0^T K₁K₂ conj K₃| ≤ c₀ x₁x₂ T + O(x₁²x₂² polylog)`. Telescoping
   `Z₁Z₂Z̄₃ − P₁P₂P̄₃ = E₁Z₂Z̄₃ + P₁E₂Z̄₃ + P₁P₂Ē₃` and Cauchy–Schwarz with
   `∫_0^T |Z|² ≲ xT log T`, `∫_0^T |P|² ≲ xT log x` give `o(x₁x₂ T log T)`.
5. **(B)** `|S₁|²|S₂|² = |Z₁Z₂|²/(16x₁x₂)`, `|P₁P₂|² = |K₁K₂|²`, `∫_0^T|K₁K₂|² = TΣc² + O(Σ m c²)`,
   `Σ d_x² ~ x log x` (corpus), `Σ d₁d₂ ≤ √(x₁x₂)(x₁/x₂) O(log² x₂) = o(√(x₁x₂) log T)` for `α < β`;
   the `E`-terms are `o(x₁x₂ T log²T)` by the `δ`-inequality of the pair assembly.

## Lean (RHTower/, compiled, wired into `RHTower.lean`)
- `MontgomeryPhaseSeriesProducts` — `phaseSeries_mul` (product = Dirichlet convolution),
  `integral_normSq_phaseSeries_sub_le` (mean value, 104), `norm_integral_phaseSeries_mul_conj_sub_le`
  (bilinear, 208).
- `MontgomeryPrimePowerPairs` — `eq_or_swap_of_mul_eq` (pair structure), `LL_le_log_sq`,
  `summable_vonMangoldt_mul_LL_div`, `summable_primePow_LL_sq_div`, `conv_mul_le`, `sum_sq_conv`,
  `sum_mul_sq_conv`.
- `MontgomeryTripleFormFactorVanishes` — **(A)** `tendsto_tripleFormFactor`; `triple_S_eq`,
  `primeSide_triple_eq`, `norm_integral_primeConjSum_triple_le`, `norm_integral_triple_le`,
  `eventually_energy_bounds`.
- `MontgomeryFourLevelFormFactorFactorizes` — **(B)** `tendsto_fourLevelFormFactor` (for
  `0 < α < β`, `α + β < 1`); `primeAmp_mul_primeAmp_le`, `eventually_tsum_primeAmp_mul_le`,
  `integral_normSq_primeConjSum_mul_bounds`, `abs_quadruple_sub_le`, `quad_ratio_le`.
- Diagonal: `tendsto_fourthMoment` — `∫_0^T |S(T^α)|⁴ ~ (α²/8) T log²T` for `0 < α < 1/2`
  (Gaussian `E|X|⁴ = 2(E|X|²)²`); `sq_conv_eq_of_not_isPrimePow`, `sum_sq_conv_ge`,
  `integral_primeConjSum_fourth_bounds`, `quad_diag_ratio_le`.

## Log
- 2026-10-29 — created; paper proof drafted.
- 2026-10-29 — (A) and (B) formalized.
