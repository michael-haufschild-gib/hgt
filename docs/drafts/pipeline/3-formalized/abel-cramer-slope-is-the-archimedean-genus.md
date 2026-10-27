# The Abel slope of the prime error is the archimedean genus exactly under RH with simple zeros

- **ID:** abel-cramer-slope-is-the-archimedean-genus
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ACP README §9.8 (mass at infinite height), §6.3 (the budget); P41, P42, P46
- **Statement:** With `g(u) = e^{−u/2}(ψ(⌊e^u⌋) − ⌊e^u⌋)` and `A(c) = ∫_0^∞ g² e^{−2cu} du`:
  `RH ∧ (all zeros simple) ⇔ 2c·A(c) → 2 + γ − log 4π` as `c ↓ 0`
  (`riemannHypothesis_and_simple_iff_tendsto_abelSlope`). The RH-only form
  `2c·A(c) → Σ_ρ m_ρ²/|ρ|²` is not formalized: the zero-part bound uses distinct ordinates.

## Goal

The `ℤ`-form of the `𝔽_q` law "prime-error slope = `Σ mult²` = `2g` iff simple spectrum" (P42):
the archimedean genus `2λ₁ = Σ_ρ 1/(ρ(1−ρ))` is the Abel slope exactly under RH with simple zeros.
Settles §9.8 for the prime-error row: under RH the Abel escape of `ψ` has no mass at infinite
height.

## Gates

- [x] 0 → 1 well-posed; inputs located in the corpus.
- [x] 1 → 2 paper proof complete (below).
- [x] 2 → 3 Lean, compiled with `lake --old env lean`, standard axioms only:
      `AnAbelSlopeAtTheGenusIsRHWithSimpleZeros` (⇐), `ThePrimeErrorSymbolSplitsAtTheZeros` (split and
      remainder), `TheZeroPartHasNoMassAtInfiniteHeight` (zero part), `TheAbelSlopeOfThePrimeErrorIsTheArchimedeanGenus`
      (assembly); corpus `RHTower.cramer_finite_zero_energy_tail`.

## Approach

(⇐) Abel-bounded ⇒ linear budget (`∫_0^L g² ≤ e·A(1/(2L))`) ⇒ RH (P46). Window atoms in Abel form:
`liminf 2cA(c) ≥ Σ_{ρ∈Z} m_ρ²/|ρ|²` for finite `Z`. Copies: `Σ_q 1/|ρ_q|² = 2 + γ − log 4π` (P46).
A zero of order `m ≥ 2` adds `≥ 2/|ρ|²` beyond the copy sum: contradiction.

(⇒) Under RH:
1. RH ⇒ `|ψ(n) − n| ≤ C√n log² n` (corpus von Koch) ⇒ κ-energy for every `κ > 0` ⇒ line symbol
   `G(c, y) = F(s)/s`, `F = −ζ′/ζ − ζ`, `s = ½ + c + iy`; Plancherel `∫|G|² = 2πA(c)`.
2. `logDeriv_xi_eq_partialFraction` and `ξ = ½ s(s−1)Γℝ(s)ζ(s)`:
   `F(s)/s = Σ'_q (−1/ρ_q)/(s − ρ_q) + E(s)/s`,
   `E(s) = −C₀ + 1/s + (1/(s−1) − ζ(s)) + logDeriv Γℝ(s)`, `C₀ = Σ'_q 1/(2ρ_q(ρ_q − ½))`
   (identity `((ρ−½)⁻¹ + (s−ρ)⁻¹)/s = 1/(ρ(s−ρ)) + 1/(2ρ(ρ−½)s)`).
3. `sup_{0<c≤1} ∫|E/s|² dy < ∞`: convexity `|ζ(σ+it)| ≪ t^{¼+η}`, `|Γℝ′/Γℝ| ≤ log t + K`,
   compactness near `y = 0` (`1/(s−1) − ζ` entire).
4. Zero part `P_c(y) = Σ'_q b_q/(c + i(y − γ_q))`, `b_q = −1/ρ_q`. Finite truncations over
   `|γ| ≤ N` are Laplace transforms of causal waves `1_{u>0} e^{−cu} Σ_{q∈F} b_q e^{iγ_q u}`;
   Fatou bounds `∫|P_c|²` by the uniform bound on the truncations, each split as head + tail with
   `|a + b|² ≤ (1 + t)|a|² + (1 + 1/t)|b|²`.
5. Dyadic shells `2^k ≤ |γ| < 2^{k+1}` (corpus `integral_norm_sq_zeroSum_div_cube_le`, local
   harmonic sums, shell counts): block energy of the tail `k ≥ k₀` is `≤ τ(k₀) → 0` per unit
   `u`-block, uniformly; so `limsup (c/π)∫|P_c − P_c^{F₀}|² ≤ C τ(k₀)`.
6. Head: with distinct ordinates, `2c ∫_0^∞ e^{−2cu}|Σ_F b e^{iγu}|² du → Σ_F |b_q|²`. With step 3
   and the same `(1 + t)` splitting, `limsup 2cA(c) ≤ Σ_q 1/|ρ_q|² = 2 + γ − log 4π`; the window
   atoms give `liminf ≥` the same.

## Log

- 2026-10-27 — formalized (⇐ in P50, ⇒ in P51); moved to 3-formalized.

- 2026-10-27 — created; inputs: `logDeriv_xi_eq_partialFraction`, `exists_norm_riemannZeta_le_convexity`,
  `norm_logDeriv_Gammaℝ_le`, `sum_inv_one_add_abs_im_sub_le`, `integral_norm_sq_zeroSum_div_cube_le`,
  `tsum_inv_zero_mul_one_sub_zero`.
