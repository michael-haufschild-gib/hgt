# The Abel slope of the prime error is the archimedean genus exactly under RH with simple zeros

- **ID:** abel-cramer-slope-is-the-archimedean-genus
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** ACP README §9.8 (mass at infinite height), §6.3 (the budget); P41, P42, P46
- **Statement:** With `g(u) = e^{−u/2}(ψ(⌊e^u⌋) − ⌊e^u⌋)` and `A(c) = ∫_0^∞ g² e^{−2cu} du`:
  `RH ∧ (all zeros simple) ⇔ 2c·A(c) → 2 + γ − log 4π` as `c ↓ 0`. Under RH alone
  `2c·A(c) → Σ_ρ m_ρ²/|ρ|²` (no mass at infinite height).

## Goal

The `ℤ`-form of the `𝔽_q` law "prime-error slope = `Σ mult²` = `2g` iff simple spectrum" (P42):
the archimedean genus `2λ₁ = Σ_ρ 1/(ρ(1−ρ))` is the Abel slope exactly under RH with simple zeros.
Settles §9.8 for the prime-error row: under RH the Abel escape of `ψ` has no mass at infinite
height.

## Gates

- [x] 0 → 1 well-posed; inputs located in the corpus.
- [ ] 1 → 2 paper proof complete (below; heavy direction steps 3–6 to be checked against Lean).
- [ ] 2 → 3 Lean: `M1` (⇐ direction), `M2` (shell tail energy), `M3` (Hadamard split), `M4`
      (assembly).

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
4. Zero part `P_c(y) = Σ'_q b_q/(c + i(y − γ_q))`, `b_q = −1/ρ_q`. Finite truncations are Laplace
   transforms of `e^{−cu} Σ_{q∈F} b_q e^{iγ_q u}`; Fatou bounds `∫|P_c − P_c^{F₀}|²` by
   `2π liminf_F ∫_0^∞ |Σ_{F∖F₀} b e^{iγu}|² e^{−2cu} du`.
5. Dyadic shells `2^k ≤ |γ| < 2^{k+1}` (corpus `integral_norm_sq_zeroSum_div_cube_le`, local
   harmonic sums, shell counts): block energy of the tail `k ≥ k₀` is `≤ τ(k₀) → 0` per unit
   `u`-block, uniformly; so `limsup (c/π)∫|P_c − P_c^{F₀}|² ≤ C τ(k₀)`.
6. Finite part: `(c/π)∫|P_c^{F₀}|² → Σ_{γ} |Σ_{γ_q = γ} b_q|²`. Minkowski with step 3 gives
   `2cA(c) → Σ_ρ m_ρ²/|ρ|²`; with simple zeros this is `Σ_q 1/|ρ_q|² = 2 + γ − log 4π`.

## Log

- 2026-10-27 — created; inputs: `logDeriv_xi_eq_partialFraction`, `exists_norm_riemannZeta_le_convexity`,
  `norm_logDeriv_Gammaℝ_le`, `sum_inv_one_add_abs_im_sub_le`, `integral_norm_sq_zeroSum_div_cube_le`,
  `tsum_inv_zero_mul_one_sub_zero`.
