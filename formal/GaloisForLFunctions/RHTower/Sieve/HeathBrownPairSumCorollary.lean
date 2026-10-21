import GaloisForLFunctions.RHTower.Sieve.HeathBrownPairSumPower
import GaloisForLFunctions.RHTower.Sieve.HeathBrownPairSumDilation
import GaloisForLFunctions.RHTower.Sieve.HeathBrownSparseMeanValueSelfBound

/-!
# Heath-Brown's Corollary 2.1 and the closing inequality

Heath-Brown's large values theorem in the range `N ∈ [T^{2/3}, T]` rests on three steps: the
approximate functional equation, which bounds the long weighted pair sum
`𝒜(N) = Σ_{t₁,t₂∈W}|Σ_{n∼N} n^{−1/2+i(t₁−t₂)}|²` by `|W|N` plus short dual pair sums
`𝒜(S)` of length `M ≲ T/N`; Corollary 2.1, which bounds each dual pair sum by `𝒜(N)^{1/2}`; and
the scalar closure `𝒜 ≤ X + Y𝒜^{1/2} ⇒ 𝒜 ≤ 2X + Y²`.

This file proves the second and third steps unconditionally.

**Corollary 2.1.**  For `S ⊆ (M, 2M]` and `M² ≤ N`,

`𝒜_{1/2}(S)² ≤ |W|² D₁⁴ · 2D₂ · 𝒜_{1/2}((N, 8N])`,

with `D₁ ≥ d` on `(M², 4M²]` and `D₂ ≥ d` on `(N, 8N]`: Cauchy–Schwarz over the `|W|²` pairs, the
square of the polynomial with divisor-bounded coefficients (`hbPairSum_sq_le_fourthMoment`), and
the dilation comparison `(M², 4M²] → (N, 8N]` (`hbAmp_half_le_of_le`, the rigorous form of
Heath-Brown's Lemma 2).  With the divisor bound `d(u) ≤ C_δ u^δ` the loss is `2(C_δ(8N)^δ)⁵`.

**Closure.**  If `Q ≤ X + Y Σ_{i∈I} q_i` and `q_i² ≤ Z Q`, then `Q ≤ 2X + Y²|I|²Z` (the corpus
scalar self-bound `le_two_mul_add_sq_mul_of_le_add_of_sq_le_mul` after Cauchy–Schwarz in `i`).
With `Q = 𝒜_{1/2}((N, 8N])`, `q_i` the dual pair sums and `Z = 2(C_δ(8N)^δ)⁵|W|²` from
Corollary 2.1, the only missing input of the range `N ∈ [T^{2/3}, T]` is the approximate
functional equation `Q ≤ X + Y Σ q_i` with `X ≪ |W|N` and `Y ≤ T^{o(1)}`.
-/

set_option autoImplicit false

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **Heath-Brown's Corollary 2.1, explicit form.**  For `S ⊆ (M, 2M]`, `1 ≤ M`, `M² ≤ N`,
`d ≤ D₁` on `(M², 4M²]` and `d ≤ D₂` on `(N, 8N]`:
`𝒜_{1/2}(S)² ≤ |W|² D₁⁴ · 2D₂ · 𝒜_{1/2}((N, 8N])`. -/
theorem hbAmp_sq_le_of_sq_le (W : Finset ℝ) {M N : ℕ} (hM : 0 < M) (hMN : M ^ 2 ≤ N)
    {S : Finset ℕ} (hS : S ⊆ Finset.Ioc M (2 * M)) {D₁ D₂ : ℝ}
    (hD₁ : ∀ u ∈ Finset.Ioc (M ^ 2) ((2 * M) ^ 2), (u.divisors.card : ℝ) ≤ D₁)
    (hD₂ : ∀ u ∈ Finset.Ioc N (8 * N), (u.divisors.card : ℝ) ≤ D₂) :
    hbAmp W (1 / 2) S ^ 2 ≤
      (W.card : ℝ) ^ 2 * D₁ ^ 4 * (2 * D₂) * hbAmp W (1 / 2) (Finset.Ioc N (8 * N)) := by
  have ha : ∀ n ∈ S, ‖((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ)‖ ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
    fun n _ => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  have h1 := hbPairSum_sq_le_fourthMoment W hS ha hD₁
  have hsq : (2 * M) ^ 2 = 4 * M ^ 2 := by ring
  have hsub : Finset.Ioc (M ^ 2) ((2 * M) ^ 2) ⊆ Finset.Ioc (M ^ 2) (4 * M ^ 2) := by
    rw [hsq]
  have hD₂' : ∀ u ∈ Finset.Ioc N (2 * 4 * N), (u.divisors.card : ℝ) ≤ D₂ := by
    simpa only [show 2 * 4 * N = 8 * N by ring] using hD₂
  have h2 := hbAmp_half_le_of_le W (pow_pos hM 2) hMN hsub hD₂'
  rw [show 2 * 4 * N = 8 * N by ring] at h2
  calc hbAmp W (1 / 2) S ^ 2
      ≤ (W.card : ℝ) ^ 2 * D₁ ^ 4 * hbAmp W (1 / 2) (Finset.Ioc (M ^ 2) ((2 * M) ^ 2)) := h1
    _ ≤ (W.card : ℝ) ^ 2 * D₁ ^ 4 * (2 * D₂ * hbAmp W (1 / 2) (Finset.Ioc N (8 * N))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

/-- **Heath-Brown's Corollary 2.1 with the divisor bound.**  For every `δ > 0`, with
`C_δ = divisorBoundConst δ`, `S ⊆ (M, 2M]`, `1 ≤ M` and `M² ≤ N`:
`𝒜_{1/2}(S)² ≤ 2 (C_δ (8N)^δ)⁵ |W|² 𝒜_{1/2}((N, 8N])`. -/
theorem hbAmp_sq_le_rpow (W : Finset ℝ) {δ : ℝ} (hδ : 0 < δ) {M N : ℕ} (hM : 0 < M)
    (hMN : M ^ 2 ≤ N) {S : Finset ℕ} (hS : S ⊆ Finset.Ioc M (2 * M)) :
    hbAmp W (1 / 2) S ^ 2 ≤ 2 * (divisorBoundConst δ * ((8 * N : ℕ) : ℝ) ^ δ) ^ 5 *
      (W.card : ℝ) ^ 2 * hbAmp W (1 / 2) (Finset.Ioc N (8 * N)) := by
  have hdiv : ∀ u : ℕ, 0 < u → u ≤ 8 * N →
      (u.divisors.card : ℝ) ≤ divisorBoundConst δ * ((8 * N : ℕ) : ℝ) ^ δ := by
    intro u hu0 hu
    refine (card_divisors_le_rpow hδ (Nat.pos_iff_ne_zero.mp hu0)).trans ?_
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hu) hδ.le)
      (divisorBoundConst_pos hδ).le
  have hD₁ : ∀ u ∈ Finset.Ioc (M ^ 2) ((2 * M) ^ 2),
      (u.divisors.card : ℝ) ≤ divisorBoundConst δ * ((8 * N : ℕ) : ℝ) ^ δ := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := Finset.mem_Ioc.mp hu
    exact hdiv u (by omega) (by nlinarith)
  have hD₂ : ∀ u ∈ Finset.Ioc N (8 * N),
      (u.divisors.card : ℝ) ≤ divisorBoundConst δ * ((8 * N : ℕ) : ℝ) ^ δ := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := Finset.mem_Ioc.mp hu
    exact hdiv u (by omega) hu2
  refine (hbAmp_sq_le_of_sq_le W hM hMN hS hD₁ hD₂).trans (le_of_eq ?_)
  ring

/-- **The closing inequality.**  If `Q ≤ X + Y Σ_{i∈I} q_i` and `q_i² ≤ Z Q` for nonnegative
`Q, q_i, Y, Z`, then `Q ≤ 2X + Y² |I|² Z`. -/
theorem le_two_mul_add_of_le_add_mul_sum {ι : Type*} (I : Finset ι) {Q X Y Z : ℝ}
    {q : ι → ℝ} (hQ : 0 ≤ Q) (hq : ∀ i ∈ I, 0 ≤ q i) (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (hmain : Q ≤ X + Y * ∑ i ∈ I, q i) (hsq : ∀ i ∈ I, q i ^ 2 ≤ Z * Q) :
    Q ≤ 2 * X + Y ^ 2 * ((I.card : ℝ) ^ 2 * Z) := by
  have hy : 0 ≤ ∑ i ∈ I, q i := Finset.sum_nonneg hq
  have hy2 : (∑ i ∈ I, q i) ^ 2 ≤ ((I.card : ℝ) ^ 2 * Z) * Q := by
    calc (∑ i ∈ I, q i) ^ 2 ≤ (I.card : ℝ) * ∑ i ∈ I, q i ^ 2 := sq_sum_le_card_mul_sum_sq
      _ ≤ (I.card : ℝ) * ∑ _i ∈ I, Z * Q :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hsq) (Nat.cast_nonneg _)
      _ = ((I.card : ℝ) ^ 2 * Z) * Q := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  exact le_two_mul_add_sq_mul_of_le_add_of_sq_le_mul hQ hy hY (by positivity) hmain hy2

end

end RHTower.Sieve
