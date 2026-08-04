import GaloisForLFunctions.RHTower.Sieve.GallagherRange

/-!
# Gallagher's identity split against a mean square

`gallagher_split` consumes a *pointwise* bound on the Dirichlet polynomial over `|w| ≤ W`.  A
large-values estimate supplies no such bound — it controls only the integral of `|F|²`.  Since the
Gallagher weight is capped by `2δ²` everywhere (`norm_fourier_triC_le`), the good range can instead
be paid for by that integral:

    ∫_ℝ |∑_{u < log n ≤ u+δ} a_n|² du ≤ 2δ²·∫_{|w| ≤ W} |F(w)|² dw + M₂·2/(π²W) .

The two splits are complementary: the pointwise one is sharp when a zero-free region reaches `W`, the
integral one when it does not.
-/

namespace RHTower.Sieve

open Complex MeasureTheory FourierTransform

/-- The Gallagher weight is capped by `2δ²`. -/
theorem fourier_triC_re_le_two_sq {δ : ℝ} (hδ : 0 < δ) (w : ℝ) :
    (𝓕 (triC δ) w).re ≤ 2 * δ ^ 2 := by
  have h1 : (𝓕 (triC δ) w).re ≤ ‖𝓕 (triC δ) w‖ := Complex.re_le_norm _
  have h2 := norm_fourier_triC_le hδ w
  have hden : (0 : ℝ) < 1 + (δ * Real.pi * w) ^ 2 := by positivity
  have h3 : 2 * δ ^ 2 / (1 + (δ * Real.pi * w) ^ 2) ≤ 2 * δ ^ 2 := by
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg (δ * Real.pi * w), sq_nonneg δ]
  linarith

/-- **Gallagher's identity, split against a mean square on the good range.** -/
theorem gallagher_split_integral (a : ℕ → ℂ) (s : Finset ℕ) {δ M₂ W I : ℝ} (hδ : 0 < δ)
    (hW : 0 < W) (hM₂ : 0 ≤ M₂)
    (hI : (∫ w in Set.Icc (-W) W, ‖logPoly a s w‖ ^ 2) ≤ I)
    (h₂ : ∀ w : ℝ, ‖logPoly a s w‖ ^ 2 ≤ M₂) :
    (∫ u : ℝ, ‖logWindowSum a s δ u‖ ^ 2)
      ≤ 2 * δ ^ 2 * I + M₂ * (2 / (Real.pi ^ 2 * W)) := by
  have hK : Integrable fun w : ℝ => (𝓕 (triC δ) w).re := (integrable_fourier_triC hδ).re
  have hF : Integrable fun w : ℝ => (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2 :=
    integrable_gallagher_weight_mul hδ a s
  have hcont : Continuous fun w : ℝ => ‖logPoly a s w‖ ^ 2 :=
    ((continuous_logPoly a s).norm).pow 2
  rw [gallagher_identity a s hδ]
  rw [← integral_add_compl (measurableSet_Icc (a := -W) (b := W)) hF]
  have hin : (∫ w in Set.Icc (-W) W, (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2)
      ≤ 2 * δ ^ 2 * I := by
    have hstep : (∫ w in Set.Icc (-W) W, (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2)
        ≤ ∫ w in Set.Icc (-W) W, 2 * δ ^ 2 * ‖logPoly a s w‖ ^ 2 := by
      refine setIntegral_mono_on hF.integrableOn
        ((hcont.const_mul (2 * δ ^ 2)).integrableOn_Icc) measurableSet_Icc fun w _ => ?_
      exact mul_le_mul_of_nonneg_right (fourier_triC_re_le_two_sq hδ w) (by positivity)
    refine le_trans hstep ?_
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hI (by positivity)
  have hout : (∫ w in (Set.Icc (-W) W)ᶜ, (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2)
      ≤ M₂ * (2 / (Real.pi ^ 2 * W)) := by
    have hstep : (∫ w in (Set.Icc (-W) W)ᶜ, (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2)
        ≤ ∫ w in (Set.Icc (-W) W)ᶜ, (𝓕 (triC δ) w).re * M₂ := by
      refine setIntegral_mono_on hF.integrableOn (hK.mul_const M₂).integrableOn
        (measurableSet_Icc.compl) fun w _ => ?_
      exact mul_le_mul_of_nonneg_left (h₂ w) (fourier_triC_re_nonneg hδ w)
    refine le_trans hstep ?_
    rw [integral_mul_const]
    have hmass := integral_compl_Icc_fourier_triC_re_le hδ hW
    calc (∫ w in (Set.Icc (-W) W)ᶜ, (𝓕 (triC δ) w).re) * M₂
        ≤ (2 / (Real.pi ^ 2 * W)) * M₂ := mul_le_mul_of_nonneg_right hmass hM₂
      _ = M₂ * (2 / (Real.pi ^ 2 * W)) := by ring
  linarith

/-- **The mean-square split on a range of positions.** -/
theorem setIntegral_normSq_logWindowSum_le_integral (a : ℕ → ℂ) (s : Finset ℕ) {δ M₂ W I : ℝ}
    (hδ : 0 < δ) (hW : 0 < W) (hM₂ : 0 ≤ M₂)
    (hI : (∫ w in Set.Icc (-W) W, ‖logPoly a s w‖ ^ 2) ≤ I)
    (h₂ : ∀ w : ℝ, ‖logPoly a s w‖ ^ 2 ≤ M₂) (E : Set ℝ) :
    (∫ u in E, ‖logWindowSum a s δ u‖ ^ 2)
      ≤ 2 * δ ^ 2 * I + M₂ * (2 / (Real.pi ^ 2 * W)) := by
  have hint := integrable_normSq_logWindowSum a s δ
  have hnn : 0 ≤ᵐ[volume] fun u : ℝ => ‖logWindowSum a s δ u‖ ^ 2 :=
    Filter.Eventually.of_forall fun u => by positivity
  refine le_trans (setIntegral_le_integral hint hnn) ?_
  exact gallagher_split_integral a s hδ hW hM₂ hI h₂

/-- **The multiplicative short-interval mean square, bounded by a frequency mean square.** -/
theorem setIntegral_normSq_multiplicative_window_le_integral (a : ℕ → ℂ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 0 < n) {δ M₂ W I : ℝ} (hδ : 0 < δ) (hW : 0 < W) (hM₂ : 0 ≤ M₂)
    (hI : (∫ w in Set.Icc (-W) W, ‖logPoly a s w‖ ^ 2) ≤ I)
    (h₂ : ∀ w : ℝ, ‖logPoly a s w‖ ^ 2 ≤ M₂) (A B : ℝ) :
    (∫ u in Set.Ioc (Real.log A) (Real.log B),
        ‖∑ n ∈ s.filter (fun n : ℕ =>
          Real.exp u < (n : ℝ) ∧ (n : ℝ) ≤ Real.exp u * Real.exp δ), a n‖ ^ 2)
      ≤ 2 * δ ^ 2 * I + M₂ * (2 / (Real.pi ^ 2 * W)) := by
  classical
  have hcongr : ∀ u : ℝ,
      ‖∑ n ∈ s.filter (fun n : ℕ =>
          Real.exp u < (n : ℝ) ∧ (n : ℝ) ≤ Real.exp u * Real.exp δ), a n‖ ^ 2
        = ‖logWindowSum a s δ u‖ ^ 2 := by
    intro u
    rw [← logWindowSum_log a s hs δ (Real.exp_pos u), Real.log_exp]
  rw [setIntegral_congr_fun measurableSet_Ioc (fun u _ => hcongr u)]
  exact setIntegral_normSq_logWindowSum_le_integral a s hδ hW hM₂ hI h₂ _

end RHTower.Sieve
