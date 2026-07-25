/-
# Conductor-uniform small-scale localization of the dual AFE weight

The exact negative contour represents `W_τ(Y)-1`.  Combining it with the
quantitative right-line power decay of `χ` restores the conductor factor
missing from the fixed-height estimate:

`|W_τ(Y)-1| ≪δ Y^δ / max(1,|τ|)^δ`.
-/
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiPowerBound

namespace RHTower

open Complex MeasureTheory

noncomputable section

/-- Conductor-uniform small-scale estimate for the exact dual weight. -/
theorem exists_norm_smoothAFEZetaDualWeight_sub_one_le_conductor
    {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) {Y : ℝ}, 0 < Y →
      ‖smoothAFEZetaDualWeight τ Y - 1‖ ≤
        C * Y ^ δ / (max 1 |τ|) ^ δ := by
  obtain ⟨K, hK, hratio⟩ :=
    exists_norm_smoothAFEZetaChiShiftRatio_pos_le hδ hδhalf
  let G : ℝ :=
    ∫ v : ℝ, (1 + |v|) * Real.exp (-(v ^ 2))
  let C : ℝ :=
    (1 / (2 * Real.pi)) * K *
      (Real.exp (δ ^ 2) / δ) * G
  have hG : 0 ≤ G :=
    integral_nonneg fun v => by positivity
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, fun τ {Y} hY => ?_⟩
  have hweight :=
    smoothAFEZetaDualWeight_eq_one_add_at_neg hδ hδhalf hY τ
  have hdiff :
      smoothAFEZetaDualWeight τ Y - 1 =
        smoothAFEZetaDualWeightAt (-δ) τ Y := by
    rw [hweight]
    ring
  rw [hdiff]
  let f : ℝ → ℂ := fun v =>
    smoothAFEZetaChiShiftRatio (linePt τ)
        (-(((-δ : ℝ) : ℂ) + (v : ℂ) * I)) *
      smoothAFEMellinIntegrand Y
        (((-δ : ℝ) : ℂ) + (v : ℂ) * I)
  let D : ℝ :=
    K * (Y ^ δ / (max 1 |τ|) ^ δ) *
      (Real.exp (δ ^ 2) / δ)
  have hf : Integrable f :=
    smoothAFEZetaDualWeightAt_neg_integrable hδ hδhalf hY τ
  have hmajor :
      Integrable (fun v : ℝ =>
        D * ((1 + |v|) * Real.exp (-(v ^ 2)))) :=
    integrable_one_add_abs_mul_exp_neg_sq.const_mul D
  have hpoint : ∀ v : ℝ,
      ‖f v‖ ≤
        D * ((1 + |v|) * Real.exp (-(v ^ 2))) := by
    intro v
    have hr := hratio τ v
    have hk := norm_smoothAFEGaussianKernel_vertical_le_of_ne
      (σ := -δ) (by linarith) v
    have hpow :
        ‖(Y : ℂ) ^ (-(((-δ : ℝ) : ℂ) + (v : ℂ) * I))‖ =
          Y ^ δ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
      simp
    have hvbase : 1 ≤ 1 + |v| := by
      linarith [abs_nonneg v]
    have hvpow :
        (1 + |v|) ^ δ ≤ 1 + |v| := by
      simpa using
        Real.rpow_le_rpow_of_exponent_le hvbase (by linarith : δ ≤ 1)
    have hqpos : 0 < (max 1 |τ|) ^ δ :=
      Real.rpow_pos_of_pos
        (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) δ
    dsimp only [f, D]
    unfold smoothAFEMellinIntegrand
    rw [norm_mul, norm_mul, hpow]
    calc
      ‖smoothAFEZetaChiShiftRatio (linePt τ)
          (-(((-δ : ℝ) : ℂ) + (v : ℂ) * I))‖ *
          (Y ^ δ *
            ‖smoothAFEGaussianKernel
              (((-δ : ℝ) : ℂ) + (v : ℂ) * I)‖)
        ≤ (K * (1 + |v|) ^ δ / (max 1 |τ|) ^ δ) *
            (Y ^ δ *
              ((Real.exp ((-δ) ^ 2) / |-δ|) *
                Real.exp (-(v ^ 2)))) := by
          gcongr
      _ ≤ (K * (1 + |v|) / (max 1 |τ|) ^ δ) *
            (Y ^ δ *
              ((Real.exp ((-δ) ^ 2) / |-δ|) *
                Real.exp (-(v ^ 2)))) := by
          gcongr
      _ = K * (Y ^ δ / (max 1 |τ|) ^ δ) *
            (Real.exp (δ ^ 2) / δ) *
            ((1 + |v|) * Real.exp (-(v ^ 2))) := by
          rw [neg_sq, abs_neg, abs_of_pos hδ]
          field_simp [hqpos.ne']
  unfold smoothAFEZetaDualWeightAt
  rw [Complex.real_smul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ 1 / (2 * Real.pi))]
  calc
    (1 / (2 * Real.pi)) * ‖∫ v : ℝ, f v‖
      ≤ (1 / (2 * Real.pi)) * ∫ v : ℝ, ‖f v‖ := by
        exact mul_le_mul_of_nonneg_left
          (norm_integral_le_integral_norm f) (by positivity)
    _ ≤ (1 / (2 * Real.pi)) *
          ∫ v : ℝ,
            D * ((1 + |v|) * Real.exp (-(v ^ 2))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply integral_mono_ae hf.norm hmajor
        exact Filter.Eventually.of_forall hpoint
    _ = C * Y ^ δ / (max 1 |τ|) ^ δ := by
      rw [integral_const_mul]
      dsimp only [C, D, G]
      ring

end

end RHTower
