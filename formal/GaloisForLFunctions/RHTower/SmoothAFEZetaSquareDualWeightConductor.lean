import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualSourcePrimitive

namespace RHTower

open Complex MeasureTheory

noncomputable section

/-- Square-dual conductor-uniform small-scale estimate on the negative-quarter contour. -/
theorem exists_norm_smoothAFEZetaSquareDualWeight_sub_one_le_conductor :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) {Y : ℝ}, 0 < Y →
      ‖smoothAFEZetaSquareDualWeight τ Y - 1‖ ≤
        C * Y ^ (1 / 4 : ℝ) /
          ((max 1 |τ|) ^ (1 / 4 : ℝ)) ^ 2 := by
  obtain ⟨K, hK, hratio⟩ :=
    exists_norm_smoothAFEZetaChiShiftRatio_pos_le
      (show (0 : ℝ) < 1 / 4 by norm_num)
      (show (1 / 4 : ℝ) < 1 / 2 by norm_num)
  let G : ℝ :=
    ∫ v : ℝ, (1 + |v|) ^ 2 * Real.exp (-(v ^ 2))
  let Q : ℝ := Real.exp ((1 / 4 : ℝ) ^ 2) / (1 / 4 : ℝ)
  let C : ℝ := (1 / (2 * Real.pi)) * K ^ 2 * Q * G
  have hG : 0 ≤ G := integral_nonneg fun v => by positivity
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro τ Y hY
  have hweight := smoothAFEZetaSquareDualWeight_eq_one_add_at_neg_quarter hY τ
  have hdiff :
      smoothAFEZetaSquareDualWeight τ Y - 1 =
        smoothAFEZetaSquareDualWeightAt (-1 / 4) τ Y := by
    rw [hweight]
    ring
  rw [hdiff]
  let f : ℝ → ℂ := fun v =>
    (smoothAFEZetaChiShiftRatio (linePt τ)
      (-(((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I))) ^ 2 *
      smoothAFEMellinIntegrand Y
        (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)
  let D : ℝ := K ^ 2 *
    (Y ^ (1 / 4 : ℝ) /
      ((max 1 |τ|) ^ (1 / 4 : ℝ)) ^ 2) * Q
  have hf : Integrable f :=
    smoothAFEZetaSquareDualWeightAt_neg_quarter_integrable hY τ
  have hmajor : Integrable (fun v : ℝ =>
      D * ((1 + |v|) ^ 2 * Real.exp (-(v ^ 2)))) :=
    integrable_one_add_abs_sq_mul_exp_neg_sq.const_mul D
  have hpoint : ∀ v : ℝ,
      ‖f v‖ ≤ D * ((1 + |v|) ^ 2 * Real.exp (-(v ^ 2))) := by
    intro v
    have hr0 := hratio τ v
    have hr :
        ‖smoothAFEZetaChiShiftRatio (linePt τ)
          (-(((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤
          K * (1 + |v|) ^ (1 / 4 : ℝ) /
            (max 1 |τ|) ^ (1 / 4 : ℝ) := by
      simpa [neg_div] using hr0
    have hk := norm_smoothAFEGaussianKernel_vertical_le_of_ne
      (σ := (-1 / 4 : ℝ)) (by norm_num) v
    have hpow :
        ‖(Y : ℂ) ^ (-((((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)))‖ =
          Y ^ (1 / 4 : ℝ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
      norm_num
    have hvbase : 1 ≤ 1 + |v| := by linarith [abs_nonneg v]
    have hvpow : (1 + |v|) ^ (1 / 4 : ℝ) ≤ 1 + |v| := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hvbase
          (by norm_num : (1 / 4 : ℝ) ≤ 1)
    have hden : 0 < (max 1 |τ|) ^ (1 / 4 : ℝ) :=
      Real.rpow_pos_of_pos
        (lt_of_lt_of_le zero_lt_one (le_max_left 1 |τ|)) _
    dsimp only [f, D]
    unfold smoothAFEMellinIntegrand
    rw [norm_mul, norm_pow, norm_mul, hpow]
    calc
      ‖smoothAFEZetaChiShiftRatio (linePt τ)
          (-(((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I))‖ ^ 2 *
          (Y ^ (1 / 4 : ℝ) *
            ‖smoothAFEGaussianKernel
              (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)‖)
        ≤ (K * (1 + |v|) ^ (1 / 4 : ℝ) /
              (max 1 |τ|) ^ (1 / 4 : ℝ)) ^ 2 *
            (Y ^ (1 / 4 : ℝ) *
              ((Real.exp ((-1 / 4 : ℝ) ^ 2) / |(-1 / 4 : ℝ)|) *
                Real.exp (-(v ^ 2)))) := by gcongr
      _ ≤ (K * (1 + |v|) /
              (max 1 |τ|) ^ (1 / 4 : ℝ)) ^ 2 *
            (Y ^ (1 / 4 : ℝ) *
              ((Real.exp ((-1 / 4 : ℝ) ^ 2) / |(-1 / 4 : ℝ)|) *
                Real.exp (-(v ^ 2)))) := by gcongr
      _ = K ^ 2 *
          (Y ^ (1 / 4 : ℝ) /
            ((max 1 |τ|) ^ (1 / 4 : ℝ)) ^ 2) *
          (Real.exp ((1 / 4 : ℝ) ^ 2) / (1 / 4 : ℝ)) *
          ((1 + |v|) ^ 2 * Real.exp (-(v ^ 2))) := by
            norm_num [abs_of_nonneg]
            field_simp [hden.ne']
  unfold smoothAFEZetaSquareDualWeightAt
  rw [Complex.real_smul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ 1 / (2 * Real.pi))]
  calc
    (1 / (2 * Real.pi)) * ‖∫ v : ℝ, f v‖
      ≤ (1 / (2 * Real.pi)) * ∫ v : ℝ, ‖f v‖ := by
        exact mul_le_mul_of_nonneg_left
          (norm_integral_le_integral_norm f) (by positivity)
    _ ≤ (1 / (2 * Real.pi)) * ∫ v : ℝ,
          D * ((1 + |v|) ^ 2 * Real.exp (-(v ^ 2))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply integral_mono_ae hf.norm hmajor
        exact Filter.Eventually.of_forall hpoint
    _ = C * Y ^ (1 / 4 : ℝ) /
          ((max 1 |τ|) ^ (1 / 4 : ℝ)) ^ 2 := by
      rw [integral_const_mul]
      dsimp only [C, D, G, Q]
      ring

end

end RHTower
