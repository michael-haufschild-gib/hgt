import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualQuarterGlobalDerivative

noncomputable section

open Complex Set MeasureTheory Filter

namespace RHTower

/-- Frequency integrand for height derivative on negative-quarter contour. -/
def smoothAFEZetaSquareDualWeightNegQuarterHeightDerivativeIntegrand
    (tau Y v : ℝ) : ℂ :=
  smoothAFEZetaChiShiftRatioSqQuarterHeightDerivative tau v *
    smoothAFEMellinIntegrand Y
      (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)

private theorem continuous_smoothAFEMellinIntegrand_at_neg_quarter
    {Y : ℝ} (hY : 0 < Y) :
    Continuous (fun v : ℝ =>
      smoothAFEMellinIntegrand Y
        (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)) := by
  haveI : NeZero (Y : ℂ) :=
    ⟨Complex.ofReal_ne_zero.mpr hY.ne'⟩
  unfold smoothAFEMellinIntegrand smoothAFEGaussianKernel
  apply Continuous.mul
  · exact (continuous_const_cpow (Y : ℂ)).comp (by fun_prop)
  · exact (Complex.continuous_exp.comp (by fun_prop)).div
      (by fun_prop) (fun v hzero => by
        have hre := congrArg Complex.re hzero
        norm_num at hre)

theorem norm_smoothAFEMellinIntegrand_neg_quarter_le
    {Y : ℝ} (hY : 0 < Y) (v : ℝ) :
    ‖smoothAFEMellinIntegrand Y
        (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
      (Y ^ (1 / 4 : ℝ) *
        (Real.exp ((1 / 4 : ℝ) ^ 2) / (1 / 4 : ℝ))) *
          Real.exp (-(v ^ 2)) := by
  have h := norm_smoothAFEMellinIntegrand_vertical_le_of_ne hY
    (show (-1 / 4 : ℝ) ≠ 0 by norm_num) v
  convert h using 1 <;> norm_num

theorem smoothAFEZetaSquareDualWeightNegQuarterHeightDerivativeIntegrand_integrable
    {Y : ℝ} (hY : 0 < Y) (tau : ℝ) :
    Integrable
      (smoothAFEZetaSquareDualWeightNegQuarterHeightDerivativeIntegrand tau Y) := by
  obtain ⟨E, hE, hglobal⟩ :=
    exists_norm_smoothAFEZetaChiShiftRatioSqQuarterHeightDerivative_le_global
  let Q : ℝ := Y ^ (1 / 4 : ℝ) *
    (Real.exp ((1 / 4 : ℝ) ^ 2) / (1 / 4 : ℝ))
  let A : ℝ := E * (1 + |tau|) * Q
  apply Integrable.mono'
    (integrable_one_add_abs_pow_four_mul_exp_neg_sq.const_mul A)
  · exact ((continuous_smoothAFEZetaChiShiftRatioSqQuarterHeightDerivative tau).mul
      (continuous_smoothAFEMellinIntegrand_at_neg_quarter hY)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun v => by
      have hd := hglobal tau v
      have hm := norm_smoothAFEMellinIntegrand_neg_quarter_le hY v
      have hq1 : 1 ≤ 1 + |v| := by linarith [abs_nonneg v]
      have hq34 : (1 + |v|) ^ 3 ≤ (1 + |v|) ^ 4 :=
        pow_le_pow_right₀ hq1 (by omega)
      unfold smoothAFEZetaSquareDualWeightNegQuarterHeightDerivativeIntegrand
      rw [norm_mul]
      calc
        ‖smoothAFEZetaChiShiftRatioSqQuarterHeightDerivative tau v‖ *
            ‖smoothAFEMellinIntegrand Y
              (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)‖
          ≤ (E * (1 + |tau|) * (1 + |v|) ^ 3) *
              (Q * Real.exp (-(v ^ 2))) := by gcongr
        _ = A * ((1 + |v|) ^ 3 * Real.exp (-(v ^ 2))) := by
          dsimp only [A]
          ring
        _ ≤ A * ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by gcongr

/-- Exact differentiation under negative-quarter contour. -/
theorem hasDerivAt_smoothAFEZetaSquareDualWeightAt_neg_quarter
    {Y : ℝ} (hY : 0 < Y) (tau : ℝ) :
    HasDerivAt
      (fun u : ℝ => smoothAFEZetaSquareDualWeightAt (-1 / 4) u Y)
      ((1 / (2 * Real.pi) : ℝ) •
        ∫ v : ℝ,
          smoothAFEZetaSquareDualWeightNegQuarterHeightDerivativeIntegrand
            tau Y v) tau := by
  obtain ⟨E, hE, hglobal⟩ :=
    exists_norm_smoothAFEZetaChiShiftRatioSqQuarterHeightDerivative_le_global
  let F : ℝ → ℝ → ℂ := fun u v =>
    (smoothAFEZetaChiShiftRatio (linePt u)
      (-(((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I))) ^ 2 *
    smoothAFEMellinIntegrand Y
      (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)
  let F' : ℝ → ℝ → ℂ := fun u v =>
    smoothAFEZetaSquareDualWeightNegQuarterHeightDerivativeIntegrand u Y v
  let Q : ℝ := Y ^ (1 / 4 : ℝ) *
    (Real.exp ((1 / 4 : ℝ) ^ 2) / (1 / 4 : ℝ))
  let B : ℝ := E * (2 + |tau|) * Q
  let bound : ℝ → ℝ := fun v =>
    B * ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2)))
  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (s := Metric.ball tau 1) (bound := bound)
    (Metric.ball_mem_nhds tau (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall fun u =>
      (smoothAFEZetaSquareDualWeightAt_neg_quarter_integrable hY u).aestronglyMeasurable)
    (smoothAFEZetaSquareDualWeightAt_neg_quarter_integrable hY tau)
    (smoothAFEZetaSquareDualWeightNegQuarterHeightDerivativeIntegrand_integrable
      hY tau).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v u hu => by
      have hd := hglobal u v
      have hm := norm_smoothAFEMellinIntegrand_neg_quarter_le hY v
      have hudist : |u - tau| < 1 := by
        simpa [Real.dist_eq] using hu
      have huabs : |u| < |tau| + 1 := by
        calc
          |u| = |(u - tau) + tau| := by ring_nf
          _ ≤ |u - tau| + |tau| := abs_add_le _ _
          _ < 1 + |tau| := by linarith
          _ = |tau| + 1 := by ring
      have hheight : 1 + |u| ≤ 2 + |tau| := by linarith
      have hq1 : 1 ≤ 1 + |v| := by linarith [abs_nonneg v]
      have hq34 : (1 + |v|) ^ 3 ≤ (1 + |v|) ^ 4 :=
        pow_le_pow_right₀ hq1 (by omega)
      dsimp only [F',
        smoothAFEZetaSquareDualWeightNegQuarterHeightDerivativeIntegrand]
      rw [norm_mul]
      calc
        ‖smoothAFEZetaChiShiftRatioSqQuarterHeightDerivative u v‖ *
            ‖smoothAFEMellinIntegrand Y
              (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)‖
          ≤ (E * (1 + |u|) * (1 + |v|) ^ 3) *
              (Q * Real.exp (-(v ^ 2))) := by gcongr
        _ ≤ (E * (2 + |tau|) * (1 + |v|) ^ 3) *
              (Q * Real.exp (-(v ^ 2))) := by gcongr
        _ = B * ((1 + |v|) ^ 3 * Real.exp (-(v ^ 2))) := by
          dsimp only [B]
          ring
        _ ≤ B * ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by gcongr
        _ = bound v := by rfl)
    (integrable_one_add_abs_pow_four_mul_exp_neg_sq.const_mul B)
    (Filter.Eventually.of_forall fun v u hu => by
      dsimp only [F, F']
      exact (hasDerivAt_smoothAFEZetaChiShiftRatioSq_quarter u v).mul_const
        (smoothAFEMellinIntegrand Y
          (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)))
  have hraw := hparam.2
  unfold smoothAFEZetaSquareDualWeightAt
  apply hraw.const_smul (1 / (2 * Real.pi) : ℝ)

/-- Constant residue implies original square-dual carrier has exactly the
negative-quarter derivative. -/
theorem hasDerivAt_smoothAFEZetaSquareDualWeight_via_neg_quarter
    {Y : ℝ} (hY : 0 < Y) (tau : ℝ) :
    HasDerivAt (fun u : ℝ => smoothAFEZetaSquareDualWeight u Y)
      ((1 / (2 * Real.pi) : ℝ) •
        ∫ v : ℝ,
          smoothAFEZetaSquareDualWeightNegQuarterHeightDerivativeIntegrand
            tau Y v) tau := by
  have hneg := hasDerivAt_smoothAFEZetaSquareDualWeightAt_neg_quarter hY tau
  have heq : (fun u : ℝ => smoothAFEZetaSquareDualWeight u Y) =
      (fun u : ℝ => 1 + smoothAFEZetaSquareDualWeightAt (-1 / 4) u Y) := by
    funext u
    exact smoothAFEZetaSquareDualWeight_eq_one_add_at_neg_quarter hY u
  rw [heq]
  exact hneg.const_add 1

end RHTower
