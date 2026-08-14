import GaloisForLFunctions.RHTower.SmoothAFEZetaChiShiftSquareDerivativeBound
import GaloisForLFunctions.RHTower.SmoothAFEZetaDualWeightDerivativeBound

/-!
# Height derivative of the exact square-dual Gaussian weight

This module constructs the square-AFE dual carrier, proves its Gaussian integrability, and
differentiates it exactly in height.  A coarse global envelope is used only for dominated
differentiation; the sharp one-conductor-power estimate is retained for the quantitative bound.
-/

noncomputable section

open Complex Set MeasureTheory Filter

namespace RHTower

/-- Exact height derivative of the squared neutral chi carrier. -/
def smoothAFEZetaChiShiftRatioSqHeightDerivative (tau v : ℝ) : ℂ :=
  2 * smoothAFEZetaChiShiftRatio (linePt tau)
      (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
    smoothAFEZetaChiShiftHeightDerivative tau v

theorem hasDerivAt_smoothAFEZetaChiShiftRatioSq (tau v : ℝ) :
    HasDerivAt (fun u : ℝ => smoothAFEZetaChiShiftRatioSq u v)
      (smoothAFEZetaChiShiftRatioSqHeightDerivative tau v) tau := by
  have h := hasDerivAt_chiShift_eq_heightDerivative tau v
  have hp := h.pow 2
  change HasDerivAt
      (fun u : ℝ =>
        (smoothAFEZetaChiShiftRatio (linePt u)
          (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))) ^ 2) _ tau at hp
  change HasDerivAt
      (fun u : ℝ =>
        (smoothAFEZetaChiShiftRatio (linePt u)
          (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))) ^ 2)
      (smoothAFEZetaChiShiftRatioSqHeightDerivative tau v) tau
  simpa [smoothAFEZetaChiShiftRatioSqHeightDerivative] using hp

theorem continuous_smoothAFEZetaChiShiftRatio_neg_right_one (tau : ℝ) :
    Continuous (fun v : ℝ =>
      smoothAFEZetaChiShiftRatio (linePt tau)
        (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))) := by
  rw [continuous_iff_continuousAt]
  intro v
  unfold smoothAFEZetaChiShiftRatio
  apply ContinuousAt.div_const
  apply (zetaChi_analyticAt ?_).continuousAt.comp
  · fun_prop
  · apply Gammaℝ_ne_zero_of_re_pos
    simp [linePt]
    norm_num

theorem continuous_smoothAFEZetaChiShiftRatioSqHeightDerivative (tau : ℝ) :
    Continuous (smoothAFEZetaChiShiftRatioSqHeightDerivative tau) := by
  unfold smoothAFEZetaChiShiftRatioSqHeightDerivative
  exact ((continuous_const.mul
    (continuous_smoothAFEZetaChiShiftRatio_neg_right_one tau)).mul
      (continuous_smoothAFEZetaChiShiftHeightDerivative tau))

/-- Coarse all-height envelope used only to justify differentiation under the
square-dual integral. -/
theorem exists_norm_smoothAFEZetaChiShiftRatioSqHeightDerivative_le_global :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ tau v : ℝ,
      ‖smoothAFEZetaChiShiftRatioSqHeightDerivative tau v‖ ≤
        E * (1 + |tau|) ^ 3 * (1 + |v|) ^ 3 := by
  obtain ⟨D, hD, hglobal⟩ :=
    exists_norm_deriv_smoothAFEZetaChiShiftRatio_le_global
  refine ⟨2 * D, by positivity, ?_⟩
  intro tau v
  have hratio := norm_smoothAFEZetaChiShiftRatio_neg_right_one_le tau v
  have hder := hglobal tau v
  rw [(hasDerivAt_chiShift_eq_heightDerivative tau v).deriv] at hder
  unfold smoothAFEZetaChiShiftRatioSqHeightDerivative
  rw [norm_mul, norm_mul]
  rw [show ‖(2 : ℂ)‖ = 2 by norm_num]
  calc
    2 * ‖smoothAFEZetaChiShiftRatio (linePt tau)
            (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))‖ *
          ‖smoothAFEZetaChiShiftHeightDerivative tau v‖
      ≤ 2 * ((1 + |tau|) * (1 + |v|)) *
          (D * (1 + |tau|) ^ 2 * (1 + |v|) ^ 2) := by gcongr
    _ = (2 * D) * (1 + |tau|) ^ 3 * (1 + |v|) ^ 3 := by ring

/-- Exact positive-line dual weight for the square approximate functional
equation.  Its conductor is quadratic in height. -/
def smoothAFEZetaSquareDualWeight (tau Y : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) • ∫ v : ℝ,
    smoothAFEZetaChiShiftRatioSq tau v *
      smoothAFEMellinIntegrand Y
        (((1 : ℝ) : ℂ) + (v : ℂ) * I)

/-- Frequency integrand for the height derivative of the square-dual weight. -/
def smoothAFEZetaSquareDualWeightHeightDerivativeIntegrand
    (tau Y v : ℝ) : ℂ :=
  smoothAFEZetaChiShiftRatioSqHeightDerivative tau v *
    smoothAFEMellinIntegrand Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)

private theorem continuous_smoothAFEMellinIntegrand_at_one
    {Y : ℝ} (hY : 0 < Y) :
    Continuous (fun v : ℝ =>
      smoothAFEMellinIntegrand Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)) := by
  haveI : NeZero (Y : ℂ) :=
    ⟨Complex.ofReal_ne_zero.mpr hY.ne'⟩
  unfold smoothAFEMellinIntegrand smoothAFEGaussianKernel
  apply Continuous.mul
  · exact (continuous_const_cpow (Y : ℂ)).comp (by fun_prop)
  · exact (Complex.continuous_exp.comp (by fun_prop)).div
      (by fun_prop) (fun v hzero => by
        have hre := congrArg Complex.re hzero
        norm_num at hre)

theorem smoothAFEZetaSquareDualWeightAt_one_integrable
    {Y : ℝ} (hY : 0 < Y) (tau : ℝ) :
    Integrable (fun v : ℝ =>
      smoothAFEZetaChiShiftRatioSq tau v *
        smoothAFEMellinIntegrand Y
          (((1 : ℝ) : ℂ) + (v : ℂ) * I)) := by
  let A : ℝ := (1 + |tau|) ^ 2 * (Y⁻¹ * Real.exp 1)
  apply Integrable.mono'
    (integrable_one_add_abs_sq_mul_exp_neg_sq.const_mul A)
  · have hc :=
      (continuous_smoothAFEZetaChiShiftRatio_neg_right_one tau).pow 2
    change Continuous (fun v : ℝ =>
      (smoothAFEZetaChiShiftRatio (linePt tau)
        (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))) ^ 2) at hc
    have hm := continuous_smoothAFEMellinIntegrand_at_one hY
    have hprod := hc.mul hm
    change Continuous (fun v : ℝ =>
      (smoothAFEZetaChiShiftRatio (linePt tau)
          (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))) ^ 2 *
        smoothAFEMellinIntegrand Y
          (((1 : ℝ) : ℂ) + (v : ℂ) * I)) at hprod
    simpa [smoothAFEZetaChiShiftRatioSq] using hprod.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun v => by
      have hratio := norm_smoothAFEZetaChiShiftRatio_neg_right_one_le tau v
      have hm := norm_smoothAFEMellinIntegrand_vertical_le hY
        (show (0 : ℝ) < 1 by norm_num) v
      have hm' :
          ‖smoothAFEMellinIntegrand Y (↑(1 : ℝ) + ↑v * I)‖ ≤
            (Y⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2)) := by
        simpa [Real.rpow_neg_one] using hm
      unfold smoothAFEZetaChiShiftRatioSq
      rw [norm_mul, norm_pow]
      calc
        ‖smoothAFEZetaChiShiftRatio (linePt tau)
            (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))‖ ^ 2 *
              ‖smoothAFEMellinIntegrand Y
                (↑(1 : ℝ) + ↑v * I)‖
          ≤ ((1 + |tau|) * (1 + |v|)) ^ 2 *
              ((Y⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2))) := by gcongr
        _ = A * ((1 + |v|) ^ 2 * Real.exp (-(v ^ 2))) := by
          dsimp only [A]
          ring

theorem smoothAFEZetaSquareDualWeightHeightDerivativeIntegrand_integrable
    {Y : ℝ} (hY : 0 < Y) (tau : ℝ) :
    Integrable (smoothAFEZetaSquareDualWeightHeightDerivativeIntegrand tau Y) := by
  obtain ⟨E, hE, hglobal⟩ :=
    exists_norm_smoothAFEZetaChiShiftRatioSqHeightDerivative_le_global
  let A : ℝ := E * (1 + |tau|) ^ 3 * (Y⁻¹ * Real.exp 1)
  apply Integrable.mono'
    (integrable_one_add_abs_pow_four_mul_exp_neg_sq.const_mul A)
  · exact ((continuous_smoothAFEZetaChiShiftRatioSqHeightDerivative tau).mul
      (continuous_smoothAFEMellinIntegrand_at_one hY)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun v => by
      have hsquare := hglobal tau v
      have hm := norm_smoothAFEMellinIntegrand_vertical_le hY
        (show (0 : ℝ) < 1 by norm_num) v
      have hm' :
          ‖smoothAFEMellinIntegrand Y (↑(1 : ℝ) + ↑v * I)‖ ≤
            (Y⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2)) := by
        simpa [Real.rpow_neg_one] using hm
      have hpow : (1 + |v|) ^ 3 ≤ (1 + |v|) ^ 4 := by
        have hb : 1 ≤ 1 + |v| := by linarith [abs_nonneg v]
        nlinarith [pow_nonneg (by linarith : 0 ≤ 1 + |v|) 3]
      have hA : 0 ≤ A := by
        dsimp only [A]
        positivity
      unfold smoothAFEZetaSquareDualWeightHeightDerivativeIntegrand
      rw [norm_mul]
      calc
        ‖smoothAFEZetaChiShiftRatioSqHeightDerivative tau v‖ *
            ‖smoothAFEMellinIntegrand Y (↑(1 : ℝ) + ↑v * I)‖
          ≤ (E * (1 + |tau|) ^ 3 * (1 + |v|) ^ 3) *
              ((Y⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2))) := by gcongr
        _ = A * ((1 + |v|) ^ 3 * Real.exp (-(v ^ 2))) := by
          dsimp only [A]
          ring
        _ ≤ A * ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by gcongr

/-- Exact differentiation under the square-dual frequency integral. -/
theorem hasDerivAt_smoothAFEZetaSquareDualWeight
    {Y : ℝ} (hY : 0 < Y) (tau : ℝ) :
    HasDerivAt (fun u : ℝ => smoothAFEZetaSquareDualWeight u Y)
      ((1 / (2 * Real.pi) : ℝ) •
        ∫ v : ℝ,
          smoothAFEZetaSquareDualWeightHeightDerivativeIntegrand tau Y v) tau := by
  obtain ⟨E, hE, hglobal⟩ :=
    exists_norm_smoothAFEZetaChiShiftRatioSqHeightDerivative_le_global
  let F : ℝ → ℝ → ℂ := fun u v =>
    smoothAFEZetaChiShiftRatioSq u v *
      smoothAFEMellinIntegrand Y
        (((1 : ℝ) : ℂ) + (v : ℂ) * I)
  let F' : ℝ → ℝ → ℂ := fun u v =>
    smoothAFEZetaSquareDualWeightHeightDerivativeIntegrand u Y v
  let B : ℝ := E * (2 + |tau|) ^ 3 * (Y⁻¹ * Real.exp 1)
  let bound : ℝ → ℝ := fun v =>
    B * ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2)))
  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (s := Metric.ball tau 1) (bound := bound)
    (Metric.ball_mem_nhds tau (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall fun u =>
      (smoothAFEZetaSquareDualWeightAt_one_integrable hY u).aestronglyMeasurable)
    (smoothAFEZetaSquareDualWeightAt_one_integrable hY tau)
    (smoothAFEZetaSquareDualWeightHeightDerivativeIntegrand_integrable hY tau).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v u hu => by
      have hsquare := hglobal u v
      have hm := norm_smoothAFEMellinIntegrand_vertical_le hY
        (show (0 : ℝ) < 1 by norm_num) v
      have hm' :
          ‖smoothAFEMellinIntegrand Y (↑(1 : ℝ) + ↑v * I)‖ ≤
            (Y⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2)) := by
        simpa [Real.rpow_neg_one] using hm
      have hudist : |u - tau| < 1 := by
        simpa [Real.dist_eq] using hu
      have huabs : |u| < |tau| + 1 := by
        calc
          |u| = |(u - tau) + tau| := by ring_nf
          _ ≤ |u - tau| + |tau| := abs_add_le _ _
          _ < 1 + |tau| := by linarith
          _ = |tau| + 1 := by ring
      have hheight : (1 + |u|) ^ 3 ≤ (2 + |tau|) ^ 3 := by
        apply pow_le_pow_left₀ (by positivity)
        linarith
      have hpow : (1 + |v|) ^ 3 ≤ (1 + |v|) ^ 4 := by
        have hb : 1 ≤ 1 + |v| := by linarith [abs_nonneg v]
        nlinarith [pow_nonneg (by linarith : 0 ≤ 1 + |v|) 3]
      dsimp only [F', smoothAFEZetaSquareDualWeightHeightDerivativeIntegrand]
      rw [norm_mul]
      calc
        ‖smoothAFEZetaChiShiftRatioSqHeightDerivative u v‖ *
            ‖smoothAFEMellinIntegrand Y (↑(1 : ℝ) + ↑v * I)‖
          ≤ (E * (1 + |u|) ^ 3 * (1 + |v|) ^ 3) *
              ((Y⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2))) := by gcongr
        _ = (E * (1 + |u|) ^ 3 * (Y⁻¹ * Real.exp 1)) *
              ((1 + |v|) ^ 3 * Real.exp (-(v ^ 2))) := by ring
        _ ≤ (E * (2 + |tau|) ^ 3 * (Y⁻¹ * Real.exp 1)) *
              ((1 + |v|) ^ 3 * Real.exp (-(v ^ 2))) := by gcongr
        _ ≤ (E * (2 + |tau|) ^ 3 * (Y⁻¹ * Real.exp 1)) *
              ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by gcongr
        _ = bound v := by
          dsimp only [bound, B])
    (integrable_one_add_abs_pow_four_mul_exp_neg_sq.const_mul B)
    (Filter.Eventually.of_forall fun v u hu => by
      dsimp only [F, F']
      exact (hasDerivAt_smoothAFEZetaChiShiftRatioSq u v).mul_const
        (smoothAFEMellinIntegrand Y
          (((1 : ℝ) : ℂ) + (v : ℂ) * I)))
  have hraw := hparam.2
  unfold smoothAFEZetaSquareDualWeight
  apply hraw.const_smul (1 / (2 * Real.pi) : ℝ)

end RHTower
