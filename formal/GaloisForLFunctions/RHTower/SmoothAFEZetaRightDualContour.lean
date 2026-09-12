import GaloisForLFunctions.RHTower.SmoothAFEZetaChiShiftRightPowerBound
import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDualContourLimit

/-!
# Direct dual contour localization on a displaced right line

For `s = 1/2+d+iτ`, move the positive dual contour from `Re w = 1`
to `Re w = -η`.  The shift is legal exactly when `d+η<1/2`, crosses
only the pole at zero, and combines with the right-line chi-ratio bound
to give `|W-1| ≪ (Y / max(1,|τ|))^η`.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Filter Topology Set

theorem displacedLinePt_neg_displacement_eq_right (d τ : ℝ) :
    displacedLinePt (-d) τ = rightDisplacedLinePt d τ := by
  unfold displacedLinePt rightDisplacedLinePt
  push_cast
  ring

/-- Direct dual weight on `1/2+d+iτ`, represented using the signed
displacement parameter of the general contour definitions. -/
def smoothAFEZetaRightDualWeightAt (a d τ Y : ℝ) : ℂ :=
  smoothAFEZetaDisplacedDualWeightAt a (-d) τ Y

/-- Positive-line direct dual weight on `1/2+d+iτ`. -/
def smoothAFEZetaRightDualWeight (d τ Y : ℝ) : ℂ :=
  smoothAFEZetaRightDualWeightAt 1 d τ Y

theorem smoothAFEZetaRightDualNumerator_zero
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2) (τ Y : ℝ) :
    smoothAFEZetaDisplacedDualNumerator (-d) τ Y 0 = 1 := by
  unfold smoothAFEZetaDisplacedDualNumerator smoothAFEZetaChiShiftRatio
  rw [displacedLinePt_neg_displacement_eq_right, neg_zero, add_zero,
    div_self (zetaChi_ne_zero_of_mem_openStrip
      (rightDisplacedLinePt_mem_openStrip hd hdhalf τ).1
      (rightDisplacedLinePt_mem_openStrip hd hdhalf τ).2)]
  norm_num

/-- Finite-height residue identity for the right-line contour. -/
theorem smoothAFEZetaRightDualWeight_finite_contour
    {d η Y T : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (hη : 0 < η) (hdηhalf : d + η < 1 / 2)
    (hY : 0 < Y) (hT : 0 < T) (τ : ℝ) :
    RHTower.rectIntegral
        (fun w : ℂ =>
          smoothAFEZetaChiShiftRatio (rightDisplacedLinePt d τ) (-w) *
            smoothAFEMellinIntegrand Y w)
        (((-η : ℝ) : ℂ) - (T : ℂ) * I)
        (((1 : ℝ) : ℂ) + (T : ℂ) * I) =
      2 * Real.pi * I := by
  let z₁ : ℂ := (((-η : ℝ) : ℂ) - (T : ℂ) * I)
  let z₂ : ℂ := (((1 : ℝ) : ℂ) + (T : ℂ) * I)
  let U : Set ℂ := {w : ℂ | d - 1 / 2 < w.re}
  have hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U := by
    intro w hw
    have hwre := (Complex.mem_reProdIm.mp hw).1
    have hzre : z₁.re = -η := by simp [z₁]
    have hz2re : z₂.re = 1 := by simp [z₂]
    rw [hzre, hz2re, uIcc_of_le (by linarith)] at hwre
    exact (by linarith : d - 1 / 2 < -η).trans_le hwre.1
  have hanalytic :=
    smoothAFEZetaDisplacedDualNumerator_analyticOnNhd (-d) τ hY
  have hUeq : {w : ℂ | -(-d + 1 / 2) < w.re} = U := by
    ext w
    simp only [U, Set.mem_setOf_eq]
    ring_nf
  rw [hUeq] at hanalytic
  have hcauchy := rectIntegral_cauchyFormula_analyticOnNhd
    (g := smoothAFEZetaDisplacedDualNumerator (-d) τ Y)
    (U := U) (p := 0) (z₁ := z₁) (z₂ := z₂)
    hsub hanalytic
    (by simp [z₁]; linarith) (by simp [z₂])
    (by simp [z₁]; linarith) (by simp [z₂]; linarith)
  have hfun :
      (fun w : ℂ =>
        smoothAFEZetaDisplacedDualNumerator (-d) τ Y w * (w - 0)⁻¹) =
      (fun w : ℂ =>
        smoothAFEZetaChiShiftRatio (rightDisplacedLinePt d τ) (-w) *
          smoothAFEMellinIntegrand Y w) := by
    funext w
    rw [← displacedLinePt_neg_displacement_eq_right]
    exact (smoothAFEZetaDisplacedDualIntegrand_eq_numerator_div
      (-d) τ Y w).symm
  rw [hfun] at hcauchy
  rw [smoothAFEZetaRightDualNumerator_zero hd hdhalf τ Y] at hcauchy
  simpa [z₁, z₂] using hcauchy

theorem smoothAFEZetaRightDualWeightAt_one_integrable
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    {Y : ℝ} (hY : 0 < Y) (τ : ℝ) :
    Integrable (fun v : ℝ =>
      smoothAFEZetaChiShiftRatio (rightDisplacedLinePt d τ)
          (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
        smoothAFEMellinIntegrand Y
          (((1 : ℝ) : ℂ) + (v : ℂ) * I)) := by
  have hσ0 : -1 / 2 + d ≠ 0 := by linarith
  obtain ⟨C, hC0, hchi⟩ := exists_bound_norm_zetaChi_vertical hσ0
    (by linarith : -1 ≤ -1 / 2 + d)
    (by linarith : -1 / 2 + d ≤ 1 / 2)
  let B : ℝ := ‖(zetaChi (rightDisplacedLinePt d τ))⁻¹‖
  let D : ℝ := C * B * (Y⁻¹ * Real.exp 1)
  apply Integrable.mono'
    ((integrable_shifted_pow_mul_exp_neg_sq (1 + |τ|) 2).const_mul D)
  · haveI : NeZero (Y : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hY.ne'⟩
    have hratio : Continuous (fun v : ℝ =>
        smoothAFEZetaChiShiftRatio (rightDisplacedLinePt d τ)
          (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))) := by
      rw [continuous_iff_continuousAt]
      intro v
      unfold smoothAFEZetaChiShiftRatio
      apply ContinuousAt.div_const
      apply (zetaChi_analyticAt ?_).continuousAt.comp
      · fun_prop
      · apply Complex.Gammaℝ_ne_zero_of_re_pos
        simp [rightDisplacedLinePt]
        linarith
    have hmellin : Continuous (fun v : ℝ =>
        smoothAFEMellinIntegrand Y
          (((1 : ℝ) : ℂ) + (v : ℂ) * I)) := by
      unfold smoothAFEMellinIntegrand smoothAFEGaussianKernel
      apply Continuous.mul
      · exact (continuous_const_cpow (Y : ℂ)).comp (by fun_prop)
      · exact (Complex.continuous_exp.comp (by fun_prop)).div
          (by fun_prop) (fun v hzero => by
            have hre := congrArg Complex.re hzero
            norm_num at hre)
    exact (hratio.mul hmellin).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun v => by
      rw [norm_mul]
      have harg :
          rightDisplacedLinePt d τ +
              -(((1 : ℝ) : ℂ) + (v : ℂ) * I) =
            (((-1 / 2 + d : ℝ) : ℂ) +
              ((τ - v : ℝ) : ℂ) * I) := by
        unfold rightDisplacedLinePt
        push_cast
        ring
      have hr :
          ‖smoothAFEZetaChiShiftRatio (rightDisplacedLinePt d τ)
              (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤
            C * (1 + |τ| + |v|) ^ 2 * B := by
        unfold smoothAFEZetaChiShiftRatio
        rw [div_eq_mul_inv, norm_mul, harg]
        have hbase := hchi (τ - v)
        have habs : 1 + |τ - v| ≤ 1 + |τ| + |v| := by
          linarith [abs_sub τ v]
        have hsq : (1 + |τ - v|) ^ 2 ≤ (1 + |τ| + |v|) ^ 2 := by
          nlinarith [abs_nonneg (τ - v), abs_nonneg τ, abs_nonneg v]
        exact mul_le_mul_of_nonneg_right
          (hbase.trans (mul_le_mul_of_nonneg_left hsq hC0)) (norm_nonneg _)
      have hm := norm_smoothAFEMellinIntegrand_vertical_le
        hY (show (0 : ℝ) < 1 by norm_num) v
      have hm' :
          ‖smoothAFEMellinIntegrand Y (↑(1 : ℝ) + ↑v * I)‖ ≤
            (Y⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2)) := by
        simpa [Real.rpow_neg_one] using hm
      dsimp only [D]
      calc
        ‖smoothAFEZetaChiShiftRatio (rightDisplacedLinePt d τ)
              (-(↑(1 : ℝ) + ↑v * I))‖ *
            ‖smoothAFEMellinIntegrand Y (↑(1 : ℝ) + ↑v * I)‖
          ≤ (C * (1 + |τ| + |v|) ^ 2 * B) *
              ((Y⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2))) := by gcongr
        _ = C * B * (Y⁻¹ * Real.exp 1) *
              ((1 + |τ| + |v|) ^ 2 * Real.exp (-(v ^ 2))) := by ring

theorem smoothAFEZetaRightDualWeightAt_neg_integrable
    {d η : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (hη : 0 < η) (hdηhalf : d + η < 1 / 2)
    {Y : ℝ} (hY : 0 < Y) (τ : ℝ) :
    Integrable (fun v : ℝ =>
      smoothAFEZetaChiShiftRatio (rightDisplacedLinePt d τ)
          (-(((-η : ℝ) : ℂ) + (v : ℂ) * I)) *
        smoothAFEMellinIntegrand Y
          (((-η : ℝ) : ℂ) + (v : ℂ) * I)) := by
  obtain ⟨K, _hK0, hratioBound⟩ :=
    exists_norm_smoothAFEZetaChiShiftRatio_rightDisplaced_le
      hd hdhalf hη hdηhalf
  let D : ℝ :=
    (K / (max 1 |τ|) ^ η) *
      (Y ^ η * (Real.exp (η ^ 2) / η))
  apply Integrable.mono'
    (integrable_one_add_abs_mul_exp_neg_sq.const_mul D)
  · haveI : NeZero (Y : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hY.ne'⟩
    have hratio : Continuous (fun v : ℝ =>
        smoothAFEZetaChiShiftRatio (rightDisplacedLinePt d τ)
          (-(((-η : ℝ) : ℂ) + (v : ℂ) * I))) := by
      rw [continuous_iff_continuousAt]
      intro v
      unfold smoothAFEZetaChiShiftRatio
      apply ContinuousAt.div_const
      apply (zetaChi_analyticAt ?_).continuousAt.comp
      · fun_prop
      · apply Complex.Gammaℝ_ne_zero_of_re_pos
        simp [rightDisplacedLinePt]
        linarith
    have hmellin : Continuous (fun v : ℝ =>
        smoothAFEMellinIntegrand Y
          (((-η : ℝ) : ℂ) + (v : ℂ) * I)) := by
      unfold smoothAFEMellinIntegrand smoothAFEGaussianKernel
      apply Continuous.mul
      · exact (continuous_const_cpow (Y : ℂ)).comp (by fun_prop)
      · exact (Complex.continuous_exp.comp (by fun_prop)).div
          (by fun_prop) (fun v hzero => by
            have hre := congrArg Complex.re hzero
            simp at hre
            linarith)
    exact (hratio.mul hmellin).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun v => by
      have hr := hratioBound τ v
      have hk := norm_smoothAFEGaussianKernel_vertical_le_of_ne
        (σ := -η) (by linarith) v
      have hpow :
          ‖(Y : ℂ) ^ (-((((-η : ℝ) : ℂ) + (v : ℂ) * I)))‖ =
            Y ^ η := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
        simp
      have hvbase : 1 ≤ 1 + |v| := by linarith [abs_nonneg v]
      have hvpow : (1 + |v|) ^ (d + η) ≤ 1 + |v| := by
        simpa using Real.rpow_le_rpow_of_exponent_le hvbase
          (by linarith : d + η ≤ 1)
      unfold smoothAFEMellinIntegrand
      rw [norm_mul, norm_mul, hpow]
      dsimp only [D]
      calc
        ‖smoothAFEZetaChiShiftRatio (rightDisplacedLinePt d τ)
            (-(((-η : ℝ) : ℂ) + (v : ℂ) * I))‖ *
            (Y ^ η *
              ‖smoothAFEGaussianKernel
                (((-η : ℝ) : ℂ) + (v : ℂ) * I)‖)
          ≤ (K * (1 + |v|) ^ (d + η) / (max 1 |τ|) ^ η) *
              (Y ^ η *
                ((Real.exp ((-η) ^ 2) / |-η|) *
                  Real.exp (-(v ^ 2)))) := by gcongr
        _ ≤ (K * (1 + |v|) / (max 1 |τ|) ^ η) *
              (Y ^ η *
                ((Real.exp ((-η) ^ 2) / |-η|) *
                  Real.exp (-(v ^ 2)))) := by gcongr
        _ = (K / (max 1 |τ|) ^ η) *
              (Y ^ η * (Real.exp (η ^ 2) / η)) *
              ((1 + |v|) * Real.exp (-(v ^ 2))) := by
          rw [neg_sq, abs_neg, abs_of_pos hη]
          ring

end RHTower
