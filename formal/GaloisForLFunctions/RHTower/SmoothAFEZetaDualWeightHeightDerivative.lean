import GaloisForLFunctions.RHTower.SmoothAFEZetaChiShiftGlobalDerivativeBound

/-!
# Height derivative of the exact dual Gaussian weight

The reflected AFE carrier must move with the height without paying the absolute
size of each reflected coefficient.  This module differentiates its exact
Gaussian contour integral.  The derivative exposes the neutral logarithmic
slope of the chi ratio; its global polynomial envelope is dominated by the
Gaussian frequency factor.
-/

noncomputable section

open Complex Set MeasureTheory Filter

namespace RHTower

/-- Exact height derivative of the shifted chi ratio on the positive dual line. -/
def smoothAFEZetaChiShiftHeightDerivative (tau v : ℝ) : ℂ :=
  I * smoothAFEZetaChiShiftRatio (linePt tau)
      (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
    (logDeriv zetaChi
        (linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
      logDeriv zetaChi (linePt tau))

theorem hasDerivAt_chiShift_eq_heightDerivative (tau v : ℝ) :
    HasDerivAt
      (fun u : ℝ => smoothAFEZetaChiShiftRatio (linePt u)
        (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)))
      (smoothAFEZetaChiShiftHeightDerivative tau v) tau := by
  exact hasDerivAt_smoothAFEZetaChiShiftRatio_neg_right_one_line tau v

private theorem positive_vertical_ne_neg_nat {sigma t : ℝ} (hsigma : 0 < sigma) :
    ∀ m : ℕ, ((sigma : ℂ) + (t : ℂ) * I) ≠ -(m : ℂ) := by
  intro m hm
  have hre := congrArg Complex.re hm
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    I_re, I_im, mul_zero, zero_mul, sub_zero, Complex.neg_re, Complex.natCast_re] at hre
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

/-- The neutral logarithmic slope is continuous in the Gaussian frequency. -/
theorem continuous_chiShiftLogSlope (tau : ℝ) :
    Continuous (fun v : ℝ =>
      logDeriv zetaChi
          (linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
        logDeriv zetaChi (linePt tau)) := by
  have hA : Continuous (fun v : ℝ => Complex.digamma
      ((linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I)) / 2)) := by
    rw [continuous_iff_continuousAt]
    intro v
    have harg :
        (linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I)) / 2 =
          ((-1 / 4 : ℝ) : ℂ) + (((tau - v) / 2 : ℝ) : ℂ) * I := by
      apply Complex.ext <;> norm_num [linePt]
    have hoff : ∀ m : ℕ,
        (linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I)) / 2 ≠ -(m : ℂ) := by
      rw [harg]
      exact quarter_vertical_ne_neg_nat (Or.inl rfl)
    have hinner : ContinuousAt (fun u : ℝ =>
        (linePt tau - (((1 : ℝ) : ℂ) + (u : ℂ) * I)) / 2) v := by
      apply ContinuousAt.div_const
      fun_prop
    have hc : ContinuousAt
        (Complex.digamma ∘ fun u : ℝ =>
          (linePt tau - (((1 : ℝ) : ℂ) + (u : ℂ) * I)) / 2) v :=
      ContinuousAt.comp (x := v)
        (GaloisForLFunctions.continuousAt_digamma _ hoff) hinner
    change ContinuousAt
      (Complex.digamma ∘ fun u : ℝ =>
        (linePt tau - (((1 : ℝ) : ℂ) + (u : ℂ) * I)) / 2) v
    exact hc
  have hC : Continuous (fun v : ℝ => Complex.digamma
      ((1 - (linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I))) / 2)) := by
    rw [continuous_iff_continuousAt]
    intro v
    have harg :
        (1 - (linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I))) / 2 =
          ((3 / 4 : ℝ) : ℂ) + (((-(tau - v)) / 2 : ℝ) : ℂ) * I := by
      apply Complex.ext <;> norm_num [linePt]
    have hoff : ∀ m : ℕ,
        (1 - (linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I))) / 2 ≠ -(m : ℂ) := by
      rw [harg]
      exact positive_vertical_ne_neg_nat (by norm_num)
    have hinner : ContinuousAt (fun u : ℝ =>
        (1 - (linePt tau - (((1 : ℝ) : ℂ) + (u : ℂ) * I))) / 2) v := by
      apply ContinuousAt.div_const
      fun_prop
    have hc : ContinuousAt
        (Complex.digamma ∘ fun u : ℝ =>
          (1 - (linePt tau - (((1 : ℝ) : ℂ) + (u : ℂ) * I))) / 2) v :=
      ContinuousAt.comp (x := v)
        (GaloisForLFunctions.continuousAt_digamma _ hoff) hinner
    change ContinuousAt
      (Complex.digamma ∘ fun u : ℝ =>
        (1 - (linePt tau - (((1 : ℝ) : ℂ) + (u : ℂ) * I))) / 2) v
    exact hc
  have heq : (fun v : ℝ =>
      logDeriv zetaChi
          (linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
        logDeriv zetaChi (linePt tau)) = fun v : ℝ =>
      -(Complex.digamma
          ((linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I)) / 2) -
          Complex.digamma (linePt tau / 2)) / 2 -
        (Complex.digamma
          ((1 - (linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I))) / 2) -
          Complex.digamma ((1 - linePt tau) / 2)) / 2 := by
    funext v
    exact logDeriv_zetaChi_shift_sub_line_eq_digamma_increments tau v
  rw [heq]
  exact (((hA.sub continuous_const).neg.div_const 2).sub
    ((hC.sub continuous_const).div_const 2))

theorem continuous_smoothAFEZetaChiShiftHeightDerivative (tau : ℝ) :
    Continuous (smoothAFEZetaChiShiftHeightDerivative tau) := by
  have hratio : Continuous (fun v : ℝ =>
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
  unfold smoothAFEZetaChiShiftHeightDerivative
  exact (continuous_const.mul hratio).mul (continuous_chiShiftLogSlope tau)

/-- Frequency integrand for the exact height derivative of the dual weight. -/
def smoothAFEZetaDualWeightHeightDerivativeIntegrand
    (tau Y v : ℝ) : ℂ :=
  smoothAFEZetaChiShiftHeightDerivative tau v *
    smoothAFEMellinIntegrand Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)

theorem smoothAFEZetaDualWeightHeightDerivativeIntegrand_integrable
    {Y : ℝ} (hY : 0 < Y) (tau : ℝ) :
    Integrable (smoothAFEZetaDualWeightHeightDerivativeIntegrand tau Y) := by
  obtain ⟨D, hD, hglobal⟩ :=
    exists_norm_deriv_smoothAFEZetaChiShiftRatio_le_global
  let A : ℝ := D * (1 + |tau|) ^ 2 * (Y⁻¹ * Real.exp 1)
  apply Integrable.mono'
    (integrable_one_add_abs_sq_mul_exp_neg_sq.const_mul A)
  · have hmellin : Continuous (fun v : ℝ =>
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
    exact ((continuous_smoothAFEZetaChiShiftHeightDerivative tau).mul hmellin).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun v => by
      have hder := hglobal tau v
      rw [(hasDerivAt_chiShift_eq_heightDerivative tau v).deriv] at hder
      have hm := norm_smoothAFEMellinIntegrand_vertical_le hY
        (show (0 : ℝ) < 1 by norm_num) v
      have hm' :
          ‖smoothAFEMellinIntegrand Y (↑(1 : ℝ) + ↑v * I)‖ ≤
            (Y⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2)) := by
        simpa [Real.rpow_neg_one] using hm
      unfold smoothAFEZetaDualWeightHeightDerivativeIntegrand
      rw [norm_mul]
      calc
        ‖smoothAFEZetaChiShiftHeightDerivative tau v‖ *
            ‖smoothAFEMellinIntegrand Y (↑(1 : ℝ) + ↑v * I)‖
          ≤ (D * (1 + |tau|) ^ 2 * (1 + |v|) ^ 2) *
              ((Y⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2))) := by gcongr
        _ = A * ((1 + |v|) ^ 2 * Real.exp (-(v ^ 2))) := by
          dsimp only [A]
          ring

/-- The exact dual Gaussian weight is differentiable in height.  Its derivative
is the integral of the neutral chi logarithmic slope, not a coefficientwise
absolute-value majorant. -/
theorem hasDerivAt_smoothAFEZetaDualWeight
    {Y : ℝ} (hY : 0 < Y) (tau : ℝ) :
    HasDerivAt (fun u : ℝ => smoothAFEZetaDualWeight u Y)
      ((1 / (2 * Real.pi) : ℝ) •
        ∫ v : ℝ,
          smoothAFEZetaDualWeightHeightDerivativeIntegrand tau Y v) tau := by
  obtain ⟨D, hD, hglobal⟩ :=
    exists_norm_deriv_smoothAFEZetaChiShiftRatio_le_global
  let F : ℝ → ℝ → ℂ := fun u v =>
    smoothAFEZetaChiShiftRatio (linePt u)
        (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
      smoothAFEMellinIntegrand Y
        (((1 : ℝ) : ℂ) + (v : ℂ) * I)
  let F' : ℝ → ℝ → ℂ := fun u v =>
    smoothAFEZetaDualWeightHeightDerivativeIntegrand u Y v
  let B : ℝ := D * (2 + |tau|) ^ 2 * (Y⁻¹ * Real.exp 1)
  let bound : ℝ → ℝ := fun v =>
    B * ((1 + |v|) ^ 2 * Real.exp (-(v ^ 2)))
  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (s := Metric.ball tau 1) (bound := bound)
    (Metric.ball_mem_nhds tau (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall fun u =>
      (smoothAFEZetaDualWeightAt_one_integrable hY u).aestronglyMeasurable)
    (smoothAFEZetaDualWeightAt_one_integrable hY tau)
    (smoothAFEZetaDualWeightHeightDerivativeIntegrand_integrable hY tau).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v u hu => by
      have hder := hglobal u v
      rw [(hasDerivAt_chiShift_eq_heightDerivative u v).deriv] at hder
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
      have hheight : (1 + |u|) ^ 2 ≤ (2 + |tau|) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity)
        · linarith
      dsimp only [F', smoothAFEZetaDualWeightHeightDerivativeIntegrand]
      rw [norm_mul]
      calc
        ‖smoothAFEZetaChiShiftHeightDerivative u v‖ *
            ‖smoothAFEMellinIntegrand Y (↑(1 : ℝ) + ↑v * I)‖
          ≤ (D * (1 + |u|) ^ 2 * (1 + |v|) ^ 2) *
              ((Y⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2))) := by gcongr
        _ = (D * (1 + |u|) ^ 2 * (Y⁻¹ * Real.exp 1)) *
              ((1 + |v|) ^ 2 * Real.exp (-(v ^ 2))) := by ring
        _ ≤ (D * (2 + |tau|) ^ 2 * (Y⁻¹ * Real.exp 1)) *
              ((1 + |v|) ^ 2 * Real.exp (-(v ^ 2))) := by
            gcongr
        _ = bound v := by
          dsimp only [bound, B])
    (integrable_one_add_abs_sq_mul_exp_neg_sq.const_mul B)
    (Filter.Eventually.of_forall fun v u hu => by
      dsimp only [F, F']
      exact (hasDerivAt_chiShift_eq_heightDerivative u v).mul_const
        (smoothAFEMellinIntegrand Y
          (((1 : ℝ) : ℂ) + (v : ℂ) * I)))
  have hraw := hparam.2
  unfold smoothAFEZetaDualWeight
  apply hraw.const_smul (1 / (2 * Real.pi) : ℝ)

end RHTower
