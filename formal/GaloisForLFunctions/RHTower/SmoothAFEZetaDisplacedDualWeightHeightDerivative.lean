import GaloisForLFunctions.RHTower.SmoothAFEZetaChiShiftDisplacedGlobalDerivativeBound

/-!
# Height derivative of the displaced exact dual Gaussian weight

The displaced dual carrier is moved to `Re w = -(d+eta)`, where its height
derivative is governed by the shifted chi-ratio logarithmic slope.  Uniform
polynomial envelopes for the ratio and slope are absorbed by the Gaussian.
-/

noncomputable section

open Complex Set MeasureTheory Filter

namespace RHTower

/-- Exact height derivative of the displaced chi ratio on the negative contour. -/
def smoothAFEZetaDisplacedChiShiftHeightDerivative
    (d eta tau v : ℝ) : ℂ :=
  I * smoothAFEZetaChiShiftRatio (displacedLinePt d tau)
      (-(((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I)) *
    (logDeriv zetaChi
        (displacedLinePt d tau -
          (((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I)) -
      logDeriv zetaChi (displacedLinePt d tau))

theorem hasDerivAt_smoothAFEZetaDisplacedChiShift
    {d eta : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (heta : 0 < eta) (hetahalf : eta < 1 / 2) (tau v : ℝ) :
    HasDerivAt
      (fun u : ℝ => smoothAFEZetaChiShiftRatio (displacedLinePt d u)
        (-(((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I)))
      (smoothAFEZetaDisplacedChiShiftHeightDerivative d eta tau v) tau := by
  exact hasDerivAt_smoothAFEZetaChiShiftRatio_displaced_neg
    hd hdhalf heta hetahalf tau v

private theorem positive_vertical_ne_neg_nat {sigma t : ℝ} (hsigma : 0 < sigma) :
    ∀ m : ℕ, ((sigma : ℂ) + (t : ℂ) * I) ≠ -(m : ℂ) := by
  intro m hm
  have hre := congrArg Complex.re hm
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    I_re, I_im, mul_zero, zero_mul, sub_zero, Complex.neg_re, Complex.natCast_re] at hre
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

/-- Displaced negative-contour logarithmic slope is continuous in frequency. -/
theorem continuous_smoothAFEZetaDisplacedChiShiftLogSlope
    {d eta : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (heta : 0 < eta) (hetahalf : eta < 1 / 2) (tau : ℝ) :
    Continuous (fun v : ℝ =>
      logDeriv zetaChi
          (displacedLinePt d tau -
            (((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I)) -
        logDeriv zetaChi (displacedLinePt d tau)) := by
  have hA : Continuous (fun v : ℝ => Complex.digamma
      ((displacedLinePt d tau -
        (((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I)) / 2)) := by
    rw [continuous_iff_continuousAt]
    intro v
    have harg :
        (displacedLinePt d tau -
          (((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I)) / 2 =
          ((1 / 4 + eta / 2 : ℝ) : ℂ) +
            (((tau - v) / 2 : ℝ) : ℂ) * I := by
      apply Complex.ext
      · norm_num [displacedLinePt]
        ring
      · norm_num [displacedLinePt]
    have hoff : ∀ m : ℕ,
        (displacedLinePt d tau -
          (((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I)) / 2 ≠ -(m : ℂ) := by
      rw [harg]
      exact positive_vertical_ne_neg_nat (by linarith)
    have hinner : ContinuousAt (fun u : ℝ =>
        (displacedLinePt d tau -
          (((-(d + eta) : ℝ) : ℂ) + (u : ℂ) * I)) / 2) v := by
      apply ContinuousAt.div_const
      fun_prop
    exact ContinuousAt.comp (x := v)
      (GaloisForLFunctions.continuousAt_digamma _ hoff) hinner
  have hC : Continuous (fun v : ℝ => Complex.digamma
      ((1 - (displacedLinePt d tau -
        (((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I))) / 2)) := by
    rw [continuous_iff_continuousAt]
    intro v
    have harg :
        (1 - (displacedLinePt d tau -
          (((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I))) / 2 =
          ((1 / 4 - eta / 2 : ℝ) : ℂ) +
            (((-(tau - v)) / 2 : ℝ) : ℂ) * I := by
      apply Complex.ext
      · norm_num [displacedLinePt]
        ring
      · norm_num [displacedLinePt]
    have hoff : ∀ m : ℕ,
        (1 - (displacedLinePt d tau -
          (((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I))) / 2 ≠ -(m : ℂ) := by
      rw [harg]
      exact positive_vertical_ne_neg_nat (by linarith)
    have hinner : ContinuousAt (fun u : ℝ =>
        (1 - (displacedLinePt d tau -
          (((-(d + eta) : ℝ) : ℂ) + (u : ℂ) * I))) / 2) v := by
      apply ContinuousAt.div_const
      fun_prop
    exact ContinuousAt.comp (x := v)
      (GaloisForLFunctions.continuousAt_digamma _ hoff) hinner
  have heq : (fun v : ℝ =>
      logDeriv zetaChi
          (displacedLinePt d tau -
            (((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I)) -
        logDeriv zetaChi (displacedLinePt d tau)) = fun v : ℝ =>
      -(Complex.digamma
          ((displacedLinePt d tau -
            (((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I)) / 2) -
          Complex.digamma (displacedLinePt d tau / 2)) / 2 -
        (Complex.digamma
          ((1 - (displacedLinePt d tau -
            (((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I))) / 2) -
          Complex.digamma ((1 - displacedLinePt d tau) / 2)) / 2 := by
    funext v
    exact logDeriv_zetaChi_displaced_neg_shift_sub_eq_digamma_increments
      hd hdhalf heta hetahalf tau v
  rw [heq]
  exact (((hA.sub continuous_const).neg.div_const 2).sub
    ((hC.sub continuous_const).div_const 2))

theorem continuous_smoothAFEZetaDisplacedChiShiftRatio_neg
    {d eta : ℝ} (hetahalf : eta < 1 / 2) (tau : ℝ) :
    Continuous (fun v : ℝ =>
      smoothAFEZetaChiShiftRatio (displacedLinePt d tau)
        (-(((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I))) := by
  rw [continuous_iff_continuousAt]
  intro v
  unfold smoothAFEZetaChiShiftRatio
  apply ContinuousAt.div_const
  apply (zetaChi_analyticAt ?_).continuousAt.comp
  · fun_prop
  · apply Gammaℝ_ne_zero_of_re_pos
    simp [displacedLinePt]
    linarith

theorem continuous_smoothAFEZetaDisplacedChiShiftHeightDerivative
    {d eta : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (heta : 0 < eta) (hetahalf : eta < 1 / 2) (tau : ℝ) :
    Continuous (smoothAFEZetaDisplacedChiShiftHeightDerivative d eta tau) := by
  unfold smoothAFEZetaDisplacedChiShiftHeightDerivative
  exact ((continuous_const.mul
    (continuous_smoothAFEZetaDisplacedChiShiftRatio_neg
      hetahalf tau)).mul
    (continuous_smoothAFEZetaDisplacedChiShiftLogSlope
      hd hdhalf heta hetahalf tau))

/-- Frequency integrand for height derivative of the displaced dual weight. -/
def smoothAFEZetaDisplacedDualWeightHeightDerivativeIntegrand
    (d eta tau Y v : ℝ) : ℂ :=
  smoothAFEZetaDisplacedChiShiftHeightDerivative d eta tau v *
    smoothAFEMellinIntegrand Y
      (((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I)

private theorem continuous_smoothAFEMellinIntegrand_at_displaced_neg
    {d eta Y : ℝ} (hd : 0 < d) (heta : 0 < eta) (hY : 0 < Y) :
    Continuous (fun v : ℝ =>
      smoothAFEMellinIntegrand Y
        (((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I)) := by
  haveI : NeZero (Y : ℂ) :=
    ⟨Complex.ofReal_ne_zero.mpr hY.ne'⟩
  unfold smoothAFEMellinIntegrand smoothAFEGaussianKernel
  apply Continuous.mul
  · exact (continuous_const_cpow (Y : ℂ)).comp (by fun_prop)
  · exact (Complex.continuous_exp.comp (by fun_prop)).div
      (by fun_prop) (fun v hzero => by
        have hre := congrArg Complex.re hzero
        simp at hre
        linarith)

theorem smoothAFEZetaDisplacedDualWeightHeightDerivativeIntegrand_integrable
    {d eta Y : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (heta : 0 < eta) (hetahalf : eta < 1 / 2)
    (hY : 0 < Y) (tau : ℝ) :
    Integrable
      (smoothAFEZetaDisplacedDualWeightHeightDerivativeIntegrand
        d eta tau Y) := by
  obtain ⟨K, hK, hratio⟩ :=
    exists_norm_smoothAFEZetaChiShiftRatio_displaced_uniform_le
      hd.le hdhalf heta hetahalf
  obtain ⟨D, hD, hslope⟩ :=
    exists_norm_logDeriv_zetaChi_displaced_neg_shift_sub_le_global
      hd.le hdhalf heta hetahalf
  let Q : ℝ := Y ^ (d + eta) *
    (Real.exp ((d + eta) ^ 2) / (d + eta))
  let A : ℝ := K * D * (1 + |tau|) * Q
  apply Integrable.mono'
    (integrable_one_add_abs_sq_mul_exp_neg_sq.const_mul A)
  · exact ((continuous_smoothAFEZetaDisplacedChiShiftHeightDerivative
      hd hdhalf heta hetahalf tau).mul
      (continuous_smoothAFEMellinIntegrand_at_displaced_neg hd heta hY)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun v => by
      let q : ℝ := 1 + |v|
      have hq1 : 1 ≤ q := by dsimp only [q]; linarith [abs_nonneg v]
      have hqeta : q ^ eta ≤ q := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hq1 (by linarith : eta ≤ 1)
      have hden : 1 ≤ (max 1 |tau|) ^ (d + eta) :=
        Real.one_le_rpow (le_max_left 1 |tau|) (by linarith)
      have hrraw := hratio d hd le_rfl tau v
      have hr :
          ‖smoothAFEZetaChiShiftRatio (displacedLinePt d tau)
              (-(((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤ K * q := by
        calc
          _ ≤ K * q ^ eta / (max 1 |tau|) ^ (d + eta) := hrraw
          _ ≤ K * q ^ eta := div_le_self (by positivity) hden
          _ ≤ K * q := mul_le_mul_of_nonneg_left hqeta hK
      have hs := hslope d hd le_rfl tau v
      have hm := norm_smoothAFEMellinIntegrand_vertical_le_of_ne hY
        (show -(d + eta) ≠ 0 by linarith) v
      have hm' :
          ‖smoothAFEMellinIntegrand Y
              (((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
            Q * Real.exp (-(v ^ 2)) := by
        have hnegSum : -eta + -d = -(d + eta) := by ring
        simpa only [Q, hnegSum, neg_neg, neg_sq, abs_neg,
          abs_of_pos (by linarith : 0 < d + eta)] using hm
      unfold smoothAFEZetaDisplacedDualWeightHeightDerivativeIntegrand
        smoothAFEZetaDisplacedChiShiftHeightDerivative
      simp only [norm_mul, norm_I, one_mul]
      calc
        (‖smoothAFEZetaChiShiftRatio (displacedLinePt d tau)
              (-(((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I))‖ *
            ‖logDeriv zetaChi
                (displacedLinePt d tau -
                  (((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I)) -
              logDeriv zetaChi (displacedLinePt d tau)‖) *
            ‖smoothAFEMellinIntegrand Y
              (((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I)‖
          ≤ ((K * q) * (D * (1 + |tau|) * q)) *
              (Q * Real.exp (-(v ^ 2))) := by gcongr
        _ = A * (q ^ 2 * Real.exp (-(v ^ 2))) := by
          dsimp only [A]
          ring
        _ = A * ((1 + |v|) ^ 2 * Real.exp (-(v ^ 2))) := by rfl

/-- Exact differentiation under the displaced negative contour. -/
theorem hasDerivAt_smoothAFEZetaDisplacedDualWeightAt_neg
    {d eta Y : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (heta : 0 < eta) (hetahalf : eta < 1 / 2)
    (hY : 0 < Y) (tau : ℝ) :
    HasDerivAt
      (fun u : ℝ => smoothAFEZetaDisplacedDualWeightAt (-(d + eta)) d u Y)
      ((1 / (2 * Real.pi) : ℝ) •
        ∫ v : ℝ,
          smoothAFEZetaDisplacedDualWeightHeightDerivativeIntegrand
            d eta tau Y v) tau := by
  obtain ⟨K, hK, hratio⟩ :=
    exists_norm_smoothAFEZetaChiShiftRatio_displaced_uniform_le
      hd.le hdhalf heta hetahalf
  obtain ⟨D, hD, hslope⟩ :=
    exists_norm_logDeriv_zetaChi_displaced_neg_shift_sub_le_global
      hd.le hdhalf heta hetahalf
  let F : ℝ → ℝ → ℂ := fun u v =>
    smoothAFEZetaChiShiftRatio (displacedLinePt d u)
        (-(((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I)) *
      smoothAFEMellinIntegrand Y
        (((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I)
  let F' : ℝ → ℝ → ℂ := fun u v =>
    smoothAFEZetaDisplacedDualWeightHeightDerivativeIntegrand d eta u Y v
  let Q : ℝ := Y ^ (d + eta) *
    (Real.exp ((d + eta) ^ 2) / (d + eta))
  let B : ℝ := K * D * (2 + |tau|) * Q
  let bound : ℝ → ℝ := fun v =>
    B * ((1 + |v|) ^ 2 * Real.exp (-(v ^ 2)))
  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (s := Metric.ball tau 1) (bound := bound)
    (Metric.ball_mem_nhds tau (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall fun u =>
      (smoothAFEZetaDisplacedDualWeightAt_neg_integrable
        hd hdhalf heta hetahalf hY u).aestronglyMeasurable)
    (smoothAFEZetaDisplacedDualWeightAt_neg_integrable
      hd hdhalf heta hetahalf hY tau)
    (smoothAFEZetaDisplacedDualWeightHeightDerivativeIntegrand_integrable
      hd hdhalf heta hetahalf hY tau).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v u hu => by
      let q : ℝ := 1 + |v|
      have hq1 : 1 ≤ q := by dsimp only [q]; linarith [abs_nonneg v]
      have hqeta : q ^ eta ≤ q := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hq1 (by linarith : eta ≤ 1)
      have hden : 1 ≤ (max 1 |u|) ^ (d + eta) :=
        Real.one_le_rpow (le_max_left 1 |u|) (by linarith)
      have hrraw := hratio d hd le_rfl u v
      have hr :
          ‖smoothAFEZetaChiShiftRatio (displacedLinePt d u)
              (-(((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤ K * q := by
        calc
          _ ≤ K * q ^ eta / (max 1 |u|) ^ (d + eta) := hrraw
          _ ≤ K * q ^ eta := div_le_self (by positivity) hden
          _ ≤ K * q := mul_le_mul_of_nonneg_left hqeta hK
      have hs := hslope d hd le_rfl u v
      have hm := norm_smoothAFEMellinIntegrand_vertical_le_of_ne hY
        (show -(d + eta) ≠ 0 by linarith) v
      have hm' :
          ‖smoothAFEMellinIntegrand Y
              (((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
            Q * Real.exp (-(v ^ 2)) := by
        have hnegSum : -eta + -d = -(d + eta) := by ring
        simpa only [Q, hnegSum, neg_neg, neg_sq, abs_neg,
          abs_of_pos (by linarith : 0 < d + eta)] using hm
      have hudist : |u - tau| < 1 := by
        simpa [Real.dist_eq] using hu
      have huabs : |u| < |tau| + 1 := by
        calc
          |u| = |(u - tau) + tau| := by ring_nf
          _ ≤ |u - tau| + |tau| := abs_add_le _ _
          _ < 1 + |tau| := by linarith
          _ = |tau| + 1 := by ring
      have hheight : 1 + |u| ≤ 2 + |tau| := by linarith
      dsimp only [F', smoothAFEZetaDisplacedDualWeightHeightDerivativeIntegrand,
        smoothAFEZetaDisplacedChiShiftHeightDerivative]
      simp only [norm_mul, norm_I, one_mul]
      calc
        (‖smoothAFEZetaChiShiftRatio (displacedLinePt d u)
              (-(((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I))‖ *
            ‖logDeriv zetaChi
                (displacedLinePt d u -
                  (((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I)) -
              logDeriv zetaChi (displacedLinePt d u)‖) *
            ‖smoothAFEMellinIntegrand Y
              (((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I)‖
          ≤ ((K * q) * (D * (1 + |u|) * q)) *
              (Q * Real.exp (-(v ^ 2))) := by gcongr
        _ ≤ ((K * q) * (D * (2 + |tau|) * q)) *
              (Q * Real.exp (-(v ^ 2))) := by gcongr
        _ = bound v := by
          dsimp only [bound, B, q]
          ring)
    (integrable_one_add_abs_sq_mul_exp_neg_sq.const_mul B)
    (Filter.Eventually.of_forall fun v u hu => by
      dsimp only [F, F']
      exact (hasDerivAt_smoothAFEZetaDisplacedChiShift
        hd hdhalf heta hetahalf u v).mul_const
          (smoothAFEMellinIntegrand Y
            (((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I)))
  have hraw := hparam.2
  unfold smoothAFEZetaDisplacedDualWeightAt
  apply hraw.const_smul (1 / (2 * Real.pi) : ℝ)

/-- Constant residue transfers the negative-contour derivative to the original
positive-line displaced dual carrier. -/
theorem hasDerivAt_smoothAFEZetaDisplacedDualWeight_via_neg
    {d eta Y : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (heta : 0 < eta) (hetahalf : eta < 1 / 2)
    (hY : 0 < Y) (tau : ℝ) :
    HasDerivAt (fun u : ℝ => smoothAFEZetaDisplacedDualWeight d u Y)
      ((1 / (2 * Real.pi) : ℝ) •
        ∫ v : ℝ,
          smoothAFEZetaDisplacedDualWeightHeightDerivativeIntegrand
            d eta tau Y v) tau := by
  have hneg := hasDerivAt_smoothAFEZetaDisplacedDualWeightAt_neg
    hd hdhalf heta hetahalf hY tau
  have heq : (fun u : ℝ => smoothAFEZetaDisplacedDualWeight d u Y) =
      (fun u : ℝ => 1 +
        smoothAFEZetaDisplacedDualWeightAt (-(d + eta)) d u Y) := by
    funext u
    exact smoothAFEZetaDisplacedDualWeight_eq_one_add_at_neg
      hd hdhalf heta hetahalf hY u
  rw [heq]
  exact hneg.const_add 1

end RHTower
