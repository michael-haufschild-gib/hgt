import GaloisForLFunctions.HTGeometry.SmoothPlateau
import GaloisForLFunctions.RHTower.EvenSectorFullPositivity

/-!
# Smooth truncation of a one-sided tail

A plateau on `(0,R)` with transition width `1/R` tends to the positive-half-line
indicator. Its total variation is at most two. Consequently truncating a smooth
profile with bounded exponentially weighted size and integrable weighted derivative
preserves a uniform inverse-frequency Fourier bound.
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
open _root_.RHTower.EvenSector

noncomputable section

namespace GaloisForLFunctions.HodgeTheoryOfAFixedPart

/-- A smooth cutoff of the positive half-line, with both transitions shrinking. -/
def tailPlateau (R x : ℝ) : ℝ := smoothPlateau 0 R R⁻¹ x

theorem contDiff_tailPlateau (R : ℝ) : ContDiff ℝ 2 (tailPlateau R) := by
  unfold tailPlateau smoothPlateau
  exact (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _))

theorem tailPlateau_nonneg (R x : ℝ) : 0 ≤ tailPlateau R x := smoothPlateau_nonneg x

theorem tailPlateau_le_one (R x : ℝ) : tailPlateau R x ≤ 1 := smoothPlateau_le_one x

theorem tailPlateau_zero {R : ℝ} (hR : 0 < R) {x : ℝ}
    (hx : x ≤ 0 ∨ R ≤ x) : tailPlateau R x = 0 := by
  rcases hx with hx | hx
  · exact smoothPlateau_eq_zero_of_le (inv_pos.mpr hR) hx
  · exact smoothPlateau_eq_zero_of_ge (inv_pos.mpr hR) hx

theorem hasCompactSupport_tailPlateau {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (tailPlateau R) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := 0) (b := R)) fun x hx => ?_
  apply tailPlateau_zero hR
  have hh : x < 0 ∨ R < x := by simpa only [mem_Icc, not_and_or, not_le] using hx
  exact hh.imp le_of_lt le_of_lt

/-- Every positive point eventually lies in the flat part of the cutoff. -/
theorem eventually_tailPlateau_eq_one {x : ℝ} (hx : 0 < x) :
    ∀ᶠ R : ℝ in atTop, tailPlateau R x = 1 := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop x⁻¹,
    eventually_ge_atTop (x + 1)] with R hR hxR hRx
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hi : R⁻¹ ≤ x := by
    rw [← one_div]
    apply (div_le_iff₀ hR0).mpr
    have hm := mul_le_mul_of_nonneg_left hxR hx.le
    simpa only [mul_inv_cancel₀ hx.ne'] using hm
  exact smoothPlateau_eq_one (inv_pos.mpr hR0) (by simpa using hi)
    (by have hh : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR; linarith only [hh, hRx])

/-- The compact smooth truncation of a profile on the positive half-line. -/
def smoothTail (g : ℝ → ℝ) (R x : ℝ) : ℝ := tailPlateau R x * g x

theorem contDiff_smoothTail {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (R : ℝ) :
    ContDiff ℝ 2 (smoothTail g R) := (contDiff_tailPlateau R).mul hg

theorem hasCompactSupport_smoothTail (g : ℝ → ℝ) {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (smoothTail g R) := (hasCompactSupport_tailPlateau hR).mul_right

theorem deriv_smoothTail {g : ℝ → ℝ} (hg : Differentiable ℝ g) (R x : ℝ) :
    deriv (smoothTail g R) x = smoothPlateauDeriv 0 R R⁻¹ x * g x +
      tailPlateau R x * deriv g x :=
  ((hasDerivAt_smoothPlateau x).mul (hg x).hasDerivAt).deriv

/-- The weighted slope of a truncated tail has a bound independent of its horizon. -/
theorem integral_weighted_deriv_smoothTail_le {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    {B : ℝ} (hB : 0 ≤ B) (hsize : ∀ x, 0 ≤ x → |g x| * Real.exp (x / 2) ≤ B)
    (hint : IntegrableOn (fun x => |deriv g x| * Real.exp (x / 2)) (Ioi 0))
    {R : ℝ} (hR : 0 < R) :
    (∫ x in 0..R, |deriv (smoothTail g R) x| * Real.exp (x / 2)) ≤
      2 * B + ∫ x in Ioi (0 : ℝ), |deriv g x| * Real.exp (x / 2) := by
  have hd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hdc : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  have htc : Continuous (deriv (smoothTail g R)) :=
    (contDiff_smoothTail hg R).continuous_deriv (by norm_num)
  have hmain : (∫ x in 0..R, |deriv (smoothTail g R) x| * Real.exp (x / 2)) ≤
      ∫ x in 0..R, B * |smoothPlateauDeriv 0 R R⁻¹ x| +
        |deriv g x| * Real.exp (x / 2) := by
    apply intervalIntegral.integral_mono_on hR.le
      ((htc.abs.mul (by fun_prop)).intervalIntegrable _ _)
      (((continuous_const.mul continuous_smoothPlateauDeriv.abs).add
        (hdc.abs.mul (by fun_prop))).intervalIntegrable _ _)
    intro x hx
    change |deriv (smoothTail g R) x| * Real.exp (x / 2) ≤
      B * |smoothPlateauDeriv 0 R R⁻¹ x| + |deriv g x| * Real.exp (x / 2)
    rw [deriv_smoothTail hd]
    have h0 := tailPlateau_nonneg R x
    have h1 := tailPlateau_le_one R x
    have he := (Real.exp_pos (x / 2)).le
    calc
      _ ≤ (|smoothPlateauDeriv 0 R R⁻¹ x * g x| +
          |tailPlateau R x * deriv g x|) * Real.exp (x / 2) :=
        mul_le_mul_of_nonneg_right (abs_add_le _ _) he
      _ = |smoothPlateauDeriv 0 R R⁻¹ x| * (|g x| * Real.exp (x / 2)) +
          tailPlateau R x * (|deriv g x| * Real.exp (x / 2)) := by
        rw [abs_mul, abs_mul, abs_of_nonneg h0]
        ring
      _ ≤ |smoothPlateauDeriv 0 R R⁻¹ x| * B +
          1 * (|deriv g x| * Real.exp (x / 2)) :=
        add_le_add (mul_le_mul_of_nonneg_left (hsize x hx.1) (abs_nonneg _))
          (mul_le_mul_of_nonneg_right h1 (by positivity))
      _ = _ := by ring
  have hi₁ : IntervalIntegrable (fun x => B * |smoothPlateauDeriv 0 R R⁻¹ x|)
      volume 0 R :=
    (continuous_const.mul continuous_smoothPlateauDeriv.abs).intervalIntegrable _ _
  have hi₂ : IntervalIntegrable (fun x => |deriv g x| * Real.exp (x / 2))
      volume 0 R := (hdc.abs.mul (by fun_prop)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hi₁ hi₂, intervalIntegral.integral_const_mul] at hmain
  have hvar := integral_abs_smoothPlateauDeriv_le (a := 0) (b := R)
    (inv_pos.mpr hR) hR.le
  have htail : (∫ x in 0..R, |deriv g x| * Real.exp (x / 2)) ≤
      ∫ x in Ioi (0 : ℝ), |deriv g x| * Real.exp (x / 2) := by
    rw [intervalIntegral.integral_of_le hR.le]
    exact setIntegral_mono_set hint (Eventually.of_forall fun _ => by positivity)
      (Eventually.of_forall fun _ hx => hx.1)
  have hv := mul_le_mul_of_nonneg_left hvar hB
  linarith only [hmain, hv, htail]

private theorem deriv_smoothTail_zero {g : ℝ → ℝ} {R x : ℝ} (hR : 0 < R)
    (hx : x ∉ Icc 0 R) : deriv (smoothTail g R) x = 0 := by
  have he : smoothTail g R =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    have hh : x < 0 ∨ R < x := by simpa only [mem_Icc, not_and_or, not_le] using hx
    rcases hh with hx | hx
    · filter_upwards [Iio_mem_nhds hx] with y hy
      rw [smoothTail, tailPlateau_zero hR (Or.inl hy.le), zero_mul]
    · filter_upwards [Ioi_mem_nhds hx] with y hy
      rw [smoothTail, tailPlateau_zero hR (Or.inr hy.le), zero_mul]
  rw [he.deriv_eq, deriv_const]

/-- One integration by parts gives a uniform bound on the entire critical strip. -/
theorem norm_paperFT_smoothTail_le {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    {B : ℝ} (hB : 0 ≤ B) (hsize : ∀ x, 0 ≤ x → |g x| * Real.exp (x / 2) ≤ B)
    (hint : IntegrableOn (fun x => |deriv g x| * Real.exp (x / 2)) (Ioi 0))
    {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : |z.im| ≤ 1 / 2) (hz0 : z ≠ 0) :
    ‖Zeta23.paperFT (fun x => (smoothTail g R x : ℂ)) z‖ ≤
      (2 * B + ∫ x in Ioi (0 : ℝ), |deriv g x| * Real.exp (x / 2)) / ‖z‖ := by
  let f := smoothTail g R
  have hf : ContDiff ℝ 2 f := contDiff_smoothTail hg R
  have hfc : HasCompactSupport f := hasCompactSupport_smoothTail g hR
  have hc : ContDiff ℝ 2 (fun x => (f x : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hcc : HasCompactSupport (fun x => (f x : ℂ)) := hfc.comp_left Complex.ofReal_zero
  have hd : deriv (fun x => (f x : ℂ)) = fun x => ((deriv f x : ℝ) : ℂ) :=
    funext fun x => ((hf.differentiable (by norm_num)) x).hasDerivAt.ofReal_comp.deriv
  have hi : (∫ x, ‖deriv (fun y => (f y : ℂ)) x‖ * Real.exp ((1 / 2) * |x|)) =
      ∫ x in 0..R, |deriv f x| * Real.exp (x / 2) := by
    rw [hd]
    have he := (setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
      (s := Icc (0 : ℝ) R)
      (f := fun x => ‖((deriv f x : ℝ) : ℂ)‖ * Real.exp ((1 / 2) * |x|))
      (fun x hx => by
        rw [show deriv f x = 0 from deriv_smoothTail_zero hR hx]
        simp only [Complex.ofReal_zero, norm_zero, zero_mul])).symm
    rw [he, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hR.le]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hR.le] at hx
    change ‖((deriv f x : ℝ) : ℂ)‖ * Real.exp ((1 / 2) * |x|) =
      |deriv f x| * Real.exp (x / 2)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1]
    congr 2
    ring
  have hb := norm_paperFT_le_of_compact (hc.continuous_deriv (by norm_num)) hcc.deriv hz
  rw [paperFT_deriv_of_compact (hc.of_le (by norm_num)) hcc,
    norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul, hi] at hb
  have ht := integral_weighted_deriv_smoothTail_le hg hB hsize hint hR
  rw [le_div_iff₀ (norm_pos_iff.mpr hz0), mul_comm]
  exact hb.trans ht

/-- Truncation converges in every Fourier coordinate of the closed critical strip. -/
theorem tendsto_paperFT_smoothTail {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hint : IntegrableOn (fun x => |g x| * Real.exp (x / 2)) (Ioi 0))
    {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    Tendsto (fun R : ℝ => Zeta23.paperFT (fun x => (smoothTail g R x : ℂ)) z) atTop
      (𝓝 (∫ x in Ioi (0 : ℝ), (g x : ℂ) * Complex.exp (I * z * x))) := by
  have hdom (R x : ℝ) (hx : 0 < x) :
      ‖(smoothTail g R x : ℂ) * Complex.exp (I * z * x)‖ ≤
        |g x| * Real.exp (x / 2) := by
    have he : ‖Complex.exp (I * z * x)‖ ≤ Real.exp (x / 2) := by
      simpa only [abs_of_pos hx, one_div, inv_mul_eq_div] using
        norm_cexp_I_mul_le_of_abs_im_le hz x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, smoothTail, abs_mul,
      abs_of_nonneg (tailPlateau_nonneg R x)]
    have hg' : tailPlateau R x * |g x| ≤ |g x| :=
      mul_le_of_le_one_left (abs_nonneg _) (tailPlateau_le_one R x)
    exact mul_le_mul hg' he (norm_nonneg _) (abs_nonneg _)
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ))) (fun x => |g x| * Real.exp (x / 2))
    (F := fun R x : ℝ => (smoothTail g R x : ℂ) * Complex.exp (I * z * x))
    (f := fun x : ℝ => (g x : ℂ) * Complex.exp (I * z * x))
    (Eventually.of_forall fun R =>
      ((Complex.continuous_ofReal.comp (contDiff_smoothTail hg R).continuous).mul
        (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun R => by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact hdom R x hx)
    hint (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_tailPlateau_eq_one hx] with R hR
      simp only [smoothTail, hR, one_mul])
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
    rw [smoothTail, tailPlateau_zero hR (Or.inl (not_lt.mp hx)), zero_mul,
      Complex.ofReal_zero, zero_mul]

end GaloisForLFunctions.HodgeTheoryOfAFixedPart
