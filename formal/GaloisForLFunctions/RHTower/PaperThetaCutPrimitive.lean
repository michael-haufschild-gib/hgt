import GaloisForLFunctions.RHTower.PaperThetaStripControl
import GaloisForLFunctions.RHTower.PaperThetaForcedTail

/-! # The two-ended primitive of the charged theta kernel

Its jump is the complete Xi connection coefficient. Both branches have all
exponential moments, including at parameters outside the Xi divisor.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex

namespace RHTower.PaperThetaEndpoint
open HedenmalmThetaSource HedenmalmQuantile ThetaFiniteTransport

def cutPrimitive (z : ℂ) (x : ℝ) : ℂ :=
  if x < 0 then -flatPrimitiveMode (-z) (-x) else flatPrimitiveMode z x

theorem measurable_cutPrimitive (z : ℂ) : Measurable (cutPrimitive z) :=
  Measurable.ite measurableSet_Iio
    (((continuous_flatPrimitiveMode_all (-z)).comp continuous_neg).neg.measurable)
    (continuous_flatPrimitiveMode_all z).measurable

theorem cutPrimitive_source_formula (z : ℂ) (x : ℝ) :
    (thetaSource.normalized x : ℂ)*cutQuotient z 0 x =
      -(I*z)*cutPrimitive z x-thetaSource.normalized x := by
  have hρ : (thetaSource.normalized x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (thetaSource.normalized_pos x).ne'
  by_cases hx : x < 0
  · simp only [cutQuotient, cutPrimitive, leftQuotient, flatQuotient, flatMode,
      if_pos hx, normalized_reflection]
    field_simp
  · simp only [cutQuotient, cutPrimitive, flatQuotient, flatMode, if_neg hx]
    field_simp

theorem hasDerivAt_cutPrimitive {z : ℂ} {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (cutPrimitive z) ((thetaSource.normalized x : ℂ)*cutQuotient z 0 x) x := by
  rcases hx.lt_or_gt with hx | hx
  · have h := ((hasDerivAt_flatPrimitiveMode_all (-z) (-x)).scomp x (hasDerivAt_neg x)).neg
    simp only [neg_smul, one_smul, neg_neg] at h
    have he : cutPrimitive z =ᶠ[𝓝 x] fun y => -flatPrimitiveMode (-z) (-y) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact if_pos hy
    apply (h.congr_of_eventuallyEq he).congr_deriv
    rw [cutPrimitive_source_formula, cutPrimitive, if_pos hx, flatMode, normalized_reflection]
    ring
  · have he : cutPrimitive z =ᶠ[𝓝 x] flatPrimitiveMode z := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact if_neg (not_lt.mpr hy.le)
    apply ((hasDerivAt_flatPrimitiveMode_all z x).congr_of_eventuallyEq he).congr_deriv
    rw [cutPrimitive_source_formula, cutPrimitive, if_neg (not_lt.mpr hx.le), flatMode]

theorem tendsto_cutPrimitive_right (z : ℂ) :
    Tendsto (cutPrimitive z) (𝓝[>] (0 : ℝ)) (𝓝 (flatPrimitiveMode z 0)) := by
  apply ((continuous_flatPrimitiveMode_all z).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (if_neg (not_lt.mpr (show 0 ≤ x from hx.le))).symm

theorem tendsto_cutPrimitive_left (z : ℂ) :
    Tendsto (cutPrimitive z) (𝓝[<] (0 : ℝ)) (𝓝 (-flatPrimitiveMode (-z) 0)) := by
  have hc : Continuous (fun x : ℝ => -flatPrimitiveMode (-z) (-x)) := by
    have hp := continuous_flatPrimitiveMode_all (-z)
    fun_prop
  have h : Tendsto (fun x : ℝ => -flatPrimitiveMode (-z) (-x))
      (𝓝[<] (0 : ℝ)) (𝓝 (-flatPrimitiveMode (-z) 0)) := by
    simpa only [neg_zero] using hc.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[<] (0 : ℝ) ≤ 𝓝 0)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (if_pos hx).symm

theorem cutPrimitive_jump (z : ℂ) :
    flatPrimitiveMode z 0+flatPrimitiveMode (-z) 0 = flatConnection z := by
  simpa using flatPrimitiveMode_connection_reflection z 0

theorem norm_flatPrimitiveMode_strip {z : ℂ} {B : ℝ} (hz : -z.im ≤ B) (x : ℝ) :
    ‖flatPrimitiveMode z x‖ ≤ stripTailControl B x*thetaSource.normalized x := by
  have hρ := thetaSource.normalized_pos x
  have h : ‖flatPrimitiveMode z x/(thetaSource.normalized x : ℂ)‖ ≤
      stripTailControl B x := by
    rw [primitive_source_ratio]
    calc
      _ ≤ ∫ h in Ioi (0 : ℝ), ‖(sourceRatio h x : ℂ)*sourceChar z h‖ :=
        norm_integral_le_integral_norm _
      _ = stripTailControl (-z.im) x := by
        simp only [norm_sourceRatio_character, stripTailControl]
      _ ≤ _ := stripTailControl_mono hz x
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ] at h
  exact (div_le_iff₀ hρ).mp h

theorem norm_cutPrimitive_strip {z : ℂ} {B : ℝ} (hz : |z.im| ≤ B) (x : ℝ) :
    ‖cutPrimitive z x‖ ≤ stripTailControl B 0*thetaSource.normalized x := by
  by_cases hx : x < 0
  · rw [cutPrimitive, if_pos hx, norm_neg]
    have hn : -(-z).im ≤ B := by simpa using (le_abs_self z.im).trans hz
    have h := norm_flatPrimitiveMode_strip hn (-x)
    rw [normalized_reflection] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (stripTailControl_antitone B (show 0 ≤ -x by linarith)) (thetaSource.normalized_pos x).le)
  · rw [cutPrimitive, if_neg hx]
    exact (norm_flatPrimitiveMode_strip ((neg_le_abs z.im).trans hz) x).trans
      (mul_le_mul_of_nonneg_right (stripTailControl_antitone B (le_of_not_gt hx))
        (thetaSource.normalized_pos x).le)

theorem norm_sourceChar_cutPrimitive (z w : ℂ) (x : ℝ) :
    ‖sourceChar w x*cutPrimitive z x‖ ≤ stripTailControl |z.im| 0*‖flatCharDensity w x‖ := by
  rw [norm_mul, norm_sourceChar, norm_flatCharDensity]
  have h := mul_le_mul_of_nonneg_left (norm_cutPrimitive_strip (z := z) le_rfl x)
    (Real.exp_nonneg (-w.im*x))
  exact h.trans_eq (by ring)

theorem integrable_sourceChar_cutPrimitive (z w : ℂ) :
    Integrable (fun x => sourceChar w x*cutPrimitive z x) :=
  ((integrable_flatCharDensity_all w).norm.const_mul (stripTailControl |z.im| 0)).mono'
    ((continuous_sourceChar w).aestronglyMeasurable.mul
      (measurable_cutPrimitive z).aestronglyMeasurable)
    (Eventually.of_forall (norm_sourceChar_cutPrimitive z w))

theorem integrable_flatCharDensity_cutQuotient (z w : ℂ) :
    Integrable (fun x => flatCharDensity w x*cutQuotient z 0 x) := by
  have hb : ∀ᵐ x : ℝ, ‖cutQuotient z 0 x‖ ≤ ‖z‖*stripTailControl |z.im| 0+1 := by
    filter_upwards [] with x
    have h := cutQuotient_add_one_strip (z := z) le_rfl x
    have ht := norm_sub_le (cutQuotient z 0 x+1) (1 : ℂ)
    rw [add_sub_cancel_right, norm_one] at ht
    linarith
  exact (integrable_flatCharDensity_all w).mul_bdd
    (measurable_cutQuotient z 0).aestronglyMeasurable hb

theorem tendsto_norm_flatCharDensity_atBot (w : ℂ) :
    Tendsto (fun x => ‖flatCharDensity w x‖) atBot (𝓝 0) := by
  simpa only [norm_flatCharDensity] using tendsto_normalized_mul_exp_atBot_all w.im

theorem tendsto_norm_flatCharDensity_atTop (w : ℂ) :
    Tendsto (fun x => ‖flatCharDensity w x‖) atTop (𝓝 0) := by
  have h := (tendsto_normalized_mul_exp_atBot_all (-w.im)).comp tendsto_neg_atTop_atBot
  simpa only [Function.comp_def, normalized_reflection, neg_neg, mul_neg,
    norm_flatCharDensity, neg_mul] using h

theorem tendsto_sourceChar_cutPrimitive_atBot (z w : ℂ) :
    Tendsto (fun x => sourceChar w x*cutPrimitive z x) atBot (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (norm_sourceChar_cutPrimitive z w)
  simpa only [mul_zero] using
    (tendsto_norm_flatCharDensity_atBot w).const_mul (stripTailControl |z.im| 0)

theorem tendsto_sourceChar_cutPrimitive_atTop (z w : ℂ) :
    Tendsto (fun x => sourceChar w x*cutPrimitive z x) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (norm_sourceChar_cutPrimitive z w)
  simpa only [mul_zero] using
    (tendsto_norm_flatCharDensity_atTop w).const_mul (stripTailControl |z.im| 0)

end RHTower.PaperThetaEndpoint
