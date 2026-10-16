import GaloisForLFunctions.RHTower.PaperThetaSourceRatio
import Mathlib.Analysis.Complex.Liouville

/-! # Entire parameter dependence before singular quantile transport

The literal right-tail quotient is entire at each source coordinate. The
proof uses the actual source ratio and its unconditional exponential moments.
This is the analytic input for admitting parameter jets in native variation.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex

namespace RHTower.PaperThetaEndpoint
open HedenmalmQuantile ThetaFiniteTransport

theorem continuous_sourceRatio_shift (x : ℝ) : Continuous (fun h => sourceRatio h x) := by
  unfold sourceRatio
  exact (continuous_thetaCuspFullSource.comp (continuous_id.add continuous_const)).div_const _

theorem differentiable_sourceRatio_integral (x : ℝ) :
    Differentiable ℂ (fun z =>
      ∫ h in Ioi (0 : ℝ), (sourceRatio h x : ℂ) * sourceChar z h) := by
  intro z
  let F : ℂ → ℝ → ℂ := fun w h => (sourceRatio h x : ℂ) * sourceChar w h
  let F' : ℂ → ℝ → ℂ := fun w h =>
    (sourceRatio h x : ℂ) * (I * (h : ℂ) * sourceChar w h)
  let B : ℝ := |z.im| + 2
  have hmeas (w : ℂ) : Continuous (F w) := by
    exact (Complex.continuous_ofReal.comp (continuous_sourceRatio_shift x)).mul
      (continuous_sourceChar w)
  have hmeas' : Continuous (F' z) := by
    exact (Complex.continuous_ofReal.comp (continuous_sourceRatio_shift x)).mul
      ((continuous_const.mul Complex.continuous_ofReal).mul (continuous_sourceChar z))
  have hbound : ∀ᵐ h ∂volume.restrict (Ioi (0 : ℝ)), ∀ w ∈ Metric.ball z 1,
      ‖F' w h‖ ≤ sourceRatio h x * Real.exp (B*h) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    intro w hw
    have hd : ‖w-z‖ < 1 := by simpa only [dist_eq_norm] using Metric.mem_ball.mp hw
    have hh0 : 0 < h := hh
    have him : |w.im-z.im| ≤ ‖w-z‖ := by
      simpa only [Complex.sub_im] using Complex.abs_im_le_norm (w-z)
    have hi : -w.im ≤ |z.im|+1 := by
      have hz := neg_abs_le z.im
      have hwz := neg_abs_le (w.im-z.im)
      linarith
    have he : h ≤ Real.exp h := by linarith [Real.add_one_le_exp h]
    have hn : ‖F' w h‖ = sourceRatio h x * (h * Real.exp (-w.im*h)) := by
      simp only [F', norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (sourceRatio_pos h x), abs_of_pos hh0,
        norm_sourceChar]
    rw [hn]
    apply mul_le_mul_of_nonneg_left _ (sourceRatio_pos h x).le
    calc
      h * Real.exp (-w.im*h) ≤ Real.exp h * Real.exp ((|z.im|+1)*h) :=
        mul_le_mul he (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hi hh.le))
          (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp (B*h) := by rw [← Real.exp_add]; congr 1; dsimp [B]; ring
  have hdiff : ∀ᵐ h ∂volume.restrict (Ioi (0 : ℝ)), ∀ w ∈ Metric.ball z 1,
      HasDerivAt (fun w => F w h) (F' w h) w := by
    filter_upwards [] with h
    intro w _
    have hd := (((hasDerivAt_id w).const_mul I).mul_const (h : ℂ)).cexp
    exact (hd.const_mul (sourceRatio h x : ℂ)).congr_deriv (by
      simp [F', sourceChar, mul_assoc, mul_comm, mul_left_comm])
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (Metric.ball_mem_nhds z one_pos)
    (Eventually.of_forall fun w => (hmeas w).aestronglyMeasurable)
    (integrable_sourceRatio_character z x).integrableOn hmeas'.aestronglyMeasurable
    hbound (integrable_sourceRatio_tilt B x).integrableOn hdiff).2.differentiableAt

/-- Entire dependence belongs to the original quotient, not a surrogate transform. -/
theorem differentiable_flatQuotient_parameter (x : ℝ) :
    Differentiable ℂ (fun z => flatQuotient z x) := by
  have he : (fun z => flatQuotient z x) = fun z =>
      -(I*z) * (∫ h in Ioi (0 : ℝ), (sourceRatio h x : ℂ)*sourceChar z h) - 1 := by
    funext z
    linear_combination flatQuotient_eq_sourceRatio_integral z x
  rw [he]
  exact (((differentiable_const I).mul differentiable_id).neg.mul
    (differentiable_sourceRatio_integral x)).sub_const _

end RHTower.PaperThetaEndpoint
