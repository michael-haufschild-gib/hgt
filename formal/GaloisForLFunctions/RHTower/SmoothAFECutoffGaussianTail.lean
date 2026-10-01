import GaloisForLFunctions.RHTower.HighBlockCutoffMonotone
import GaloisForLFunctions.RHTower.SmoothAFECutoffBounds
import Mathlib.MeasureTheory.Integral.IntegralEqImproper


open Filter Topology MeasureTheory
noncomputable section
namespace RHTower

/-- The cutoff derivative on logarithmic scale is the negative Gaussian density. -/
theorem hasDerivAt_smoothAFECutoff_exp_re (x : ℝ) :
    HasDerivAt (fun y : ℝ => (smoothAFECutoff (Real.exp y)).re)
      (-(Real.exp (-x ^ 2 / 4) / (2 * Real.sqrt Real.pi))) x := by
  have h := (hasDerivAt_smoothAFECutoff_re (Real.exp_pos x)).comp x (Real.hasDerivAt_exp x)
  change HasDerivAt ((fun y : ℝ => (smoothAFECutoff y).re) ∘ Real.exp) _ x
  apply h.congr_deriv
  dsimp only [smoothAFECutoffDeriv]
  rw [Real.log_exp]
  field_simp [Real.exp_ne_zero]

/-- The actual cutoff tends to zero at the upper endpoint on logarithmic scale. -/
theorem tendsto_smoothAFECutoff_exp_re_zero :
    Tendsto (fun x : ℝ => (smoothAFECutoff (Real.exp x)).re) atTop (𝓝 0) := by
  obtain ⟨C, _hC, hbound⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (by norm_num : (0 : ℝ) < 1)
  have hlim : Tendsto (fun x : ℝ => C / Real.exp x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_exp_atTop
  apply squeeze_zero' (Filter.Eventually.of_forall (fun x =>
    smoothAFECutoff_re_nonneg (Real.exp_pos x))) ?_ hlim
  apply Filter.Eventually.of_forall
  intro x
  exact (Complex.re_le_norm _).trans (by
    simpa only [Real.rpow_neg_one, div_eq_mul_inv] using hbound (Real.exp_pos x))

/-- The literal real cutoff is exactly a Gaussian upper-tail integral. -/
theorem smoothAFECutoff_exp_re_eq_gaussian_tail (x : ℝ) :
    (smoothAFECutoff (Real.exp x)).re =
      ∫ y in Set.Ioi x, Real.exp (-y ^ 2 / 4) / (2 * Real.sqrt Real.pi) := by
  have h := integral_Ioi_of_hasDerivAt_of_nonpos'
    (fun y (_hy : y ∈ Set.Ici x) => hasDerivAt_smoothAFECutoff_exp_re y)
    (fun y (_hy : y ∈ Set.Ioi x) => show
      -(Real.exp (-y ^ 2 / 4) / (2 * Real.sqrt Real.pi)) ≤ 0 by
        have hp := Real.sqrt_pos.mpr Real.pi_pos
        exact neg_nonpos.mpr (by positivity))
    tendsto_smoothAFECutoff_exp_re_zero
  rw [integral_neg, zero_sub] at h
  linarith

/-- Exact Gaussian averaging formula for the complex-valued inverse-Mellin cutoff. -/
theorem smoothAFECutoff_exp_eq_gaussian_tail (x : ℝ) :
    smoothAFECutoff (Real.exp x) =
      ((∫ y in Set.Ioi x, Real.exp (-y ^ 2 / 4) / (2 * Real.sqrt Real.pi) : ℝ) : ℂ) := by
  apply Complex.ext
  · simpa only [Complex.ofReal_re] using smoothAFECutoff_exp_re_eq_gaussian_tail x
  · simp only [smoothAFECutoff_im_eq_zero (Real.exp_pos x), Complex.ofReal_im]

end RHTower
