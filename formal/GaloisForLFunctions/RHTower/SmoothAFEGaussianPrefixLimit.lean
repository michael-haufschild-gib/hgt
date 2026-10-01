import GaloisForLFunctions.RHTower.SmoothAFELogGaussianMoment
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.Floor


open MeasureTheory Filter Topology
noncomputable section
namespace RHTower

private theorem exp_real_cpow (y : ℝ) (z : ℂ) :
    (Real.exp y : ℂ) ^ z = Complex.exp (z * (y : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero y)),
    ← Complex.ofReal_log (Real.exp_pos y).le, Real.log_exp, mul_comm]

private theorem scaled_cpow_cancel {R : ℝ} (hR : 0 < R) (y : ℝ) (z : ℂ) :
    ((R * Real.exp y : ℝ) : ℂ) ^ (-z) * Complex.exp (z * (y : ℂ)) =
      (R : ℂ) ^ (-z) := by
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hR.le (Real.exp_pos y).le,
    mul_assoc, Complex.cpow_neg (Real.exp y : ℂ) z, exp_real_cpow,
    inv_mul_cancel₀ (Complex.exp_ne_zero _), mul_one]

private theorem normalized_prefix_tendsto {P : ℕ → ℂ} {z L : ℂ}
    (hlim : Tendsto (fun x : ℝ => P ⌊x⌋₊ * (x : ℂ) ^ (-z)) atTop (𝓝 L))
    (y : ℝ) :
    Tendsto (fun R : ℝ => P ⌊R * Real.exp y⌋₊ * (R : ℂ) ^ (-z)) atTop
      (𝓝 (L * Complex.exp (z * (y : ℂ)))) := by
  have h := (hlim.comp ((tendsto_id : Tendsto (fun R : ℝ => R) atTop atTop).atTop_mul_const (Real.exp_pos y))).mul_const (Complex.exp (z * (y : ℂ)))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  dsimp only [Function.comp_apply, id]
  rw [mul_assoc, scaled_cpow_cancel hR]

private theorem normalized_prefix_bound {P : ℕ → ℂ} {z : ℂ} {C : ℝ}
    (hbound : ∀ x : ℝ, 0 ≤ x → ‖P ⌊x⌋₊‖ ≤ C * x ^ z.re)
    {R : ℝ} (hR : 0 < R) (y : ℝ) :
    ‖P ⌊R * Real.exp y⌋₊ * (R : ℂ) ^ (-z)‖ ≤ C * Real.exp (z.re * y) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hR, Complex.neg_re]
  calc
    _ ≤ (C * (R * Real.exp y) ^ z.re) * R ^ (-z.re) :=
      mul_le_mul_of_nonneg_right (hbound _ (by positivity)) (Real.rpow_nonneg hR.le _)
    _ = C * Real.exp (z.re * y) := by
      rw [Real.mul_rpow hR.le (Real.exp_pos y).le, ← Real.exp_mul,
        Real.rpow_neg hR.le]
      have hn := (Real.rpow_pos_of_pos hR z.re).ne'
      field_simp [hn]

/-- A Gaussian average preserves every power-normalized sharp-prefix limit, with its exact
complex Gaussian moment. The all-cutoff power bound supplies the integrable majorant. -/
theorem tendsto_logGaussian_prefix_integral
    (P : ℕ → ℂ) (z L : ℂ) {C : ℝ}
    (hlim : Tendsto (fun x : ℝ => P ⌊x⌋₊ * (x : ℂ) ^ (-z)) atTop (𝓝 L))
    (hbound : ∀ x : ℝ, 0 ≤ x → ‖P ⌊x⌋₊‖ ≤ C * x ^ z.re) :
    Tendsto (fun R : ℝ =>
      (∫ y : ℝ, (smoothAFELogGaussian y : ℂ) * P ⌊R * Real.exp y⌋₊) *
        (R : ℂ) ^ (-z)) atTop (𝓝 (L * Complex.exp (z ^ 2))) := by
  let F : ℝ → ℝ → ℂ := fun R y =>
    (smoothAFELogGaussian y : ℂ) * (P ⌊R * Real.exp y⌋₊ * (R : ℂ) ^ (-z))
  let f : ℝ → ℂ := fun y =>
    (smoothAFELogGaussian y : ℂ) * (L * Complex.exp (z * (y : ℂ)))
  let bound : ℝ → ℝ := fun y => C * (smoothAFELogGaussian y * Real.exp (z.re * y))
  have hphi : Continuous smoothAFELogGaussian := by
    unfold smoothAFELogGaussian
    fun_prop
  have hmeas (R : ℝ) : AEStronglyMeasurable (F R) := by
    have hprefix : Measurable (fun y : ℝ => P ⌊R * Real.exp y⌋₊) :=
      measurable_from_nat.comp
        ((measurable_const.mul Real.continuous_exp.measurable).nat_floor)
    exact (hphi.measurable.complex_ofReal.mul
      (hprefix.mul_const ((R : ℂ) ^ (-z)))).aestronglyMeasurable
  have hdom : ∀ᶠ R : ℝ in atTop, ∀ᵐ y : ℝ, ‖F R y‖ ≤ bound y := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    filter_upwards with y
    have hp : 0 ≤ smoothAFELogGaussian y := by unfold smoothAFELogGaussian; positivity
    dsimp only [F, bound]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]
    exact (mul_le_mul_of_nonneg_left (normalized_prefix_bound hbound hR y) hp).trans_eq
      (by ring)
  have hpoint : ∀ᵐ y : ℝ, Tendsto (fun R => F R y) atTop (𝓝 (f y)) := by
    filter_upwards with y
    exact (normalized_prefix_tendsto hlim y).const_mul (smoothAFELogGaussian y : ℂ)
  have h := tendsto_integral_filter_of_dominated_convergence bound
    (Eventually.of_forall hmeas) hdom
    ((integrable_smoothAFELogGaussian_mul_real_exp z.re).const_mul C) hpoint
  have hleft (R : ℝ) : (∫ y : ℝ, F R y) =
      (∫ y : ℝ, (smoothAFELogGaussian y : ℂ) * P ⌊R * Real.exp y⌋₊) *
        (R : ℂ) ^ (-z) := by
    simp only [F, ← mul_assoc, integral_mul_const]
  have hright : (∫ y : ℝ, f y) = L * Complex.exp (z ^ 2) := by
    calc
      _ = L * ∫ y : ℝ, (smoothAFELogGaussian y : ℂ) * Complex.exp (z * (y : ℂ)) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with y
        dsimp only [f]
        ring
      _ = _ := by rw [integral_smoothAFELogGaussian_mul_exp]
  simpa only [hleft, hright] using h

end RHTower
