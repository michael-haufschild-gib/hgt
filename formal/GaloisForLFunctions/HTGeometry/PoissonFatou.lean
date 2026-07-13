import Mathlib.Analysis.Complex.Poisson
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Fatou's theorem: a.e. boundary limits of Poisson integrals

The Poisson integral of an `L¹` function on the circle converges almost everywhere to the function
as the radius tends to `1`.  This is the analytic crux of the Szegő outer function's boundary
identity `|D|² = w` (and hence of the upper bound half of the first Szegő limit theorem).  mathlib
supplies the Poisson kernel with its pointwise bounds and normalization (via the Poisson
representation of continuous functions) and the Lebesgue differentiation theorem; this module builds
the a.e. boundary convergence on top of them.

This file develops the angular Poisson kernel `P_r(t) = (1-r²)/(1 - 2r cos t + r²)` and its
elementary estimates.
-/

namespace GaloisForLFunctions.HTGeometry

open Real MeasureTheory Complex intervalIntegral Metric
open scoped Real

/-- The angular Poisson kernel `P_r(t) = (1-r²)/(1 - 2r cos t + r²)`. -/
noncomputable def poissonKer (r t : ℝ) : ℝ := (1 - r ^ 2) / (1 - 2 * r * Real.cos t + r ^ 2)

/-- The Poisson kernel denominator is strictly positive for `|r| < 1`. -/
theorem poissonKer_denom_pos {r : ℝ} (hr : |r| < 1) (t : ℝ) :
    0 < 1 - 2 * r * Real.cos t + r ^ 2 := by
  have hrc : r * Real.cos t ≤ |r| := by
    calc r * Real.cos t ≤ |r * Real.cos t| := le_abs_self _
      _ = |r| * |Real.cos t| := abs_mul r _
      _ ≤ |r| * 1 := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg r); exact Real.abs_cos_le_one t
      _ = |r| := mul_one _
  have hrr : r ^ 2 = |r| ^ 2 := (sq_abs r).symm
  have hp : 0 < 1 - |r| := by linarith
  nlinarith [hrc, hrr, mul_pos hp hp]

/-- The Poisson kernel is nonnegative for `0 ≤ r < 1`. -/
theorem poissonKer_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    0 ≤ poissonKer r t := by
  rw [poissonKer]
  apply div_nonneg
  · nlinarith
  · exact (poissonKer_denom_pos (by rw [abs_of_nonneg hr0]; exact hr1) t).le

/-- The Poisson kernel denominator equals `‖e^{it} - r‖²`. -/
theorem poissonKer_denom_eq (r t : ℝ) :
    1 - 2 * r * Real.cos t + r ^ 2 = ‖Complex.exp (t * Complex.I) - (r : ℂ)‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im]
  nlinarith [Real.sin_sq_add_cos_sq t]

/-- Uniform upper bound: `P_r(t) ≤ (1+r)/(1-r)`, attained at `t = 0`. -/
theorem poissonKer_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    poissonKer r t ≤ (1 + r) / (1 - r) := by
  rw [poissonKer]
  have hden : 0 < 1 - 2 * r * Real.cos t + r ^ 2 :=
    poissonKer_denom_pos (by rw [abs_of_nonneg hr0]; exact hr1) t
  have hden' : (1 - r) ^ 2 ≤ 1 - 2 * r * Real.cos t + r ^ 2 := by
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr (Real.cos_le_one t))]
  rw [div_le_div_iff₀ hden (by linarith : (0:ℝ) < 1 - r)]
  nlinarith [mul_le_mul_of_nonneg_left hden' (show (0:ℝ) ≤ 1 + r by linarith)]

/-- The angular Poisson kernel is mathlib's geometric Poisson kernel at a real disk point. -/
theorem poissonKer_eq_poissonKernel {r : ℝ} (hr0 : 0 ≤ r) (t : ℝ) :
    poissonKer r t = poissonKernel 0 (r : ℂ) (Complex.exp (t * Complex.I)) := by
  rw [poissonKernel_def, poissonKer, poissonKer_denom_eq r t]
  simp only [sub_zero, Complex.norm_exp_ofReal_mul_I]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  ring_nf

/-- **Normalization of the Poisson kernel**: `∫₀²π P_r(t) dt = 2π`.  Obtained from mathlib's Poisson
representation applied to the constant function `1`. -/
theorem poissonKer_integral {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫ t in (0:ℝ)..(2 * π), poissonKer r t = 2 * π := by
  have hw : (r : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
  have hf : DiffContOnCl ℂ (fun _ : ℂ => (1 : ℂ)) (ball 0 1) :=
    (differentiable_const (1 : ℂ)).differentiableOn.diffContOnCl
  have hrep := hf.circleAverage_poissonKernel_smul hw
  have hfun : (poissonKernel 0 (r : ℂ) • (fun _ : ℂ => (1 : ℂ)))
      = fun z => ((poissonKernel 0 (r : ℂ) z : ℝ) : ℂ) := by
    funext z; rw [Pi.smul_apply', Complex.real_smul, mul_one]
  rw [hfun, Real.circleAverage] at hrep
  have hcm : ∀ θ : ℝ, poissonKernel 0 (r : ℂ) (circleMap 0 1 θ) = poissonKer r θ := by
    intro θ
    rw [poissonKer_eq_poissonKernel hr0]
    congr 1
    simp [circleMap]
  simp_rw [hcm] at hrep
  rw [intervalIntegral.integral_ofReal] at hrep
  have hr : (2 * π)⁻¹ * (∫ θ in (0:ℝ)..(2 * π), poissonKer r θ) = 1 := by
    have := hrep
    rw [Complex.real_smul, ← Complex.ofReal_mul] at this
    exact_mod_cast this
  have hpi : (2 * π) ≠ 0 := by positivity
  field_simp at hr
  linarith [hr]

end GaloisForLFunctions.HTGeometry
