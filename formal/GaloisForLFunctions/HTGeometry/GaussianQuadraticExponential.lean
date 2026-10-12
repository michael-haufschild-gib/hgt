import Mathlib.Probability.Distributions.Gaussian.Real

/-! Exact quadratic exponential integrability for a centered Gaussian and
subcritical envelopes with an additional linear absolute-value term. -/

open MeasureTheory ProbabilityTheory Filter

namespace GaloisForLFunctions.HTGeometry

theorem gaussianReal_integrable_iff_pdf_mul (m : ℝ) (v : NNReal) (hv : v ≠ 0) (f : ℝ → ℝ) :
    Integrable f (gaussianReal m v) ↔ Integrable (fun x => gaussianPDFReal m v x * f x) := by
  rw [gaussianReal_of_var_ne_zero m hv,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF m v)
      (Eventually.of_forall fun _ => gaussianPDF_lt_top)]
  simp only [toReal_gaussianPDF, smul_eq_mul]

theorem integrable_exp_neg_quadratic_abs_linear {b : ℝ} (hb : 0 < b) (a : ℝ) :
    Integrable (fun x : ℝ => Real.exp (-b * x ^ 2 + a * |x|)) := by
  have hbase := (integrable_exp_neg_mul_sq (half_pos hb)).const_mul (Real.exp (a ^ 2 / (2 * b)))
  apply hbase.mono' (by fun_prop)
  exact Eventually.of_forall fun x => by
    have hsq := sq_nonneg (b * |x| - a)
    simp only [sub_sq, mul_pow, sq_abs] at hsq
    have hy : (a * |x| - b / 2 * x ^ 2) * (2 * b) ≤ a ^ 2 := by nlinarith only [hsq]
    have hy' := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * b)).mpr hy
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith only [hy']

theorem gaussianPDF_mul_exp_quadratic (v : NNReal) (c x : ℝ) :
    gaussianPDFReal 0 v x * Real.exp (c * x ^ 2) =
      (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(1 / (2 * (v : ℝ)) - c) * x ^ 2) := by
  rw [gaussianPDFReal, sub_zero, mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem gaussianZero_integrable_exp_quadratic_iff (v : NNReal) (hv : v ≠ 0) (c : ℝ) :
    Integrable (fun x : ℝ => Real.exp (c * x ^ 2)) (gaussianReal 0 v) ↔
      c < 1 / (2 * (v : ℝ)) := by
  have hvpos : (0 : ℝ) < v := by exact_mod_cast (pos_iff_ne_zero.mpr hv : 0 < v)
  rw [gaussianReal_integrable_iff_pdf_mul 0 v hv]
  simp_rw [gaussianPDF_mul_exp_quadratic]
  rw [integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (by positivity))]
  rw [integrable_exp_neg_mul_sq_iff]
  exact sub_pos

theorem gaussianZero_integral_exp_quadratic (v : NNReal) (hv : v ≠ 0) (c : ℝ) :
    (∫ x : ℝ, Real.exp (c * x ^ 2) ∂(gaussianReal 0 v)) =
      Real.sqrt (1 / (1 - 2 * (v : ℝ) * c)) := by
  have hvpos : (0 : ℝ) < v := by exact_mod_cast (pos_iff_ne_zero.mpr hv : 0 < v)
  have hvne : (v : ℝ) ≠ 0 := ne_of_gt hvpos
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp_rw [smul_eq_mul, gaussianPDF_mul_exp_quadratic]
  rw [integral_const_mul, integral_gaussian, ← Real.sqrt_inv,
    ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 * Real.pi * v)⁻¹)]
  congr 1
  have hden : 1 / (2 * (v : ℝ)) - c = (1 - 2 * (v : ℝ) * c) / (2 * (v : ℝ)) := by
    field_simp
  rw [hden, div_div_eq_mul_div, ← mul_div_assoc]
  have hcancel : (2 * Real.pi * (v : ℝ))⁻¹ * (Real.pi * (2 * (v : ℝ))) = 1 := by
    field_simp [Real.pi_ne_zero, hvne]
  rw [hcancel]

theorem gaussianZero_integrable_exp_abs_add_quadratic (v : NNReal) (hv : v ≠ 0)
    (a c : ℝ) (hc : c < 1 / (2 * (v : ℝ))) :
    Integrable (fun x : ℝ => Real.exp (a * |x| + c * x ^ 2)) (gaussianReal 0 v) := by
  rw [gaussianReal_integrable_iff_pdf_mul 0 v hv]
  have hform : (fun x : ℝ => gaussianPDFReal 0 v x * Real.exp (a * |x| + c * x ^ 2)) =
      (fun x : ℝ => (Real.sqrt (2 * Real.pi * v))⁻¹ *
        Real.exp (-(1 / (2 * (v : ℝ)) - c) * x ^ 2 + a * |x|)) := by
    funext x
    rw [gaussianPDFReal, sub_zero, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hform]
  exact (integrable_exp_neg_quadratic_abs_linear (sub_pos.mpr hc) a).const_mul _

end GaloisForLFunctions.HTGeometry
