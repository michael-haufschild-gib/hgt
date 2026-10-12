import GaloisForLFunctions.HTGeometry.GaussianQuadraticExponential
import Mathlib.MeasureTheory.Measure.Tilted

/-! A centered Gaussian quadratic tilt changes its precision exactly. -/

open MeasureTheory ProbabilityTheory

namespace GaloisForLFunctions.HTGeometry

theorem gaussianZero_precision_tilt_integral (v w : NNReal) (hv : v ≠ 0) (hw : w ≠ 0) :
    (∫ x : ℝ, Real.exp ((1 / (2 * (v : ℝ)) - 1 / (2 * (w : ℝ))) * x ^ 2)
      ∂(gaussianReal 0 v)) = Real.sqrt ((w : ℝ) / v) := by
  have hvpos : (0 : ℝ) < v := by exact_mod_cast (pos_iff_ne_zero.mpr hv : 0 < v)
  have hwpos : (0 : ℝ) < w := by exact_mod_cast (pos_iff_ne_zero.mpr hw : 0 < w)
  rw [gaussianZero_integral_exp_quadratic v hv]
  congr 1
  field_simp [hvpos.ne', hwpos.ne']
  ring

theorem gaussianPDF_precision_tilt (v w : NNReal) (hv : v ≠ 0) (hw : w ≠ 0) (x : ℝ) :
    gaussianPDFReal 0 v x * Real.exp ((1 / (2 * (v : ℝ)) - 1 / (2 * (w : ℝ))) * x ^ 2) =
      Real.sqrt ((w : ℝ) / v) * gaussianPDFReal 0 w x := by
  have hvpos : (0 : ℝ) < v := by exact_mod_cast (pos_iff_ne_zero.mpr hv : 0 < v)
  have hwpos : (0 : ℝ) < w := by exact_mod_cast (pos_iff_ne_zero.mpr hw : 0 < w)
  have hc : (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ =
      Real.sqrt ((w : ℝ) / v) * (Real.sqrt (2 * Real.pi * (w : ℝ)))⁻¹ := by
    rw [← Real.sqrt_inv, ← Real.sqrt_inv,
      ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (w : ℝ) / v)]
    congr 1
    field_simp [hvpos.ne', hwpos.ne', Real.pi_ne_zero]
  rw [gaussianPDF_mul_exp_quadratic, sub_sub_cancel, gaussianPDFReal, sub_zero, hc, mul_assoc]
  rw [show -(1 / (2 * (w : ℝ))) * x ^ 2 = -x ^ 2 / (2 * (w : ℝ)) by ring]

theorem gaussianZero_quadratic_tilt_precision_change
    (v w : NNReal) (hv : v ≠ 0) (hw : w ≠ 0) :
    (gaussianReal 0 v).tilted (fun x : ℝ =>
      (1 / (2 * (v : ℝ)) - 1 / (2 * (w : ℝ))) * x ^ 2) = gaussianReal 0 w := by
  have hvpos : (0 : ℝ) < v := by exact_mod_cast (pos_iff_ne_zero.mpr hv : 0 < v)
  have hwpos : (0 : ℝ) < w := by exact_mod_cast (pos_iff_ne_zero.mpr hw : 0 < w)
  have hZ : Real.sqrt ((w : ℝ) / v) ≠ 0 := ne_of_gt (by positivity)
  rw [Measure.tilted, gaussianZero_precision_tilt_integral v w hv hw,
    gaussianReal_of_var_ne_zero 0 hv, gaussianReal_of_var_ne_zero 0 hw,
    ← withDensity_mul volume (measurable_gaussianPDF 0 v) (by fun_prop)]
  apply withDensity_congr_ae
  refine Filter.Eventually.of_forall fun x => ?_
  change ENNReal.ofReal (gaussianPDFReal 0 v x) * ENNReal.ofReal
    (Real.exp ((1 / (2 * (v : ℝ)) - 1 / (2 * (w : ℝ))) * x ^ 2) /
      Real.sqrt ((w : ℝ) / v)) = ENNReal.ofReal (gaussianPDFReal 0 w x)
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 v x)]
  congr 1
  rw [← mul_div_assoc, gaussianPDF_precision_tilt v w hv hw x]
  field_simp

end GaloisForLFunctions.HTGeometry
