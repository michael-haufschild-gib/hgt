import GaloisForLFunctions.RHTower.ThetaCuspRatioUpperSeamPower
import GaloisForLFunctions.RHTower.ThetaCuspRatioUpperCenterComplexIdentity

namespace RHTower.ThetaCuspUpperSeam
noncomputable section
set_option autoImplicit false
open MvPolynomial HTGeometry.ThetaRatioSource HTGeometry.ThetaRatioWeightedSquare
open HTGeometry.ThetaRatioInfinity ThetaCuspModularRatio

def reducedSeamNormalizer (x : ℝ) : ℝ :=
  (6:ℝ)^30*(k x-1/6)^7*(x/u x)

theorem actual_upper_core_quadratic_complex (eta : ℝ) {x : ℝ} (hx : 0 < x) :
    eval (actualSquarePoint x) (upperQuadraticCore (10000000000000:ℂ) (eta:ℂ))=
      ((reducedSeamNormalizer x*(scaledUpperA x+2*scaledB x*eta+scaledD x*eta^2):ℝ):ℂ) := by
  have hu : (u x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx)).ne'
  apply mul_left_cancel₀ (pow_ne_zero 26 hu)
  calc
    _ = eval (actualSquarePoint x) (upperCenterQuadratic (10000000000000:ℂ) (eta:ℂ)) := by
      rw [upper_quadratic_core_eq,map_mul,map_pow,eval_X]
      change (u x:ℂ)^26*_ = ((u x:ℂ)^2)^13*_
      ring
    _ = _ := by
      rw [actual_upper_quadratic_scaled_complex eta hx]
      unfold endpointNormalizer reducedSeamNormalizer
      push_cast
      field_simp [hu]

private theorem actual_upper_constant_core_complex {x : ℝ} (hx : 0 < x) :
    eval (actualSquarePoint x) (upperConstantCore (10000000000000:ℂ))=
      ((reducedSeamNormalizer x*scaledUpperA x:ℝ):ℂ) := by
  simpa only [upperConstantCore,Complex.ofReal_zero,mul_zero,
    zero_pow (by omega : (2:ℕ)≠0),add_zero] using
    actual_upper_core_quadratic_complex 0 hx

private theorem actual_upper_border_core_complex {x : ℝ} (hx : 0 < x) :
    eval (actualSquarePoint x) (upperBorderCore (10000000000000:ℂ))=
      ((reducedSeamNormalizer x*scaledB x:ℝ):ℂ) := by
  simp only [upperBorderCore,map_mul,map_sub,eval_C]
  have h1 := actual_upper_core_quadratic_complex 1 hx
  have hn := actual_upper_core_quadratic_complex (-1) hx
  simp only [Complex.ofReal_one,Complex.ofReal_neg] at h1 hn
  rw [h1,hn]
  push_cast
  ring

private theorem actual_upper_last_core_complex {x : ℝ} (hx : 0 < x) :
    eval (actualSquarePoint x) (upperLastCore (10000000000000:ℂ))=
      ((reducedSeamNormalizer x*scaledD x:ℝ):ℂ) := by
  simp only [upperLastCore,map_mul,map_add,map_sub,eval_C,map_ofNat]
  have h1 := actual_upper_core_quadratic_complex 1 hx
  have hn := actual_upper_core_quadratic_complex (-1) hx
  have h0 := actual_upper_core_quadratic_complex 0 hx
  simp only [Complex.ofReal_one,Complex.ofReal_neg,Complex.ofReal_zero] at h1 hn h0
  rw [h1,hn,h0]
  push_cast
  ring

def scaledUpperDeterminant (x : ℝ) : ℝ :=
  scaledUpperA x*scaledD x-scaledB x^2

theorem actual_reduced_determinant_seam_complex {x : ℝ} (hx : 0 < x) :
    eval (actualSquarePoint x) (upperDeterminantCore (10000000000000:ℂ))=
      (((reducedSeamNormalizer x)^2*scaledUpperDeterminant x:ℝ):ℂ) := by
  rw [upperDeterminantCore,map_sub,map_mul,map_pow,
    actual_upper_constant_core_complex hx,actual_upper_border_core_complex hx,
    actual_upper_last_core_complex hx]
  unfold scaledUpperDeterminant
  push_cast
  ring

theorem actual_reduced_determinant_seam_real {x : ℝ} (hx : 0 < x) :
    (eval (actualSquarePoint x) (upperDeterminantCore (10000000000000:ℂ))).re=
      (reducedSeamNormalizer x)^2*scaledUpperDeterminant x := by
  rw [actual_reduced_determinant_seam_complex hx,Complex.ofReal_re]

end
end RHTower.ThetaCuspUpperSeam
