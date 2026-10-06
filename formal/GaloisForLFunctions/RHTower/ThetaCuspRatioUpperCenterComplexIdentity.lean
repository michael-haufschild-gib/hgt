import GaloisForLFunctions.RHTower.ThetaCuspRatioComplexSourceSlopes
import GaloisForLFunctions.RHTower.ThetaCuspRatioUpperCenterSeamPositive

namespace RHTower.ThetaCuspUpperSeam
noncomputable section
set_option autoImplicit false
open MvPolynomial HTGeometry.ThetaRatioSource HTGeometry.ThetaRatioWeightedSquare
open HTGeometry.ThetaRatioInfinity HTGeometry.ThetaRatioQuadraticSource
open ThetaRatioSourceIncidence ThetaCuspModularRatio ThetaCuspOddDirectionTransport

private theorem source_zero_value (x : ℝ) :
    eval (state x) (sourceJet 0)=((k x-1/6:ℝ):ℂ) := by
  rw [sourceJet_zero_eval]
  change (k x:ℂ)-1/6=((k x-1/6:ℝ):ℂ)
  push_cast
  rfl

theorem actual_weighted_quadratic_complex (c eta : ℝ) {x : ℝ} (hx : 0 < x) :
    eval (actualSquarePoint x)
      (weightedSourceQuadratic (c:ℂ) ((x/u x:ℝ):ℂ) (eta:ℂ))=
        ((endpointNormalizer x*(deriv (normalizedBase c) x+
          2*deriv normalizedB x*eta+deriv normalizedD x*eta^2):ℝ):ℂ) := by
  have he := congrArg (fun z : ℂ => z*(eval (state x) (sourceJet 0))^7)
    (normalized_source_quadratic_complex c eta hx)
  rw [div_mul_cancel₀ _ (pow_ne_zero 7 (sourceZero_ne hx.le))] at he
  rw [actual_weighted_quadratic c eta hx,←he,source_zero_value]
  unfold endpointNormalizer
  push_cast
  ring

theorem actual_center_slope_complex (c : ℝ) {x : ℝ} (hx : 0 < x) :
    eval (actualSquarePoint x) (centerSlopeCoefficient (c:ℂ))=
      ((endpointNormalizer x*u x*deriv (ThetaCuspHeadGrowth.centerDrive c) x:ℝ):ℂ) := by
  have he := congrArg (fun z : ℂ => z*(eval (state x) (sourceJet 0))^7)
    (centerDrive_slope_complex c hx)
  rw [div_mul_cancel₀ _ (pow_ne_zero 7 (sourceZero_ne hx.le))] at he
  rw [actual_center_slope_eq c hx,←he,source_zero_value]
  unfold endpointNormalizer
  push_cast
  ring

theorem actual_upper_center_complex_identity (c eta : ℝ) {x : ℝ} (hx : 0 < x) :
    eval (actualSquarePoint x) (upperCenterQuadratic (c:ℂ) (eta:ℂ))=
      ((endpointNormalizer x*(deriv (normalizedBase c) x+
        shearGap x*deriv (ThetaCuspHeadGrowth.centerDrive c) x/4+
        2*deriv normalizedB x*eta+deriv normalizedD x*eta^2):ℝ):ℂ) := by
  have hr : endpointNormalizer x*(deriv (normalizedBase c) x+
        2*deriv normalizedB x*eta+deriv normalizedD x*eta^2)+
      (actualCenterUpper x-x/u x)*
        (endpointNormalizer x*u x*deriv (ThetaCuspHeadGrowth.centerDrive c) x)=
      endpointNormalizer x*(deriv (normalizedBase c) x+
        shearGap x*deriv (ThetaCuspHeadGrowth.centerDrive c) x/4+
        2*deriv normalizedB x*eta+deriv normalizedD x*eta^2) := by
    calc
      _ = endpointNormalizer x*(deriv (normalizedBase c) x+
          2*deriv normalizedB x*eta+deriv normalizedD x*eta^2+
          ((actualCenterUpper x-x/u x)*u x)*
            deriv (ThetaCuspHeadGrowth.centerDrive c) x) := by ring
      _ = _ := by rw [upper_center_gap_identity hx]; ring
  calc
    _ = eval (actualSquarePoint x)
          (weightedSourceQuadratic (c:ℂ) ((x/u x:ℝ):ℂ) (eta:ℂ))+
        (((actualCenterUpper x-x/u x:ℝ):ℂ))*
          eval (actualSquarePoint x) (centerSlopeCoefficient (c:ℂ)) := by
      rw [upperCenterQuadratic,weightedSourceQuadratic_affine]
      simp only [map_add,map_mul,eval_C,actual_upper_center_eval]
      push_cast
      ring
    _ = _ := by
      rw [actual_weighted_quadratic_complex c eta hx,actual_center_slope_complex c hx]
      exact_mod_cast hr

theorem actual_upper_quadratic_scaled_complex (eta : ℝ) {x : ℝ} (hx : 0 < x) :
    eval (actualSquarePoint x) (upperCenterQuadratic (10000000000000:ℂ) (eta:ℂ))=
      ((endpointNormalizer x*x*
        (scaledUpperA x+2*scaledB x*eta+scaledD x*eta^2):ℝ):ℂ) := by
  have he := actual_upper_center_complex_identity (10000000000000:ℝ) eta hx
  simp only [Complex.ofReal_ofNat] at he
  rw [he]
  congr 1
  calc
    _ = endpointNormalizer x*(x*scaledUpperA x+
        2*(x*scaledB x)*eta+(x*scaledD x)*eta^2) := by
      rw [scaledUpperA_identity,scaledB_identity,scaledD_identity]
    _ = _ := by ring

end
end RHTower.ThetaCuspUpperSeam
