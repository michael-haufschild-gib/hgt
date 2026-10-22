import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioCenterOrdering

namespace RHTower.ThetaCuspUpperSeam
noncomputable section
set_option autoImplicit false
open MvPolynomial HTGeometry.ThetaRatioSource HTGeometry.ThetaRatioSquare
open HTGeometry.ThetaRatioWeightedSquare HTGeometry.ThetaRatioInfinity
open ThetaRatioSourceIncidence ThetaCuspModularRatio ThetaCuspOddDirectionTransport

/-- Exact source shear gap; no projective division at the seam. -/
def shearGap (x : ℝ) : ℝ :=
  thetaCuspModularTransverseShear x-2*u x/3-4*x

def endpointNormalizer (x : ℝ) : ℝ :=
  (6:ℝ)^30*(u x)^25*(k x-1/6)^7

theorem endpointNormalizer_pos {x : ℝ} (hx : 0 < x) :
    0 < endpointNormalizer x := actual_endpoint_normalizer_pos hx

theorem upper_center_gap_identity {x : ℝ} (hx : 0 < x) :
    (actualCenterUpper x-x/u x)*u x=shearGap x/4 := by
  have hu : u x ≠ 0 :=
    (neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx)).ne'
  unfold actualCenterUpper shearGap J
  field_simp [hu]
  ring

theorem actual_center_slope_real (c : ℝ) {x : ℝ} (hx : 0 < x) :
    (eval (actualSquarePoint x) (centerSlopeCoefficient (c:ℂ))).re=
      endpointNormalizer x*u x*deriv (ThetaCuspHeadGrowth.centerDrive c) x := by
  have hp : eval (state x) (sourceJet 0)=((k x-1/6:ℝ):ℂ) := by
    rw [sourceJet_zero_eval]
    change (k x:ℂ)-1/6=((k x-1/6:ℝ):ℂ)
    push_cast
    rfl
  have hk : k x-1/6 ≠ 0 := by linarith [k_gt hx.le]
  rw [centerDrive_slope c hx,hp,←Complex.ofReal_pow,Complex.div_ofReal_re,
    actual_center_slope_eq c hx]
  have h6 : (6:ℂ)^30=(((6:ℝ)^30:ℝ):ℂ) := by norm_cast
  have hu26 : (u x:ℂ)^26=(((u x)^26:ℝ):ℂ) := by norm_cast
  rw [h6,hu26,←Complex.ofReal_mul,Complex.re_ofReal_mul]
  unfold endpointNormalizer
  calc
    _ = ((6:ℝ)^30*(u x)^26)*
        (((eval (state x) (HTGeometry.ThetaRatioQuadraticSource.slopeLinear (c:ℂ))).re /
          (k x-1/6)^7)*(k x-1/6)^7) := by
      rw [div_mul_cancel₀ _ (pow_ne_zero 7 hk)]
    _ = _ := by ring

theorem actual_upper_center_real_identity (c eta : ℝ) {x : ℝ} (hx : 0 < x) :
    (eval (actualSquarePoint x) (upperCenterQuadratic (c:ℂ) (eta:ℂ))).re=
      endpointNormalizer x*(deriv (normalizedBase c) x+
        shearGap x*deriv (ThetaCuspHeadGrowth.centerDrive c) x/4+
        2*deriv normalizedB x*eta+deriv normalizedD x*eta^2) := by
  have ha := actual_weighted_quadratic_real c eta hx
  rw [weightedSourceQuadratic_affine] at ha
  simp only [map_add,map_mul,eval_C,Complex.add_re,Complex.re_ofReal_mul] at ha
  change (eval (actualSquarePoint x) (lowerCenterQuadratic (c:ℂ) (eta:ℂ))).re+
    (x/u x)*(eval (actualSquarePoint x) (centerSlopeCoefficient (c:ℂ))).re=
      endpointNormalizer x*(deriv (normalizedBase c) x+
        2*deriv normalizedB x*eta+deriv normalizedD x*eta^2) at ha
  rw [upperCenterQuadratic]
  simp only [map_add,map_mul,actual_upper_center_eval,Complex.add_re,
    Complex.re_ofReal_mul]
  calc
    _ = ((eval (actualSquarePoint x) (lowerCenterQuadratic (c:ℂ) (eta:ℂ))).re+
          (x/u x)*(eval (actualSquarePoint x) (centerSlopeCoefficient (c:ℂ))).re)+
        (actualCenterUpper x-x/u x)*
          (eval (actualSquarePoint x) (centerSlopeCoefficient (c:ℂ))).re := by ring
    _ = endpointNormalizer x*(deriv (normalizedBase c) x+
          2*deriv normalizedB x*eta+deriv normalizedD x*eta^2)+
        endpointNormalizer x*((actualCenterUpper x-x/u x)*u x)*
          deriv (ThetaCuspHeadGrowth.centerDrive c) x := by
      rw [ha,actual_center_slope_real c hx]
      ring
    _ = _ := by rw [upper_center_gap_identity hx]; ring

end
end RHTower.ThetaCuspUpperSeam
