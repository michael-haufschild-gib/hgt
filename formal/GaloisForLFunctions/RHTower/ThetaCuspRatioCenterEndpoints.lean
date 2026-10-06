import GaloisForLFunctions.RHTower.ThetaCuspRatioActualWeightedQuadratic

namespace HTGeometry.ThetaRatioWeightedSquare
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource

def centerSlopeCoefficient (c : ℂ) : Poly :=
  weightedSixthSlope 23 (weightedLoadedLinear c)
def lowerCenterQuadratic (c eta : ℂ) : Poly := weightedSourceQuadratic c 0 eta
def upperCenterPolynomial : Poly := C (1/4:ℂ)*(X .K-C (2/3:ℂ)-X .J)
def upperCenterQuadratic (c eta : ℂ) : Poly :=
  lowerCenterQuadratic c eta+upperCenterPolynomial*centerSlopeCoefficient c

theorem weightedSourceQuadratic_affine (c center eta : ℂ) :
    weightedSourceQuadratic c center eta=
      lowerCenterQuadratic c eta+C center*centerSlopeCoefficient c := by
  simp only [lowerCenterQuadratic,centerSlopeCoefficient,weightedSourceQuadratic,map_zero,zero_mul]
  ring

def centerConstantCoefficient (c : ℂ) : Poly :=
  weightedSixthSlope 22 (weightedLoadedConstant c)+
    6*X .U*weightedJet 0*weightedLoadedLinear c

def weightedBorderCoefficient : Poly := 36*X .U*weightedSixthSlope 20 weightedB

def weightedLastCoefficient : Poly := 1296*(X .U)^2*weightedSixthSlope 18 weightedD

def lowerCenterDeterminant (c : ℂ) : Poly :=
  centerConstantCoefficient c*weightedLastCoefficient-weightedBorderCoefficient^2

def upperCenterDeterminant (c : ℂ) : Poly :=
  (centerConstantCoefficient c+upperCenterPolynomial*centerSlopeCoefficient c)*
    weightedLastCoefficient-weightedBorderCoefficient^2

theorem lower_center_square_completion (c eta : ℂ) :
    weightedLastCoefficient*lowerCenterQuadratic c eta=
      (weightedLastCoefficient*C eta+weightedBorderCoefficient)^2+
        lowerCenterDeterminant c := by
  simp only [weightedLastCoefficient,lowerCenterQuadratic,weightedSourceQuadratic,
    weightedBorderCoefficient,lowerCenterDeterminant,centerConstantCoefficient,
    map_zero,zero_mul,map_pow]
  ring

theorem upper_center_square_completion (c eta : ℂ) :
    weightedLastCoefficient*upperCenterQuadratic c eta=
      (weightedLastCoefficient*C eta+weightedBorderCoefficient)^2+
        upperCenterDeterminant c := by
  unfold upperCenterQuadratic
  rw [mul_add,lower_center_square_completion]
  unfold upperCenterDeterminant lowerCenterDeterminant
  ring

end
end HTGeometry.ThetaRatioWeightedSquare

namespace RHTower.ThetaRatioSourceIncidence
noncomputable section
set_option autoImplicit false
open MvPolynomial HTGeometry.ThetaRatioSource HTGeometry.ThetaRatioWeightedSquare
open HTGeometry.ThetaRatioInfinity ThetaCuspModularRatio

def actualCenterFraction (x : ℝ) : ℝ := (x/u x)/actualCenterUpper x

theorem actual_center_fraction_bounds {x : ℝ} (hx : 0 < x) :
    0 < actualCenterFraction x ∧ actualCenterFraction x ≤ 1 := by
  obtain ⟨h0,h1⟩ := actual_center_ratio_bounds hx
  have hh : 0 < actualCenterUpper x := h0.trans_le h1
  exact ⟨div_pos h0 hh,(div_le_one hh).mpr h1⟩

theorem actual_upper_center_eval (x : ℝ) :
    eval (actualSquarePoint x) upperCenterPolynomial=(actualCenterUpper x:ℂ) := by
  simp only [upperCenterPolynomial,actualCenterUpper,map_mul,map_sub,eval_X,eval_C,actualSquarePoint]
  push_cast
  ring

theorem actual_center_endpoint_decomposition (c eta : ℝ) {x : ℝ} (hx : 0 < x) :
    (eval (actualSquarePoint x)
      (weightedSourceQuadratic (c:ℂ) ((x/u x:ℝ):ℂ) (eta:ℂ))).re=
      (1-actualCenterFraction x)*
          (eval (actualSquarePoint x) (lowerCenterQuadratic (c:ℂ) (eta:ℂ))).re+
        actualCenterFraction x*
          (eval (actualSquarePoint x) (upperCenterQuadratic (c:ℂ) (eta:ℂ))).re := by
  have hh : 0 < actualCenterUpper x :=
    (actual_center_ratio_bounds hx).1.trans_le (actual_center_ratio_bounds hx).2
  have he : (actualCenterFraction x:ℂ)*(actualCenterUpper x:ℂ)=((x/u x:ℝ):ℂ) := by
    rw [←Complex.ofReal_mul]
    congr 1
    exact div_mul_cancel₀ _ hh.ne'
  have hpoly := weightedSourceQuadratic_affine (c:ℂ) ((x/u x:ℝ):ℂ) (eta:ℂ)
  have hid :
      eval (actualSquarePoint x) (weightedSourceQuadratic (c:ℂ) ((x/u x:ℝ):ℂ) (eta:ℂ))=
      (1-(actualCenterFraction x:ℂ))*
        eval (actualSquarePoint x) (lowerCenterQuadratic (c:ℂ) (eta:ℂ))+
        (actualCenterFraction x:ℂ)*
        eval (actualSquarePoint x) (upperCenterQuadratic (c:ℂ) (eta:ℂ)) := by
    rw [hpoly]
    simp only [upperCenterQuadratic,map_add,map_mul,eval_C,actual_upper_center_eval]
    rw [←he]
    ring
  have hr := congrArg Complex.re hid
  rw [show (1-(actualCenterFraction x:ℂ))=((1-actualCenterFraction x:ℝ):ℂ) by push_cast; rfl] at hr
  simpa only [Complex.add_re,Complex.re_ofReal_mul] using hr

theorem actual_endpoint_normalizer_pos {x : ℝ} (hx : 0 < x) :
    0 < (6:ℝ)^30*(u x)^25*(k x-1/6)^7 := by
  have hu : 0 < u x := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx)
  have hk : 0 < k x-1/6 := by linarith [k_gt hx.le]
  positivity

theorem actual_source_quadratic_endpoint_decomposition (c eta : ℝ)
    {x : ℝ} (hx : 0 < x) :
    (6:ℝ)^30*(u x)^25*(k x-1/6)^7*
      (deriv (ThetaCuspOddDirectionTransport.normalizedBase c) x+
        2*deriv ThetaCuspOddDirectionTransport.normalizedB x*eta+
        deriv ThetaCuspOddDirectionTransport.normalizedD x*eta^2)=
      (1-actualCenterFraction x)*
        (eval (actualSquarePoint x) (lowerCenterQuadratic (c:ℂ) (eta:ℂ))).re+
      actualCenterFraction x*
        (eval (actualSquarePoint x) (upperCenterQuadratic (c:ℂ) (eta:ℂ))).re := by
  rw [←actual_weighted_quadratic_real c eta hx]
  exact actual_center_endpoint_decomposition c eta hx

end
end RHTower.ThetaRatioSourceIncidence
