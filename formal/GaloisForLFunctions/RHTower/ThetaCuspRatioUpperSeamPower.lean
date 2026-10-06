import GaloisForLFunctions.RHTower.ThetaCuspRatioSquarePowerDescent
import GaloisForLFunctions.RHTower.ThetaCuspRatioCenterEndpoints

namespace HTGeometry.ThetaRatioWeightedSquare
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioQuadraticSource

theorem weighted_quadratic_power_factor (c center eta : ℂ) :
    ∃ R : Poly, weightedSourceQuadratic c center eta=(X Coord.U)^13*R := by
  apply square_odd_power_descent 12 _
    (C ((6:ℂ)^30)*(shear (slopeConstant c)+X Coord.U*C center*shear (slopeLinear c)+
      2*C eta*shear (sixthSlope minorB)+C (eta^2)*shear thirdSlope))
  rw [weightedSourceQuadratic_eq]
  norm_num only
  ring

theorem center_slope_power_factor (c : ℂ) :
    ∃ R : Poly, centerSlopeCoefficient c=(X Coord.U)^13*R := by
  apply square_odd_power_descent 12 _
    (C (36*(6:ℂ)^28)*X Coord.U*shear (sixthSlope (loadedLinear c)))
  rw [centerSlopeCoefficient,weightedSixthSlope_eq 23 _ _ _ (weightedLoadedLinear_eq c)]
  norm_num only
  ring

theorem upper_quadratic_power_factor (c eta : ℂ) :
    ∃ R : Poly, upperCenterQuadratic c eta=(X Coord.U)^13*R := by
  obtain ⟨P,hP⟩ := weighted_quadratic_power_factor c 0 eta
  obtain ⟨Q,hQ⟩ := center_slope_power_factor c
  refine ⟨P+upperCenterPolynomial*Q,?_⟩
  simp only [upperCenterQuadratic,lowerCenterQuadratic,hP,hQ]
  ring

def upperQuadraticCore (c eta : ℂ) : Poly :=
  (upperCenterQuadratic c eta).divMonomial (Finsupp.single Coord.U 13)

theorem upper_quadratic_core_eq (c eta : ℂ) :
    upperCenterQuadratic c eta=(X Coord.U)^13*upperQuadraticCore c eta := by
  obtain ⟨R,hR⟩ := upper_quadratic_power_factor c eta
  have hcore : upperQuadraticCore c eta=R := by
    rw [upperQuadraticCore,hR,MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.divMonomial_monomial_mul]
  rwa [hcore]

def upperConstantCore (c : ℂ) : Poly := upperQuadraticCore c 0
def upperBorderCore (c : ℂ) : Poly :=
  C (1/4:ℂ)*(upperQuadraticCore c 1-upperQuadraticCore c (-1))
def upperLastCore (c : ℂ) : Poly :=
  C (1/2:ℂ)*(upperQuadraticCore c 1+upperQuadraticCore c (-1)-2*upperQuadraticCore c 0)
def upperDeterminantCore (c : ℂ) : Poly :=
  upperConstantCore c*upperLastCore c-(upperBorderCore c)^2

private theorem upper_constant_polarization (c : ℂ) :
    centerConstantCoefficient c+upperCenterPolynomial*centerSlopeCoefficient c=
      upperCenterQuadratic c 0 := by
  simp only [upperCenterQuadratic,lowerCenterQuadratic,weightedSourceQuadratic,
    centerConstantCoefficient,map_zero,zero_mul,mul_zero,zero_pow (by omega : (2:ℕ)≠0),add_zero]

private theorem upper_border_polarization (c : ℂ) :
    weightedBorderCoefficient=
      C (1/4:ℂ)*(upperCenterQuadratic c 1-upperCenterQuadratic c (-1)) := by
  apply MvPolynomial.funext
  intro v
  norm_num only [upperCenterQuadratic,lowerCenterQuadratic,weightedSourceQuadratic,
    weightedBorderCoefficient,map_add,map_sub,map_mul,map_pow,map_neg,map_zero,map_one,
    map_ofNat,eval_C]
  ring

private theorem upper_last_polarization (c : ℂ) :
    weightedLastCoefficient=C (1/2:ℂ)*(upperCenterQuadratic c 1+
      upperCenterQuadratic c (-1)-2*upperCenterQuadratic c 0) := by
  apply MvPolynomial.funext
  intro v
  norm_num only [upperCenterQuadratic,lowerCenterQuadratic,weightedSourceQuadratic,
    weightedLastCoefficient,map_add,map_sub,map_mul,map_pow,map_neg,map_zero,map_one,
    map_ofNat,eval_C]
  ring

theorem upper_constant_core_eq (c : ℂ) :
    centerConstantCoefficient c+upperCenterPolynomial*centerSlopeCoefficient c=
      (X Coord.U)^13*upperConstantCore c := by
  rw [upper_constant_polarization]
  exact upper_quadratic_core_eq c 0

theorem upper_border_core_eq (c : ℂ) :
    weightedBorderCoefficient=(X Coord.U)^13*upperBorderCore c := by
  rw [upper_border_polarization,upper_quadratic_core_eq,upper_quadratic_core_eq]
  unfold upperBorderCore
  ring

theorem upper_last_core_eq (c : ℂ) :
    weightedLastCoefficient=(X Coord.U)^13*upperLastCore c := by
  rw [upper_last_polarization,upper_quadratic_core_eq,upper_quadratic_core_eq,
    upper_quadratic_core_eq]
  unfold upperLastCore
  ring

/-- Complete determinant: all native moments, cofactors and arbitrary load retained. -/
theorem upper_determinant_core_eq (c : ℂ) :
    upperCenterDeterminant c=(X Coord.U)^26*upperDeterminantCore c := by
  rw [upperCenterDeterminant,upper_constant_core_eq,upper_border_core_eq,
    upper_last_core_eq]
  unfold upperDeterminantCore
  ring

theorem upper_determinant_core_divMonomial (c : ℂ) :
    (upperCenterDeterminant c).divMonomial (Finsupp.single Coord.U 26)=
      upperDeterminantCore c := by
  rw [upper_determinant_core_eq,MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.divMonomial_monomial_mul]

end
end HTGeometry.ThetaRatioWeightedSquare
