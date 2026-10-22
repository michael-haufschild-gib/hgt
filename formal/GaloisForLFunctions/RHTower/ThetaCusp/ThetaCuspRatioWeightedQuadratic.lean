import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioWeightedCofactors

namespace HTGeometry.ThetaRatioWeightedSquare
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioQuadraticSource

def weightedSixthSlope (m : ℕ) (P : Poly) : Poly :=
  weightedJet 0*(X .U*squareLie P-6*(m:Poly)*X .U*X .K*(9-X .U)*P)-
    6*X .U*P*squareLie (weightedJet 0)

theorem weightedSixthSlope_eq (m : ℕ) (P Q : Poly) (c : ℂ)
    (hP : square P=C c*(X Coord.U)^m*shear Q) :
    square (weightedSixthSlope m P)=
      C (36*c)*(X Coord.U)^(m+3)*shear (sixthSlope Q) := by
  have hz : square (weightedJet 0)=6*shear (sourceJet 0) := by
    rw [weightedJet_eq,integerJet_eq]
    norm_num only [pow_zero,one_mul,pow_one,map_mul,shear_C,map_ofNat]
  have hc (a : ℂ) : chartLie (C a)=0 := flow_C chartField a
  unfold weightedSixthSlope
  simp only [map_sub,map_mul,map_natCast,square_X]
  rw [←chartLie_square,←chartLie_square,hP,hz]
  have h6 : chartLie (6:Poly)=0 := hc 6
  simp only [chartLie_mul,hc,h6,zero_mul,zero_add,chartLie_U_pow,chartLie_shear,
    integerLie_eq,map_mul,map_ofNat,sixthSlope,map_sub]
  apply MvPolynomial.funext
  intro v
  norm_num only [map_sub,map_add,map_mul,map_pow,map_ofNat,map_natCast,
    eval_C,eval_X,squareCoord,pow_add,pow_succ]
  ring

def weightedSourceQuadratic (c centerRatio eta : ℂ) : Poly :=
  weightedSixthSlope 22 (weightedLoadedConstant c)+
    6*X .U*weightedJet 0*weightedLoadedLinear c+
    C centerRatio*weightedSixthSlope 23 (weightedLoadedLinear c)+
    72*X .U*C eta*weightedSixthSlope 20 weightedB+
    1296*(X .U)^2*C (eta^2)*weightedSixthSlope 18 weightedD

/-- Exact full quadratic at center=U*X, with no sign or trajectory hypothesis. -/
theorem weightedSourceQuadratic_eq (c centerRatio eta : ℂ) :
    square (weightedSourceQuadratic c centerRatio eta)=
      C ((6:ℂ)^30)*(X Coord.U)^25*
        (shear (slopeConstant c)+X Coord.U*C centerRatio*shear (slopeLinear c)+
          2*C eta*shear (sixthSlope minorB)+C (eta^2)*shear thirdSlope) := by
  simp only [weightedSourceQuadratic,map_add,map_mul,map_pow,map_ofNat,square_X,square_C]
  rw [weightedSixthSlope_eq 22 _ _ _ (weightedLoadedConstant_eq c),
    weightedSixthSlope_eq 23 _ _ _ (weightedLoadedLinear_eq c),
    weightedSixthSlope_eq 20 _ _ _ weightedB_eq,
    weightedSixthSlope_eq 18 _ _ _ weightedD_eq,
    weightedJet_eq,weightedLoadedLinear_eq,integerJet_eq]
  have hd : sixthSlope thirdMinor=thirdSlope := rfl
  rw [hd]
  simp only [slopeConstant,slopeLinear,map_add,map_mul,shear_C]
  apply MvPolynomial.funext
  intro v
  norm_num only [map_add,map_mul,map_pow,map_ofNat,eval_C,eval_X,squareCoord]
  ring

end
end HTGeometry.ThetaRatioWeightedSquare
