import GaloisForLFunctions.RHTower.ThetaCuspRatioWeightedSquareJets
import GaloisForLFunctions.RHTower.ThetaCuspRatioQuadraticSource

namespace HTGeometry.ThetaRatioWeightedSquare
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioQuadraticSource

def weightedHead : Poly := weightedMoment 1*weightedMoment 3-(weightedMoment 2)^2
def weightedA : Poly :=
  weightedMoment 1*weightedMoment 3*weightedMoment 7-weightedMoment 1*(weightedMoment 5)^2-
    (weightedMoment 2)^2*weightedMoment 7+2*weightedMoment 2*weightedMoment 4*weightedMoment 5-
    weightedMoment 3*(weightedMoment 4)^2

def weightedB : Poly :=
  -(weightedMoment 1*weightedMoment 3*weightedMoment 6-weightedMoment 1*weightedMoment 4*weightedMoment 5-
    (weightedMoment 2)^2*weightedMoment 6+weightedMoment 2*weightedMoment 3*weightedMoment 5+
    weightedMoment 2*(weightedMoment 4)^2-(weightedMoment 3)^2*weightedMoment 4)

def weightedD : Poly :=
  weightedMoment 1*weightedMoment 3*weightedMoment 5-weightedMoment 1*(weightedMoment 4)^2-
    (weightedMoment 2)^2*weightedMoment 5+2*weightedMoment 2*weightedMoment 3*weightedMoment 4-
    (weightedMoment 3)^3

theorem weightedHead_eq :
    square weightedHead=C ((6:ℂ)^12)*(X Coord.U)^8*shear headMinor := by
  simp only [weightedHead,headMinor,map_sub,map_mul,map_pow,weightedMoment_eq,
    integerSignedMoment_eq,shear_C]
  apply MvPolynomial.funext
  intro v
  norm_num only [map_sub,map_mul,map_pow,eval_C,eval_X]
  ring

theorem weightedA_eq :
    square weightedA=C ((6:ℂ)^28)*(X Coord.U)^22*shear minorA := by
  simp only [weightedA,minorA,map_sub,map_add,map_mul,map_pow,map_ofNat,weightedMoment_eq,
    integerSignedMoment_eq]
  apply MvPolynomial.funext
  intro v
  norm_num only [map_sub,map_add,map_mul,map_pow,map_ofNat,eval_C,eval_X]
  ring

theorem weightedB_eq :
    square weightedB=C ((6:ℂ)^26)*(X Coord.U)^20*shear minorB := by
  simp only [weightedB,minorB,map_neg,map_sub,map_add,map_mul,map_pow,map_ofNat,weightedMoment_eq,
    integerSignedMoment_eq]
  apply MvPolynomial.funext
  intro v
  norm_num only [map_neg,map_sub,map_add,map_mul,map_pow,map_ofNat,eval_C,eval_X]
  ring

theorem weightedD_eq :
    square weightedD=C ((6:ℂ)^24)*(X Coord.U)^18*shear thirdMinor := by
  simp only [weightedD,thirdMinor,map_sub,map_add,map_mul,map_pow,map_ofNat,weightedMoment_eq,
    integerSignedMoment_eq]
  apply MvPolynomial.funext
  intro v
  norm_num only [map_sub,map_add,map_mul,map_pow,map_ofNat,eval_C,eval_X]
  ring

/-- Center-independent coefficient after weighting the whole loaded cofactor. -/
def weightedLoadedConstant (c : ℂ) : Poly :=
  weightedA+3*C c*C ((6:ℂ)^14)*(X Coord.U)^7*(weightedJet 0)^2*weightedHead

/-- Coefficient of X=center/U in the same weighted cofactor. -/
def weightedLoadedLinear (c : ℂ) : Poly :=
  2*C c*C ((6:ℂ)^13)*(X Coord.U)^7*weightedJet 0*weightedHead*weightedJet 1

theorem weightedLoadedConstant_eq (c : ℂ) :
    square (weightedLoadedConstant c)=
      C ((6:ℂ)^28)*(X Coord.U)^22*shear (loadedConstant c) := by
  simp only [weightedLoadedConstant,loadedConstant,map_add,map_mul,map_pow,map_ofNat,
    square_C,square_X,weightedA_eq,weightedJet_eq,weightedHead_eq,integerJet_eq,shear_C]
  apply MvPolynomial.funext
  intro v
  norm_num only [map_add,map_mul,map_pow,map_ofNat,eval_C,eval_X,squareCoord]
  ring

theorem weightedLoadedLinear_eq (c : ℂ) :
    square (weightedLoadedLinear c)=
      C ((6:ℂ)^28)*(X Coord.U)^23*shear (loadedLinear c) := by
  simp only [weightedLoadedLinear,loadedLinear,map_mul,map_pow,map_ofNat,
    square_C,square_X,weightedJet_eq,weightedHead_eq,integerJet_eq,shear_C]
  apply MvPolynomial.funext
  intro v
  norm_num only [map_mul,map_pow,map_ofNat,eval_C,eval_X,squareCoord]
  ring

end
end HTGeometry.ThetaRatioWeightedSquare
