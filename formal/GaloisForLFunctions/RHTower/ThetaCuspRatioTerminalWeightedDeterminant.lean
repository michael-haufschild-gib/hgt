import GaloisForLFunctions.RHTower.ThetaCuspRatioTerminalWeightedFlow

namespace HTGeometry.ThetaRatioWeightedSquare
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity Filter Topology
open RHTower.ThetaCuspModularRatio

def terminalWeightedHead : Polynomial ℂ :=
  terminalWeightedMoment 1*terminalWeightedMoment 3-(terminalWeightedMoment 2)^2

def terminalWeightedA : Polynomial ℂ :=
  terminalWeightedMoment 1*terminalWeightedMoment 3*terminalWeightedMoment 7-
    terminalWeightedMoment 1*(terminalWeightedMoment 5)^2-
    (terminalWeightedMoment 2)^2*terminalWeightedMoment 7+
    2*terminalWeightedMoment 2*terminalWeightedMoment 4*terminalWeightedMoment 5-
    terminalWeightedMoment 3*(terminalWeightedMoment 4)^2

def terminalWeightedB : Polynomial ℂ :=
  -(terminalWeightedMoment 1*terminalWeightedMoment 3*terminalWeightedMoment 6-
    terminalWeightedMoment 1*terminalWeightedMoment 4*terminalWeightedMoment 5-
    (terminalWeightedMoment 2)^2*terminalWeightedMoment 6+
    terminalWeightedMoment 2*terminalWeightedMoment 3*terminalWeightedMoment 5+
    terminalWeightedMoment 2*(terminalWeightedMoment 4)^2-
    (terminalWeightedMoment 3)^2*terminalWeightedMoment 4)

def terminalWeightedD : Polynomial ℂ :=
  terminalWeightedMoment 1*terminalWeightedMoment 3*terminalWeightedMoment 5-
    terminalWeightedMoment 1*(terminalWeightedMoment 4)^2-
    (terminalWeightedMoment 2)^2*terminalWeightedMoment 5+
    2*terminalWeightedMoment 2*terminalWeightedMoment 3*terminalWeightedMoment 4-
    (terminalWeightedMoment 3)^3

theorem terminalWeighted_head : terminalWeighted weightedHead=terminalWeightedHead := by
  simp only [weightedHead,terminalWeightedHead,map_sub,map_mul,map_pow,
    terminalWeighted_moment]

theorem terminalWeighted_A : terminalWeighted weightedA=terminalWeightedA := by
  simp only [weightedA,terminalWeightedA,map_sub,map_add,map_mul,map_pow,map_ofNat,
    terminalWeighted_moment]

theorem terminalWeighted_B : terminalWeighted weightedB=terminalWeightedB := by
  simp only [weightedB,terminalWeightedB,map_neg,map_sub,map_add,map_mul,map_pow,
    terminalWeighted_moment]

theorem terminalWeighted_D : terminalWeighted weightedD=terminalWeightedD := by
  simp only [weightedD,terminalWeightedD,map_sub,map_add,map_mul,map_pow,map_ofNat,
    terminalWeighted_moment]

def terminalWeightedLoadedConstant (c : ℂ) : Polynomial ℂ :=
  terminalWeightedA+3*Polynomial.C c*Polynomial.C ((6:ℂ)^14)*9^7*
    (terminalWeightedJet 0)^2*terminalWeightedHead

def terminalWeightedLoadedLinear (c : ℂ) : Polynomial ℂ :=
  2*Polynomial.C c*Polynomial.C ((6:ℂ)^13)*9^7*
    terminalWeightedJet 0*terminalWeightedHead*terminalWeightedJet 1

theorem terminalWeighted_loadedConstant (c : ℂ) :
    terminalWeighted (weightedLoadedConstant c)=terminalWeightedLoadedConstant c := by
  simp only [weightedLoadedConstant,terminalWeightedLoadedConstant,map_add,map_mul,
    map_pow,map_ofNat,terminalWeighted_C,terminalWeighted_X,terminalWeightedCoord,
    terminalWeighted_A,terminalWeighted_jet,terminalWeighted_head]

theorem terminalWeighted_loadedLinear (c : ℂ) :
    terminalWeighted (weightedLoadedLinear c)=terminalWeightedLoadedLinear c := by
  simp only [weightedLoadedLinear,terminalWeightedLoadedLinear,map_mul,map_pow,
    map_ofNat,terminalWeighted_C,terminalWeighted_X,terminalWeightedCoord,
    terminalWeighted_jet,terminalWeighted_head]

def terminalUpperConstant (c : ℂ) : Polynomial ℂ :=
  terminalWeightedSlope (terminalWeightedLoadedConstant c)+
    6*9*terminalWeightedJet 0*terminalWeightedLoadedLinear c+
    Polynomial.C (1/4)*(Polynomial.X-1)*
      terminalWeightedSlope (terminalWeightedLoadedLinear c)

def terminalUpperBorder : Polynomial ℂ := 36*9*terminalWeightedSlope terminalWeightedB
def terminalUpperLast : Polynomial ℂ := 1296*9^2*terminalWeightedSlope terminalWeightedD
def terminalUpperDeterminant (c : ℂ) : Polynomial ℂ :=
  terminalUpperConstant c*terminalUpperLast-terminalUpperBorder^2

theorem terminalWeighted_upperCenter :
    terminalWeighted upperCenterPolynomial=Polynomial.C (1/4)*(Polynomial.X-1) := by
  apply Polynomial.funext
  intro k
  norm_num [upperCenterPolynomial,terminalWeighted,terminalWeightedCoord]
  ring

theorem terminalWeighted_upperConstant (c : ℂ) :
    terminalWeighted (centerConstantCoefficient c+
      upperCenterPolynomial*centerSlopeCoefficient c)=terminalUpperConstant c := by
  simp only [centerConstantCoefficient,centerSlopeCoefficient,terminalUpperConstant,
    map_add,map_mul,map_ofNat,terminalWeighted_X,terminalWeightedCoord,
    terminalWeighted_sixthSlope,terminalWeighted_jet,terminalWeighted_loadedConstant,
    terminalWeighted_loadedLinear,terminalWeighted_upperCenter]

theorem terminalWeighted_upperBorder :
    terminalWeighted weightedBorderCoefficient=terminalUpperBorder := by
  simp only [weightedBorderCoefficient,terminalUpperBorder,map_mul,map_ofNat,
    terminalWeighted_X,terminalWeightedCoord,terminalWeighted_sixthSlope,terminalWeighted_B]

theorem terminalWeighted_upperLast :
    terminalWeighted weightedLastCoefficient=terminalUpperLast := by
  simp only [weightedLastCoefficient,terminalUpperLast,map_mul,map_pow,map_ofNat,
    terminalWeighted_X,terminalWeightedCoord,terminalWeighted_sixthSlope,terminalWeighted_D]

theorem terminalWeighted_upperDeterminant (c : ℂ) :
    terminalWeighted (upperCenterDeterminant c)=terminalUpperDeterminant c := by
  simp only [upperCenterDeterminant,terminalUpperDeterminant,map_sub,map_mul,map_pow,
    terminalWeighted_upperConstant,terminalWeighted_upperLast,terminalWeighted_upperBorder]

theorem terminalUpperDeterminant_eval (c k : ℂ) :
    (terminalUpperDeterminant c).eval k=
      eval (basePoint 9 k (1/3)) (upperCenterDeterminant c) := by
  rw [←terminalWeighted_upperDeterminant,terminalWeighted_eval]

end
end HTGeometry.ThetaRatioWeightedSquare
