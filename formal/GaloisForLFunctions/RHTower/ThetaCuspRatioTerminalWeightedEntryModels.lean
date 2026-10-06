import GaloisForLFunctions.RHTower.ThetaCuspRatioTerminalWeightedCofactorModels

namespace HTGeometry.ThetaRatioWeightedSquare
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity Filter Topology
open RHTower.ThetaCuspModularRatio

def terminalUpperConstantNorm : {P : Polynomial ℂ // terminalUpperConstant (10000000000000:ℂ)=P} := by
  have h : terminalUpperConstant (10000000000000:ℂ)=terminalUpperConstant (10000000000000:ℂ) := rfl
  conv at h =>
    rhs
    simp only [terminalUpperConstant,terminalWeightedSlope,terminalWeightedLoadedConstant,terminalWeightedLoadedLinear,terminalHeadNorm.property,terminalANorm.property,terminalJetNorm0.property,terminalJetNorm1.property]
    dsimp only [terminalHeadNorm,terminalANorm,terminalJetNorm0,terminalJetNorm1]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.C_ofNat,Polynomial.derivative_pow]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def terminalUpperBorderNorm : {P : Polynomial ℂ // terminalUpperBorder=P} := by
  have h : terminalUpperBorder=terminalUpperBorder := rfl
  conv at h =>
    rhs
    simp only [terminalUpperBorder,terminalWeightedSlope,terminalBNorm.property]
    dsimp only [terminalBNorm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.C_ofNat,Polynomial.derivative_pow]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def terminalUpperLastNorm : {P : Polynomial ℂ // terminalUpperLast=P} := by
  have h : terminalUpperLast=terminalUpperLast := rfl
  conv at h =>
    rhs
    simp only [terminalUpperLast,terminalWeightedSlope,terminalDNorm.property]
    dsimp only [terminalDNorm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.C_ofNat,Polynomial.derivative_pow]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def terminalUpperDeterminantNorm : {P : Polynomial ℂ // terminalUpperDeterminant (10000000000000:ℂ)=P} := by
  have h : terminalUpperDeterminant (10000000000000:ℂ)=terminalUpperDeterminant (10000000000000:ℂ) := rfl
  conv at h =>
    rhs
    simp only [terminalUpperDeterminant,terminalUpperConstantNorm.property,terminalUpperBorderNorm.property,terminalUpperLastNorm.property]
    dsimp only [terminalUpperConstantNorm,terminalUpperBorderNorm,terminalUpperLastNorm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.C_ofNat,Polynomial.derivative_pow]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

end
end HTGeometry.ThetaRatioWeightedSquare
