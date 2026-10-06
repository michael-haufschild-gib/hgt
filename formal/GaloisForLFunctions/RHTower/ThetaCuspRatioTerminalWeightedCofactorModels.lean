import GaloisForLFunctions.RHTower.ThetaCuspRatioTerminalWeightedMoments

namespace HTGeometry.ThetaRatioWeightedSquare
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity Filter Topology
open RHTower.ThetaCuspModularRatio

def terminalHeadNorm : {P : Polynomial ℂ // terminalWeightedHead=P} := by
  have h : terminalWeightedHead=terminalWeightedHead := rfl
  conv at h =>
    rhs
    simp only [terminalWeightedHead,terminalMomentNorm1.property,terminalMomentNorm2.property,terminalMomentNorm3.property]
    dsimp only [terminalMomentNorm1,terminalMomentNorm2,terminalMomentNorm3]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.C_ofNat,Polynomial.derivative_pow]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def terminalANorm : {P : Polynomial ℂ // terminalWeightedA=P} := by
  have h : terminalWeightedA=terminalWeightedA := rfl
  conv at h =>
    rhs
    simp only [terminalWeightedA,terminalMomentNorm1.property,terminalMomentNorm2.property,terminalMomentNorm3.property,terminalMomentNorm4.property,terminalMomentNorm5.property,terminalMomentNorm7.property]
    dsimp only [terminalMomentNorm1,terminalMomentNorm2,terminalMomentNorm3,terminalMomentNorm4,terminalMomentNorm5,terminalMomentNorm7]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.C_ofNat,Polynomial.derivative_pow]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def terminalBNorm : {P : Polynomial ℂ // terminalWeightedB=P} := by
  have h : terminalWeightedB=terminalWeightedB := rfl
  conv at h =>
    rhs
    simp only [terminalWeightedB,terminalMomentNorm1.property,terminalMomentNorm2.property,terminalMomentNorm3.property,terminalMomentNorm4.property,terminalMomentNorm5.property,terminalMomentNorm6.property]
    dsimp only [terminalMomentNorm1,terminalMomentNorm2,terminalMomentNorm3,terminalMomentNorm4,terminalMomentNorm5,terminalMomentNorm6]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.C_ofNat,Polynomial.derivative_pow]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def terminalDNorm : {P : Polynomial ℂ // terminalWeightedD=P} := by
  have h : terminalWeightedD=terminalWeightedD := rfl
  conv at h =>
    rhs
    simp only [terminalWeightedD,terminalMomentNorm1.property,terminalMomentNorm2.property,terminalMomentNorm3.property,terminalMomentNorm4.property,terminalMomentNorm5.property]
    dsimp only [terminalMomentNorm1,terminalMomentNorm2,terminalMomentNorm3,terminalMomentNorm4,terminalMomentNorm5]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.C_ofNat,Polynomial.derivative_pow]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

end
end HTGeometry.ThetaRatioWeightedSquare
