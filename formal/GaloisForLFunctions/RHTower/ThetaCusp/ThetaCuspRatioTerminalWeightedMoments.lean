import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioTerminalWeightedJets

namespace HTGeometry.ThetaRatioWeightedSquare
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity Filter Topology
open RHTower.ThetaCuspModularRatio

def terminalMomentNorm1 : {P : Polynomial ℂ // terminalWeightedMoment 1=P} := by
  have h : terminalWeightedMoment 1=terminalWeightedMoment 1 := rfl
  conv at h =>
    rhs
    simp only [terminalWeightedMoment,terminalWeightedReflection,Finset.sum_range_succ,Finset.sum_range_zero,terminalJetNorm0.property,terminalJetNorm1.property,terminalJetNorm2.property]
    dsimp only [terminalJetNorm0,terminalJetNorm1,terminalJetNorm2]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.C_ofNat,Polynomial.derivative_pow]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def terminalMomentNorm2 : {P : Polynomial ℂ // terminalWeightedMoment 2=P} := by
  have h : terminalWeightedMoment 2=terminalWeightedMoment 2 := rfl
  conv at h =>
    rhs
    simp only [terminalWeightedMoment,terminalWeightedReflection,Finset.sum_range_succ,Finset.sum_range_zero,terminalJetNorm0.property,terminalJetNorm1.property,terminalJetNorm2.property,terminalJetNorm3.property,terminalJetNorm4.property]
    dsimp only [terminalJetNorm0,terminalJetNorm1,terminalJetNorm2,terminalJetNorm3,terminalJetNorm4]
    norm_num [Nat.rawCast,Int.rawCast,Nat.choose,Polynomial.C_ofNat,Polynomial.derivative_pow]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def terminalMomentNorm3 : {P : Polynomial ℂ // terminalWeightedMoment 3=P} := by
  have h : terminalWeightedMoment 3=terminalWeightedMoment 3 := rfl
  conv at h =>
    rhs
    simp only [terminalWeightedMoment,terminalWeightedReflection,Finset.sum_range_succ,Finset.sum_range_zero,terminalJetNorm0.property,terminalJetNorm1.property,terminalJetNorm2.property,terminalJetNorm3.property,terminalJetNorm4.property,terminalJetNorm5.property,terminalJetNorm6.property]
    dsimp only [terminalJetNorm0,terminalJetNorm1,terminalJetNorm2,terminalJetNorm3,terminalJetNorm4,terminalJetNorm5,terminalJetNorm6]
    norm_num [Nat.rawCast,Int.rawCast,Nat.choose,Polynomial.C_ofNat,Polynomial.derivative_pow]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def terminalMomentNorm4 : {P : Polynomial ℂ // terminalWeightedMoment 4=P} := by
  have h : terminalWeightedMoment 4=terminalWeightedMoment 4 := rfl
  conv at h =>
    rhs
    simp only [terminalWeightedMoment,terminalWeightedReflection,Finset.sum_range_succ,Finset.sum_range_zero,terminalJetNorm0.property,terminalJetNorm1.property,terminalJetNorm2.property,terminalJetNorm3.property,terminalJetNorm4.property,terminalJetNorm5.property,terminalJetNorm6.property,terminalJetNorm7.property,terminalJetNorm8.property]
    dsimp only [terminalJetNorm0,terminalJetNorm1,terminalJetNorm2,terminalJetNorm3,terminalJetNorm4,terminalJetNorm5,terminalJetNorm6,terminalJetNorm7,terminalJetNorm8]
    norm_num [Nat.rawCast,Int.rawCast,Nat.choose,Polynomial.C_ofNat,Polynomial.derivative_pow]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def terminalMomentNorm5 : {P : Polynomial ℂ // terminalWeightedMoment 5=P} := by
  have h : terminalWeightedMoment 5=terminalWeightedMoment 5 := rfl
  conv at h =>
    rhs
    simp only [terminalWeightedMoment,terminalWeightedReflection,Finset.sum_range_succ,Finset.sum_range_zero,terminalJetNorm0.property,terminalJetNorm1.property,terminalJetNorm2.property,terminalJetNorm3.property,terminalJetNorm4.property,terminalJetNorm5.property,terminalJetNorm6.property,terminalJetNorm7.property,terminalJetNorm8.property,terminalJetNorm9.property,terminalJetNorm10.property]
    dsimp only [terminalJetNorm0,terminalJetNorm1,terminalJetNorm2,terminalJetNorm3,terminalJetNorm4,terminalJetNorm5,terminalJetNorm6,terminalJetNorm7,terminalJetNorm8,terminalJetNorm9,terminalJetNorm10]
    norm_num [Nat.rawCast,Int.rawCast,Nat.choose,Polynomial.C_ofNat,Polynomial.derivative_pow]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def terminalMomentNorm6 : {P : Polynomial ℂ // terminalWeightedMoment 6=P} := by
  have h : terminalWeightedMoment 6=terminalWeightedMoment 6 := rfl
  conv at h =>
    rhs
    simp only [terminalWeightedMoment,terminalWeightedReflection,Finset.sum_range_succ,Finset.sum_range_zero,terminalJetNorm0.property,terminalJetNorm1.property,terminalJetNorm2.property,terminalJetNorm3.property,terminalJetNorm4.property,terminalJetNorm5.property,terminalJetNorm6.property,terminalJetNorm7.property,terminalJetNorm8.property,terminalJetNorm9.property,terminalJetNorm10.property,terminalJetNorm11.property,terminalJetNorm12.property]
    dsimp only [terminalJetNorm0,terminalJetNorm1,terminalJetNorm2,terminalJetNorm3,terminalJetNorm4,terminalJetNorm5,terminalJetNorm6,terminalJetNorm7,terminalJetNorm8,terminalJetNorm9,terminalJetNorm10,terminalJetNorm11,terminalJetNorm12]
    norm_num [Nat.rawCast,Int.rawCast,Nat.choose,Polynomial.C_ofNat,Polynomial.derivative_pow]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def terminalMomentNorm7 : {P : Polynomial ℂ // terminalWeightedMoment 7=P} := by
  have h : terminalWeightedMoment 7=terminalWeightedMoment 7 := rfl
  conv at h =>
    rhs
    simp only [terminalWeightedMoment,terminalWeightedReflection,Finset.sum_range_succ,Finset.sum_range_zero,terminalJetNorm0.property,terminalJetNorm1.property,terminalJetNorm2.property,terminalJetNorm3.property,terminalJetNorm4.property,terminalJetNorm5.property,terminalJetNorm6.property,terminalJetNorm7.property,terminalJetNorm8.property,terminalJetNorm9.property,terminalJetNorm10.property,terminalJetNorm11.property,terminalJetNorm12.property,terminalJetNorm13.property,terminalJetNorm14.property]
    dsimp only [terminalJetNorm0,terminalJetNorm1,terminalJetNorm2,terminalJetNorm3,terminalJetNorm4,terminalJetNorm5,terminalJetNorm6,terminalJetNorm7,terminalJetNorm8,terminalJetNorm9,terminalJetNorm10,terminalJetNorm11,terminalJetNorm12,terminalJetNorm13,terminalJetNorm14]
    norm_num [Nat.rawCast,Int.rawCast,Nat.choose,Polynomial.C_ofNat,Polynomial.derivative_pow]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

end
end HTGeometry.ThetaRatioWeightedSquare
