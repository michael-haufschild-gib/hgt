import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioTerminalWeightedDeterminant

namespace HTGeometry.ThetaRatioWeightedSquare
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity Filter Topology
open RHTower.ThetaCuspModularRatio

def terminalJetNorm0 : {P : Polynomial ℂ // terminalWeightedJet 0=P} := by
  exact ⟨6*Polynomial.X-1,rfl⟩

def terminalJetNorm1 : {P : Polynomial ℂ // terminalWeightedJet 1=P} := by
  have h : terminalWeightedJet 1=terminalWeightedJet 1 := rfl
  conv at h =>
    rhs
    rw [terminalWeightedJet,terminalJetNorm0.property]
    dsimp only [terminalJetNorm0]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def terminalJetNorm2 : {P : Polynomial ℂ // terminalWeightedJet 2=P} := by
  have h : terminalWeightedJet 2=terminalWeightedJet 2 := rfl
  conv at h =>
    rhs
    rw [terminalWeightedJet,terminalJetNorm1.property]
    dsimp only [terminalJetNorm1]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.C_ofNat,Polynomial.derivative_pow]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def terminalJetNorm3 : {P : Polynomial ℂ // terminalWeightedJet 3=P} := by
  have h : terminalWeightedJet 3=terminalWeightedJet 3 := rfl
  conv at h =>
    rhs
    rw [terminalWeightedJet,terminalJetNorm2.property]
    dsimp only [terminalJetNorm2]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.C_ofNat,Polynomial.derivative_pow]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def terminalJetNorm4 : {P : Polynomial ℂ // terminalWeightedJet 4=P} := by
  have h : terminalWeightedJet 4=terminalWeightedJet 4 := rfl
  conv at h =>
    rhs
    rw [terminalWeightedJet,terminalJetNorm3.property]
    dsimp only [terminalJetNorm3]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.C_ofNat,Polynomial.derivative_pow]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def terminalJetNorm5 : {P : Polynomial ℂ // terminalWeightedJet 5=P} := by
  have h : terminalWeightedJet 5=terminalWeightedJet 5 := rfl
  conv at h =>
    rhs
    rw [terminalWeightedJet,terminalJetNorm4.property]
    dsimp only [terminalJetNorm4]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.C_ofNat,Polynomial.derivative_pow]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def terminalJetNorm6 : {P : Polynomial ℂ // terminalWeightedJet 6=P} := by
  have h : terminalWeightedJet 6=terminalWeightedJet 6 := rfl
  conv at h =>
    rhs
    rw [terminalWeightedJet,terminalJetNorm5.property]
    dsimp only [terminalJetNorm5]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.C_ofNat,Polynomial.derivative_pow]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def terminalJetNorm7 : {P : Polynomial ℂ // terminalWeightedJet 7=P} := by
  have h : terminalWeightedJet 7=terminalWeightedJet 7 := rfl
  conv at h =>
    rhs
    rw [terminalWeightedJet,terminalJetNorm6.property]
    dsimp only [terminalJetNorm6]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.C_ofNat,Polynomial.derivative_pow]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def terminalJetNorm8 : {P : Polynomial ℂ // terminalWeightedJet 8=P} := by
  have h : terminalWeightedJet 8=terminalWeightedJet 8 := rfl
  conv at h =>
    rhs
    rw [terminalWeightedJet,terminalJetNorm7.property]
    dsimp only [terminalJetNorm7]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.C_ofNat,Polynomial.derivative_pow]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def terminalJetNorm9 : {P : Polynomial ℂ // terminalWeightedJet 9=P} := by
  have h : terminalWeightedJet 9=terminalWeightedJet 9 := rfl
  conv at h =>
    rhs
    rw [terminalWeightedJet,terminalJetNorm8.property]
    dsimp only [terminalJetNorm8]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.C_ofNat,Polynomial.derivative_pow]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def terminalJetNorm10 : {P : Polynomial ℂ // terminalWeightedJet 10=P} := by
  have h : terminalWeightedJet 10=terminalWeightedJet 10 := rfl
  conv at h =>
    rhs
    rw [terminalWeightedJet,terminalJetNorm9.property]
    dsimp only [terminalJetNorm9]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.C_ofNat,Polynomial.derivative_pow]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def terminalJetNorm11 : {P : Polynomial ℂ // terminalWeightedJet 11=P} := by
  have h : terminalWeightedJet 11=terminalWeightedJet 11 := rfl
  conv at h =>
    rhs
    rw [terminalWeightedJet,terminalJetNorm10.property]
    dsimp only [terminalJetNorm10]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.C_ofNat,Polynomial.derivative_pow]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def terminalJetNorm12 : {P : Polynomial ℂ // terminalWeightedJet 12=P} := by
  have h : terminalWeightedJet 12=terminalWeightedJet 12 := rfl
  conv at h =>
    rhs
    rw [terminalWeightedJet,terminalJetNorm11.property]
    dsimp only [terminalJetNorm11]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.C_ofNat,Polynomial.derivative_pow]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def terminalJetNorm13 : {P : Polynomial ℂ // terminalWeightedJet 13=P} := by
  have h : terminalWeightedJet 13=terminalWeightedJet 13 := rfl
  conv at h =>
    rhs
    rw [terminalWeightedJet,terminalJetNorm12.property]
    dsimp only [terminalJetNorm12]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.C_ofNat,Polynomial.derivative_pow]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

def terminalJetNorm14 : {P : Polynomial ℂ // terminalWeightedJet 14=P} := by
  have h : terminalWeightedJet 14=terminalWeightedJet 14 := rfl
  conv at h =>
    rhs
    rw [terminalWeightedJet,terminalJetNorm13.property]
    dsimp only [terminalJetNorm13]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.C_ofNat,Polynomial.derivative_pow]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

end
end HTGeometry.ThetaRatioWeightedSquare
