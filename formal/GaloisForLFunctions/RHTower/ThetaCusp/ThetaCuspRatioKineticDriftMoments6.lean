import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticDriftReader
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticDegree
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def kineticDriftMoment6Coeff0Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment6KineticCoeff0).coeff 0=c} := by
  have he : (driftReader h clearMoment6KineticCoeff0).coeff 0=(driftReader h clearMoment6KineticCoeff0).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment6KineticCoeff0Norm.property]
    dsimp only [clearMoment6KineticCoeff0Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
      driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,
      Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftMoment6Coeff0Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment6KineticCoeff0).coeff 1=c} := by
  have he : (driftReader h clearMoment6KineticCoeff0).coeff 1=(driftReader h clearMoment6KineticCoeff0).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment6KineticCoeff0Norm.property]
    dsimp only [clearMoment6KineticCoeff0Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
      driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,
      Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftMoment6Coeff0Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment6KineticCoeff0).coeff 2=c} := by
  have he : (driftReader h clearMoment6KineticCoeff0).coeff 2=(driftReader h clearMoment6KineticCoeff0).coeff 2 := rfl
  conv at he =>
    rhs
    rw [clearMoment6KineticCoeff0Norm.property]
    dsimp only [clearMoment6KineticCoeff0Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
      driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,
      Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftMoment6Coeff0Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment6KineticCoeff0).coeff 3=c} := by
  have he : (driftReader h clearMoment6KineticCoeff0).coeff 3=(driftReader h clearMoment6KineticCoeff0).coeff 3 := rfl
  conv at he =>
    rhs
    rw [clearMoment6KineticCoeff0Norm.property]
    dsimp only [clearMoment6KineticCoeff0Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
      driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,
      Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftMoment6Coeff1Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment6KineticCoeff1).coeff 0=c} := by
  have he : (driftReader h clearMoment6KineticCoeff1).coeff 0=(driftReader h clearMoment6KineticCoeff1).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment6KineticCoeff1Norm.property]
    dsimp only [clearMoment6KineticCoeff1Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
      driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,
      Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftMoment6Coeff1Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment6KineticCoeff1).coeff 1=c} := by
  have he : (driftReader h clearMoment6KineticCoeff1).coeff 1=(driftReader h clearMoment6KineticCoeff1).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment6KineticCoeff1Norm.property]
    dsimp only [clearMoment6KineticCoeff1Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
      driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,
      Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftMoment6Coeff1Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment6KineticCoeff1).coeff 2=c} := by
  have he : (driftReader h clearMoment6KineticCoeff1).coeff 2=(driftReader h clearMoment6KineticCoeff1).coeff 2 := rfl
  conv at he =>
    rhs
    rw [clearMoment6KineticCoeff1Norm.property]
    dsimp only [clearMoment6KineticCoeff1Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
      driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,
      Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftMoment6Coeff1Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment6KineticCoeff1).coeff 3=c} := by
  have he : (driftReader h clearMoment6KineticCoeff1).coeff 3=(driftReader h clearMoment6KineticCoeff1).coeff 3 := rfl
  conv at he =>
    rhs
    rw [clearMoment6KineticCoeff1Norm.property]
    dsimp only [clearMoment6KineticCoeff1Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
      driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,
      Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftMoment6Coeff2Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment6KineticCoeff2).coeff 0=c} := by
  have he : (driftReader h clearMoment6KineticCoeff2).coeff 0=(driftReader h clearMoment6KineticCoeff2).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment6KineticCoeff2Norm.property]
    dsimp only [clearMoment6KineticCoeff2Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
      driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,
      Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftMoment6Coeff2Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment6KineticCoeff2).coeff 1=c} := by
  have he : (driftReader h clearMoment6KineticCoeff2).coeff 1=(driftReader h clearMoment6KineticCoeff2).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment6KineticCoeff2Norm.property]
    dsimp only [clearMoment6KineticCoeff2Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
      driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,
      Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftMoment6Coeff2Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment6KineticCoeff2).coeff 2=c} := by
  have he : (driftReader h clearMoment6KineticCoeff2).coeff 2=(driftReader h clearMoment6KineticCoeff2).coeff 2 := rfl
  conv at he =>
    rhs
    rw [clearMoment6KineticCoeff2Norm.property]
    dsimp only [clearMoment6KineticCoeff2Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
      driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,
      Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftMoment6Coeff2Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment6KineticCoeff2).coeff 3=c} := by
  have he : (driftReader h clearMoment6KineticCoeff2).coeff 3=(driftReader h clearMoment6KineticCoeff2).coeff 3 := rfl
  conv at he =>
    rhs
    rw [clearMoment6KineticCoeff2Norm.property]
    dsimp only [clearMoment6KineticCoeff2Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
      driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,
      Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftMoment6Coeff3Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment6KineticCoeff3).coeff 0=c} := by
  have he : (driftReader h clearMoment6KineticCoeff3).coeff 0=(driftReader h clearMoment6KineticCoeff3).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment6KineticCoeff3Norm.property]
    dsimp only [clearMoment6KineticCoeff3Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
      driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,
      Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftMoment6Coeff3Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment6KineticCoeff3).coeff 1=c} := by
  have he : (driftReader h clearMoment6KineticCoeff3).coeff 1=(driftReader h clearMoment6KineticCoeff3).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment6KineticCoeff3Norm.property]
    dsimp only [clearMoment6KineticCoeff3Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
      driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,
      Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftMoment6Coeff3Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment6KineticCoeff3).coeff 2=c} := by
  have he : (driftReader h clearMoment6KineticCoeff3).coeff 2=(driftReader h clearMoment6KineticCoeff3).coeff 2 := rfl
  conv at he =>
    rhs
    rw [clearMoment6KineticCoeff3Norm.property]
    dsimp only [clearMoment6KineticCoeff3Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
      driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,
      Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftMoment6Coeff3Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment6KineticCoeff3).coeff 3=c} := by
  have he : (driftReader h clearMoment6KineticCoeff3).coeff 3=(driftReader h clearMoment6KineticCoeff3).coeff 3 := rfl
  conv at he =>
    rhs
    rw [clearMoment6KineticCoeff3Norm.property]
    dsimp only [clearMoment6KineticCoeff3Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
      driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,
      Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftMoment6Coeff4Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment6KineticCoeff4).coeff 0=c} := by
  have he : (driftReader h clearMoment6KineticCoeff4).coeff 0=(driftReader h clearMoment6KineticCoeff4).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment6KineticCoeff4Norm.property]
    dsimp only [clearMoment6KineticCoeff4Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
      driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,
      Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftMoment6Coeff4Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment6KineticCoeff4).coeff 1=c} := by
  have he : (driftReader h clearMoment6KineticCoeff4).coeff 1=(driftReader h clearMoment6KineticCoeff4).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment6KineticCoeff4Norm.property]
    dsimp only [clearMoment6KineticCoeff4Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
      driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,
      Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftMoment6Coeff4Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment6KineticCoeff4).coeff 2=c} := by
  have he : (driftReader h clearMoment6KineticCoeff4).coeff 2=(driftReader h clearMoment6KineticCoeff4).coeff 2 := rfl
  conv at he =>
    rhs
    rw [clearMoment6KineticCoeff4Norm.property]
    dsimp only [clearMoment6KineticCoeff4Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
      driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,
      Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftMoment6Coeff4Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment6KineticCoeff4).coeff 3=c} := by
  have he : (driftReader h clearMoment6KineticCoeff4).coeff 3=(driftReader h clearMoment6KineticCoeff4).coeff 3 := rfl
  conv at he =>
    rhs
    rw [clearMoment6KineticCoeff4Norm.property]
    dsimp only [clearMoment6KineticCoeff4Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
      driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,
      Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftMoment6Coeff5Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment6KineticCoeff5).coeff 0=c} := by
  have he : (driftReader h clearMoment6KineticCoeff5).coeff 0=(driftReader h clearMoment6KineticCoeff5).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment6KineticCoeff5Norm.property]
    dsimp only [clearMoment6KineticCoeff5Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
      driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,
      Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftMoment6Coeff5Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment6KineticCoeff5).coeff 1=c} := by
  have he : (driftReader h clearMoment6KineticCoeff5).coeff 1=(driftReader h clearMoment6KineticCoeff5).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment6KineticCoeff5Norm.property]
    dsimp only [clearMoment6KineticCoeff5Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
      driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,
      Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftMoment6Coeff5Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment6KineticCoeff5).coeff 2=c} := by
  have he : (driftReader h clearMoment6KineticCoeff5).coeff 2=(driftReader h clearMoment6KineticCoeff5).coeff 2 := rfl
  conv at he =>
    rhs
    rw [clearMoment6KineticCoeff5Norm.property]
    dsimp only [clearMoment6KineticCoeff5Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
      driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,
      Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftMoment6Coeff5Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment6KineticCoeff5).coeff 3=c} := by
  have he : (driftReader h clearMoment6KineticCoeff5).coeff 3=(driftReader h clearMoment6KineticCoeff5).coeff 3 := rfl
  conv at he =>
    rhs
    rw [clearMoment6KineticCoeff5Norm.property]
    dsimp only [clearMoment6KineticCoeff5Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
      driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,
      Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftMoment6Coeff6Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment6KineticCoeff6).coeff 0=c} := by
  have he : (driftReader h clearMoment6KineticCoeff6).coeff 0=(driftReader h clearMoment6KineticCoeff6).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment6KineticCoeff6Norm.property]
    dsimp only [clearMoment6KineticCoeff6Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
      driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,
      Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftMoment6Coeff6Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment6KineticCoeff6).coeff 1=c} := by
  have he : (driftReader h clearMoment6KineticCoeff6).coeff 1=(driftReader h clearMoment6KineticCoeff6).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment6KineticCoeff6Norm.property]
    dsimp only [clearMoment6KineticCoeff6Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
      driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,
      Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftMoment6Coeff6Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment6KineticCoeff6).coeff 2=c} := by
  have he : (driftReader h clearMoment6KineticCoeff6).coeff 2=(driftReader h clearMoment6KineticCoeff6).coeff 2 := rfl
  conv at he =>
    rhs
    rw [clearMoment6KineticCoeff6Norm.property]
    dsimp only [clearMoment6KineticCoeff6Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
      driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,
      Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftMoment6Coeff6Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment6KineticCoeff6).coeff 3=c} := by
  have he : (driftReader h clearMoment6KineticCoeff6).coeff 3=(driftReader h clearMoment6KineticCoeff6).coeff 3 := rfl
  conv at he =>
    rhs
    rw [clearMoment6KineticCoeff6Norm.property]
    dsimp only [clearMoment6KineticCoeff6Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
      driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,
      Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem clearMoment6KineticCoeff0_drift_degree (h : ℂ) :
    (driftReader h clearMoment6KineticCoeff0).natDegree≤3 := by
  rw [clearMoment6KineticCoeff0Norm.property]
  dsimp only [clearMoment6KineticCoeff0Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment6KineticCoeff0_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment6KineticCoeff0=
      ∑ b ∈ Finset.range 4, (driftReader h clearMoment6KineticCoeff0).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment6KineticCoeff0_drift_degree h; omega) v

theorem clearMoment6KineticCoeff1_drift_degree (h : ℂ) :
    (driftReader h clearMoment6KineticCoeff1).natDegree≤3 := by
  rw [clearMoment6KineticCoeff1Norm.property]
  dsimp only [clearMoment6KineticCoeff1Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment6KineticCoeff1_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment6KineticCoeff1=
      ∑ b ∈ Finset.range 4, (driftReader h clearMoment6KineticCoeff1).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment6KineticCoeff1_drift_degree h; omega) v

theorem clearMoment6KineticCoeff2_drift_degree (h : ℂ) :
    (driftReader h clearMoment6KineticCoeff2).natDegree≤3 := by
  rw [clearMoment6KineticCoeff2Norm.property]
  dsimp only [clearMoment6KineticCoeff2Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment6KineticCoeff2_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment6KineticCoeff2=
      ∑ b ∈ Finset.range 4, (driftReader h clearMoment6KineticCoeff2).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment6KineticCoeff2_drift_degree h; omega) v

theorem clearMoment6KineticCoeff3_drift_degree (h : ℂ) :
    (driftReader h clearMoment6KineticCoeff3).natDegree≤3 := by
  rw [clearMoment6KineticCoeff3Norm.property]
  dsimp only [clearMoment6KineticCoeff3Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment6KineticCoeff3_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment6KineticCoeff3=
      ∑ b ∈ Finset.range 4, (driftReader h clearMoment6KineticCoeff3).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment6KineticCoeff3_drift_degree h; omega) v

theorem clearMoment6KineticCoeff4_drift_degree (h : ℂ) :
    (driftReader h clearMoment6KineticCoeff4).natDegree≤3 := by
  rw [clearMoment6KineticCoeff4Norm.property]
  dsimp only [clearMoment6KineticCoeff4Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment6KineticCoeff4_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment6KineticCoeff4=
      ∑ b ∈ Finset.range 4, (driftReader h clearMoment6KineticCoeff4).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment6KineticCoeff4_drift_degree h; omega) v

theorem clearMoment6KineticCoeff5_drift_degree (h : ℂ) :
    (driftReader h clearMoment6KineticCoeff5).natDegree≤3 := by
  rw [clearMoment6KineticCoeff5Norm.property]
  dsimp only [clearMoment6KineticCoeff5Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment6KineticCoeff5_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment6KineticCoeff5=
      ∑ b ∈ Finset.range 4, (driftReader h clearMoment6KineticCoeff5).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment6KineticCoeff5_drift_degree h; omega) v

theorem clearMoment6KineticCoeff6_drift_degree (h : ℂ) :
    (driftReader h clearMoment6KineticCoeff6).natDegree≤3 := by
  rw [clearMoment6KineticCoeff6Norm.property]
  dsimp only [clearMoment6KineticCoeff6Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment6KineticCoeff6_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment6KineticCoeff6=
      ∑ b ∈ Finset.range 4, (driftReader h clearMoment6KineticCoeff6).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment6KineticCoeff6_drift_degree h; omega) v

end
end HTGeometry.ThetaRatioKineticContraction
