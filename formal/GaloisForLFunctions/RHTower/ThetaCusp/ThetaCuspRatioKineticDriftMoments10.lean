import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticDriftReader
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticDegree
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def kineticDriftMoment10Coeff0Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff0).coeff 0=c} := by
  have he : (driftReader h clearMoment10KineticCoeff0).coeff 0=(driftReader h clearMoment10KineticCoeff0).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff0Norm.property]
    dsimp only [clearMoment10KineticCoeff0Norm]
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

def kineticDriftMoment10Coeff0Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff0).coeff 1=c} := by
  have he : (driftReader h clearMoment10KineticCoeff0).coeff 1=(driftReader h clearMoment10KineticCoeff0).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff0Norm.property]
    dsimp only [clearMoment10KineticCoeff0Norm]
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

def kineticDriftMoment10Coeff0Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff0).coeff 2=c} := by
  have he : (driftReader h clearMoment10KineticCoeff0).coeff 2=(driftReader h clearMoment10KineticCoeff0).coeff 2 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff0Norm.property]
    dsimp only [clearMoment10KineticCoeff0Norm]
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

def kineticDriftMoment10Coeff0Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff0).coeff 3=c} := by
  have he : (driftReader h clearMoment10KineticCoeff0).coeff 3=(driftReader h clearMoment10KineticCoeff0).coeff 3 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff0Norm.property]
    dsimp only [clearMoment10KineticCoeff0Norm]
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

def kineticDriftMoment10Coeff0Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff0).coeff 4=c} := by
  have he : (driftReader h clearMoment10KineticCoeff0).coeff 4=(driftReader h clearMoment10KineticCoeff0).coeff 4 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff0Norm.property]
    dsimp only [clearMoment10KineticCoeff0Norm]
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

def kineticDriftMoment10Coeff0Row5Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff0).coeff 5=c} := by
  have he : (driftReader h clearMoment10KineticCoeff0).coeff 5=(driftReader h clearMoment10KineticCoeff0).coeff 5 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff0Norm.property]
    dsimp only [clearMoment10KineticCoeff0Norm]
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

def kineticDriftMoment10Coeff1Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff1).coeff 0=c} := by
  have he : (driftReader h clearMoment10KineticCoeff1).coeff 0=(driftReader h clearMoment10KineticCoeff1).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff1Norm.property]
    dsimp only [clearMoment10KineticCoeff1Norm]
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

def kineticDriftMoment10Coeff1Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff1).coeff 1=c} := by
  have he : (driftReader h clearMoment10KineticCoeff1).coeff 1=(driftReader h clearMoment10KineticCoeff1).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff1Norm.property]
    dsimp only [clearMoment10KineticCoeff1Norm]
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

def kineticDriftMoment10Coeff1Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff1).coeff 2=c} := by
  have he : (driftReader h clearMoment10KineticCoeff1).coeff 2=(driftReader h clearMoment10KineticCoeff1).coeff 2 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff1Norm.property]
    dsimp only [clearMoment10KineticCoeff1Norm]
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

def kineticDriftMoment10Coeff1Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff1).coeff 3=c} := by
  have he : (driftReader h clearMoment10KineticCoeff1).coeff 3=(driftReader h clearMoment10KineticCoeff1).coeff 3 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff1Norm.property]
    dsimp only [clearMoment10KineticCoeff1Norm]
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

def kineticDriftMoment10Coeff1Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff1).coeff 4=c} := by
  have he : (driftReader h clearMoment10KineticCoeff1).coeff 4=(driftReader h clearMoment10KineticCoeff1).coeff 4 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff1Norm.property]
    dsimp only [clearMoment10KineticCoeff1Norm]
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

def kineticDriftMoment10Coeff1Row5Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff1).coeff 5=c} := by
  have he : (driftReader h clearMoment10KineticCoeff1).coeff 5=(driftReader h clearMoment10KineticCoeff1).coeff 5 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff1Norm.property]
    dsimp only [clearMoment10KineticCoeff1Norm]
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

def kineticDriftMoment10Coeff2Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff2).coeff 0=c} := by
  have he : (driftReader h clearMoment10KineticCoeff2).coeff 0=(driftReader h clearMoment10KineticCoeff2).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff2Norm.property]
    dsimp only [clearMoment10KineticCoeff2Norm]
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

def kineticDriftMoment10Coeff2Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff2).coeff 1=c} := by
  have he : (driftReader h clearMoment10KineticCoeff2).coeff 1=(driftReader h clearMoment10KineticCoeff2).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff2Norm.property]
    dsimp only [clearMoment10KineticCoeff2Norm]
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

def kineticDriftMoment10Coeff2Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff2).coeff 2=c} := by
  have he : (driftReader h clearMoment10KineticCoeff2).coeff 2=(driftReader h clearMoment10KineticCoeff2).coeff 2 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff2Norm.property]
    dsimp only [clearMoment10KineticCoeff2Norm]
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

def kineticDriftMoment10Coeff2Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff2).coeff 3=c} := by
  have he : (driftReader h clearMoment10KineticCoeff2).coeff 3=(driftReader h clearMoment10KineticCoeff2).coeff 3 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff2Norm.property]
    dsimp only [clearMoment10KineticCoeff2Norm]
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

def kineticDriftMoment10Coeff2Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff2).coeff 4=c} := by
  have he : (driftReader h clearMoment10KineticCoeff2).coeff 4=(driftReader h clearMoment10KineticCoeff2).coeff 4 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff2Norm.property]
    dsimp only [clearMoment10KineticCoeff2Norm]
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

def kineticDriftMoment10Coeff2Row5Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff2).coeff 5=c} := by
  have he : (driftReader h clearMoment10KineticCoeff2).coeff 5=(driftReader h clearMoment10KineticCoeff2).coeff 5 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff2Norm.property]
    dsimp only [clearMoment10KineticCoeff2Norm]
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

def kineticDriftMoment10Coeff3Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff3).coeff 0=c} := by
  have he : (driftReader h clearMoment10KineticCoeff3).coeff 0=(driftReader h clearMoment10KineticCoeff3).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff3Norm.property]
    dsimp only [clearMoment10KineticCoeff3Norm]
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

def kineticDriftMoment10Coeff3Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff3).coeff 1=c} := by
  have he : (driftReader h clearMoment10KineticCoeff3).coeff 1=(driftReader h clearMoment10KineticCoeff3).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff3Norm.property]
    dsimp only [clearMoment10KineticCoeff3Norm]
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

def kineticDriftMoment10Coeff3Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff3).coeff 2=c} := by
  have he : (driftReader h clearMoment10KineticCoeff3).coeff 2=(driftReader h clearMoment10KineticCoeff3).coeff 2 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff3Norm.property]
    dsimp only [clearMoment10KineticCoeff3Norm]
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

def kineticDriftMoment10Coeff3Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff3).coeff 3=c} := by
  have he : (driftReader h clearMoment10KineticCoeff3).coeff 3=(driftReader h clearMoment10KineticCoeff3).coeff 3 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff3Norm.property]
    dsimp only [clearMoment10KineticCoeff3Norm]
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

def kineticDriftMoment10Coeff3Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff3).coeff 4=c} := by
  have he : (driftReader h clearMoment10KineticCoeff3).coeff 4=(driftReader h clearMoment10KineticCoeff3).coeff 4 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff3Norm.property]
    dsimp only [clearMoment10KineticCoeff3Norm]
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

def kineticDriftMoment10Coeff3Row5Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff3).coeff 5=c} := by
  have he : (driftReader h clearMoment10KineticCoeff3).coeff 5=(driftReader h clearMoment10KineticCoeff3).coeff 5 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff3Norm.property]
    dsimp only [clearMoment10KineticCoeff3Norm]
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

def kineticDriftMoment10Coeff4Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff4).coeff 0=c} := by
  have he : (driftReader h clearMoment10KineticCoeff4).coeff 0=(driftReader h clearMoment10KineticCoeff4).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff4Norm.property]
    dsimp only [clearMoment10KineticCoeff4Norm]
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

def kineticDriftMoment10Coeff4Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff4).coeff 1=c} := by
  have he : (driftReader h clearMoment10KineticCoeff4).coeff 1=(driftReader h clearMoment10KineticCoeff4).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff4Norm.property]
    dsimp only [clearMoment10KineticCoeff4Norm]
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

def kineticDriftMoment10Coeff4Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff4).coeff 2=c} := by
  have he : (driftReader h clearMoment10KineticCoeff4).coeff 2=(driftReader h clearMoment10KineticCoeff4).coeff 2 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff4Norm.property]
    dsimp only [clearMoment10KineticCoeff4Norm]
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

def kineticDriftMoment10Coeff4Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff4).coeff 3=c} := by
  have he : (driftReader h clearMoment10KineticCoeff4).coeff 3=(driftReader h clearMoment10KineticCoeff4).coeff 3 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff4Norm.property]
    dsimp only [clearMoment10KineticCoeff4Norm]
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

def kineticDriftMoment10Coeff4Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff4).coeff 4=c} := by
  have he : (driftReader h clearMoment10KineticCoeff4).coeff 4=(driftReader h clearMoment10KineticCoeff4).coeff 4 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff4Norm.property]
    dsimp only [clearMoment10KineticCoeff4Norm]
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

def kineticDriftMoment10Coeff4Row5Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff4).coeff 5=c} := by
  have he : (driftReader h clearMoment10KineticCoeff4).coeff 5=(driftReader h clearMoment10KineticCoeff4).coeff 5 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff4Norm.property]
    dsimp only [clearMoment10KineticCoeff4Norm]
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

def kineticDriftMoment10Coeff5Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff5).coeff 0=c} := by
  have he : (driftReader h clearMoment10KineticCoeff5).coeff 0=(driftReader h clearMoment10KineticCoeff5).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff5Norm.property]
    dsimp only [clearMoment10KineticCoeff5Norm]
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

def kineticDriftMoment10Coeff5Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff5).coeff 1=c} := by
  have he : (driftReader h clearMoment10KineticCoeff5).coeff 1=(driftReader h clearMoment10KineticCoeff5).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff5Norm.property]
    dsimp only [clearMoment10KineticCoeff5Norm]
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

def kineticDriftMoment10Coeff5Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff5).coeff 2=c} := by
  have he : (driftReader h clearMoment10KineticCoeff5).coeff 2=(driftReader h clearMoment10KineticCoeff5).coeff 2 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff5Norm.property]
    dsimp only [clearMoment10KineticCoeff5Norm]
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

def kineticDriftMoment10Coeff5Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff5).coeff 3=c} := by
  have he : (driftReader h clearMoment10KineticCoeff5).coeff 3=(driftReader h clearMoment10KineticCoeff5).coeff 3 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff5Norm.property]
    dsimp only [clearMoment10KineticCoeff5Norm]
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

def kineticDriftMoment10Coeff5Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff5).coeff 4=c} := by
  have he : (driftReader h clearMoment10KineticCoeff5).coeff 4=(driftReader h clearMoment10KineticCoeff5).coeff 4 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff5Norm.property]
    dsimp only [clearMoment10KineticCoeff5Norm]
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

def kineticDriftMoment10Coeff5Row5Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff5).coeff 5=c} := by
  have he : (driftReader h clearMoment10KineticCoeff5).coeff 5=(driftReader h clearMoment10KineticCoeff5).coeff 5 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff5Norm.property]
    dsimp only [clearMoment10KineticCoeff5Norm]
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

def kineticDriftMoment10Coeff6Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff6).coeff 0=c} := by
  have he : (driftReader h clearMoment10KineticCoeff6).coeff 0=(driftReader h clearMoment10KineticCoeff6).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff6Norm.property]
    dsimp only [clearMoment10KineticCoeff6Norm]
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

def kineticDriftMoment10Coeff6Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff6).coeff 1=c} := by
  have he : (driftReader h clearMoment10KineticCoeff6).coeff 1=(driftReader h clearMoment10KineticCoeff6).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff6Norm.property]
    dsimp only [clearMoment10KineticCoeff6Norm]
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

def kineticDriftMoment10Coeff6Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff6).coeff 2=c} := by
  have he : (driftReader h clearMoment10KineticCoeff6).coeff 2=(driftReader h clearMoment10KineticCoeff6).coeff 2 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff6Norm.property]
    dsimp only [clearMoment10KineticCoeff6Norm]
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

def kineticDriftMoment10Coeff6Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff6).coeff 3=c} := by
  have he : (driftReader h clearMoment10KineticCoeff6).coeff 3=(driftReader h clearMoment10KineticCoeff6).coeff 3 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff6Norm.property]
    dsimp only [clearMoment10KineticCoeff6Norm]
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

def kineticDriftMoment10Coeff6Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff6).coeff 4=c} := by
  have he : (driftReader h clearMoment10KineticCoeff6).coeff 4=(driftReader h clearMoment10KineticCoeff6).coeff 4 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff6Norm.property]
    dsimp only [clearMoment10KineticCoeff6Norm]
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

def kineticDriftMoment10Coeff6Row5Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff6).coeff 5=c} := by
  have he : (driftReader h clearMoment10KineticCoeff6).coeff 5=(driftReader h clearMoment10KineticCoeff6).coeff 5 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff6Norm.property]
    dsimp only [clearMoment10KineticCoeff6Norm]
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

def kineticDriftMoment10Coeff7Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff7).coeff 0=c} := by
  have he : (driftReader h clearMoment10KineticCoeff7).coeff 0=(driftReader h clearMoment10KineticCoeff7).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff7Norm.property]
    dsimp only [clearMoment10KineticCoeff7Norm]
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

def kineticDriftMoment10Coeff7Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff7).coeff 1=c} := by
  have he : (driftReader h clearMoment10KineticCoeff7).coeff 1=(driftReader h clearMoment10KineticCoeff7).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff7Norm.property]
    dsimp only [clearMoment10KineticCoeff7Norm]
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

def kineticDriftMoment10Coeff7Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff7).coeff 2=c} := by
  have he : (driftReader h clearMoment10KineticCoeff7).coeff 2=(driftReader h clearMoment10KineticCoeff7).coeff 2 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff7Norm.property]
    dsimp only [clearMoment10KineticCoeff7Norm]
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

def kineticDriftMoment10Coeff7Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff7).coeff 3=c} := by
  have he : (driftReader h clearMoment10KineticCoeff7).coeff 3=(driftReader h clearMoment10KineticCoeff7).coeff 3 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff7Norm.property]
    dsimp only [clearMoment10KineticCoeff7Norm]
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

def kineticDriftMoment10Coeff7Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff7).coeff 4=c} := by
  have he : (driftReader h clearMoment10KineticCoeff7).coeff 4=(driftReader h clearMoment10KineticCoeff7).coeff 4 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff7Norm.property]
    dsimp only [clearMoment10KineticCoeff7Norm]
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

def kineticDriftMoment10Coeff7Row5Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff7).coeff 5=c} := by
  have he : (driftReader h clearMoment10KineticCoeff7).coeff 5=(driftReader h clearMoment10KineticCoeff7).coeff 5 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff7Norm.property]
    dsimp only [clearMoment10KineticCoeff7Norm]
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

def kineticDriftMoment10Coeff8Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff8).coeff 0=c} := by
  have he : (driftReader h clearMoment10KineticCoeff8).coeff 0=(driftReader h clearMoment10KineticCoeff8).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff8Norm.property]
    dsimp only [clearMoment10KineticCoeff8Norm]
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

def kineticDriftMoment10Coeff8Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff8).coeff 1=c} := by
  have he : (driftReader h clearMoment10KineticCoeff8).coeff 1=(driftReader h clearMoment10KineticCoeff8).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff8Norm.property]
    dsimp only [clearMoment10KineticCoeff8Norm]
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

def kineticDriftMoment10Coeff8Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff8).coeff 2=c} := by
  have he : (driftReader h clearMoment10KineticCoeff8).coeff 2=(driftReader h clearMoment10KineticCoeff8).coeff 2 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff8Norm.property]
    dsimp only [clearMoment10KineticCoeff8Norm]
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

def kineticDriftMoment10Coeff8Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff8).coeff 3=c} := by
  have he : (driftReader h clearMoment10KineticCoeff8).coeff 3=(driftReader h clearMoment10KineticCoeff8).coeff 3 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff8Norm.property]
    dsimp only [clearMoment10KineticCoeff8Norm]
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

def kineticDriftMoment10Coeff8Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff8).coeff 4=c} := by
  have he : (driftReader h clearMoment10KineticCoeff8).coeff 4=(driftReader h clearMoment10KineticCoeff8).coeff 4 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff8Norm.property]
    dsimp only [clearMoment10KineticCoeff8Norm]
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

def kineticDriftMoment10Coeff8Row5Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff8).coeff 5=c} := by
  have he : (driftReader h clearMoment10KineticCoeff8).coeff 5=(driftReader h clearMoment10KineticCoeff8).coeff 5 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff8Norm.property]
    dsimp only [clearMoment10KineticCoeff8Norm]
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

def kineticDriftMoment10Coeff9Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff9).coeff 0=c} := by
  have he : (driftReader h clearMoment10KineticCoeff9).coeff 0=(driftReader h clearMoment10KineticCoeff9).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff9Norm.property]
    dsimp only [clearMoment10KineticCoeff9Norm]
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

def kineticDriftMoment10Coeff9Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff9).coeff 1=c} := by
  have he : (driftReader h clearMoment10KineticCoeff9).coeff 1=(driftReader h clearMoment10KineticCoeff9).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff9Norm.property]
    dsimp only [clearMoment10KineticCoeff9Norm]
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

def kineticDriftMoment10Coeff9Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff9).coeff 2=c} := by
  have he : (driftReader h clearMoment10KineticCoeff9).coeff 2=(driftReader h clearMoment10KineticCoeff9).coeff 2 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff9Norm.property]
    dsimp only [clearMoment10KineticCoeff9Norm]
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

def kineticDriftMoment10Coeff9Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff9).coeff 3=c} := by
  have he : (driftReader h clearMoment10KineticCoeff9).coeff 3=(driftReader h clearMoment10KineticCoeff9).coeff 3 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff9Norm.property]
    dsimp only [clearMoment10KineticCoeff9Norm]
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

def kineticDriftMoment10Coeff9Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff9).coeff 4=c} := by
  have he : (driftReader h clearMoment10KineticCoeff9).coeff 4=(driftReader h clearMoment10KineticCoeff9).coeff 4 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff9Norm.property]
    dsimp only [clearMoment10KineticCoeff9Norm]
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

def kineticDriftMoment10Coeff9Row5Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff9).coeff 5=c} := by
  have he : (driftReader h clearMoment10KineticCoeff9).coeff 5=(driftReader h clearMoment10KineticCoeff9).coeff 5 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff9Norm.property]
    dsimp only [clearMoment10KineticCoeff9Norm]
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

def kineticDriftMoment10Coeff10Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff10).coeff 0=c} := by
  have he : (driftReader h clearMoment10KineticCoeff10).coeff 0=(driftReader h clearMoment10KineticCoeff10).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff10Norm.property]
    dsimp only [clearMoment10KineticCoeff10Norm]
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

def kineticDriftMoment10Coeff10Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff10).coeff 1=c} := by
  have he : (driftReader h clearMoment10KineticCoeff10).coeff 1=(driftReader h clearMoment10KineticCoeff10).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff10Norm.property]
    dsimp only [clearMoment10KineticCoeff10Norm]
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

def kineticDriftMoment10Coeff10Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff10).coeff 2=c} := by
  have he : (driftReader h clearMoment10KineticCoeff10).coeff 2=(driftReader h clearMoment10KineticCoeff10).coeff 2 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff10Norm.property]
    dsimp only [clearMoment10KineticCoeff10Norm]
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

def kineticDriftMoment10Coeff10Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff10).coeff 3=c} := by
  have he : (driftReader h clearMoment10KineticCoeff10).coeff 3=(driftReader h clearMoment10KineticCoeff10).coeff 3 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff10Norm.property]
    dsimp only [clearMoment10KineticCoeff10Norm]
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

def kineticDriftMoment10Coeff10Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff10).coeff 4=c} := by
  have he : (driftReader h clearMoment10KineticCoeff10).coeff 4=(driftReader h clearMoment10KineticCoeff10).coeff 4 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff10Norm.property]
    dsimp only [clearMoment10KineticCoeff10Norm]
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

def kineticDriftMoment10Coeff10Row5Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment10KineticCoeff10).coeff 5=c} := by
  have he : (driftReader h clearMoment10KineticCoeff10).coeff 5=(driftReader h clearMoment10KineticCoeff10).coeff 5 := rfl
  conv at he =>
    rhs
    rw [clearMoment10KineticCoeff10Norm.property]
    dsimp only [clearMoment10KineticCoeff10Norm]
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

theorem clearMoment10KineticCoeff0_drift_degree (h : ℂ) :
    (driftReader h clearMoment10KineticCoeff0).natDegree≤5 := by
  rw [clearMoment10KineticCoeff0Norm.property]
  dsimp only [clearMoment10KineticCoeff0Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment10KineticCoeff0_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment10KineticCoeff0=
      ∑ b ∈ Finset.range 6, (driftReader h clearMoment10KineticCoeff0).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment10KineticCoeff0_drift_degree h; omega) v

theorem clearMoment10KineticCoeff1_drift_degree (h : ℂ) :
    (driftReader h clearMoment10KineticCoeff1).natDegree≤5 := by
  rw [clearMoment10KineticCoeff1Norm.property]
  dsimp only [clearMoment10KineticCoeff1Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment10KineticCoeff1_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment10KineticCoeff1=
      ∑ b ∈ Finset.range 6, (driftReader h clearMoment10KineticCoeff1).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment10KineticCoeff1_drift_degree h; omega) v

theorem clearMoment10KineticCoeff2_drift_degree (h : ℂ) :
    (driftReader h clearMoment10KineticCoeff2).natDegree≤5 := by
  rw [clearMoment10KineticCoeff2Norm.property]
  dsimp only [clearMoment10KineticCoeff2Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment10KineticCoeff2_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment10KineticCoeff2=
      ∑ b ∈ Finset.range 6, (driftReader h clearMoment10KineticCoeff2).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment10KineticCoeff2_drift_degree h; omega) v

theorem clearMoment10KineticCoeff3_drift_degree (h : ℂ) :
    (driftReader h clearMoment10KineticCoeff3).natDegree≤5 := by
  rw [clearMoment10KineticCoeff3Norm.property]
  dsimp only [clearMoment10KineticCoeff3Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment10KineticCoeff3_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment10KineticCoeff3=
      ∑ b ∈ Finset.range 6, (driftReader h clearMoment10KineticCoeff3).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment10KineticCoeff3_drift_degree h; omega) v

theorem clearMoment10KineticCoeff4_drift_degree (h : ℂ) :
    (driftReader h clearMoment10KineticCoeff4).natDegree≤5 := by
  rw [clearMoment10KineticCoeff4Norm.property]
  dsimp only [clearMoment10KineticCoeff4Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment10KineticCoeff4_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment10KineticCoeff4=
      ∑ b ∈ Finset.range 6, (driftReader h clearMoment10KineticCoeff4).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment10KineticCoeff4_drift_degree h; omega) v

theorem clearMoment10KineticCoeff5_drift_degree (h : ℂ) :
    (driftReader h clearMoment10KineticCoeff5).natDegree≤5 := by
  rw [clearMoment10KineticCoeff5Norm.property]
  dsimp only [clearMoment10KineticCoeff5Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment10KineticCoeff5_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment10KineticCoeff5=
      ∑ b ∈ Finset.range 6, (driftReader h clearMoment10KineticCoeff5).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment10KineticCoeff5_drift_degree h; omega) v

theorem clearMoment10KineticCoeff6_drift_degree (h : ℂ) :
    (driftReader h clearMoment10KineticCoeff6).natDegree≤5 := by
  rw [clearMoment10KineticCoeff6Norm.property]
  dsimp only [clearMoment10KineticCoeff6Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment10KineticCoeff6_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment10KineticCoeff6=
      ∑ b ∈ Finset.range 6, (driftReader h clearMoment10KineticCoeff6).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment10KineticCoeff6_drift_degree h; omega) v

theorem clearMoment10KineticCoeff7_drift_degree (h : ℂ) :
    (driftReader h clearMoment10KineticCoeff7).natDegree≤5 := by
  rw [clearMoment10KineticCoeff7Norm.property]
  dsimp only [clearMoment10KineticCoeff7Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment10KineticCoeff7_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment10KineticCoeff7=
      ∑ b ∈ Finset.range 6, (driftReader h clearMoment10KineticCoeff7).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment10KineticCoeff7_drift_degree h; omega) v

theorem clearMoment10KineticCoeff8_drift_degree (h : ℂ) :
    (driftReader h clearMoment10KineticCoeff8).natDegree≤5 := by
  rw [clearMoment10KineticCoeff8Norm.property]
  dsimp only [clearMoment10KineticCoeff8Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment10KineticCoeff8_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment10KineticCoeff8=
      ∑ b ∈ Finset.range 6, (driftReader h clearMoment10KineticCoeff8).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment10KineticCoeff8_drift_degree h; omega) v

theorem clearMoment10KineticCoeff9_drift_degree (h : ℂ) :
    (driftReader h clearMoment10KineticCoeff9).natDegree≤5 := by
  rw [clearMoment10KineticCoeff9Norm.property]
  dsimp only [clearMoment10KineticCoeff9Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment10KineticCoeff9_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment10KineticCoeff9=
      ∑ b ∈ Finset.range 6, (driftReader h clearMoment10KineticCoeff9).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment10KineticCoeff9_drift_degree h; omega) v

theorem clearMoment10KineticCoeff10_drift_degree (h : ℂ) :
    (driftReader h clearMoment10KineticCoeff10).natDegree≤5 := by
  rw [clearMoment10KineticCoeff10Norm.property]
  dsimp only [clearMoment10KineticCoeff10Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment10KineticCoeff10_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment10KineticCoeff10=
      ∑ b ∈ Finset.range 6, (driftReader h clearMoment10KineticCoeff10).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment10KineticCoeff10_drift_degree h; omega) v

end
end HTGeometry.ThetaRatioKineticContraction
