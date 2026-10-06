import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticBlockCoefficients8
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticDriftReader
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticDegree
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticDriftSupport
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def kineticDriftBlock8Coeff0Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 0)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock8.coeff 0)).coeff 0=(driftReader h (kineticBlock8.coeff 0)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff0Norm.property]
    dsimp only [kineticBlock8Coeff0Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff0Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 0)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock8.coeff 0)).coeff 1=(driftReader h (kineticBlock8.coeff 0)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff0Norm.property]
    dsimp only [kineticBlock8Coeff0Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff0Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 0)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock8.coeff 0)).coeff 2=(driftReader h (kineticBlock8.coeff 0)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff0Norm.property]
    dsimp only [kineticBlock8Coeff0Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff0Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 0)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock8.coeff 0)).coeff 3=(driftReader h (kineticBlock8.coeff 0)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff0Norm.property]
    dsimp only [kineticBlock8Coeff0Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff0Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 0)).coeff 4=c} := by
  have he : (driftReader h (kineticBlock8.coeff 0)).coeff 4=(driftReader h (kineticBlock8.coeff 0)).coeff 4 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff0Norm.property]
    dsimp only [kineticBlock8Coeff0Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff0Row5Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 0)).coeff 5=c} := by
  have he : (driftReader h (kineticBlock8.coeff 0)).coeff 5=(driftReader h (kineticBlock8.coeff 0)).coeff 5 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff0Norm.property]
    dsimp only [kineticBlock8Coeff0Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem kineticBlock8Coeff0_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock8.coeff 0)).natDegree≤5 := by
  rw [kineticBlock8Coeff0Norm.property]
  dsimp only [kineticBlock8Coeff0Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock8Coeff1Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 1)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock8.coeff 1)).coeff 0=(driftReader h (kineticBlock8.coeff 1)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff1Norm.property]
    dsimp only [kineticBlock8Coeff1Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff1Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 1)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock8.coeff 1)).coeff 1=(driftReader h (kineticBlock8.coeff 1)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff1Norm.property]
    dsimp only [kineticBlock8Coeff1Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff1Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 1)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock8.coeff 1)).coeff 2=(driftReader h (kineticBlock8.coeff 1)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff1Norm.property]
    dsimp only [kineticBlock8Coeff1Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff1Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 1)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock8.coeff 1)).coeff 3=(driftReader h (kineticBlock8.coeff 1)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff1Norm.property]
    dsimp only [kineticBlock8Coeff1Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff1Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 1)).coeff 4=c} := by
  have he : (driftReader h (kineticBlock8.coeff 1)).coeff 4=(driftReader h (kineticBlock8.coeff 1)).coeff 4 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff1Norm.property]
    dsimp only [kineticBlock8Coeff1Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff1Row5Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 1)).coeff 5=c} := by
  have he : (driftReader h (kineticBlock8.coeff 1)).coeff 5=(driftReader h (kineticBlock8.coeff 1)).coeff 5 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff1Norm.property]
    dsimp only [kineticBlock8Coeff1Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem kineticBlock8Coeff1_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock8.coeff 1)).natDegree≤5 := by
  rw [kineticBlock8Coeff1Norm.property]
  dsimp only [kineticBlock8Coeff1Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock8Coeff2Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 2)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock8.coeff 2)).coeff 0=(driftReader h (kineticBlock8.coeff 2)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff2Norm.property]
    dsimp only [kineticBlock8Coeff2Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff2Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 2)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock8.coeff 2)).coeff 1=(driftReader h (kineticBlock8.coeff 2)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff2Norm.property]
    dsimp only [kineticBlock8Coeff2Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff2Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 2)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock8.coeff 2)).coeff 2=(driftReader h (kineticBlock8.coeff 2)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff2Norm.property]
    dsimp only [kineticBlock8Coeff2Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff2Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 2)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock8.coeff 2)).coeff 3=(driftReader h (kineticBlock8.coeff 2)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff2Norm.property]
    dsimp only [kineticBlock8Coeff2Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff2Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 2)).coeff 4=c} := by
  have he : (driftReader h (kineticBlock8.coeff 2)).coeff 4=(driftReader h (kineticBlock8.coeff 2)).coeff 4 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff2Norm.property]
    dsimp only [kineticBlock8Coeff2Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff2Row5Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 2)).coeff 5=c} := by
  have he : (driftReader h (kineticBlock8.coeff 2)).coeff 5=(driftReader h (kineticBlock8.coeff 2)).coeff 5 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff2Norm.property]
    dsimp only [kineticBlock8Coeff2Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem kineticBlock8Coeff2_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock8.coeff 2)).natDegree≤5 := by
  rw [kineticBlock8Coeff2Norm.property]
  dsimp only [kineticBlock8Coeff2Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock8Coeff3Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 3)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock8.coeff 3)).coeff 0=(driftReader h (kineticBlock8.coeff 3)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff3Norm.property]
    dsimp only [kineticBlock8Coeff3Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff3Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 3)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock8.coeff 3)).coeff 1=(driftReader h (kineticBlock8.coeff 3)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff3Norm.property]
    dsimp only [kineticBlock8Coeff3Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff3Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 3)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock8.coeff 3)).coeff 2=(driftReader h (kineticBlock8.coeff 3)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff3Norm.property]
    dsimp only [kineticBlock8Coeff3Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff3Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 3)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock8.coeff 3)).coeff 3=(driftReader h (kineticBlock8.coeff 3)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff3Norm.property]
    dsimp only [kineticBlock8Coeff3Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff3Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 3)).coeff 4=c} := by
  have he : (driftReader h (kineticBlock8.coeff 3)).coeff 4=(driftReader h (kineticBlock8.coeff 3)).coeff 4 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff3Norm.property]
    dsimp only [kineticBlock8Coeff3Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff3Row5Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 3)).coeff 5=c} := by
  have he : (driftReader h (kineticBlock8.coeff 3)).coeff 5=(driftReader h (kineticBlock8.coeff 3)).coeff 5 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff3Norm.property]
    dsimp only [kineticBlock8Coeff3Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem kineticBlock8Coeff3_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock8.coeff 3)).natDegree≤5 := by
  rw [kineticBlock8Coeff3Norm.property]
  dsimp only [kineticBlock8Coeff3Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock8Coeff4Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 4)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock8.coeff 4)).coeff 0=(driftReader h (kineticBlock8.coeff 4)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff4Norm.property]
    dsimp only [kineticBlock8Coeff4Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff4Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 4)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock8.coeff 4)).coeff 1=(driftReader h (kineticBlock8.coeff 4)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff4Norm.property]
    dsimp only [kineticBlock8Coeff4Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff4Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 4)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock8.coeff 4)).coeff 2=(driftReader h (kineticBlock8.coeff 4)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff4Norm.property]
    dsimp only [kineticBlock8Coeff4Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff4Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 4)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock8.coeff 4)).coeff 3=(driftReader h (kineticBlock8.coeff 4)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff4Norm.property]
    dsimp only [kineticBlock8Coeff4Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff4Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 4)).coeff 4=c} := by
  have he : (driftReader h (kineticBlock8.coeff 4)).coeff 4=(driftReader h (kineticBlock8.coeff 4)).coeff 4 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff4Norm.property]
    dsimp only [kineticBlock8Coeff4Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff4Row5Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 4)).coeff 5=c} := by
  have he : (driftReader h (kineticBlock8.coeff 4)).coeff 5=(driftReader h (kineticBlock8.coeff 4)).coeff 5 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff4Norm.property]
    dsimp only [kineticBlock8Coeff4Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem kineticBlock8Coeff4_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock8.coeff 4)).natDegree≤5 := by
  rw [kineticBlock8Coeff4Norm.property]
  dsimp only [kineticBlock8Coeff4Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock8Coeff5Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 5)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock8.coeff 5)).coeff 0=(driftReader h (kineticBlock8.coeff 5)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff5Norm.property]
    dsimp only [kineticBlock8Coeff5Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff5Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 5)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock8.coeff 5)).coeff 1=(driftReader h (kineticBlock8.coeff 5)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff5Norm.property]
    dsimp only [kineticBlock8Coeff5Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff5Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 5)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock8.coeff 5)).coeff 2=(driftReader h (kineticBlock8.coeff 5)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff5Norm.property]
    dsimp only [kineticBlock8Coeff5Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff5Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 5)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock8.coeff 5)).coeff 3=(driftReader h (kineticBlock8.coeff 5)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff5Norm.property]
    dsimp only [kineticBlock8Coeff5Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff5Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 5)).coeff 4=c} := by
  have he : (driftReader h (kineticBlock8.coeff 5)).coeff 4=(driftReader h (kineticBlock8.coeff 5)).coeff 4 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff5Norm.property]
    dsimp only [kineticBlock8Coeff5Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff5Row5Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 5)).coeff 5=c} := by
  have he : (driftReader h (kineticBlock8.coeff 5)).coeff 5=(driftReader h (kineticBlock8.coeff 5)).coeff 5 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff5Norm.property]
    dsimp only [kineticBlock8Coeff5Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem kineticBlock8Coeff5_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock8.coeff 5)).natDegree≤5 := by
  rw [kineticBlock8Coeff5Norm.property]
  dsimp only [kineticBlock8Coeff5Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock8Coeff6Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 6)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock8.coeff 6)).coeff 0=(driftReader h (kineticBlock8.coeff 6)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff6Norm.property]
    dsimp only [kineticBlock8Coeff6Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff6Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 6)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock8.coeff 6)).coeff 1=(driftReader h (kineticBlock8.coeff 6)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff6Norm.property]
    dsimp only [kineticBlock8Coeff6Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff6Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 6)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock8.coeff 6)).coeff 2=(driftReader h (kineticBlock8.coeff 6)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff6Norm.property]
    dsimp only [kineticBlock8Coeff6Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff6Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 6)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock8.coeff 6)).coeff 3=(driftReader h (kineticBlock8.coeff 6)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff6Norm.property]
    dsimp only [kineticBlock8Coeff6Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff6Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 6)).coeff 4=c} := by
  have he : (driftReader h (kineticBlock8.coeff 6)).coeff 4=(driftReader h (kineticBlock8.coeff 6)).coeff 4 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff6Norm.property]
    dsimp only [kineticBlock8Coeff6Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff6Row5Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 6)).coeff 5=c} := by
  have he : (driftReader h (kineticBlock8.coeff 6)).coeff 5=(driftReader h (kineticBlock8.coeff 6)).coeff 5 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff6Norm.property]
    dsimp only [kineticBlock8Coeff6Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem kineticBlock8Coeff6_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock8.coeff 6)).natDegree≤5 := by
  rw [kineticBlock8Coeff6Norm.property]
  dsimp only [kineticBlock8Coeff6Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock8Coeff7Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 7)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock8.coeff 7)).coeff 0=(driftReader h (kineticBlock8.coeff 7)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff7Norm.property]
    dsimp only [kineticBlock8Coeff7Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff7Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 7)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock8.coeff 7)).coeff 1=(driftReader h (kineticBlock8.coeff 7)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff7Norm.property]
    dsimp only [kineticBlock8Coeff7Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff7Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 7)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock8.coeff 7)).coeff 2=(driftReader h (kineticBlock8.coeff 7)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff7Norm.property]
    dsimp only [kineticBlock8Coeff7Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff7Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 7)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock8.coeff 7)).coeff 3=(driftReader h (kineticBlock8.coeff 7)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff7Norm.property]
    dsimp only [kineticBlock8Coeff7Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff7Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 7)).coeff 4=c} := by
  have he : (driftReader h (kineticBlock8.coeff 7)).coeff 4=(driftReader h (kineticBlock8.coeff 7)).coeff 4 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff7Norm.property]
    dsimp only [kineticBlock8Coeff7Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff7Row5Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 7)).coeff 5=c} := by
  have he : (driftReader h (kineticBlock8.coeff 7)).coeff 5=(driftReader h (kineticBlock8.coeff 7)).coeff 5 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff7Norm.property]
    dsimp only [kineticBlock8Coeff7Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem kineticBlock8Coeff7_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock8.coeff 7)).natDegree≤5 := by
  rw [kineticBlock8Coeff7Norm.property]
  dsimp only [kineticBlock8Coeff7Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock8Coeff8Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 8)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock8.coeff 8)).coeff 0=(driftReader h (kineticBlock8.coeff 8)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff8Norm.property]
    dsimp only [kineticBlock8Coeff8Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff8Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 8)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock8.coeff 8)).coeff 1=(driftReader h (kineticBlock8.coeff 8)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff8Norm.property]
    dsimp only [kineticBlock8Coeff8Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff8Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 8)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock8.coeff 8)).coeff 2=(driftReader h (kineticBlock8.coeff 8)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff8Norm.property]
    dsimp only [kineticBlock8Coeff8Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff8Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 8)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock8.coeff 8)).coeff 3=(driftReader h (kineticBlock8.coeff 8)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff8Norm.property]
    dsimp only [kineticBlock8Coeff8Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff8Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 8)).coeff 4=c} := by
  have he : (driftReader h (kineticBlock8.coeff 8)).coeff 4=(driftReader h (kineticBlock8.coeff 8)).coeff 4 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff8Norm.property]
    dsimp only [kineticBlock8Coeff8Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff8Row5Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 8)).coeff 5=c} := by
  have he : (driftReader h (kineticBlock8.coeff 8)).coeff 5=(driftReader h (kineticBlock8.coeff 8)).coeff 5 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff8Norm.property]
    dsimp only [kineticBlock8Coeff8Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem kineticBlock8Coeff8_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock8.coeff 8)).natDegree≤5 := by
  rw [kineticBlock8Coeff8Norm.property]
  dsimp only [kineticBlock8Coeff8Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock8Coeff9Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 9)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock8.coeff 9)).coeff 0=(driftReader h (kineticBlock8.coeff 9)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff9Norm.property]
    dsimp only [kineticBlock8Coeff9Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff9Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 9)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock8.coeff 9)).coeff 1=(driftReader h (kineticBlock8.coeff 9)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff9Norm.property]
    dsimp only [kineticBlock8Coeff9Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff9Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 9)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock8.coeff 9)).coeff 2=(driftReader h (kineticBlock8.coeff 9)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff9Norm.property]
    dsimp only [kineticBlock8Coeff9Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff9Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 9)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock8.coeff 9)).coeff 3=(driftReader h (kineticBlock8.coeff 9)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff9Norm.property]
    dsimp only [kineticBlock8Coeff9Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff9Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 9)).coeff 4=c} := by
  have he : (driftReader h (kineticBlock8.coeff 9)).coeff 4=(driftReader h (kineticBlock8.coeff 9)).coeff 4 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff9Norm.property]
    dsimp only [kineticBlock8Coeff9Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftBlock8Coeff9Row5Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock8.coeff 9)).coeff 5=c} := by
  have he : (driftReader h (kineticBlock8.coeff 9)).coeff 5=(driftReader h (kineticBlock8.coeff 9)).coeff 5 := rfl
  conv at he =>
    rhs
    rw [kineticBlock8Coeff9Norm.property]
    dsimp only [kineticBlock8Coeff9Norm]
    norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
      _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
    simp only [←Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_neg,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_ofNat_mul,Polynomial.coeff_C,Polynomial.coeff_X_pow,
      Polynomial.coeff_mul_natCast,Polynomial.coeff_natCast_mul,Polynomial.coeff_natCast_ite]
    norm_num only [ite_true,ite_false,zero_add,add_zero,mul_zero,zero_mul]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem kineticBlock8Coeff9_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock8.coeff 9)).natDegree≤5 := by
  rw [kineticBlock8Coeff9Norm.property]
  dsimp only [kineticBlock8Coeff9Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!


def kineticDriftBlock8Row0 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock8Coeff0Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock8Coeff0Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock8Coeff0Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock8Coeff0Row3Norm h).val else 0) + (if b=4 then (kineticDriftBlock8Coeff0Row4Norm h).val else 0) + (if b=5 then (kineticDriftBlock8Coeff0Row5Norm h).val else 0)

theorem kineticDriftBlock8Coeff0_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock8 0 b=kineticDriftBlock8Row0 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock8.coeff 0))
    (n := 6) (by have := kineticBlock8Coeff0_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock8.coeff 0)).coeff 0=(kineticDriftBlock8Coeff0Row0Norm h).val :=
    (kineticDriftBlock8Coeff0Row0Norm h).property
  have h1 : (driftReader h (kineticBlock8.coeff 0)).coeff 1=(kineticDriftBlock8Coeff0Row1Norm h).val :=
    (kineticDriftBlock8Coeff0Row1Norm h).property
  have h2 : (driftReader h (kineticBlock8.coeff 0)).coeff 2=(kineticDriftBlock8Coeff0Row2Norm h).val :=
    (kineticDriftBlock8Coeff0Row2Norm h).property
  have h3 : (driftReader h (kineticBlock8.coeff 0)).coeff 3=(kineticDriftBlock8Coeff0Row3Norm h).val :=
    (kineticDriftBlock8Coeff0Row3Norm h).property
  have h4 : (driftReader h (kineticBlock8.coeff 0)).coeff 4=(kineticDriftBlock8Coeff0Row4Norm h).val :=
    (kineticDriftBlock8Coeff0Row4Norm h).property
  have h5 : (driftReader h (kineticBlock8.coeff 0)).coeff 5=(kineticDriftBlock8Coeff0Row5Norm h).val :=
    (kineticDriftBlock8Coeff0Row5Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock8Row0,h0,h1,h2,h3,h4,h5] using he

def kineticDriftBlock8Row1 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock8Coeff1Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock8Coeff1Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock8Coeff1Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock8Coeff1Row3Norm h).val else 0) + (if b=4 then (kineticDriftBlock8Coeff1Row4Norm h).val else 0) + (if b=5 then (kineticDriftBlock8Coeff1Row5Norm h).val else 0)

theorem kineticDriftBlock8Coeff1_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock8 1 b=kineticDriftBlock8Row1 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock8.coeff 1))
    (n := 6) (by have := kineticBlock8Coeff1_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock8.coeff 1)).coeff 0=(kineticDriftBlock8Coeff1Row0Norm h).val :=
    (kineticDriftBlock8Coeff1Row0Norm h).property
  have h1 : (driftReader h (kineticBlock8.coeff 1)).coeff 1=(kineticDriftBlock8Coeff1Row1Norm h).val :=
    (kineticDriftBlock8Coeff1Row1Norm h).property
  have h2 : (driftReader h (kineticBlock8.coeff 1)).coeff 2=(kineticDriftBlock8Coeff1Row2Norm h).val :=
    (kineticDriftBlock8Coeff1Row2Norm h).property
  have h3 : (driftReader h (kineticBlock8.coeff 1)).coeff 3=(kineticDriftBlock8Coeff1Row3Norm h).val :=
    (kineticDriftBlock8Coeff1Row3Norm h).property
  have h4 : (driftReader h (kineticBlock8.coeff 1)).coeff 4=(kineticDriftBlock8Coeff1Row4Norm h).val :=
    (kineticDriftBlock8Coeff1Row4Norm h).property
  have h5 : (driftReader h (kineticBlock8.coeff 1)).coeff 5=(kineticDriftBlock8Coeff1Row5Norm h).val :=
    (kineticDriftBlock8Coeff1Row5Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock8Row1,h0,h1,h2,h3,h4,h5] using he

def kineticDriftBlock8Row2 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock8Coeff2Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock8Coeff2Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock8Coeff2Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock8Coeff2Row3Norm h).val else 0) + (if b=4 then (kineticDriftBlock8Coeff2Row4Norm h).val else 0) + (if b=5 then (kineticDriftBlock8Coeff2Row5Norm h).val else 0)

theorem kineticDriftBlock8Coeff2_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock8 2 b=kineticDriftBlock8Row2 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock8.coeff 2))
    (n := 6) (by have := kineticBlock8Coeff2_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock8.coeff 2)).coeff 0=(kineticDriftBlock8Coeff2Row0Norm h).val :=
    (kineticDriftBlock8Coeff2Row0Norm h).property
  have h1 : (driftReader h (kineticBlock8.coeff 2)).coeff 1=(kineticDriftBlock8Coeff2Row1Norm h).val :=
    (kineticDriftBlock8Coeff2Row1Norm h).property
  have h2 : (driftReader h (kineticBlock8.coeff 2)).coeff 2=(kineticDriftBlock8Coeff2Row2Norm h).val :=
    (kineticDriftBlock8Coeff2Row2Norm h).property
  have h3 : (driftReader h (kineticBlock8.coeff 2)).coeff 3=(kineticDriftBlock8Coeff2Row3Norm h).val :=
    (kineticDriftBlock8Coeff2Row3Norm h).property
  have h4 : (driftReader h (kineticBlock8.coeff 2)).coeff 4=(kineticDriftBlock8Coeff2Row4Norm h).val :=
    (kineticDriftBlock8Coeff2Row4Norm h).property
  have h5 : (driftReader h (kineticBlock8.coeff 2)).coeff 5=(kineticDriftBlock8Coeff2Row5Norm h).val :=
    (kineticDriftBlock8Coeff2Row5Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock8Row2,h0,h1,h2,h3,h4,h5] using he

def kineticDriftBlock8Row3 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock8Coeff3Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock8Coeff3Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock8Coeff3Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock8Coeff3Row3Norm h).val else 0) + (if b=4 then (kineticDriftBlock8Coeff3Row4Norm h).val else 0) + (if b=5 then (kineticDriftBlock8Coeff3Row5Norm h).val else 0)

theorem kineticDriftBlock8Coeff3_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock8 3 b=kineticDriftBlock8Row3 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock8.coeff 3))
    (n := 6) (by have := kineticBlock8Coeff3_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock8.coeff 3)).coeff 0=(kineticDriftBlock8Coeff3Row0Norm h).val :=
    (kineticDriftBlock8Coeff3Row0Norm h).property
  have h1 : (driftReader h (kineticBlock8.coeff 3)).coeff 1=(kineticDriftBlock8Coeff3Row1Norm h).val :=
    (kineticDriftBlock8Coeff3Row1Norm h).property
  have h2 : (driftReader h (kineticBlock8.coeff 3)).coeff 2=(kineticDriftBlock8Coeff3Row2Norm h).val :=
    (kineticDriftBlock8Coeff3Row2Norm h).property
  have h3 : (driftReader h (kineticBlock8.coeff 3)).coeff 3=(kineticDriftBlock8Coeff3Row3Norm h).val :=
    (kineticDriftBlock8Coeff3Row3Norm h).property
  have h4 : (driftReader h (kineticBlock8.coeff 3)).coeff 4=(kineticDriftBlock8Coeff3Row4Norm h).val :=
    (kineticDriftBlock8Coeff3Row4Norm h).property
  have h5 : (driftReader h (kineticBlock8.coeff 3)).coeff 5=(kineticDriftBlock8Coeff3Row5Norm h).val :=
    (kineticDriftBlock8Coeff3Row5Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock8Row3,h0,h1,h2,h3,h4,h5] using he

def kineticDriftBlock8Row4 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock8Coeff4Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock8Coeff4Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock8Coeff4Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock8Coeff4Row3Norm h).val else 0) + (if b=4 then (kineticDriftBlock8Coeff4Row4Norm h).val else 0) + (if b=5 then (kineticDriftBlock8Coeff4Row5Norm h).val else 0)

theorem kineticDriftBlock8Coeff4_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock8 4 b=kineticDriftBlock8Row4 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock8.coeff 4))
    (n := 6) (by have := kineticBlock8Coeff4_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock8.coeff 4)).coeff 0=(kineticDriftBlock8Coeff4Row0Norm h).val :=
    (kineticDriftBlock8Coeff4Row0Norm h).property
  have h1 : (driftReader h (kineticBlock8.coeff 4)).coeff 1=(kineticDriftBlock8Coeff4Row1Norm h).val :=
    (kineticDriftBlock8Coeff4Row1Norm h).property
  have h2 : (driftReader h (kineticBlock8.coeff 4)).coeff 2=(kineticDriftBlock8Coeff4Row2Norm h).val :=
    (kineticDriftBlock8Coeff4Row2Norm h).property
  have h3 : (driftReader h (kineticBlock8.coeff 4)).coeff 3=(kineticDriftBlock8Coeff4Row3Norm h).val :=
    (kineticDriftBlock8Coeff4Row3Norm h).property
  have h4 : (driftReader h (kineticBlock8.coeff 4)).coeff 4=(kineticDriftBlock8Coeff4Row4Norm h).val :=
    (kineticDriftBlock8Coeff4Row4Norm h).property
  have h5 : (driftReader h (kineticBlock8.coeff 4)).coeff 5=(kineticDriftBlock8Coeff4Row5Norm h).val :=
    (kineticDriftBlock8Coeff4Row5Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock8Row4,h0,h1,h2,h3,h4,h5] using he

def kineticDriftBlock8Row5 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock8Coeff5Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock8Coeff5Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock8Coeff5Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock8Coeff5Row3Norm h).val else 0) + (if b=4 then (kineticDriftBlock8Coeff5Row4Norm h).val else 0) + (if b=5 then (kineticDriftBlock8Coeff5Row5Norm h).val else 0)

theorem kineticDriftBlock8Coeff5_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock8 5 b=kineticDriftBlock8Row5 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock8.coeff 5))
    (n := 6) (by have := kineticBlock8Coeff5_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock8.coeff 5)).coeff 0=(kineticDriftBlock8Coeff5Row0Norm h).val :=
    (kineticDriftBlock8Coeff5Row0Norm h).property
  have h1 : (driftReader h (kineticBlock8.coeff 5)).coeff 1=(kineticDriftBlock8Coeff5Row1Norm h).val :=
    (kineticDriftBlock8Coeff5Row1Norm h).property
  have h2 : (driftReader h (kineticBlock8.coeff 5)).coeff 2=(kineticDriftBlock8Coeff5Row2Norm h).val :=
    (kineticDriftBlock8Coeff5Row2Norm h).property
  have h3 : (driftReader h (kineticBlock8.coeff 5)).coeff 3=(kineticDriftBlock8Coeff5Row3Norm h).val :=
    (kineticDriftBlock8Coeff5Row3Norm h).property
  have h4 : (driftReader h (kineticBlock8.coeff 5)).coeff 4=(kineticDriftBlock8Coeff5Row4Norm h).val :=
    (kineticDriftBlock8Coeff5Row4Norm h).property
  have h5 : (driftReader h (kineticBlock8.coeff 5)).coeff 5=(kineticDriftBlock8Coeff5Row5Norm h).val :=
    (kineticDriftBlock8Coeff5Row5Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock8Row5,h0,h1,h2,h3,h4,h5] using he

def kineticDriftBlock8Row6 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock8Coeff6Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock8Coeff6Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock8Coeff6Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock8Coeff6Row3Norm h).val else 0) + (if b=4 then (kineticDriftBlock8Coeff6Row4Norm h).val else 0) + (if b=5 then (kineticDriftBlock8Coeff6Row5Norm h).val else 0)

theorem kineticDriftBlock8Coeff6_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock8 6 b=kineticDriftBlock8Row6 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock8.coeff 6))
    (n := 6) (by have := kineticBlock8Coeff6_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock8.coeff 6)).coeff 0=(kineticDriftBlock8Coeff6Row0Norm h).val :=
    (kineticDriftBlock8Coeff6Row0Norm h).property
  have h1 : (driftReader h (kineticBlock8.coeff 6)).coeff 1=(kineticDriftBlock8Coeff6Row1Norm h).val :=
    (kineticDriftBlock8Coeff6Row1Norm h).property
  have h2 : (driftReader h (kineticBlock8.coeff 6)).coeff 2=(kineticDriftBlock8Coeff6Row2Norm h).val :=
    (kineticDriftBlock8Coeff6Row2Norm h).property
  have h3 : (driftReader h (kineticBlock8.coeff 6)).coeff 3=(kineticDriftBlock8Coeff6Row3Norm h).val :=
    (kineticDriftBlock8Coeff6Row3Norm h).property
  have h4 : (driftReader h (kineticBlock8.coeff 6)).coeff 4=(kineticDriftBlock8Coeff6Row4Norm h).val :=
    (kineticDriftBlock8Coeff6Row4Norm h).property
  have h5 : (driftReader h (kineticBlock8.coeff 6)).coeff 5=(kineticDriftBlock8Coeff6Row5Norm h).val :=
    (kineticDriftBlock8Coeff6Row5Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock8Row6,h0,h1,h2,h3,h4,h5] using he

def kineticDriftBlock8Row7 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock8Coeff7Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock8Coeff7Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock8Coeff7Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock8Coeff7Row3Norm h).val else 0) + (if b=4 then (kineticDriftBlock8Coeff7Row4Norm h).val else 0) + (if b=5 then (kineticDriftBlock8Coeff7Row5Norm h).val else 0)

theorem kineticDriftBlock8Coeff7_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock8 7 b=kineticDriftBlock8Row7 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock8.coeff 7))
    (n := 6) (by have := kineticBlock8Coeff7_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock8.coeff 7)).coeff 0=(kineticDriftBlock8Coeff7Row0Norm h).val :=
    (kineticDriftBlock8Coeff7Row0Norm h).property
  have h1 : (driftReader h (kineticBlock8.coeff 7)).coeff 1=(kineticDriftBlock8Coeff7Row1Norm h).val :=
    (kineticDriftBlock8Coeff7Row1Norm h).property
  have h2 : (driftReader h (kineticBlock8.coeff 7)).coeff 2=(kineticDriftBlock8Coeff7Row2Norm h).val :=
    (kineticDriftBlock8Coeff7Row2Norm h).property
  have h3 : (driftReader h (kineticBlock8.coeff 7)).coeff 3=(kineticDriftBlock8Coeff7Row3Norm h).val :=
    (kineticDriftBlock8Coeff7Row3Norm h).property
  have h4 : (driftReader h (kineticBlock8.coeff 7)).coeff 4=(kineticDriftBlock8Coeff7Row4Norm h).val :=
    (kineticDriftBlock8Coeff7Row4Norm h).property
  have h5 : (driftReader h (kineticBlock8.coeff 7)).coeff 5=(kineticDriftBlock8Coeff7Row5Norm h).val :=
    (kineticDriftBlock8Coeff7Row5Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock8Row7,h0,h1,h2,h3,h4,h5] using he

def kineticDriftBlock8Row8 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock8Coeff8Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock8Coeff8Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock8Coeff8Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock8Coeff8Row3Norm h).val else 0) + (if b=4 then (kineticDriftBlock8Coeff8Row4Norm h).val else 0) + (if b=5 then (kineticDriftBlock8Coeff8Row5Norm h).val else 0)

theorem kineticDriftBlock8Coeff8_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock8 8 b=kineticDriftBlock8Row8 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock8.coeff 8))
    (n := 6) (by have := kineticBlock8Coeff8_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock8.coeff 8)).coeff 0=(kineticDriftBlock8Coeff8Row0Norm h).val :=
    (kineticDriftBlock8Coeff8Row0Norm h).property
  have h1 : (driftReader h (kineticBlock8.coeff 8)).coeff 1=(kineticDriftBlock8Coeff8Row1Norm h).val :=
    (kineticDriftBlock8Coeff8Row1Norm h).property
  have h2 : (driftReader h (kineticBlock8.coeff 8)).coeff 2=(kineticDriftBlock8Coeff8Row2Norm h).val :=
    (kineticDriftBlock8Coeff8Row2Norm h).property
  have h3 : (driftReader h (kineticBlock8.coeff 8)).coeff 3=(kineticDriftBlock8Coeff8Row3Norm h).val :=
    (kineticDriftBlock8Coeff8Row3Norm h).property
  have h4 : (driftReader h (kineticBlock8.coeff 8)).coeff 4=(kineticDriftBlock8Coeff8Row4Norm h).val :=
    (kineticDriftBlock8Coeff8Row4Norm h).property
  have h5 : (driftReader h (kineticBlock8.coeff 8)).coeff 5=(kineticDriftBlock8Coeff8Row5Norm h).val :=
    (kineticDriftBlock8Coeff8Row5Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock8Row8,h0,h1,h2,h3,h4,h5] using he

def kineticDriftBlock8Row9 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock8Coeff9Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock8Coeff9Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock8Coeff9Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock8Coeff9Row3Norm h).val else 0) + (if b=4 then (kineticDriftBlock8Coeff9Row4Norm h).val else 0) + (if b=5 then (kineticDriftBlock8Coeff9Row5Norm h).val else 0)

theorem kineticDriftBlock8Coeff9_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock8 9 b=kineticDriftBlock8Row9 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock8.coeff 9))
    (n := 6) (by have := kineticBlock8Coeff9_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock8.coeff 9)).coeff 0=(kineticDriftBlock8Coeff9Row0Norm h).val :=
    (kineticDriftBlock8Coeff9Row0Norm h).property
  have h1 : (driftReader h (kineticBlock8.coeff 9)).coeff 1=(kineticDriftBlock8Coeff9Row1Norm h).val :=
    (kineticDriftBlock8Coeff9Row1Norm h).property
  have h2 : (driftReader h (kineticBlock8.coeff 9)).coeff 2=(kineticDriftBlock8Coeff9Row2Norm h).val :=
    (kineticDriftBlock8Coeff9Row2Norm h).property
  have h3 : (driftReader h (kineticBlock8.coeff 9)).coeff 3=(kineticDriftBlock8Coeff9Row3Norm h).val :=
    (kineticDriftBlock8Coeff9Row3Norm h).property
  have h4 : (driftReader h (kineticBlock8.coeff 9)).coeff 4=(kineticDriftBlock8Coeff9Row4Norm h).val :=
    (kineticDriftBlock8Coeff9Row4Norm h).property
  have h5 : (driftReader h (kineticBlock8.coeff 9)).coeff 5=(kineticDriftBlock8Coeff9Row5Norm h).val :=
    (kineticDriftBlock8Coeff9Row5Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock8Row9,h0,h1,h2,h3,h4,h5] using he

theorem kineticDriftBlock8_rows (h : ℂ) (j b : ℕ) :
    kineticDriftCell h kineticBlock8 j b=(if j=0 then kineticDriftBlock8Row0 h b else 0) + (if j=1 then kineticDriftBlock8Row1 h b else 0) + (if j=2 then kineticDriftBlock8Row2 h b else 0) + (if j=3 then kineticDriftBlock8Row3 h b else 0) + (if j=4 then kineticDriftBlock8Row4 h b else 0) + (if j=5 then kineticDriftBlock8Row5 h b else 0) + (if j=6 then kineticDriftBlock8Row6 h b else 0) + (if j=7 then kineticDriftBlock8Row7 h b else 0) + (if j=8 then kineticDriftBlock8Row8 h b else 0) + (if j=9 then kineticDriftBlock8Row9 h b else 0) := by
  by_cases hj : j≤9
  · interval_cases j
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock8Coeff0_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock8Coeff1_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock8Coeff2_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock8Coeff3_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock8Coeff4_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock8Coeff5_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock8Coeff6_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock8Coeff7_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock8Coeff8_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock8Coeff9_rows h b
  · have hp : kineticBlock8.coeff j=0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (kineticBlock8_degree.trans_lt (by omega))
    simp only [kineticDriftCell,hp,map_zero,Polynomial.coeff_zero,if_neg (show j≠0 by omega),if_neg (show j≠1 by omega),if_neg (show j≠2 by omega),if_neg (show j≠3 by omega),if_neg (show j≠4 by omega),if_neg (show j≠5 by omega),if_neg (show j≠6 by omega),if_neg (show j≠7 by omega),if_neg (show j≠8 by omega),if_neg (show j≠9 by omega),zero_add]

theorem kineticBlock8_drift_bound : KineticDriftBound kineticBlock8 5 := by
  intro h j b hb
  by_cases hj : j≤9
  · interval_cases j
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock8Coeff0_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock8Coeff1_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock8Coeff2_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock8Coeff3_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock8Coeff4_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock8Coeff5_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock8Coeff6_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock8Coeff7_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock8Coeff8_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock8Coeff9_drift_degree h).trans_lt hb)
  · have hp : kineticBlock8.coeff j=0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (kineticBlock8_degree.trans_lt (by omega))
    simp only [kineticDriftCell,hp,map_zero,Polynomial.coeff_zero]

end
end HTGeometry.ThetaRatioKineticContraction
