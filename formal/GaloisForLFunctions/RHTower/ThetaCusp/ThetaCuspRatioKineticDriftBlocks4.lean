import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticBlockCoefficients4
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticDriftReader
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticDegree
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticDriftSupport
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def kineticDriftBlock4Coeff0Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock4.coeff 0)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock4.coeff 0)).coeff 0=(driftReader h (kineticBlock4.coeff 0)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock4Coeff0Norm.property]
    dsimp only [kineticBlock4Coeff0Norm]
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

def kineticDriftBlock4Coeff0Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock4.coeff 0)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock4.coeff 0)).coeff 1=(driftReader h (kineticBlock4.coeff 0)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock4Coeff0Norm.property]
    dsimp only [kineticBlock4Coeff0Norm]
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

def kineticDriftBlock4Coeff0Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock4.coeff 0)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock4.coeff 0)).coeff 2=(driftReader h (kineticBlock4.coeff 0)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock4Coeff0Norm.property]
    dsimp only [kineticBlock4Coeff0Norm]
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

def kineticDriftBlock4Coeff0Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock4.coeff 0)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock4.coeff 0)).coeff 3=(driftReader h (kineticBlock4.coeff 0)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock4Coeff0Norm.property]
    dsimp only [kineticBlock4Coeff0Norm]
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

theorem kineticBlock4Coeff0_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock4.coeff 0)).natDegree≤3 := by
  rw [kineticBlock4Coeff0Norm.property]
  dsimp only [kineticBlock4Coeff0Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock4Coeff1Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock4.coeff 1)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock4.coeff 1)).coeff 0=(driftReader h (kineticBlock4.coeff 1)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock4Coeff1Norm.property]
    dsimp only [kineticBlock4Coeff1Norm]
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

def kineticDriftBlock4Coeff1Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock4.coeff 1)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock4.coeff 1)).coeff 1=(driftReader h (kineticBlock4.coeff 1)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock4Coeff1Norm.property]
    dsimp only [kineticBlock4Coeff1Norm]
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

def kineticDriftBlock4Coeff1Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock4.coeff 1)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock4.coeff 1)).coeff 2=(driftReader h (kineticBlock4.coeff 1)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock4Coeff1Norm.property]
    dsimp only [kineticBlock4Coeff1Norm]
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

def kineticDriftBlock4Coeff1Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock4.coeff 1)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock4.coeff 1)).coeff 3=(driftReader h (kineticBlock4.coeff 1)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock4Coeff1Norm.property]
    dsimp only [kineticBlock4Coeff1Norm]
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

theorem kineticBlock4Coeff1_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock4.coeff 1)).natDegree≤3 := by
  rw [kineticBlock4Coeff1Norm.property]
  dsimp only [kineticBlock4Coeff1Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock4Coeff2Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock4.coeff 2)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock4.coeff 2)).coeff 0=(driftReader h (kineticBlock4.coeff 2)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock4Coeff2Norm.property]
    dsimp only [kineticBlock4Coeff2Norm]
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

def kineticDriftBlock4Coeff2Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock4.coeff 2)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock4.coeff 2)).coeff 1=(driftReader h (kineticBlock4.coeff 2)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock4Coeff2Norm.property]
    dsimp only [kineticBlock4Coeff2Norm]
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

def kineticDriftBlock4Coeff2Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock4.coeff 2)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock4.coeff 2)).coeff 2=(driftReader h (kineticBlock4.coeff 2)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock4Coeff2Norm.property]
    dsimp only [kineticBlock4Coeff2Norm]
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

def kineticDriftBlock4Coeff2Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock4.coeff 2)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock4.coeff 2)).coeff 3=(driftReader h (kineticBlock4.coeff 2)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock4Coeff2Norm.property]
    dsimp only [kineticBlock4Coeff2Norm]
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

theorem kineticBlock4Coeff2_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock4.coeff 2)).natDegree≤3 := by
  rw [kineticBlock4Coeff2Norm.property]
  dsimp only [kineticBlock4Coeff2Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock4Coeff3Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock4.coeff 3)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock4.coeff 3)).coeff 0=(driftReader h (kineticBlock4.coeff 3)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock4Coeff3Norm.property]
    dsimp only [kineticBlock4Coeff3Norm]
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

def kineticDriftBlock4Coeff3Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock4.coeff 3)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock4.coeff 3)).coeff 1=(driftReader h (kineticBlock4.coeff 3)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock4Coeff3Norm.property]
    dsimp only [kineticBlock4Coeff3Norm]
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

def kineticDriftBlock4Coeff3Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock4.coeff 3)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock4.coeff 3)).coeff 2=(driftReader h (kineticBlock4.coeff 3)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock4Coeff3Norm.property]
    dsimp only [kineticBlock4Coeff3Norm]
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

def kineticDriftBlock4Coeff3Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock4.coeff 3)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock4.coeff 3)).coeff 3=(driftReader h (kineticBlock4.coeff 3)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock4Coeff3Norm.property]
    dsimp only [kineticBlock4Coeff3Norm]
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

theorem kineticBlock4Coeff3_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock4.coeff 3)).natDegree≤3 := by
  rw [kineticBlock4Coeff3Norm.property]
  dsimp only [kineticBlock4Coeff3Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock4Coeff4Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock4.coeff 4)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock4.coeff 4)).coeff 0=(driftReader h (kineticBlock4.coeff 4)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock4Coeff4Norm.property]
    dsimp only [kineticBlock4Coeff4Norm]
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

def kineticDriftBlock4Coeff4Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock4.coeff 4)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock4.coeff 4)).coeff 1=(driftReader h (kineticBlock4.coeff 4)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock4Coeff4Norm.property]
    dsimp only [kineticBlock4Coeff4Norm]
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

def kineticDriftBlock4Coeff4Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock4.coeff 4)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock4.coeff 4)).coeff 2=(driftReader h (kineticBlock4.coeff 4)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock4Coeff4Norm.property]
    dsimp only [kineticBlock4Coeff4Norm]
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

def kineticDriftBlock4Coeff4Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock4.coeff 4)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock4.coeff 4)).coeff 3=(driftReader h (kineticBlock4.coeff 4)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock4Coeff4Norm.property]
    dsimp only [kineticBlock4Coeff4Norm]
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

theorem kineticBlock4Coeff4_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock4.coeff 4)).natDegree≤3 := by
  rw [kineticBlock4Coeff4Norm.property]
  dsimp only [kineticBlock4Coeff4Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock4Coeff5Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock4.coeff 5)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock4.coeff 5)).coeff 0=(driftReader h (kineticBlock4.coeff 5)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock4Coeff5Norm.property]
    dsimp only [kineticBlock4Coeff5Norm]
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

def kineticDriftBlock4Coeff5Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock4.coeff 5)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock4.coeff 5)).coeff 1=(driftReader h (kineticBlock4.coeff 5)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock4Coeff5Norm.property]
    dsimp only [kineticBlock4Coeff5Norm]
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

def kineticDriftBlock4Coeff5Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock4.coeff 5)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock4.coeff 5)).coeff 2=(driftReader h (kineticBlock4.coeff 5)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock4Coeff5Norm.property]
    dsimp only [kineticBlock4Coeff5Norm]
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

def kineticDriftBlock4Coeff5Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock4.coeff 5)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock4.coeff 5)).coeff 3=(driftReader h (kineticBlock4.coeff 5)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock4Coeff5Norm.property]
    dsimp only [kineticBlock4Coeff5Norm]
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

theorem kineticBlock4Coeff5_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock4.coeff 5)).natDegree≤3 := by
  rw [kineticBlock4Coeff5Norm.property]
  dsimp only [kineticBlock4Coeff5Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!


def kineticDriftBlock4Row0 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock4Coeff0Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock4Coeff0Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock4Coeff0Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock4Coeff0Row3Norm h).val else 0)

theorem kineticDriftBlock4Coeff0_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock4 0 b=kineticDriftBlock4Row0 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock4.coeff 0))
    (n := 4) (by have := kineticBlock4Coeff0_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock4.coeff 0)).coeff 0=(kineticDriftBlock4Coeff0Row0Norm h).val :=
    (kineticDriftBlock4Coeff0Row0Norm h).property
  have h1 : (driftReader h (kineticBlock4.coeff 0)).coeff 1=(kineticDriftBlock4Coeff0Row1Norm h).val :=
    (kineticDriftBlock4Coeff0Row1Norm h).property
  have h2 : (driftReader h (kineticBlock4.coeff 0)).coeff 2=(kineticDriftBlock4Coeff0Row2Norm h).val :=
    (kineticDriftBlock4Coeff0Row2Norm h).property
  have h3 : (driftReader h (kineticBlock4.coeff 0)).coeff 3=(kineticDriftBlock4Coeff0Row3Norm h).val :=
    (kineticDriftBlock4Coeff0Row3Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock4Row0,h0,h1,h2,h3] using he

def kineticDriftBlock4Row1 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock4Coeff1Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock4Coeff1Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock4Coeff1Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock4Coeff1Row3Norm h).val else 0)

theorem kineticDriftBlock4Coeff1_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock4 1 b=kineticDriftBlock4Row1 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock4.coeff 1))
    (n := 4) (by have := kineticBlock4Coeff1_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock4.coeff 1)).coeff 0=(kineticDriftBlock4Coeff1Row0Norm h).val :=
    (kineticDriftBlock4Coeff1Row0Norm h).property
  have h1 : (driftReader h (kineticBlock4.coeff 1)).coeff 1=(kineticDriftBlock4Coeff1Row1Norm h).val :=
    (kineticDriftBlock4Coeff1Row1Norm h).property
  have h2 : (driftReader h (kineticBlock4.coeff 1)).coeff 2=(kineticDriftBlock4Coeff1Row2Norm h).val :=
    (kineticDriftBlock4Coeff1Row2Norm h).property
  have h3 : (driftReader h (kineticBlock4.coeff 1)).coeff 3=(kineticDriftBlock4Coeff1Row3Norm h).val :=
    (kineticDriftBlock4Coeff1Row3Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock4Row1,h0,h1,h2,h3] using he

def kineticDriftBlock4Row2 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock4Coeff2Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock4Coeff2Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock4Coeff2Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock4Coeff2Row3Norm h).val else 0)

theorem kineticDriftBlock4Coeff2_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock4 2 b=kineticDriftBlock4Row2 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock4.coeff 2))
    (n := 4) (by have := kineticBlock4Coeff2_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock4.coeff 2)).coeff 0=(kineticDriftBlock4Coeff2Row0Norm h).val :=
    (kineticDriftBlock4Coeff2Row0Norm h).property
  have h1 : (driftReader h (kineticBlock4.coeff 2)).coeff 1=(kineticDriftBlock4Coeff2Row1Norm h).val :=
    (kineticDriftBlock4Coeff2Row1Norm h).property
  have h2 : (driftReader h (kineticBlock4.coeff 2)).coeff 2=(kineticDriftBlock4Coeff2Row2Norm h).val :=
    (kineticDriftBlock4Coeff2Row2Norm h).property
  have h3 : (driftReader h (kineticBlock4.coeff 2)).coeff 3=(kineticDriftBlock4Coeff2Row3Norm h).val :=
    (kineticDriftBlock4Coeff2Row3Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock4Row2,h0,h1,h2,h3] using he

def kineticDriftBlock4Row3 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock4Coeff3Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock4Coeff3Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock4Coeff3Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock4Coeff3Row3Norm h).val else 0)

theorem kineticDriftBlock4Coeff3_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock4 3 b=kineticDriftBlock4Row3 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock4.coeff 3))
    (n := 4) (by have := kineticBlock4Coeff3_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock4.coeff 3)).coeff 0=(kineticDriftBlock4Coeff3Row0Norm h).val :=
    (kineticDriftBlock4Coeff3Row0Norm h).property
  have h1 : (driftReader h (kineticBlock4.coeff 3)).coeff 1=(kineticDriftBlock4Coeff3Row1Norm h).val :=
    (kineticDriftBlock4Coeff3Row1Norm h).property
  have h2 : (driftReader h (kineticBlock4.coeff 3)).coeff 2=(kineticDriftBlock4Coeff3Row2Norm h).val :=
    (kineticDriftBlock4Coeff3Row2Norm h).property
  have h3 : (driftReader h (kineticBlock4.coeff 3)).coeff 3=(kineticDriftBlock4Coeff3Row3Norm h).val :=
    (kineticDriftBlock4Coeff3Row3Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock4Row3,h0,h1,h2,h3] using he

def kineticDriftBlock4Row4 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock4Coeff4Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock4Coeff4Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock4Coeff4Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock4Coeff4Row3Norm h).val else 0)

theorem kineticDriftBlock4Coeff4_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock4 4 b=kineticDriftBlock4Row4 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock4.coeff 4))
    (n := 4) (by have := kineticBlock4Coeff4_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock4.coeff 4)).coeff 0=(kineticDriftBlock4Coeff4Row0Norm h).val :=
    (kineticDriftBlock4Coeff4Row0Norm h).property
  have h1 : (driftReader h (kineticBlock4.coeff 4)).coeff 1=(kineticDriftBlock4Coeff4Row1Norm h).val :=
    (kineticDriftBlock4Coeff4Row1Norm h).property
  have h2 : (driftReader h (kineticBlock4.coeff 4)).coeff 2=(kineticDriftBlock4Coeff4Row2Norm h).val :=
    (kineticDriftBlock4Coeff4Row2Norm h).property
  have h3 : (driftReader h (kineticBlock4.coeff 4)).coeff 3=(kineticDriftBlock4Coeff4Row3Norm h).val :=
    (kineticDriftBlock4Coeff4Row3Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock4Row4,h0,h1,h2,h3] using he

def kineticDriftBlock4Row5 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock4Coeff5Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock4Coeff5Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock4Coeff5Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock4Coeff5Row3Norm h).val else 0)

theorem kineticDriftBlock4Coeff5_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock4 5 b=kineticDriftBlock4Row5 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock4.coeff 5))
    (n := 4) (by have := kineticBlock4Coeff5_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock4.coeff 5)).coeff 0=(kineticDriftBlock4Coeff5Row0Norm h).val :=
    (kineticDriftBlock4Coeff5Row0Norm h).property
  have h1 : (driftReader h (kineticBlock4.coeff 5)).coeff 1=(kineticDriftBlock4Coeff5Row1Norm h).val :=
    (kineticDriftBlock4Coeff5Row1Norm h).property
  have h2 : (driftReader h (kineticBlock4.coeff 5)).coeff 2=(kineticDriftBlock4Coeff5Row2Norm h).val :=
    (kineticDriftBlock4Coeff5Row2Norm h).property
  have h3 : (driftReader h (kineticBlock4.coeff 5)).coeff 3=(kineticDriftBlock4Coeff5Row3Norm h).val :=
    (kineticDriftBlock4Coeff5Row3Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock4Row5,h0,h1,h2,h3] using he

theorem kineticDriftBlock4_rows (h : ℂ) (j b : ℕ) :
    kineticDriftCell h kineticBlock4 j b=(if j=0 then kineticDriftBlock4Row0 h b else 0) + (if j=1 then kineticDriftBlock4Row1 h b else 0) + (if j=2 then kineticDriftBlock4Row2 h b else 0) + (if j=3 then kineticDriftBlock4Row3 h b else 0) + (if j=4 then kineticDriftBlock4Row4 h b else 0) + (if j=5 then kineticDriftBlock4Row5 h b else 0) := by
  by_cases hj : j≤5
  · interval_cases j
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock4Coeff0_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock4Coeff1_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock4Coeff2_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock4Coeff3_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock4Coeff4_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock4Coeff5_rows h b
  · have hp : kineticBlock4.coeff j=0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (kineticBlock4_degree.trans_lt (by omega))
    simp only [kineticDriftCell,hp,map_zero,Polynomial.coeff_zero,if_neg (show j≠0 by omega),if_neg (show j≠1 by omega),if_neg (show j≠2 by omega),if_neg (show j≠3 by omega),if_neg (show j≠4 by omega),if_neg (show j≠5 by omega),zero_add]

theorem kineticBlock4_drift_bound : KineticDriftBound kineticBlock4 3 := by
  intro h j b hb
  by_cases hj : j≤5
  · interval_cases j
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock4Coeff0_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock4Coeff1_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock4Coeff2_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock4Coeff3_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock4Coeff4_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock4Coeff5_drift_degree h).trans_lt hb)
  · have hp : kineticBlock4.coeff j=0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (kineticBlock4_degree.trans_lt (by omega))
    simp only [kineticDriftCell,hp,map_zero,Polynomial.coeff_zero]

end
end HTGeometry.ThetaRatioKineticContraction
