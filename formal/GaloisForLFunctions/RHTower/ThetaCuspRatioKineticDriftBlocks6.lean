import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticBlockCoefficients6
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticDriftReader
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticDegree
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticDriftSupport
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def kineticDriftBlock6Coeff0Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 0)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock6.coeff 0)).coeff 0=(driftReader h (kineticBlock6.coeff 0)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff0Norm.property]
    dsimp only [kineticBlock6Coeff0Norm]
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

def kineticDriftBlock6Coeff0Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 0)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock6.coeff 0)).coeff 1=(driftReader h (kineticBlock6.coeff 0)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff0Norm.property]
    dsimp only [kineticBlock6Coeff0Norm]
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

def kineticDriftBlock6Coeff0Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 0)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock6.coeff 0)).coeff 2=(driftReader h (kineticBlock6.coeff 0)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff0Norm.property]
    dsimp only [kineticBlock6Coeff0Norm]
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

def kineticDriftBlock6Coeff0Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 0)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock6.coeff 0)).coeff 3=(driftReader h (kineticBlock6.coeff 0)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff0Norm.property]
    dsimp only [kineticBlock6Coeff0Norm]
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

def kineticDriftBlock6Coeff0Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 0)).coeff 4=c} := by
  have he : (driftReader h (kineticBlock6.coeff 0)).coeff 4=(driftReader h (kineticBlock6.coeff 0)).coeff 4 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff0Norm.property]
    dsimp only [kineticBlock6Coeff0Norm]
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

theorem kineticBlock6Coeff0_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock6.coeff 0)).natDegree≤4 := by
  rw [kineticBlock6Coeff0Norm.property]
  dsimp only [kineticBlock6Coeff0Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock6Coeff1Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 1)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock6.coeff 1)).coeff 0=(driftReader h (kineticBlock6.coeff 1)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff1Norm.property]
    dsimp only [kineticBlock6Coeff1Norm]
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

def kineticDriftBlock6Coeff1Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 1)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock6.coeff 1)).coeff 1=(driftReader h (kineticBlock6.coeff 1)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff1Norm.property]
    dsimp only [kineticBlock6Coeff1Norm]
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

def kineticDriftBlock6Coeff1Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 1)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock6.coeff 1)).coeff 2=(driftReader h (kineticBlock6.coeff 1)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff1Norm.property]
    dsimp only [kineticBlock6Coeff1Norm]
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

def kineticDriftBlock6Coeff1Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 1)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock6.coeff 1)).coeff 3=(driftReader h (kineticBlock6.coeff 1)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff1Norm.property]
    dsimp only [kineticBlock6Coeff1Norm]
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

def kineticDriftBlock6Coeff1Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 1)).coeff 4=c} := by
  have he : (driftReader h (kineticBlock6.coeff 1)).coeff 4=(driftReader h (kineticBlock6.coeff 1)).coeff 4 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff1Norm.property]
    dsimp only [kineticBlock6Coeff1Norm]
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

theorem kineticBlock6Coeff1_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock6.coeff 1)).natDegree≤4 := by
  rw [kineticBlock6Coeff1Norm.property]
  dsimp only [kineticBlock6Coeff1Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock6Coeff2Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 2)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock6.coeff 2)).coeff 0=(driftReader h (kineticBlock6.coeff 2)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff2Norm.property]
    dsimp only [kineticBlock6Coeff2Norm]
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

def kineticDriftBlock6Coeff2Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 2)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock6.coeff 2)).coeff 1=(driftReader h (kineticBlock6.coeff 2)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff2Norm.property]
    dsimp only [kineticBlock6Coeff2Norm]
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

def kineticDriftBlock6Coeff2Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 2)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock6.coeff 2)).coeff 2=(driftReader h (kineticBlock6.coeff 2)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff2Norm.property]
    dsimp only [kineticBlock6Coeff2Norm]
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

def kineticDriftBlock6Coeff2Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 2)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock6.coeff 2)).coeff 3=(driftReader h (kineticBlock6.coeff 2)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff2Norm.property]
    dsimp only [kineticBlock6Coeff2Norm]
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

def kineticDriftBlock6Coeff2Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 2)).coeff 4=c} := by
  have he : (driftReader h (kineticBlock6.coeff 2)).coeff 4=(driftReader h (kineticBlock6.coeff 2)).coeff 4 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff2Norm.property]
    dsimp only [kineticBlock6Coeff2Norm]
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

theorem kineticBlock6Coeff2_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock6.coeff 2)).natDegree≤4 := by
  rw [kineticBlock6Coeff2Norm.property]
  dsimp only [kineticBlock6Coeff2Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock6Coeff3Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 3)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock6.coeff 3)).coeff 0=(driftReader h (kineticBlock6.coeff 3)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff3Norm.property]
    dsimp only [kineticBlock6Coeff3Norm]
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

def kineticDriftBlock6Coeff3Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 3)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock6.coeff 3)).coeff 1=(driftReader h (kineticBlock6.coeff 3)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff3Norm.property]
    dsimp only [kineticBlock6Coeff3Norm]
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

def kineticDriftBlock6Coeff3Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 3)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock6.coeff 3)).coeff 2=(driftReader h (kineticBlock6.coeff 3)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff3Norm.property]
    dsimp only [kineticBlock6Coeff3Norm]
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

def kineticDriftBlock6Coeff3Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 3)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock6.coeff 3)).coeff 3=(driftReader h (kineticBlock6.coeff 3)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff3Norm.property]
    dsimp only [kineticBlock6Coeff3Norm]
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

def kineticDriftBlock6Coeff3Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 3)).coeff 4=c} := by
  have he : (driftReader h (kineticBlock6.coeff 3)).coeff 4=(driftReader h (kineticBlock6.coeff 3)).coeff 4 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff3Norm.property]
    dsimp only [kineticBlock6Coeff3Norm]
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

theorem kineticBlock6Coeff3_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock6.coeff 3)).natDegree≤4 := by
  rw [kineticBlock6Coeff3Norm.property]
  dsimp only [kineticBlock6Coeff3Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock6Coeff4Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 4)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock6.coeff 4)).coeff 0=(driftReader h (kineticBlock6.coeff 4)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff4Norm.property]
    dsimp only [kineticBlock6Coeff4Norm]
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

def kineticDriftBlock6Coeff4Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 4)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock6.coeff 4)).coeff 1=(driftReader h (kineticBlock6.coeff 4)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff4Norm.property]
    dsimp only [kineticBlock6Coeff4Norm]
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

def kineticDriftBlock6Coeff4Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 4)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock6.coeff 4)).coeff 2=(driftReader h (kineticBlock6.coeff 4)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff4Norm.property]
    dsimp only [kineticBlock6Coeff4Norm]
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

def kineticDriftBlock6Coeff4Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 4)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock6.coeff 4)).coeff 3=(driftReader h (kineticBlock6.coeff 4)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff4Norm.property]
    dsimp only [kineticBlock6Coeff4Norm]
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

def kineticDriftBlock6Coeff4Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 4)).coeff 4=c} := by
  have he : (driftReader h (kineticBlock6.coeff 4)).coeff 4=(driftReader h (kineticBlock6.coeff 4)).coeff 4 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff4Norm.property]
    dsimp only [kineticBlock6Coeff4Norm]
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

theorem kineticBlock6Coeff4_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock6.coeff 4)).natDegree≤4 := by
  rw [kineticBlock6Coeff4Norm.property]
  dsimp only [kineticBlock6Coeff4Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock6Coeff5Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 5)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock6.coeff 5)).coeff 0=(driftReader h (kineticBlock6.coeff 5)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff5Norm.property]
    dsimp only [kineticBlock6Coeff5Norm]
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

def kineticDriftBlock6Coeff5Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 5)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock6.coeff 5)).coeff 1=(driftReader h (kineticBlock6.coeff 5)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff5Norm.property]
    dsimp only [kineticBlock6Coeff5Norm]
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

def kineticDriftBlock6Coeff5Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 5)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock6.coeff 5)).coeff 2=(driftReader h (kineticBlock6.coeff 5)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff5Norm.property]
    dsimp only [kineticBlock6Coeff5Norm]
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

def kineticDriftBlock6Coeff5Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 5)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock6.coeff 5)).coeff 3=(driftReader h (kineticBlock6.coeff 5)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff5Norm.property]
    dsimp only [kineticBlock6Coeff5Norm]
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

def kineticDriftBlock6Coeff5Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 5)).coeff 4=c} := by
  have he : (driftReader h (kineticBlock6.coeff 5)).coeff 4=(driftReader h (kineticBlock6.coeff 5)).coeff 4 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff5Norm.property]
    dsimp only [kineticBlock6Coeff5Norm]
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

theorem kineticBlock6Coeff5_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock6.coeff 5)).natDegree≤4 := by
  rw [kineticBlock6Coeff5Norm.property]
  dsimp only [kineticBlock6Coeff5Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock6Coeff6Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 6)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock6.coeff 6)).coeff 0=(driftReader h (kineticBlock6.coeff 6)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff6Norm.property]
    dsimp only [kineticBlock6Coeff6Norm]
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

def kineticDriftBlock6Coeff6Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 6)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock6.coeff 6)).coeff 1=(driftReader h (kineticBlock6.coeff 6)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff6Norm.property]
    dsimp only [kineticBlock6Coeff6Norm]
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

def kineticDriftBlock6Coeff6Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 6)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock6.coeff 6)).coeff 2=(driftReader h (kineticBlock6.coeff 6)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff6Norm.property]
    dsimp only [kineticBlock6Coeff6Norm]
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

def kineticDriftBlock6Coeff6Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 6)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock6.coeff 6)).coeff 3=(driftReader h (kineticBlock6.coeff 6)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff6Norm.property]
    dsimp only [kineticBlock6Coeff6Norm]
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

def kineticDriftBlock6Coeff6Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 6)).coeff 4=c} := by
  have he : (driftReader h (kineticBlock6.coeff 6)).coeff 4=(driftReader h (kineticBlock6.coeff 6)).coeff 4 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff6Norm.property]
    dsimp only [kineticBlock6Coeff6Norm]
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

theorem kineticBlock6Coeff6_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock6.coeff 6)).natDegree≤4 := by
  rw [kineticBlock6Coeff6Norm.property]
  dsimp only [kineticBlock6Coeff6Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock6Coeff7Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 7)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock6.coeff 7)).coeff 0=(driftReader h (kineticBlock6.coeff 7)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff7Norm.property]
    dsimp only [kineticBlock6Coeff7Norm]
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

def kineticDriftBlock6Coeff7Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 7)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock6.coeff 7)).coeff 1=(driftReader h (kineticBlock6.coeff 7)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff7Norm.property]
    dsimp only [kineticBlock6Coeff7Norm]
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

def kineticDriftBlock6Coeff7Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 7)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock6.coeff 7)).coeff 2=(driftReader h (kineticBlock6.coeff 7)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff7Norm.property]
    dsimp only [kineticBlock6Coeff7Norm]
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

def kineticDriftBlock6Coeff7Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 7)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock6.coeff 7)).coeff 3=(driftReader h (kineticBlock6.coeff 7)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff7Norm.property]
    dsimp only [kineticBlock6Coeff7Norm]
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

def kineticDriftBlock6Coeff7Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock6.coeff 7)).coeff 4=c} := by
  have he : (driftReader h (kineticBlock6.coeff 7)).coeff 4=(driftReader h (kineticBlock6.coeff 7)).coeff 4 := rfl
  conv at he =>
    rhs
    rw [kineticBlock6Coeff7Norm.property]
    dsimp only [kineticBlock6Coeff7Norm]
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

theorem kineticBlock6Coeff7_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock6.coeff 7)).natDegree≤4 := by
  rw [kineticBlock6Coeff7Norm.property]
  dsimp only [kineticBlock6Coeff7Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!


def kineticDriftBlock6Row0 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock6Coeff0Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock6Coeff0Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock6Coeff0Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock6Coeff0Row3Norm h).val else 0) + (if b=4 then (kineticDriftBlock6Coeff0Row4Norm h).val else 0)

theorem kineticDriftBlock6Coeff0_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock6 0 b=kineticDriftBlock6Row0 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock6.coeff 0))
    (n := 5) (by have := kineticBlock6Coeff0_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock6.coeff 0)).coeff 0=(kineticDriftBlock6Coeff0Row0Norm h).val :=
    (kineticDriftBlock6Coeff0Row0Norm h).property
  have h1 : (driftReader h (kineticBlock6.coeff 0)).coeff 1=(kineticDriftBlock6Coeff0Row1Norm h).val :=
    (kineticDriftBlock6Coeff0Row1Norm h).property
  have h2 : (driftReader h (kineticBlock6.coeff 0)).coeff 2=(kineticDriftBlock6Coeff0Row2Norm h).val :=
    (kineticDriftBlock6Coeff0Row2Norm h).property
  have h3 : (driftReader h (kineticBlock6.coeff 0)).coeff 3=(kineticDriftBlock6Coeff0Row3Norm h).val :=
    (kineticDriftBlock6Coeff0Row3Norm h).property
  have h4 : (driftReader h (kineticBlock6.coeff 0)).coeff 4=(kineticDriftBlock6Coeff0Row4Norm h).val :=
    (kineticDriftBlock6Coeff0Row4Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock6Row0,h0,h1,h2,h3,h4] using he

def kineticDriftBlock6Row1 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock6Coeff1Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock6Coeff1Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock6Coeff1Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock6Coeff1Row3Norm h).val else 0) + (if b=4 then (kineticDriftBlock6Coeff1Row4Norm h).val else 0)

theorem kineticDriftBlock6Coeff1_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock6 1 b=kineticDriftBlock6Row1 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock6.coeff 1))
    (n := 5) (by have := kineticBlock6Coeff1_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock6.coeff 1)).coeff 0=(kineticDriftBlock6Coeff1Row0Norm h).val :=
    (kineticDriftBlock6Coeff1Row0Norm h).property
  have h1 : (driftReader h (kineticBlock6.coeff 1)).coeff 1=(kineticDriftBlock6Coeff1Row1Norm h).val :=
    (kineticDriftBlock6Coeff1Row1Norm h).property
  have h2 : (driftReader h (kineticBlock6.coeff 1)).coeff 2=(kineticDriftBlock6Coeff1Row2Norm h).val :=
    (kineticDriftBlock6Coeff1Row2Norm h).property
  have h3 : (driftReader h (kineticBlock6.coeff 1)).coeff 3=(kineticDriftBlock6Coeff1Row3Norm h).val :=
    (kineticDriftBlock6Coeff1Row3Norm h).property
  have h4 : (driftReader h (kineticBlock6.coeff 1)).coeff 4=(kineticDriftBlock6Coeff1Row4Norm h).val :=
    (kineticDriftBlock6Coeff1Row4Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock6Row1,h0,h1,h2,h3,h4] using he

def kineticDriftBlock6Row2 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock6Coeff2Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock6Coeff2Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock6Coeff2Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock6Coeff2Row3Norm h).val else 0) + (if b=4 then (kineticDriftBlock6Coeff2Row4Norm h).val else 0)

theorem kineticDriftBlock6Coeff2_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock6 2 b=kineticDriftBlock6Row2 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock6.coeff 2))
    (n := 5) (by have := kineticBlock6Coeff2_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock6.coeff 2)).coeff 0=(kineticDriftBlock6Coeff2Row0Norm h).val :=
    (kineticDriftBlock6Coeff2Row0Norm h).property
  have h1 : (driftReader h (kineticBlock6.coeff 2)).coeff 1=(kineticDriftBlock6Coeff2Row1Norm h).val :=
    (kineticDriftBlock6Coeff2Row1Norm h).property
  have h2 : (driftReader h (kineticBlock6.coeff 2)).coeff 2=(kineticDriftBlock6Coeff2Row2Norm h).val :=
    (kineticDriftBlock6Coeff2Row2Norm h).property
  have h3 : (driftReader h (kineticBlock6.coeff 2)).coeff 3=(kineticDriftBlock6Coeff2Row3Norm h).val :=
    (kineticDriftBlock6Coeff2Row3Norm h).property
  have h4 : (driftReader h (kineticBlock6.coeff 2)).coeff 4=(kineticDriftBlock6Coeff2Row4Norm h).val :=
    (kineticDriftBlock6Coeff2Row4Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock6Row2,h0,h1,h2,h3,h4] using he

def kineticDriftBlock6Row3 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock6Coeff3Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock6Coeff3Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock6Coeff3Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock6Coeff3Row3Norm h).val else 0) + (if b=4 then (kineticDriftBlock6Coeff3Row4Norm h).val else 0)

theorem kineticDriftBlock6Coeff3_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock6 3 b=kineticDriftBlock6Row3 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock6.coeff 3))
    (n := 5) (by have := kineticBlock6Coeff3_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock6.coeff 3)).coeff 0=(kineticDriftBlock6Coeff3Row0Norm h).val :=
    (kineticDriftBlock6Coeff3Row0Norm h).property
  have h1 : (driftReader h (kineticBlock6.coeff 3)).coeff 1=(kineticDriftBlock6Coeff3Row1Norm h).val :=
    (kineticDriftBlock6Coeff3Row1Norm h).property
  have h2 : (driftReader h (kineticBlock6.coeff 3)).coeff 2=(kineticDriftBlock6Coeff3Row2Norm h).val :=
    (kineticDriftBlock6Coeff3Row2Norm h).property
  have h3 : (driftReader h (kineticBlock6.coeff 3)).coeff 3=(kineticDriftBlock6Coeff3Row3Norm h).val :=
    (kineticDriftBlock6Coeff3Row3Norm h).property
  have h4 : (driftReader h (kineticBlock6.coeff 3)).coeff 4=(kineticDriftBlock6Coeff3Row4Norm h).val :=
    (kineticDriftBlock6Coeff3Row4Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock6Row3,h0,h1,h2,h3,h4] using he

def kineticDriftBlock6Row4 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock6Coeff4Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock6Coeff4Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock6Coeff4Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock6Coeff4Row3Norm h).val else 0) + (if b=4 then (kineticDriftBlock6Coeff4Row4Norm h).val else 0)

theorem kineticDriftBlock6Coeff4_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock6 4 b=kineticDriftBlock6Row4 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock6.coeff 4))
    (n := 5) (by have := kineticBlock6Coeff4_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock6.coeff 4)).coeff 0=(kineticDriftBlock6Coeff4Row0Norm h).val :=
    (kineticDriftBlock6Coeff4Row0Norm h).property
  have h1 : (driftReader h (kineticBlock6.coeff 4)).coeff 1=(kineticDriftBlock6Coeff4Row1Norm h).val :=
    (kineticDriftBlock6Coeff4Row1Norm h).property
  have h2 : (driftReader h (kineticBlock6.coeff 4)).coeff 2=(kineticDriftBlock6Coeff4Row2Norm h).val :=
    (kineticDriftBlock6Coeff4Row2Norm h).property
  have h3 : (driftReader h (kineticBlock6.coeff 4)).coeff 3=(kineticDriftBlock6Coeff4Row3Norm h).val :=
    (kineticDriftBlock6Coeff4Row3Norm h).property
  have h4 : (driftReader h (kineticBlock6.coeff 4)).coeff 4=(kineticDriftBlock6Coeff4Row4Norm h).val :=
    (kineticDriftBlock6Coeff4Row4Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock6Row4,h0,h1,h2,h3,h4] using he

def kineticDriftBlock6Row5 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock6Coeff5Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock6Coeff5Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock6Coeff5Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock6Coeff5Row3Norm h).val else 0) + (if b=4 then (kineticDriftBlock6Coeff5Row4Norm h).val else 0)

theorem kineticDriftBlock6Coeff5_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock6 5 b=kineticDriftBlock6Row5 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock6.coeff 5))
    (n := 5) (by have := kineticBlock6Coeff5_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock6.coeff 5)).coeff 0=(kineticDriftBlock6Coeff5Row0Norm h).val :=
    (kineticDriftBlock6Coeff5Row0Norm h).property
  have h1 : (driftReader h (kineticBlock6.coeff 5)).coeff 1=(kineticDriftBlock6Coeff5Row1Norm h).val :=
    (kineticDriftBlock6Coeff5Row1Norm h).property
  have h2 : (driftReader h (kineticBlock6.coeff 5)).coeff 2=(kineticDriftBlock6Coeff5Row2Norm h).val :=
    (kineticDriftBlock6Coeff5Row2Norm h).property
  have h3 : (driftReader h (kineticBlock6.coeff 5)).coeff 3=(kineticDriftBlock6Coeff5Row3Norm h).val :=
    (kineticDriftBlock6Coeff5Row3Norm h).property
  have h4 : (driftReader h (kineticBlock6.coeff 5)).coeff 4=(kineticDriftBlock6Coeff5Row4Norm h).val :=
    (kineticDriftBlock6Coeff5Row4Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock6Row5,h0,h1,h2,h3,h4] using he

def kineticDriftBlock6Row6 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock6Coeff6Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock6Coeff6Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock6Coeff6Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock6Coeff6Row3Norm h).val else 0) + (if b=4 then (kineticDriftBlock6Coeff6Row4Norm h).val else 0)

theorem kineticDriftBlock6Coeff6_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock6 6 b=kineticDriftBlock6Row6 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock6.coeff 6))
    (n := 5) (by have := kineticBlock6Coeff6_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock6.coeff 6)).coeff 0=(kineticDriftBlock6Coeff6Row0Norm h).val :=
    (kineticDriftBlock6Coeff6Row0Norm h).property
  have h1 : (driftReader h (kineticBlock6.coeff 6)).coeff 1=(kineticDriftBlock6Coeff6Row1Norm h).val :=
    (kineticDriftBlock6Coeff6Row1Norm h).property
  have h2 : (driftReader h (kineticBlock6.coeff 6)).coeff 2=(kineticDriftBlock6Coeff6Row2Norm h).val :=
    (kineticDriftBlock6Coeff6Row2Norm h).property
  have h3 : (driftReader h (kineticBlock6.coeff 6)).coeff 3=(kineticDriftBlock6Coeff6Row3Norm h).val :=
    (kineticDriftBlock6Coeff6Row3Norm h).property
  have h4 : (driftReader h (kineticBlock6.coeff 6)).coeff 4=(kineticDriftBlock6Coeff6Row4Norm h).val :=
    (kineticDriftBlock6Coeff6Row4Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock6Row6,h0,h1,h2,h3,h4] using he

def kineticDriftBlock6Row7 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock6Coeff7Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock6Coeff7Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock6Coeff7Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock6Coeff7Row3Norm h).val else 0) + (if b=4 then (kineticDriftBlock6Coeff7Row4Norm h).val else 0)

theorem kineticDriftBlock6Coeff7_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock6 7 b=kineticDriftBlock6Row7 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock6.coeff 7))
    (n := 5) (by have := kineticBlock6Coeff7_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock6.coeff 7)).coeff 0=(kineticDriftBlock6Coeff7Row0Norm h).val :=
    (kineticDriftBlock6Coeff7Row0Norm h).property
  have h1 : (driftReader h (kineticBlock6.coeff 7)).coeff 1=(kineticDriftBlock6Coeff7Row1Norm h).val :=
    (kineticDriftBlock6Coeff7Row1Norm h).property
  have h2 : (driftReader h (kineticBlock6.coeff 7)).coeff 2=(kineticDriftBlock6Coeff7Row2Norm h).val :=
    (kineticDriftBlock6Coeff7Row2Norm h).property
  have h3 : (driftReader h (kineticBlock6.coeff 7)).coeff 3=(kineticDriftBlock6Coeff7Row3Norm h).val :=
    (kineticDriftBlock6Coeff7Row3Norm h).property
  have h4 : (driftReader h (kineticBlock6.coeff 7)).coeff 4=(kineticDriftBlock6Coeff7Row4Norm h).val :=
    (kineticDriftBlock6Coeff7Row4Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock6Row7,h0,h1,h2,h3,h4] using he

theorem kineticDriftBlock6_rows (h : ℂ) (j b : ℕ) :
    kineticDriftCell h kineticBlock6 j b=(if j=0 then kineticDriftBlock6Row0 h b else 0) + (if j=1 then kineticDriftBlock6Row1 h b else 0) + (if j=2 then kineticDriftBlock6Row2 h b else 0) + (if j=3 then kineticDriftBlock6Row3 h b else 0) + (if j=4 then kineticDriftBlock6Row4 h b else 0) + (if j=5 then kineticDriftBlock6Row5 h b else 0) + (if j=6 then kineticDriftBlock6Row6 h b else 0) + (if j=7 then kineticDriftBlock6Row7 h b else 0) := by
  by_cases hj : j≤7
  · interval_cases j
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock6Coeff0_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock6Coeff1_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock6Coeff2_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock6Coeff3_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock6Coeff4_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock6Coeff5_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock6Coeff6_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock6Coeff7_rows h b
  · have hp : kineticBlock6.coeff j=0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (kineticBlock6_degree.trans_lt (by omega))
    simp only [kineticDriftCell,hp,map_zero,Polynomial.coeff_zero,if_neg (show j≠0 by omega),if_neg (show j≠1 by omega),if_neg (show j≠2 by omega),if_neg (show j≠3 by omega),if_neg (show j≠4 by omega),if_neg (show j≠5 by omega),if_neg (show j≠6 by omega),if_neg (show j≠7 by omega),zero_add]

theorem kineticBlock6_drift_bound : KineticDriftBound kineticBlock6 4 := by
  intro h j b hb
  by_cases hj : j≤7
  · interval_cases j
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock6Coeff0_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock6Coeff1_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock6Coeff2_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock6Coeff3_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock6Coeff4_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock6Coeff5_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock6Coeff6_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock6Coeff7_drift_degree h).trans_lt hb)
  · have hp : kineticBlock6.coeff j=0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (kineticBlock6_degree.trans_lt (by omega))
    simp only [kineticDriftCell,hp,map_zero,Polynomial.coeff_zero]

end
end HTGeometry.ThetaRatioKineticContraction
