import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticBlockCoefficients10
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticDriftReader
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticDegree
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticDriftSupport
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def kineticDriftBlock10Coeff0Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 0)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock10.coeff 0)).coeff 0=(driftReader h (kineticBlock10.coeff 0)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff0Norm.property]
    dsimp only [kineticBlock10Coeff0Norm]
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

def kineticDriftBlock10Coeff0Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 0)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock10.coeff 0)).coeff 1=(driftReader h (kineticBlock10.coeff 0)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff0Norm.property]
    dsimp only [kineticBlock10Coeff0Norm]
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

def kineticDriftBlock10Coeff0Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 0)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock10.coeff 0)).coeff 2=(driftReader h (kineticBlock10.coeff 0)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff0Norm.property]
    dsimp only [kineticBlock10Coeff0Norm]
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

def kineticDriftBlock10Coeff0Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 0)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock10.coeff 0)).coeff 3=(driftReader h (kineticBlock10.coeff 0)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff0Norm.property]
    dsimp only [kineticBlock10Coeff0Norm]
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

def kineticDriftBlock10Coeff0Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 0)).coeff 4=c} := by
  have he : (driftReader h (kineticBlock10.coeff 0)).coeff 4=(driftReader h (kineticBlock10.coeff 0)).coeff 4 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff0Norm.property]
    dsimp only [kineticBlock10Coeff0Norm]
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

def kineticDriftBlock10Coeff0Row5Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 0)).coeff 5=c} := by
  have he : (driftReader h (kineticBlock10.coeff 0)).coeff 5=(driftReader h (kineticBlock10.coeff 0)).coeff 5 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff0Norm.property]
    dsimp only [kineticBlock10Coeff0Norm]
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

def kineticDriftBlock10Coeff0Row6Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 0)).coeff 6=c} := by
  have he : (driftReader h (kineticBlock10.coeff 0)).coeff 6=(driftReader h (kineticBlock10.coeff 0)).coeff 6 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff0Norm.property]
    dsimp only [kineticBlock10Coeff0Norm]
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

theorem kineticBlock10Coeff0_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock10.coeff 0)).natDegree≤6 := by
  rw [kineticBlock10Coeff0Norm.property]
  dsimp only [kineticBlock10Coeff0Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock10Coeff1Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 1)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock10.coeff 1)).coeff 0=(driftReader h (kineticBlock10.coeff 1)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff1Norm.property]
    dsimp only [kineticBlock10Coeff1Norm]
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

def kineticDriftBlock10Coeff1Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 1)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock10.coeff 1)).coeff 1=(driftReader h (kineticBlock10.coeff 1)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff1Norm.property]
    dsimp only [kineticBlock10Coeff1Norm]
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

def kineticDriftBlock10Coeff1Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 1)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock10.coeff 1)).coeff 2=(driftReader h (kineticBlock10.coeff 1)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff1Norm.property]
    dsimp only [kineticBlock10Coeff1Norm]
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

def kineticDriftBlock10Coeff1Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 1)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock10.coeff 1)).coeff 3=(driftReader h (kineticBlock10.coeff 1)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff1Norm.property]
    dsimp only [kineticBlock10Coeff1Norm]
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

def kineticDriftBlock10Coeff1Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 1)).coeff 4=c} := by
  have he : (driftReader h (kineticBlock10.coeff 1)).coeff 4=(driftReader h (kineticBlock10.coeff 1)).coeff 4 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff1Norm.property]
    dsimp only [kineticBlock10Coeff1Norm]
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

def kineticDriftBlock10Coeff1Row5Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 1)).coeff 5=c} := by
  have he : (driftReader h (kineticBlock10.coeff 1)).coeff 5=(driftReader h (kineticBlock10.coeff 1)).coeff 5 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff1Norm.property]
    dsimp only [kineticBlock10Coeff1Norm]
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

def kineticDriftBlock10Coeff1Row6Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 1)).coeff 6=c} := by
  have he : (driftReader h (kineticBlock10.coeff 1)).coeff 6=(driftReader h (kineticBlock10.coeff 1)).coeff 6 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff1Norm.property]
    dsimp only [kineticBlock10Coeff1Norm]
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

theorem kineticBlock10Coeff1_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock10.coeff 1)).natDegree≤6 := by
  rw [kineticBlock10Coeff1Norm.property]
  dsimp only [kineticBlock10Coeff1Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock10Coeff2Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 2)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock10.coeff 2)).coeff 0=(driftReader h (kineticBlock10.coeff 2)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff2Norm.property]
    dsimp only [kineticBlock10Coeff2Norm]
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

def kineticDriftBlock10Coeff2Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 2)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock10.coeff 2)).coeff 1=(driftReader h (kineticBlock10.coeff 2)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff2Norm.property]
    dsimp only [kineticBlock10Coeff2Norm]
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

def kineticDriftBlock10Coeff2Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 2)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock10.coeff 2)).coeff 2=(driftReader h (kineticBlock10.coeff 2)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff2Norm.property]
    dsimp only [kineticBlock10Coeff2Norm]
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

def kineticDriftBlock10Coeff2Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 2)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock10.coeff 2)).coeff 3=(driftReader h (kineticBlock10.coeff 2)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff2Norm.property]
    dsimp only [kineticBlock10Coeff2Norm]
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

def kineticDriftBlock10Coeff2Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 2)).coeff 4=c} := by
  have he : (driftReader h (kineticBlock10.coeff 2)).coeff 4=(driftReader h (kineticBlock10.coeff 2)).coeff 4 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff2Norm.property]
    dsimp only [kineticBlock10Coeff2Norm]
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

def kineticDriftBlock10Coeff2Row5Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 2)).coeff 5=c} := by
  have he : (driftReader h (kineticBlock10.coeff 2)).coeff 5=(driftReader h (kineticBlock10.coeff 2)).coeff 5 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff2Norm.property]
    dsimp only [kineticBlock10Coeff2Norm]
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

def kineticDriftBlock10Coeff2Row6Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 2)).coeff 6=c} := by
  have he : (driftReader h (kineticBlock10.coeff 2)).coeff 6=(driftReader h (kineticBlock10.coeff 2)).coeff 6 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff2Norm.property]
    dsimp only [kineticBlock10Coeff2Norm]
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

theorem kineticBlock10Coeff2_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock10.coeff 2)).natDegree≤6 := by
  rw [kineticBlock10Coeff2Norm.property]
  dsimp only [kineticBlock10Coeff2Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock10Coeff3Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 3)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock10.coeff 3)).coeff 0=(driftReader h (kineticBlock10.coeff 3)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff3Norm.property]
    dsimp only [kineticBlock10Coeff3Norm]
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

def kineticDriftBlock10Coeff3Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 3)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock10.coeff 3)).coeff 1=(driftReader h (kineticBlock10.coeff 3)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff3Norm.property]
    dsimp only [kineticBlock10Coeff3Norm]
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

def kineticDriftBlock10Coeff3Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 3)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock10.coeff 3)).coeff 2=(driftReader h (kineticBlock10.coeff 3)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff3Norm.property]
    dsimp only [kineticBlock10Coeff3Norm]
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

def kineticDriftBlock10Coeff3Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 3)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock10.coeff 3)).coeff 3=(driftReader h (kineticBlock10.coeff 3)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff3Norm.property]
    dsimp only [kineticBlock10Coeff3Norm]
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

def kineticDriftBlock10Coeff3Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 3)).coeff 4=c} := by
  have he : (driftReader h (kineticBlock10.coeff 3)).coeff 4=(driftReader h (kineticBlock10.coeff 3)).coeff 4 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff3Norm.property]
    dsimp only [kineticBlock10Coeff3Norm]
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

def kineticDriftBlock10Coeff3Row5Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 3)).coeff 5=c} := by
  have he : (driftReader h (kineticBlock10.coeff 3)).coeff 5=(driftReader h (kineticBlock10.coeff 3)).coeff 5 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff3Norm.property]
    dsimp only [kineticBlock10Coeff3Norm]
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

def kineticDriftBlock10Coeff3Row6Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 3)).coeff 6=c} := by
  have he : (driftReader h (kineticBlock10.coeff 3)).coeff 6=(driftReader h (kineticBlock10.coeff 3)).coeff 6 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff3Norm.property]
    dsimp only [kineticBlock10Coeff3Norm]
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

theorem kineticBlock10Coeff3_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock10.coeff 3)).natDegree≤6 := by
  rw [kineticBlock10Coeff3Norm.property]
  dsimp only [kineticBlock10Coeff3Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock10Coeff4Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 4)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock10.coeff 4)).coeff 0=(driftReader h (kineticBlock10.coeff 4)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff4Norm.property]
    dsimp only [kineticBlock10Coeff4Norm]
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

def kineticDriftBlock10Coeff4Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 4)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock10.coeff 4)).coeff 1=(driftReader h (kineticBlock10.coeff 4)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff4Norm.property]
    dsimp only [kineticBlock10Coeff4Norm]
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

def kineticDriftBlock10Coeff4Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 4)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock10.coeff 4)).coeff 2=(driftReader h (kineticBlock10.coeff 4)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff4Norm.property]
    dsimp only [kineticBlock10Coeff4Norm]
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

def kineticDriftBlock10Coeff4Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 4)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock10.coeff 4)).coeff 3=(driftReader h (kineticBlock10.coeff 4)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff4Norm.property]
    dsimp only [kineticBlock10Coeff4Norm]
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

def kineticDriftBlock10Coeff4Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 4)).coeff 4=c} := by
  have he : (driftReader h (kineticBlock10.coeff 4)).coeff 4=(driftReader h (kineticBlock10.coeff 4)).coeff 4 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff4Norm.property]
    dsimp only [kineticBlock10Coeff4Norm]
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

def kineticDriftBlock10Coeff4Row5Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 4)).coeff 5=c} := by
  have he : (driftReader h (kineticBlock10.coeff 4)).coeff 5=(driftReader h (kineticBlock10.coeff 4)).coeff 5 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff4Norm.property]
    dsimp only [kineticBlock10Coeff4Norm]
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

def kineticDriftBlock10Coeff4Row6Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 4)).coeff 6=c} := by
  have he : (driftReader h (kineticBlock10.coeff 4)).coeff 6=(driftReader h (kineticBlock10.coeff 4)).coeff 6 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff4Norm.property]
    dsimp only [kineticBlock10Coeff4Norm]
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

theorem kineticBlock10Coeff4_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock10.coeff 4)).natDegree≤6 := by
  rw [kineticBlock10Coeff4Norm.property]
  dsimp only [kineticBlock10Coeff4Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock10Coeff5Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 5)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock10.coeff 5)).coeff 0=(driftReader h (kineticBlock10.coeff 5)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff5Norm.property]
    dsimp only [kineticBlock10Coeff5Norm]
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

def kineticDriftBlock10Coeff5Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 5)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock10.coeff 5)).coeff 1=(driftReader h (kineticBlock10.coeff 5)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff5Norm.property]
    dsimp only [kineticBlock10Coeff5Norm]
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

def kineticDriftBlock10Coeff5Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 5)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock10.coeff 5)).coeff 2=(driftReader h (kineticBlock10.coeff 5)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff5Norm.property]
    dsimp only [kineticBlock10Coeff5Norm]
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

def kineticDriftBlock10Coeff5Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 5)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock10.coeff 5)).coeff 3=(driftReader h (kineticBlock10.coeff 5)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff5Norm.property]
    dsimp only [kineticBlock10Coeff5Norm]
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

def kineticDriftBlock10Coeff5Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 5)).coeff 4=c} := by
  have he : (driftReader h (kineticBlock10.coeff 5)).coeff 4=(driftReader h (kineticBlock10.coeff 5)).coeff 4 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff5Norm.property]
    dsimp only [kineticBlock10Coeff5Norm]
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

def kineticDriftBlock10Coeff5Row5Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 5)).coeff 5=c} := by
  have he : (driftReader h (kineticBlock10.coeff 5)).coeff 5=(driftReader h (kineticBlock10.coeff 5)).coeff 5 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff5Norm.property]
    dsimp only [kineticBlock10Coeff5Norm]
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

def kineticDriftBlock10Coeff5Row6Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 5)).coeff 6=c} := by
  have he : (driftReader h (kineticBlock10.coeff 5)).coeff 6=(driftReader h (kineticBlock10.coeff 5)).coeff 6 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff5Norm.property]
    dsimp only [kineticBlock10Coeff5Norm]
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

theorem kineticBlock10Coeff5_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock10.coeff 5)).natDegree≤6 := by
  rw [kineticBlock10Coeff5Norm.property]
  dsimp only [kineticBlock10Coeff5Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock10Coeff6Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 6)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock10.coeff 6)).coeff 0=(driftReader h (kineticBlock10.coeff 6)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff6Norm.property]
    dsimp only [kineticBlock10Coeff6Norm]
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

def kineticDriftBlock10Coeff6Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 6)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock10.coeff 6)).coeff 1=(driftReader h (kineticBlock10.coeff 6)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff6Norm.property]
    dsimp only [kineticBlock10Coeff6Norm]
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

def kineticDriftBlock10Coeff6Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 6)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock10.coeff 6)).coeff 2=(driftReader h (kineticBlock10.coeff 6)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff6Norm.property]
    dsimp only [kineticBlock10Coeff6Norm]
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

def kineticDriftBlock10Coeff6Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 6)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock10.coeff 6)).coeff 3=(driftReader h (kineticBlock10.coeff 6)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff6Norm.property]
    dsimp only [kineticBlock10Coeff6Norm]
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

def kineticDriftBlock10Coeff6Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 6)).coeff 4=c} := by
  have he : (driftReader h (kineticBlock10.coeff 6)).coeff 4=(driftReader h (kineticBlock10.coeff 6)).coeff 4 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff6Norm.property]
    dsimp only [kineticBlock10Coeff6Norm]
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

def kineticDriftBlock10Coeff6Row5Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 6)).coeff 5=c} := by
  have he : (driftReader h (kineticBlock10.coeff 6)).coeff 5=(driftReader h (kineticBlock10.coeff 6)).coeff 5 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff6Norm.property]
    dsimp only [kineticBlock10Coeff6Norm]
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

def kineticDriftBlock10Coeff6Row6Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 6)).coeff 6=c} := by
  have he : (driftReader h (kineticBlock10.coeff 6)).coeff 6=(driftReader h (kineticBlock10.coeff 6)).coeff 6 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff6Norm.property]
    dsimp only [kineticBlock10Coeff6Norm]
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

theorem kineticBlock10Coeff6_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock10.coeff 6)).natDegree≤6 := by
  rw [kineticBlock10Coeff6Norm.property]
  dsimp only [kineticBlock10Coeff6Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock10Coeff7Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 7)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock10.coeff 7)).coeff 0=(driftReader h (kineticBlock10.coeff 7)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff7Norm.property]
    dsimp only [kineticBlock10Coeff7Norm]
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

def kineticDriftBlock10Coeff7Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 7)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock10.coeff 7)).coeff 1=(driftReader h (kineticBlock10.coeff 7)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff7Norm.property]
    dsimp only [kineticBlock10Coeff7Norm]
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

def kineticDriftBlock10Coeff7Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 7)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock10.coeff 7)).coeff 2=(driftReader h (kineticBlock10.coeff 7)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff7Norm.property]
    dsimp only [kineticBlock10Coeff7Norm]
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

def kineticDriftBlock10Coeff7Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 7)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock10.coeff 7)).coeff 3=(driftReader h (kineticBlock10.coeff 7)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff7Norm.property]
    dsimp only [kineticBlock10Coeff7Norm]
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

def kineticDriftBlock10Coeff7Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 7)).coeff 4=c} := by
  have he : (driftReader h (kineticBlock10.coeff 7)).coeff 4=(driftReader h (kineticBlock10.coeff 7)).coeff 4 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff7Norm.property]
    dsimp only [kineticBlock10Coeff7Norm]
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

def kineticDriftBlock10Coeff7Row5Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 7)).coeff 5=c} := by
  have he : (driftReader h (kineticBlock10.coeff 7)).coeff 5=(driftReader h (kineticBlock10.coeff 7)).coeff 5 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff7Norm.property]
    dsimp only [kineticBlock10Coeff7Norm]
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

def kineticDriftBlock10Coeff7Row6Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 7)).coeff 6=c} := by
  have he : (driftReader h (kineticBlock10.coeff 7)).coeff 6=(driftReader h (kineticBlock10.coeff 7)).coeff 6 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff7Norm.property]
    dsimp only [kineticBlock10Coeff7Norm]
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

theorem kineticBlock10Coeff7_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock10.coeff 7)).natDegree≤6 := by
  rw [kineticBlock10Coeff7Norm.property]
  dsimp only [kineticBlock10Coeff7Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock10Coeff8Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 8)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock10.coeff 8)).coeff 0=(driftReader h (kineticBlock10.coeff 8)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff8Norm.property]
    dsimp only [kineticBlock10Coeff8Norm]
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

def kineticDriftBlock10Coeff8Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 8)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock10.coeff 8)).coeff 1=(driftReader h (kineticBlock10.coeff 8)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff8Norm.property]
    dsimp only [kineticBlock10Coeff8Norm]
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

def kineticDriftBlock10Coeff8Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 8)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock10.coeff 8)).coeff 2=(driftReader h (kineticBlock10.coeff 8)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff8Norm.property]
    dsimp only [kineticBlock10Coeff8Norm]
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

def kineticDriftBlock10Coeff8Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 8)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock10.coeff 8)).coeff 3=(driftReader h (kineticBlock10.coeff 8)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff8Norm.property]
    dsimp only [kineticBlock10Coeff8Norm]
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

def kineticDriftBlock10Coeff8Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 8)).coeff 4=c} := by
  have he : (driftReader h (kineticBlock10.coeff 8)).coeff 4=(driftReader h (kineticBlock10.coeff 8)).coeff 4 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff8Norm.property]
    dsimp only [kineticBlock10Coeff8Norm]
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

def kineticDriftBlock10Coeff8Row5Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 8)).coeff 5=c} := by
  have he : (driftReader h (kineticBlock10.coeff 8)).coeff 5=(driftReader h (kineticBlock10.coeff 8)).coeff 5 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff8Norm.property]
    dsimp only [kineticBlock10Coeff8Norm]
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

def kineticDriftBlock10Coeff8Row6Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 8)).coeff 6=c} := by
  have he : (driftReader h (kineticBlock10.coeff 8)).coeff 6=(driftReader h (kineticBlock10.coeff 8)).coeff 6 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff8Norm.property]
    dsimp only [kineticBlock10Coeff8Norm]
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

theorem kineticBlock10Coeff8_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock10.coeff 8)).natDegree≤6 := by
  rw [kineticBlock10Coeff8Norm.property]
  dsimp only [kineticBlock10Coeff8Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock10Coeff9Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 9)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock10.coeff 9)).coeff 0=(driftReader h (kineticBlock10.coeff 9)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff9Norm.property]
    dsimp only [kineticBlock10Coeff9Norm]
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

def kineticDriftBlock10Coeff9Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 9)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock10.coeff 9)).coeff 1=(driftReader h (kineticBlock10.coeff 9)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff9Norm.property]
    dsimp only [kineticBlock10Coeff9Norm]
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

def kineticDriftBlock10Coeff9Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 9)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock10.coeff 9)).coeff 2=(driftReader h (kineticBlock10.coeff 9)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff9Norm.property]
    dsimp only [kineticBlock10Coeff9Norm]
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

def kineticDriftBlock10Coeff9Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 9)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock10.coeff 9)).coeff 3=(driftReader h (kineticBlock10.coeff 9)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff9Norm.property]
    dsimp only [kineticBlock10Coeff9Norm]
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

def kineticDriftBlock10Coeff9Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 9)).coeff 4=c} := by
  have he : (driftReader h (kineticBlock10.coeff 9)).coeff 4=(driftReader h (kineticBlock10.coeff 9)).coeff 4 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff9Norm.property]
    dsimp only [kineticBlock10Coeff9Norm]
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

def kineticDriftBlock10Coeff9Row5Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 9)).coeff 5=c} := by
  have he : (driftReader h (kineticBlock10.coeff 9)).coeff 5=(driftReader h (kineticBlock10.coeff 9)).coeff 5 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff9Norm.property]
    dsimp only [kineticBlock10Coeff9Norm]
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

def kineticDriftBlock10Coeff9Row6Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 9)).coeff 6=c} := by
  have he : (driftReader h (kineticBlock10.coeff 9)).coeff 6=(driftReader h (kineticBlock10.coeff 9)).coeff 6 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff9Norm.property]
    dsimp only [kineticBlock10Coeff9Norm]
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

theorem kineticBlock10Coeff9_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock10.coeff 9)).natDegree≤6 := by
  rw [kineticBlock10Coeff9Norm.property]
  dsimp only [kineticBlock10Coeff9Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock10Coeff10Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 10)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock10.coeff 10)).coeff 0=(driftReader h (kineticBlock10.coeff 10)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff10Norm.property]
    dsimp only [kineticBlock10Coeff10Norm]
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

def kineticDriftBlock10Coeff10Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 10)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock10.coeff 10)).coeff 1=(driftReader h (kineticBlock10.coeff 10)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff10Norm.property]
    dsimp only [kineticBlock10Coeff10Norm]
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

def kineticDriftBlock10Coeff10Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 10)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock10.coeff 10)).coeff 2=(driftReader h (kineticBlock10.coeff 10)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff10Norm.property]
    dsimp only [kineticBlock10Coeff10Norm]
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

def kineticDriftBlock10Coeff10Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 10)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock10.coeff 10)).coeff 3=(driftReader h (kineticBlock10.coeff 10)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff10Norm.property]
    dsimp only [kineticBlock10Coeff10Norm]
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

def kineticDriftBlock10Coeff10Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 10)).coeff 4=c} := by
  have he : (driftReader h (kineticBlock10.coeff 10)).coeff 4=(driftReader h (kineticBlock10.coeff 10)).coeff 4 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff10Norm.property]
    dsimp only [kineticBlock10Coeff10Norm]
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

def kineticDriftBlock10Coeff10Row5Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 10)).coeff 5=c} := by
  have he : (driftReader h (kineticBlock10.coeff 10)).coeff 5=(driftReader h (kineticBlock10.coeff 10)).coeff 5 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff10Norm.property]
    dsimp only [kineticBlock10Coeff10Norm]
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

def kineticDriftBlock10Coeff10Row6Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 10)).coeff 6=c} := by
  have he : (driftReader h (kineticBlock10.coeff 10)).coeff 6=(driftReader h (kineticBlock10.coeff 10)).coeff 6 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff10Norm.property]
    dsimp only [kineticBlock10Coeff10Norm]
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

theorem kineticBlock10Coeff10_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock10.coeff 10)).natDegree≤6 := by
  rw [kineticBlock10Coeff10Norm.property]
  dsimp only [kineticBlock10Coeff10Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock10Coeff11Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 11)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock10.coeff 11)).coeff 0=(driftReader h (kineticBlock10.coeff 11)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff11Norm.property]
    dsimp only [kineticBlock10Coeff11Norm]
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

def kineticDriftBlock10Coeff11Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 11)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock10.coeff 11)).coeff 1=(driftReader h (kineticBlock10.coeff 11)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff11Norm.property]
    dsimp only [kineticBlock10Coeff11Norm]
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

def kineticDriftBlock10Coeff11Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 11)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock10.coeff 11)).coeff 2=(driftReader h (kineticBlock10.coeff 11)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff11Norm.property]
    dsimp only [kineticBlock10Coeff11Norm]
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

def kineticDriftBlock10Coeff11Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 11)).coeff 3=c} := by
  have he : (driftReader h (kineticBlock10.coeff 11)).coeff 3=(driftReader h (kineticBlock10.coeff 11)).coeff 3 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff11Norm.property]
    dsimp only [kineticBlock10Coeff11Norm]
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

def kineticDriftBlock10Coeff11Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 11)).coeff 4=c} := by
  have he : (driftReader h (kineticBlock10.coeff 11)).coeff 4=(driftReader h (kineticBlock10.coeff 11)).coeff 4 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff11Norm.property]
    dsimp only [kineticBlock10Coeff11Norm]
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

def kineticDriftBlock10Coeff11Row5Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 11)).coeff 5=c} := by
  have he : (driftReader h (kineticBlock10.coeff 11)).coeff 5=(driftReader h (kineticBlock10.coeff 11)).coeff 5 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff11Norm.property]
    dsimp only [kineticBlock10Coeff11Norm]
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

def kineticDriftBlock10Coeff11Row6Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock10.coeff 11)).coeff 6=c} := by
  have he : (driftReader h (kineticBlock10.coeff 11)).coeff 6=(driftReader h (kineticBlock10.coeff 11)).coeff 6 := rfl
  conv at he =>
    rhs
    rw [kineticBlock10Coeff11Norm.property]
    dsimp only [kineticBlock10Coeff11Norm]
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

theorem kineticBlock10Coeff11_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock10.coeff 11)).natDegree≤6 := by
  rw [kineticBlock10Coeff11Norm.property]
  dsimp only [kineticBlock10Coeff11Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!


def kineticDriftBlock10Row0 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock10Coeff0Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock10Coeff0Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock10Coeff0Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock10Coeff0Row3Norm h).val else 0) + (if b=4 then (kineticDriftBlock10Coeff0Row4Norm h).val else 0) + (if b=5 then (kineticDriftBlock10Coeff0Row5Norm h).val else 0) + (if b=6 then (kineticDriftBlock10Coeff0Row6Norm h).val else 0)

theorem kineticDriftBlock10Coeff0_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock10 0 b=kineticDriftBlock10Row0 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock10.coeff 0))
    (n := 7) (by have := kineticBlock10Coeff0_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock10.coeff 0)).coeff 0=(kineticDriftBlock10Coeff0Row0Norm h).val :=
    (kineticDriftBlock10Coeff0Row0Norm h).property
  have h1 : (driftReader h (kineticBlock10.coeff 0)).coeff 1=(kineticDriftBlock10Coeff0Row1Norm h).val :=
    (kineticDriftBlock10Coeff0Row1Norm h).property
  have h2 : (driftReader h (kineticBlock10.coeff 0)).coeff 2=(kineticDriftBlock10Coeff0Row2Norm h).val :=
    (kineticDriftBlock10Coeff0Row2Norm h).property
  have h3 : (driftReader h (kineticBlock10.coeff 0)).coeff 3=(kineticDriftBlock10Coeff0Row3Norm h).val :=
    (kineticDriftBlock10Coeff0Row3Norm h).property
  have h4 : (driftReader h (kineticBlock10.coeff 0)).coeff 4=(kineticDriftBlock10Coeff0Row4Norm h).val :=
    (kineticDriftBlock10Coeff0Row4Norm h).property
  have h5 : (driftReader h (kineticBlock10.coeff 0)).coeff 5=(kineticDriftBlock10Coeff0Row5Norm h).val :=
    (kineticDriftBlock10Coeff0Row5Norm h).property
  have h6 : (driftReader h (kineticBlock10.coeff 0)).coeff 6=(kineticDriftBlock10Coeff0Row6Norm h).val :=
    (kineticDriftBlock10Coeff0Row6Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock10Row0,h0,h1,h2,h3,h4,h5,h6] using he

def kineticDriftBlock10Row1 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock10Coeff1Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock10Coeff1Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock10Coeff1Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock10Coeff1Row3Norm h).val else 0) + (if b=4 then (kineticDriftBlock10Coeff1Row4Norm h).val else 0) + (if b=5 then (kineticDriftBlock10Coeff1Row5Norm h).val else 0) + (if b=6 then (kineticDriftBlock10Coeff1Row6Norm h).val else 0)

theorem kineticDriftBlock10Coeff1_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock10 1 b=kineticDriftBlock10Row1 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock10.coeff 1))
    (n := 7) (by have := kineticBlock10Coeff1_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock10.coeff 1)).coeff 0=(kineticDriftBlock10Coeff1Row0Norm h).val :=
    (kineticDriftBlock10Coeff1Row0Norm h).property
  have h1 : (driftReader h (kineticBlock10.coeff 1)).coeff 1=(kineticDriftBlock10Coeff1Row1Norm h).val :=
    (kineticDriftBlock10Coeff1Row1Norm h).property
  have h2 : (driftReader h (kineticBlock10.coeff 1)).coeff 2=(kineticDriftBlock10Coeff1Row2Norm h).val :=
    (kineticDriftBlock10Coeff1Row2Norm h).property
  have h3 : (driftReader h (kineticBlock10.coeff 1)).coeff 3=(kineticDriftBlock10Coeff1Row3Norm h).val :=
    (kineticDriftBlock10Coeff1Row3Norm h).property
  have h4 : (driftReader h (kineticBlock10.coeff 1)).coeff 4=(kineticDriftBlock10Coeff1Row4Norm h).val :=
    (kineticDriftBlock10Coeff1Row4Norm h).property
  have h5 : (driftReader h (kineticBlock10.coeff 1)).coeff 5=(kineticDriftBlock10Coeff1Row5Norm h).val :=
    (kineticDriftBlock10Coeff1Row5Norm h).property
  have h6 : (driftReader h (kineticBlock10.coeff 1)).coeff 6=(kineticDriftBlock10Coeff1Row6Norm h).val :=
    (kineticDriftBlock10Coeff1Row6Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock10Row1,h0,h1,h2,h3,h4,h5,h6] using he

def kineticDriftBlock10Row2 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock10Coeff2Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock10Coeff2Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock10Coeff2Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock10Coeff2Row3Norm h).val else 0) + (if b=4 then (kineticDriftBlock10Coeff2Row4Norm h).val else 0) + (if b=5 then (kineticDriftBlock10Coeff2Row5Norm h).val else 0) + (if b=6 then (kineticDriftBlock10Coeff2Row6Norm h).val else 0)

theorem kineticDriftBlock10Coeff2_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock10 2 b=kineticDriftBlock10Row2 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock10.coeff 2))
    (n := 7) (by have := kineticBlock10Coeff2_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock10.coeff 2)).coeff 0=(kineticDriftBlock10Coeff2Row0Norm h).val :=
    (kineticDriftBlock10Coeff2Row0Norm h).property
  have h1 : (driftReader h (kineticBlock10.coeff 2)).coeff 1=(kineticDriftBlock10Coeff2Row1Norm h).val :=
    (kineticDriftBlock10Coeff2Row1Norm h).property
  have h2 : (driftReader h (kineticBlock10.coeff 2)).coeff 2=(kineticDriftBlock10Coeff2Row2Norm h).val :=
    (kineticDriftBlock10Coeff2Row2Norm h).property
  have h3 : (driftReader h (kineticBlock10.coeff 2)).coeff 3=(kineticDriftBlock10Coeff2Row3Norm h).val :=
    (kineticDriftBlock10Coeff2Row3Norm h).property
  have h4 : (driftReader h (kineticBlock10.coeff 2)).coeff 4=(kineticDriftBlock10Coeff2Row4Norm h).val :=
    (kineticDriftBlock10Coeff2Row4Norm h).property
  have h5 : (driftReader h (kineticBlock10.coeff 2)).coeff 5=(kineticDriftBlock10Coeff2Row5Norm h).val :=
    (kineticDriftBlock10Coeff2Row5Norm h).property
  have h6 : (driftReader h (kineticBlock10.coeff 2)).coeff 6=(kineticDriftBlock10Coeff2Row6Norm h).val :=
    (kineticDriftBlock10Coeff2Row6Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock10Row2,h0,h1,h2,h3,h4,h5,h6] using he

def kineticDriftBlock10Row3 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock10Coeff3Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock10Coeff3Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock10Coeff3Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock10Coeff3Row3Norm h).val else 0) + (if b=4 then (kineticDriftBlock10Coeff3Row4Norm h).val else 0) + (if b=5 then (kineticDriftBlock10Coeff3Row5Norm h).val else 0) + (if b=6 then (kineticDriftBlock10Coeff3Row6Norm h).val else 0)

theorem kineticDriftBlock10Coeff3_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock10 3 b=kineticDriftBlock10Row3 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock10.coeff 3))
    (n := 7) (by have := kineticBlock10Coeff3_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock10.coeff 3)).coeff 0=(kineticDriftBlock10Coeff3Row0Norm h).val :=
    (kineticDriftBlock10Coeff3Row0Norm h).property
  have h1 : (driftReader h (kineticBlock10.coeff 3)).coeff 1=(kineticDriftBlock10Coeff3Row1Norm h).val :=
    (kineticDriftBlock10Coeff3Row1Norm h).property
  have h2 : (driftReader h (kineticBlock10.coeff 3)).coeff 2=(kineticDriftBlock10Coeff3Row2Norm h).val :=
    (kineticDriftBlock10Coeff3Row2Norm h).property
  have h3 : (driftReader h (kineticBlock10.coeff 3)).coeff 3=(kineticDriftBlock10Coeff3Row3Norm h).val :=
    (kineticDriftBlock10Coeff3Row3Norm h).property
  have h4 : (driftReader h (kineticBlock10.coeff 3)).coeff 4=(kineticDriftBlock10Coeff3Row4Norm h).val :=
    (kineticDriftBlock10Coeff3Row4Norm h).property
  have h5 : (driftReader h (kineticBlock10.coeff 3)).coeff 5=(kineticDriftBlock10Coeff3Row5Norm h).val :=
    (kineticDriftBlock10Coeff3Row5Norm h).property
  have h6 : (driftReader h (kineticBlock10.coeff 3)).coeff 6=(kineticDriftBlock10Coeff3Row6Norm h).val :=
    (kineticDriftBlock10Coeff3Row6Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock10Row3,h0,h1,h2,h3,h4,h5,h6] using he

def kineticDriftBlock10Row4 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock10Coeff4Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock10Coeff4Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock10Coeff4Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock10Coeff4Row3Norm h).val else 0) + (if b=4 then (kineticDriftBlock10Coeff4Row4Norm h).val else 0) + (if b=5 then (kineticDriftBlock10Coeff4Row5Norm h).val else 0) + (if b=6 then (kineticDriftBlock10Coeff4Row6Norm h).val else 0)

theorem kineticDriftBlock10Coeff4_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock10 4 b=kineticDriftBlock10Row4 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock10.coeff 4))
    (n := 7) (by have := kineticBlock10Coeff4_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock10.coeff 4)).coeff 0=(kineticDriftBlock10Coeff4Row0Norm h).val :=
    (kineticDriftBlock10Coeff4Row0Norm h).property
  have h1 : (driftReader h (kineticBlock10.coeff 4)).coeff 1=(kineticDriftBlock10Coeff4Row1Norm h).val :=
    (kineticDriftBlock10Coeff4Row1Norm h).property
  have h2 : (driftReader h (kineticBlock10.coeff 4)).coeff 2=(kineticDriftBlock10Coeff4Row2Norm h).val :=
    (kineticDriftBlock10Coeff4Row2Norm h).property
  have h3 : (driftReader h (kineticBlock10.coeff 4)).coeff 3=(kineticDriftBlock10Coeff4Row3Norm h).val :=
    (kineticDriftBlock10Coeff4Row3Norm h).property
  have h4 : (driftReader h (kineticBlock10.coeff 4)).coeff 4=(kineticDriftBlock10Coeff4Row4Norm h).val :=
    (kineticDriftBlock10Coeff4Row4Norm h).property
  have h5 : (driftReader h (kineticBlock10.coeff 4)).coeff 5=(kineticDriftBlock10Coeff4Row5Norm h).val :=
    (kineticDriftBlock10Coeff4Row5Norm h).property
  have h6 : (driftReader h (kineticBlock10.coeff 4)).coeff 6=(kineticDriftBlock10Coeff4Row6Norm h).val :=
    (kineticDriftBlock10Coeff4Row6Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock10Row4,h0,h1,h2,h3,h4,h5,h6] using he

def kineticDriftBlock10Row5 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock10Coeff5Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock10Coeff5Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock10Coeff5Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock10Coeff5Row3Norm h).val else 0) + (if b=4 then (kineticDriftBlock10Coeff5Row4Norm h).val else 0) + (if b=5 then (kineticDriftBlock10Coeff5Row5Norm h).val else 0) + (if b=6 then (kineticDriftBlock10Coeff5Row6Norm h).val else 0)

theorem kineticDriftBlock10Coeff5_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock10 5 b=kineticDriftBlock10Row5 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock10.coeff 5))
    (n := 7) (by have := kineticBlock10Coeff5_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock10.coeff 5)).coeff 0=(kineticDriftBlock10Coeff5Row0Norm h).val :=
    (kineticDriftBlock10Coeff5Row0Norm h).property
  have h1 : (driftReader h (kineticBlock10.coeff 5)).coeff 1=(kineticDriftBlock10Coeff5Row1Norm h).val :=
    (kineticDriftBlock10Coeff5Row1Norm h).property
  have h2 : (driftReader h (kineticBlock10.coeff 5)).coeff 2=(kineticDriftBlock10Coeff5Row2Norm h).val :=
    (kineticDriftBlock10Coeff5Row2Norm h).property
  have h3 : (driftReader h (kineticBlock10.coeff 5)).coeff 3=(kineticDriftBlock10Coeff5Row3Norm h).val :=
    (kineticDriftBlock10Coeff5Row3Norm h).property
  have h4 : (driftReader h (kineticBlock10.coeff 5)).coeff 4=(kineticDriftBlock10Coeff5Row4Norm h).val :=
    (kineticDriftBlock10Coeff5Row4Norm h).property
  have h5 : (driftReader h (kineticBlock10.coeff 5)).coeff 5=(kineticDriftBlock10Coeff5Row5Norm h).val :=
    (kineticDriftBlock10Coeff5Row5Norm h).property
  have h6 : (driftReader h (kineticBlock10.coeff 5)).coeff 6=(kineticDriftBlock10Coeff5Row6Norm h).val :=
    (kineticDriftBlock10Coeff5Row6Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock10Row5,h0,h1,h2,h3,h4,h5,h6] using he

def kineticDriftBlock10Row6 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock10Coeff6Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock10Coeff6Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock10Coeff6Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock10Coeff6Row3Norm h).val else 0) + (if b=4 then (kineticDriftBlock10Coeff6Row4Norm h).val else 0) + (if b=5 then (kineticDriftBlock10Coeff6Row5Norm h).val else 0) + (if b=6 then (kineticDriftBlock10Coeff6Row6Norm h).val else 0)

theorem kineticDriftBlock10Coeff6_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock10 6 b=kineticDriftBlock10Row6 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock10.coeff 6))
    (n := 7) (by have := kineticBlock10Coeff6_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock10.coeff 6)).coeff 0=(kineticDriftBlock10Coeff6Row0Norm h).val :=
    (kineticDriftBlock10Coeff6Row0Norm h).property
  have h1 : (driftReader h (kineticBlock10.coeff 6)).coeff 1=(kineticDriftBlock10Coeff6Row1Norm h).val :=
    (kineticDriftBlock10Coeff6Row1Norm h).property
  have h2 : (driftReader h (kineticBlock10.coeff 6)).coeff 2=(kineticDriftBlock10Coeff6Row2Norm h).val :=
    (kineticDriftBlock10Coeff6Row2Norm h).property
  have h3 : (driftReader h (kineticBlock10.coeff 6)).coeff 3=(kineticDriftBlock10Coeff6Row3Norm h).val :=
    (kineticDriftBlock10Coeff6Row3Norm h).property
  have h4 : (driftReader h (kineticBlock10.coeff 6)).coeff 4=(kineticDriftBlock10Coeff6Row4Norm h).val :=
    (kineticDriftBlock10Coeff6Row4Norm h).property
  have h5 : (driftReader h (kineticBlock10.coeff 6)).coeff 5=(kineticDriftBlock10Coeff6Row5Norm h).val :=
    (kineticDriftBlock10Coeff6Row5Norm h).property
  have h6 : (driftReader h (kineticBlock10.coeff 6)).coeff 6=(kineticDriftBlock10Coeff6Row6Norm h).val :=
    (kineticDriftBlock10Coeff6Row6Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock10Row6,h0,h1,h2,h3,h4,h5,h6] using he

def kineticDriftBlock10Row7 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock10Coeff7Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock10Coeff7Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock10Coeff7Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock10Coeff7Row3Norm h).val else 0) + (if b=4 then (kineticDriftBlock10Coeff7Row4Norm h).val else 0) + (if b=5 then (kineticDriftBlock10Coeff7Row5Norm h).val else 0) + (if b=6 then (kineticDriftBlock10Coeff7Row6Norm h).val else 0)

theorem kineticDriftBlock10Coeff7_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock10 7 b=kineticDriftBlock10Row7 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock10.coeff 7))
    (n := 7) (by have := kineticBlock10Coeff7_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock10.coeff 7)).coeff 0=(kineticDriftBlock10Coeff7Row0Norm h).val :=
    (kineticDriftBlock10Coeff7Row0Norm h).property
  have h1 : (driftReader h (kineticBlock10.coeff 7)).coeff 1=(kineticDriftBlock10Coeff7Row1Norm h).val :=
    (kineticDriftBlock10Coeff7Row1Norm h).property
  have h2 : (driftReader h (kineticBlock10.coeff 7)).coeff 2=(kineticDriftBlock10Coeff7Row2Norm h).val :=
    (kineticDriftBlock10Coeff7Row2Norm h).property
  have h3 : (driftReader h (kineticBlock10.coeff 7)).coeff 3=(kineticDriftBlock10Coeff7Row3Norm h).val :=
    (kineticDriftBlock10Coeff7Row3Norm h).property
  have h4 : (driftReader h (kineticBlock10.coeff 7)).coeff 4=(kineticDriftBlock10Coeff7Row4Norm h).val :=
    (kineticDriftBlock10Coeff7Row4Norm h).property
  have h5 : (driftReader h (kineticBlock10.coeff 7)).coeff 5=(kineticDriftBlock10Coeff7Row5Norm h).val :=
    (kineticDriftBlock10Coeff7Row5Norm h).property
  have h6 : (driftReader h (kineticBlock10.coeff 7)).coeff 6=(kineticDriftBlock10Coeff7Row6Norm h).val :=
    (kineticDriftBlock10Coeff7Row6Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock10Row7,h0,h1,h2,h3,h4,h5,h6] using he

def kineticDriftBlock10Row8 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock10Coeff8Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock10Coeff8Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock10Coeff8Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock10Coeff8Row3Norm h).val else 0) + (if b=4 then (kineticDriftBlock10Coeff8Row4Norm h).val else 0) + (if b=5 then (kineticDriftBlock10Coeff8Row5Norm h).val else 0) + (if b=6 then (kineticDriftBlock10Coeff8Row6Norm h).val else 0)

theorem kineticDriftBlock10Coeff8_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock10 8 b=kineticDriftBlock10Row8 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock10.coeff 8))
    (n := 7) (by have := kineticBlock10Coeff8_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock10.coeff 8)).coeff 0=(kineticDriftBlock10Coeff8Row0Norm h).val :=
    (kineticDriftBlock10Coeff8Row0Norm h).property
  have h1 : (driftReader h (kineticBlock10.coeff 8)).coeff 1=(kineticDriftBlock10Coeff8Row1Norm h).val :=
    (kineticDriftBlock10Coeff8Row1Norm h).property
  have h2 : (driftReader h (kineticBlock10.coeff 8)).coeff 2=(kineticDriftBlock10Coeff8Row2Norm h).val :=
    (kineticDriftBlock10Coeff8Row2Norm h).property
  have h3 : (driftReader h (kineticBlock10.coeff 8)).coeff 3=(kineticDriftBlock10Coeff8Row3Norm h).val :=
    (kineticDriftBlock10Coeff8Row3Norm h).property
  have h4 : (driftReader h (kineticBlock10.coeff 8)).coeff 4=(kineticDriftBlock10Coeff8Row4Norm h).val :=
    (kineticDriftBlock10Coeff8Row4Norm h).property
  have h5 : (driftReader h (kineticBlock10.coeff 8)).coeff 5=(kineticDriftBlock10Coeff8Row5Norm h).val :=
    (kineticDriftBlock10Coeff8Row5Norm h).property
  have h6 : (driftReader h (kineticBlock10.coeff 8)).coeff 6=(kineticDriftBlock10Coeff8Row6Norm h).val :=
    (kineticDriftBlock10Coeff8Row6Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock10Row8,h0,h1,h2,h3,h4,h5,h6] using he

def kineticDriftBlock10Row9 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock10Coeff9Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock10Coeff9Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock10Coeff9Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock10Coeff9Row3Norm h).val else 0) + (if b=4 then (kineticDriftBlock10Coeff9Row4Norm h).val else 0) + (if b=5 then (kineticDriftBlock10Coeff9Row5Norm h).val else 0) + (if b=6 then (kineticDriftBlock10Coeff9Row6Norm h).val else 0)

theorem kineticDriftBlock10Coeff9_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock10 9 b=kineticDriftBlock10Row9 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock10.coeff 9))
    (n := 7) (by have := kineticBlock10Coeff9_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock10.coeff 9)).coeff 0=(kineticDriftBlock10Coeff9Row0Norm h).val :=
    (kineticDriftBlock10Coeff9Row0Norm h).property
  have h1 : (driftReader h (kineticBlock10.coeff 9)).coeff 1=(kineticDriftBlock10Coeff9Row1Norm h).val :=
    (kineticDriftBlock10Coeff9Row1Norm h).property
  have h2 : (driftReader h (kineticBlock10.coeff 9)).coeff 2=(kineticDriftBlock10Coeff9Row2Norm h).val :=
    (kineticDriftBlock10Coeff9Row2Norm h).property
  have h3 : (driftReader h (kineticBlock10.coeff 9)).coeff 3=(kineticDriftBlock10Coeff9Row3Norm h).val :=
    (kineticDriftBlock10Coeff9Row3Norm h).property
  have h4 : (driftReader h (kineticBlock10.coeff 9)).coeff 4=(kineticDriftBlock10Coeff9Row4Norm h).val :=
    (kineticDriftBlock10Coeff9Row4Norm h).property
  have h5 : (driftReader h (kineticBlock10.coeff 9)).coeff 5=(kineticDriftBlock10Coeff9Row5Norm h).val :=
    (kineticDriftBlock10Coeff9Row5Norm h).property
  have h6 : (driftReader h (kineticBlock10.coeff 9)).coeff 6=(kineticDriftBlock10Coeff9Row6Norm h).val :=
    (kineticDriftBlock10Coeff9Row6Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock10Row9,h0,h1,h2,h3,h4,h5,h6] using he

def kineticDriftBlock10Row10 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock10Coeff10Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock10Coeff10Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock10Coeff10Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock10Coeff10Row3Norm h).val else 0) + (if b=4 then (kineticDriftBlock10Coeff10Row4Norm h).val else 0) + (if b=5 then (kineticDriftBlock10Coeff10Row5Norm h).val else 0) + (if b=6 then (kineticDriftBlock10Coeff10Row6Norm h).val else 0)

theorem kineticDriftBlock10Coeff10_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock10 10 b=kineticDriftBlock10Row10 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock10.coeff 10))
    (n := 7) (by have := kineticBlock10Coeff10_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock10.coeff 10)).coeff 0=(kineticDriftBlock10Coeff10Row0Norm h).val :=
    (kineticDriftBlock10Coeff10Row0Norm h).property
  have h1 : (driftReader h (kineticBlock10.coeff 10)).coeff 1=(kineticDriftBlock10Coeff10Row1Norm h).val :=
    (kineticDriftBlock10Coeff10Row1Norm h).property
  have h2 : (driftReader h (kineticBlock10.coeff 10)).coeff 2=(kineticDriftBlock10Coeff10Row2Norm h).val :=
    (kineticDriftBlock10Coeff10Row2Norm h).property
  have h3 : (driftReader h (kineticBlock10.coeff 10)).coeff 3=(kineticDriftBlock10Coeff10Row3Norm h).val :=
    (kineticDriftBlock10Coeff10Row3Norm h).property
  have h4 : (driftReader h (kineticBlock10.coeff 10)).coeff 4=(kineticDriftBlock10Coeff10Row4Norm h).val :=
    (kineticDriftBlock10Coeff10Row4Norm h).property
  have h5 : (driftReader h (kineticBlock10.coeff 10)).coeff 5=(kineticDriftBlock10Coeff10Row5Norm h).val :=
    (kineticDriftBlock10Coeff10Row5Norm h).property
  have h6 : (driftReader h (kineticBlock10.coeff 10)).coeff 6=(kineticDriftBlock10Coeff10Row6Norm h).val :=
    (kineticDriftBlock10Coeff10Row6Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock10Row10,h0,h1,h2,h3,h4,h5,h6] using he

def kineticDriftBlock10Row11 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock10Coeff11Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock10Coeff11Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock10Coeff11Row2Norm h).val else 0) + (if b=3 then (kineticDriftBlock10Coeff11Row3Norm h).val else 0) + (if b=4 then (kineticDriftBlock10Coeff11Row4Norm h).val else 0) + (if b=5 then (kineticDriftBlock10Coeff11Row5Norm h).val else 0) + (if b=6 then (kineticDriftBlock10Coeff11Row6Norm h).val else 0)

theorem kineticDriftBlock10Coeff11_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock10 11 b=kineticDriftBlock10Row11 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock10.coeff 11))
    (n := 7) (by have := kineticBlock10Coeff11_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock10.coeff 11)).coeff 0=(kineticDriftBlock10Coeff11Row0Norm h).val :=
    (kineticDriftBlock10Coeff11Row0Norm h).property
  have h1 : (driftReader h (kineticBlock10.coeff 11)).coeff 1=(kineticDriftBlock10Coeff11Row1Norm h).val :=
    (kineticDriftBlock10Coeff11Row1Norm h).property
  have h2 : (driftReader h (kineticBlock10.coeff 11)).coeff 2=(kineticDriftBlock10Coeff11Row2Norm h).val :=
    (kineticDriftBlock10Coeff11Row2Norm h).property
  have h3 : (driftReader h (kineticBlock10.coeff 11)).coeff 3=(kineticDriftBlock10Coeff11Row3Norm h).val :=
    (kineticDriftBlock10Coeff11Row3Norm h).property
  have h4 : (driftReader h (kineticBlock10.coeff 11)).coeff 4=(kineticDriftBlock10Coeff11Row4Norm h).val :=
    (kineticDriftBlock10Coeff11Row4Norm h).property
  have h5 : (driftReader h (kineticBlock10.coeff 11)).coeff 5=(kineticDriftBlock10Coeff11Row5Norm h).val :=
    (kineticDriftBlock10Coeff11Row5Norm h).property
  have h6 : (driftReader h (kineticBlock10.coeff 11)).coeff 6=(kineticDriftBlock10Coeff11Row6Norm h).val :=
    (kineticDriftBlock10Coeff11Row6Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock10Row11,h0,h1,h2,h3,h4,h5,h6] using he

theorem kineticDriftBlock10_rows (h : ℂ) (j b : ℕ) :
    kineticDriftCell h kineticBlock10 j b=(if j=0 then kineticDriftBlock10Row0 h b else 0) + (if j=1 then kineticDriftBlock10Row1 h b else 0) + (if j=2 then kineticDriftBlock10Row2 h b else 0) + (if j=3 then kineticDriftBlock10Row3 h b else 0) + (if j=4 then kineticDriftBlock10Row4 h b else 0) + (if j=5 then kineticDriftBlock10Row5 h b else 0) + (if j=6 then kineticDriftBlock10Row6 h b else 0) + (if j=7 then kineticDriftBlock10Row7 h b else 0) + (if j=8 then kineticDriftBlock10Row8 h b else 0) + (if j=9 then kineticDriftBlock10Row9 h b else 0) + (if j=10 then kineticDriftBlock10Row10 h b else 0) + (if j=11 then kineticDriftBlock10Row11 h b else 0) := by
  by_cases hj : j≤11
  · interval_cases j
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock10Coeff0_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock10Coeff1_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock10Coeff2_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock10Coeff3_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock10Coeff4_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock10Coeff5_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock10Coeff6_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock10Coeff7_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock10Coeff8_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock10Coeff9_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock10Coeff10_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock10Coeff11_rows h b
  · have hp : kineticBlock10.coeff j=0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (kineticBlock10_degree.trans_lt (by omega))
    simp only [kineticDriftCell,hp,map_zero,Polynomial.coeff_zero,if_neg (show j≠0 by omega),if_neg (show j≠1 by omega),if_neg (show j≠2 by omega),if_neg (show j≠3 by omega),if_neg (show j≠4 by omega),if_neg (show j≠5 by omega),if_neg (show j≠6 by omega),if_neg (show j≠7 by omega),if_neg (show j≠8 by omega),if_neg (show j≠9 by omega),if_neg (show j≠10 by omega),if_neg (show j≠11 by omega),zero_add]

theorem kineticBlock10_drift_bound : KineticDriftBound kineticBlock10 6 := by
  intro h j b hb
  by_cases hj : j≤11
  · interval_cases j
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock10Coeff0_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock10Coeff1_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock10Coeff2_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock10Coeff3_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock10Coeff4_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock10Coeff5_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock10Coeff6_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock10Coeff7_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock10Coeff8_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock10Coeff9_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock10Coeff10_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock10Coeff11_drift_degree h).trans_lt hb)
  · have hp : kineticBlock10.coeff j=0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (kineticBlock10_degree.trans_lt (by omega))
    simp only [kineticDriftCell,hp,map_zero,Polynomial.coeff_zero]

end
end HTGeometry.ThetaRatioKineticContraction
