import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticDriftReader
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticDegree
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def kineticDriftMoment4Coeff0Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment4KineticCoeff0).coeff 0=c} := by
  have he : (driftReader h clearMoment4KineticCoeff0).coeff 0=(driftReader h clearMoment4KineticCoeff0).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment4KineticCoeff0Norm.property]
    dsimp only [clearMoment4KineticCoeff0Norm]
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

def kineticDriftMoment4Coeff0Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment4KineticCoeff0).coeff 1=c} := by
  have he : (driftReader h clearMoment4KineticCoeff0).coeff 1=(driftReader h clearMoment4KineticCoeff0).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment4KineticCoeff0Norm.property]
    dsimp only [clearMoment4KineticCoeff0Norm]
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

def kineticDriftMoment4Coeff0Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment4KineticCoeff0).coeff 2=c} := by
  have he : (driftReader h clearMoment4KineticCoeff0).coeff 2=(driftReader h clearMoment4KineticCoeff0).coeff 2 := rfl
  conv at he =>
    rhs
    rw [clearMoment4KineticCoeff0Norm.property]
    dsimp only [clearMoment4KineticCoeff0Norm]
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

def kineticDriftMoment4Coeff1Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment4KineticCoeff1).coeff 0=c} := by
  have he : (driftReader h clearMoment4KineticCoeff1).coeff 0=(driftReader h clearMoment4KineticCoeff1).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment4KineticCoeff1Norm.property]
    dsimp only [clearMoment4KineticCoeff1Norm]
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

def kineticDriftMoment4Coeff1Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment4KineticCoeff1).coeff 1=c} := by
  have he : (driftReader h clearMoment4KineticCoeff1).coeff 1=(driftReader h clearMoment4KineticCoeff1).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment4KineticCoeff1Norm.property]
    dsimp only [clearMoment4KineticCoeff1Norm]
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

def kineticDriftMoment4Coeff1Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment4KineticCoeff1).coeff 2=c} := by
  have he : (driftReader h clearMoment4KineticCoeff1).coeff 2=(driftReader h clearMoment4KineticCoeff1).coeff 2 := rfl
  conv at he =>
    rhs
    rw [clearMoment4KineticCoeff1Norm.property]
    dsimp only [clearMoment4KineticCoeff1Norm]
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

def kineticDriftMoment4Coeff2Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment4KineticCoeff2).coeff 0=c} := by
  have he : (driftReader h clearMoment4KineticCoeff2).coeff 0=(driftReader h clearMoment4KineticCoeff2).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment4KineticCoeff2Norm.property]
    dsimp only [clearMoment4KineticCoeff2Norm]
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

def kineticDriftMoment4Coeff2Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment4KineticCoeff2).coeff 1=c} := by
  have he : (driftReader h clearMoment4KineticCoeff2).coeff 1=(driftReader h clearMoment4KineticCoeff2).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment4KineticCoeff2Norm.property]
    dsimp only [clearMoment4KineticCoeff2Norm]
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

def kineticDriftMoment4Coeff2Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment4KineticCoeff2).coeff 2=c} := by
  have he : (driftReader h clearMoment4KineticCoeff2).coeff 2=(driftReader h clearMoment4KineticCoeff2).coeff 2 := rfl
  conv at he =>
    rhs
    rw [clearMoment4KineticCoeff2Norm.property]
    dsimp only [clearMoment4KineticCoeff2Norm]
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

def kineticDriftMoment4Coeff3Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment4KineticCoeff3).coeff 0=c} := by
  have he : (driftReader h clearMoment4KineticCoeff3).coeff 0=(driftReader h clearMoment4KineticCoeff3).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment4KineticCoeff3Norm.property]
    dsimp only [clearMoment4KineticCoeff3Norm]
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

def kineticDriftMoment4Coeff3Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment4KineticCoeff3).coeff 1=c} := by
  have he : (driftReader h clearMoment4KineticCoeff3).coeff 1=(driftReader h clearMoment4KineticCoeff3).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment4KineticCoeff3Norm.property]
    dsimp only [clearMoment4KineticCoeff3Norm]
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

def kineticDriftMoment4Coeff3Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment4KineticCoeff3).coeff 2=c} := by
  have he : (driftReader h clearMoment4KineticCoeff3).coeff 2=(driftReader h clearMoment4KineticCoeff3).coeff 2 := rfl
  conv at he =>
    rhs
    rw [clearMoment4KineticCoeff3Norm.property]
    dsimp only [clearMoment4KineticCoeff3Norm]
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

def kineticDriftMoment4Coeff4Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment4KineticCoeff4).coeff 0=c} := by
  have he : (driftReader h clearMoment4KineticCoeff4).coeff 0=(driftReader h clearMoment4KineticCoeff4).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment4KineticCoeff4Norm.property]
    dsimp only [clearMoment4KineticCoeff4Norm]
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

def kineticDriftMoment4Coeff4Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment4KineticCoeff4).coeff 1=c} := by
  have he : (driftReader h clearMoment4KineticCoeff4).coeff 1=(driftReader h clearMoment4KineticCoeff4).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment4KineticCoeff4Norm.property]
    dsimp only [clearMoment4KineticCoeff4Norm]
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

def kineticDriftMoment4Coeff4Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment4KineticCoeff4).coeff 2=c} := by
  have he : (driftReader h clearMoment4KineticCoeff4).coeff 2=(driftReader h clearMoment4KineticCoeff4).coeff 2 := rfl
  conv at he =>
    rhs
    rw [clearMoment4KineticCoeff4Norm.property]
    dsimp only [clearMoment4KineticCoeff4Norm]
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

theorem clearMoment4KineticCoeff0_drift_degree (h : ℂ) :
    (driftReader h clearMoment4KineticCoeff0).natDegree≤2 := by
  rw [clearMoment4KineticCoeff0Norm.property]
  dsimp only [clearMoment4KineticCoeff0Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment4KineticCoeff0_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment4KineticCoeff0=
      ∑ b ∈ Finset.range 3, (driftReader h clearMoment4KineticCoeff0).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment4KineticCoeff0_drift_degree h; omega) v

theorem clearMoment4KineticCoeff1_drift_degree (h : ℂ) :
    (driftReader h clearMoment4KineticCoeff1).natDegree≤2 := by
  rw [clearMoment4KineticCoeff1Norm.property]
  dsimp only [clearMoment4KineticCoeff1Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment4KineticCoeff1_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment4KineticCoeff1=
      ∑ b ∈ Finset.range 3, (driftReader h clearMoment4KineticCoeff1).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment4KineticCoeff1_drift_degree h; omega) v

theorem clearMoment4KineticCoeff2_drift_degree (h : ℂ) :
    (driftReader h clearMoment4KineticCoeff2).natDegree≤2 := by
  rw [clearMoment4KineticCoeff2Norm.property]
  dsimp only [clearMoment4KineticCoeff2Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment4KineticCoeff2_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment4KineticCoeff2=
      ∑ b ∈ Finset.range 3, (driftReader h clearMoment4KineticCoeff2).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment4KineticCoeff2_drift_degree h; omega) v

theorem clearMoment4KineticCoeff3_drift_degree (h : ℂ) :
    (driftReader h clearMoment4KineticCoeff3).natDegree≤2 := by
  rw [clearMoment4KineticCoeff3Norm.property]
  dsimp only [clearMoment4KineticCoeff3Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment4KineticCoeff3_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment4KineticCoeff3=
      ∑ b ∈ Finset.range 3, (driftReader h clearMoment4KineticCoeff3).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment4KineticCoeff3_drift_degree h; omega) v

theorem clearMoment4KineticCoeff4_drift_degree (h : ℂ) :
    (driftReader h clearMoment4KineticCoeff4).natDegree≤2 := by
  rw [clearMoment4KineticCoeff4Norm.property]
  dsimp only [clearMoment4KineticCoeff4Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment4KineticCoeff4_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment4KineticCoeff4=
      ∑ b ∈ Finset.range 3, (driftReader h clearMoment4KineticCoeff4).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment4KineticCoeff4_drift_degree h; omega) v

end
end HTGeometry.ThetaRatioKineticContraction
