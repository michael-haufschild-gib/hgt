import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticBlockCoefficients2
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticDriftReader
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticDegree
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticDriftSupport
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def kineticDriftBlock2Coeff0Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock2.coeff 0)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock2.coeff 0)).coeff 0=(driftReader h (kineticBlock2.coeff 0)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock2Coeff0Norm.property]
    dsimp only [kineticBlock2Coeff0Norm]
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

def kineticDriftBlock2Coeff0Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock2.coeff 0)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock2.coeff 0)).coeff 1=(driftReader h (kineticBlock2.coeff 0)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock2Coeff0Norm.property]
    dsimp only [kineticBlock2Coeff0Norm]
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

def kineticDriftBlock2Coeff0Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock2.coeff 0)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock2.coeff 0)).coeff 2=(driftReader h (kineticBlock2.coeff 0)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock2Coeff0Norm.property]
    dsimp only [kineticBlock2Coeff0Norm]
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

theorem kineticBlock2Coeff0_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock2.coeff 0)).natDegree≤2 := by
  rw [kineticBlock2Coeff0Norm.property]
  dsimp only [kineticBlock2Coeff0Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock2Coeff1Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock2.coeff 1)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock2.coeff 1)).coeff 0=(driftReader h (kineticBlock2.coeff 1)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock2Coeff1Norm.property]
    dsimp only [kineticBlock2Coeff1Norm]
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

def kineticDriftBlock2Coeff1Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock2.coeff 1)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock2.coeff 1)).coeff 1=(driftReader h (kineticBlock2.coeff 1)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock2Coeff1Norm.property]
    dsimp only [kineticBlock2Coeff1Norm]
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

def kineticDriftBlock2Coeff1Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock2.coeff 1)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock2.coeff 1)).coeff 2=(driftReader h (kineticBlock2.coeff 1)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock2Coeff1Norm.property]
    dsimp only [kineticBlock2Coeff1Norm]
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

theorem kineticBlock2Coeff1_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock2.coeff 1)).natDegree≤2 := by
  rw [kineticBlock2Coeff1Norm.property]
  dsimp only [kineticBlock2Coeff1Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock2Coeff2Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock2.coeff 2)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock2.coeff 2)).coeff 0=(driftReader h (kineticBlock2.coeff 2)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock2Coeff2Norm.property]
    dsimp only [kineticBlock2Coeff2Norm]
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

def kineticDriftBlock2Coeff2Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock2.coeff 2)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock2.coeff 2)).coeff 1=(driftReader h (kineticBlock2.coeff 2)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock2Coeff2Norm.property]
    dsimp only [kineticBlock2Coeff2Norm]
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

def kineticDriftBlock2Coeff2Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock2.coeff 2)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock2.coeff 2)).coeff 2=(driftReader h (kineticBlock2.coeff 2)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock2Coeff2Norm.property]
    dsimp only [kineticBlock2Coeff2Norm]
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

theorem kineticBlock2Coeff2_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock2.coeff 2)).natDegree≤2 := by
  rw [kineticBlock2Coeff2Norm.property]
  dsimp only [kineticBlock2Coeff2Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

def kineticDriftBlock2Coeff3Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock2.coeff 3)).coeff 0=c} := by
  have he : (driftReader h (kineticBlock2.coeff 3)).coeff 0=(driftReader h (kineticBlock2.coeff 3)).coeff 0 := rfl
  conv at he =>
    rhs
    rw [kineticBlock2Coeff3Norm.property]
    dsimp only [kineticBlock2Coeff3Norm]
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

def kineticDriftBlock2Coeff3Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock2.coeff 3)).coeff 1=c} := by
  have he : (driftReader h (kineticBlock2.coeff 3)).coeff 1=(driftReader h (kineticBlock2.coeff 3)).coeff 1 := rfl
  conv at he =>
    rhs
    rw [kineticBlock2Coeff3Norm.property]
    dsimp only [kineticBlock2Coeff3Norm]
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

def kineticDriftBlock2Coeff3Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h (kineticBlock2.coeff 3)).coeff 2=c} := by
  have he : (driftReader h (kineticBlock2.coeff 3)).coeff 2=(driftReader h (kineticBlock2.coeff 3)).coeff 2 := rfl
  conv at he =>
    rhs
    rw [kineticBlock2Coeff3Norm.property]
    dsimp only [kineticBlock2Coeff3Norm]
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

theorem kineticBlock2Coeff3_drift_degree (h : ℂ) :
    (driftReader h (kineticBlock2.coeff 3)).natDegree≤2 := by
  rw [kineticBlock2Coeff3Norm.property]
  dsimp only [kineticBlock2Coeff3Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,
    _root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!


def kineticDriftBlock2Row0 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock2Coeff0Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock2Coeff0Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock2Coeff0Row2Norm h).val else 0)

theorem kineticDriftBlock2Coeff0_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock2 0 b=kineticDriftBlock2Row0 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock2.coeff 0))
    (n := 3) (by have := kineticBlock2Coeff0_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock2.coeff 0)).coeff 0=(kineticDriftBlock2Coeff0Row0Norm h).val :=
    (kineticDriftBlock2Coeff0Row0Norm h).property
  have h1 : (driftReader h (kineticBlock2.coeff 0)).coeff 1=(kineticDriftBlock2Coeff0Row1Norm h).val :=
    (kineticDriftBlock2Coeff0Row1Norm h).property
  have h2 : (driftReader h (kineticBlock2.coeff 0)).coeff 2=(kineticDriftBlock2Coeff0Row2Norm h).val :=
    (kineticDriftBlock2Coeff0Row2Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock2Row0,h0,h1,h2] using he

def kineticDriftBlock2Row1 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock2Coeff1Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock2Coeff1Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock2Coeff1Row2Norm h).val else 0)

theorem kineticDriftBlock2Coeff1_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock2 1 b=kineticDriftBlock2Row1 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock2.coeff 1))
    (n := 3) (by have := kineticBlock2Coeff1_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock2.coeff 1)).coeff 0=(kineticDriftBlock2Coeff1Row0Norm h).val :=
    (kineticDriftBlock2Coeff1Row0Norm h).property
  have h1 : (driftReader h (kineticBlock2.coeff 1)).coeff 1=(kineticDriftBlock2Coeff1Row1Norm h).val :=
    (kineticDriftBlock2Coeff1Row1Norm h).property
  have h2 : (driftReader h (kineticBlock2.coeff 1)).coeff 2=(kineticDriftBlock2Coeff1Row2Norm h).val :=
    (kineticDriftBlock2Coeff1Row2Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock2Row1,h0,h1,h2] using he

def kineticDriftBlock2Row2 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock2Coeff2Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock2Coeff2Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock2Coeff2Row2Norm h).val else 0)

theorem kineticDriftBlock2Coeff2_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock2 2 b=kineticDriftBlock2Row2 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock2.coeff 2))
    (n := 3) (by have := kineticBlock2Coeff2_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock2.coeff 2)).coeff 0=(kineticDriftBlock2Coeff2Row0Norm h).val :=
    (kineticDriftBlock2Coeff2Row0Norm h).property
  have h1 : (driftReader h (kineticBlock2.coeff 2)).coeff 1=(kineticDriftBlock2Coeff2Row1Norm h).val :=
    (kineticDriftBlock2Coeff2Row1Norm h).property
  have h2 : (driftReader h (kineticBlock2.coeff 2)).coeff 2=(kineticDriftBlock2Coeff2Row2Norm h).val :=
    (kineticDriftBlock2Coeff2Row2Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock2Row2,h0,h1,h2] using he

def kineticDriftBlock2Row3 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftBlock2Coeff3Row0Norm h).val else 0) + (if b=1 then (kineticDriftBlock2Coeff3Row1Norm h).val else 0) + (if b=2 then (kineticDriftBlock2Coeff3Row2Norm h).val else 0)

theorem kineticDriftBlock2Coeff3_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticBlock2 3 b=kineticDriftBlock2Row3 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticBlock2.coeff 3))
    (n := 3) (by have := kineticBlock2Coeff3_drift_degree h; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticBlock2.coeff 3)).coeff 0=(kineticDriftBlock2Coeff3Row0Norm h).val :=
    (kineticDriftBlock2Coeff3Row0Norm h).property
  have h1 : (driftReader h (kineticBlock2.coeff 3)).coeff 1=(kineticDriftBlock2Coeff3Row1Norm h).val :=
    (kineticDriftBlock2Coeff3Row1Norm h).property
  have h2 : (driftReader h (kineticBlock2.coeff 3)).coeff 2=(kineticDriftBlock2Coeff3Row2Norm h).val :=
    (kineticDriftBlock2Coeff3Row2Norm h).property
  simpa only [kineticDriftCell,kineticDriftBlock2Row3,h0,h1,h2] using he

theorem kineticDriftBlock2_rows (h : ℂ) (j b : ℕ) :
    kineticDriftCell h kineticBlock2 j b=(if j=0 then kineticDriftBlock2Row0 h b else 0) + (if j=1 then kineticDriftBlock2Row1 h b else 0) + (if j=2 then kineticDriftBlock2Row2 h b else 0) + (if j=3 then kineticDriftBlock2Row3 h b else 0) := by
  by_cases hj : j≤3
  · interval_cases j
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock2Coeff0_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock2Coeff1_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock2Coeff2_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftBlock2Coeff3_rows h b
  · have hp : kineticBlock2.coeff j=0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (kineticBlock2_degree.trans_lt (by omega))
    simp only [kineticDriftCell,hp,map_zero,Polynomial.coeff_zero,if_neg (show j≠0 by omega),if_neg (show j≠1 by omega),if_neg (show j≠2 by omega),if_neg (show j≠3 by omega),zero_add]

theorem kineticBlock2_drift_bound : KineticDriftBound kineticBlock2 2 := by
  intro h j b hb
  by_cases hj : j≤3
  · interval_cases j
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock2Coeff0_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock2Coeff1_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock2Coeff2_drift_degree h).trans_lt hb)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((kineticBlock2Coeff3_drift_degree h).trans_lt hb)
  · have hp : kineticBlock2.coeff j=0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (kineticBlock2_degree.trans_lt (by omega))
    simp only [kineticDriftCell,hp,map_zero,Polynomial.coeff_zero]

end
end HTGeometry.ThetaRatioKineticContraction
