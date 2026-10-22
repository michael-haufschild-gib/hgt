import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticDriftReader
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticDegree
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def kineticDriftMoment8Coeff0Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff0).coeff 0=c} := by
  have he : (driftReader h clearMoment8KineticCoeff0).coeff 0=(driftReader h clearMoment8KineticCoeff0).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff0Norm.property]
    dsimp only [clearMoment8KineticCoeff0Norm]
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

def kineticDriftMoment8Coeff0Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff0).coeff 1=c} := by
  have he : (driftReader h clearMoment8KineticCoeff0).coeff 1=(driftReader h clearMoment8KineticCoeff0).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff0Norm.property]
    dsimp only [clearMoment8KineticCoeff0Norm]
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

def kineticDriftMoment8Coeff0Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff0).coeff 2=c} := by
  have he : (driftReader h clearMoment8KineticCoeff0).coeff 2=(driftReader h clearMoment8KineticCoeff0).coeff 2 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff0Norm.property]
    dsimp only [clearMoment8KineticCoeff0Norm]
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

def kineticDriftMoment8Coeff0Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff0).coeff 3=c} := by
  have he : (driftReader h clearMoment8KineticCoeff0).coeff 3=(driftReader h clearMoment8KineticCoeff0).coeff 3 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff0Norm.property]
    dsimp only [clearMoment8KineticCoeff0Norm]
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

def kineticDriftMoment8Coeff0Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff0).coeff 4=c} := by
  have he : (driftReader h clearMoment8KineticCoeff0).coeff 4=(driftReader h clearMoment8KineticCoeff0).coeff 4 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff0Norm.property]
    dsimp only [clearMoment8KineticCoeff0Norm]
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

def kineticDriftMoment8Coeff1Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff1).coeff 0=c} := by
  have he : (driftReader h clearMoment8KineticCoeff1).coeff 0=(driftReader h clearMoment8KineticCoeff1).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff1Norm.property]
    dsimp only [clearMoment8KineticCoeff1Norm]
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

def kineticDriftMoment8Coeff1Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff1).coeff 1=c} := by
  have he : (driftReader h clearMoment8KineticCoeff1).coeff 1=(driftReader h clearMoment8KineticCoeff1).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff1Norm.property]
    dsimp only [clearMoment8KineticCoeff1Norm]
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

def kineticDriftMoment8Coeff1Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff1).coeff 2=c} := by
  have he : (driftReader h clearMoment8KineticCoeff1).coeff 2=(driftReader h clearMoment8KineticCoeff1).coeff 2 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff1Norm.property]
    dsimp only [clearMoment8KineticCoeff1Norm]
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

def kineticDriftMoment8Coeff1Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff1).coeff 3=c} := by
  have he : (driftReader h clearMoment8KineticCoeff1).coeff 3=(driftReader h clearMoment8KineticCoeff1).coeff 3 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff1Norm.property]
    dsimp only [clearMoment8KineticCoeff1Norm]
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

def kineticDriftMoment8Coeff1Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff1).coeff 4=c} := by
  have he : (driftReader h clearMoment8KineticCoeff1).coeff 4=(driftReader h clearMoment8KineticCoeff1).coeff 4 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff1Norm.property]
    dsimp only [clearMoment8KineticCoeff1Norm]
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

def kineticDriftMoment8Coeff2Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff2).coeff 0=c} := by
  have he : (driftReader h clearMoment8KineticCoeff2).coeff 0=(driftReader h clearMoment8KineticCoeff2).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff2Norm.property]
    dsimp only [clearMoment8KineticCoeff2Norm]
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

def kineticDriftMoment8Coeff2Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff2).coeff 1=c} := by
  have he : (driftReader h clearMoment8KineticCoeff2).coeff 1=(driftReader h clearMoment8KineticCoeff2).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff2Norm.property]
    dsimp only [clearMoment8KineticCoeff2Norm]
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

def kineticDriftMoment8Coeff2Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff2).coeff 2=c} := by
  have he : (driftReader h clearMoment8KineticCoeff2).coeff 2=(driftReader h clearMoment8KineticCoeff2).coeff 2 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff2Norm.property]
    dsimp only [clearMoment8KineticCoeff2Norm]
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

def kineticDriftMoment8Coeff2Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff2).coeff 3=c} := by
  have he : (driftReader h clearMoment8KineticCoeff2).coeff 3=(driftReader h clearMoment8KineticCoeff2).coeff 3 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff2Norm.property]
    dsimp only [clearMoment8KineticCoeff2Norm]
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

def kineticDriftMoment8Coeff2Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff2).coeff 4=c} := by
  have he : (driftReader h clearMoment8KineticCoeff2).coeff 4=(driftReader h clearMoment8KineticCoeff2).coeff 4 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff2Norm.property]
    dsimp only [clearMoment8KineticCoeff2Norm]
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

def kineticDriftMoment8Coeff3Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff3).coeff 0=c} := by
  have he : (driftReader h clearMoment8KineticCoeff3).coeff 0=(driftReader h clearMoment8KineticCoeff3).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff3Norm.property]
    dsimp only [clearMoment8KineticCoeff3Norm]
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

def kineticDriftMoment8Coeff3Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff3).coeff 1=c} := by
  have he : (driftReader h clearMoment8KineticCoeff3).coeff 1=(driftReader h clearMoment8KineticCoeff3).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff3Norm.property]
    dsimp only [clearMoment8KineticCoeff3Norm]
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

def kineticDriftMoment8Coeff3Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff3).coeff 2=c} := by
  have he : (driftReader h clearMoment8KineticCoeff3).coeff 2=(driftReader h clearMoment8KineticCoeff3).coeff 2 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff3Norm.property]
    dsimp only [clearMoment8KineticCoeff3Norm]
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

def kineticDriftMoment8Coeff3Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff3).coeff 3=c} := by
  have he : (driftReader h clearMoment8KineticCoeff3).coeff 3=(driftReader h clearMoment8KineticCoeff3).coeff 3 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff3Norm.property]
    dsimp only [clearMoment8KineticCoeff3Norm]
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

def kineticDriftMoment8Coeff3Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff3).coeff 4=c} := by
  have he : (driftReader h clearMoment8KineticCoeff3).coeff 4=(driftReader h clearMoment8KineticCoeff3).coeff 4 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff3Norm.property]
    dsimp only [clearMoment8KineticCoeff3Norm]
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

def kineticDriftMoment8Coeff4Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff4).coeff 0=c} := by
  have he : (driftReader h clearMoment8KineticCoeff4).coeff 0=(driftReader h clearMoment8KineticCoeff4).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff4Norm.property]
    dsimp only [clearMoment8KineticCoeff4Norm]
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

def kineticDriftMoment8Coeff4Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff4).coeff 1=c} := by
  have he : (driftReader h clearMoment8KineticCoeff4).coeff 1=(driftReader h clearMoment8KineticCoeff4).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff4Norm.property]
    dsimp only [clearMoment8KineticCoeff4Norm]
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

def kineticDriftMoment8Coeff4Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff4).coeff 2=c} := by
  have he : (driftReader h clearMoment8KineticCoeff4).coeff 2=(driftReader h clearMoment8KineticCoeff4).coeff 2 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff4Norm.property]
    dsimp only [clearMoment8KineticCoeff4Norm]
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

def kineticDriftMoment8Coeff4Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff4).coeff 3=c} := by
  have he : (driftReader h clearMoment8KineticCoeff4).coeff 3=(driftReader h clearMoment8KineticCoeff4).coeff 3 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff4Norm.property]
    dsimp only [clearMoment8KineticCoeff4Norm]
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

def kineticDriftMoment8Coeff4Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff4).coeff 4=c} := by
  have he : (driftReader h clearMoment8KineticCoeff4).coeff 4=(driftReader h clearMoment8KineticCoeff4).coeff 4 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff4Norm.property]
    dsimp only [clearMoment8KineticCoeff4Norm]
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

def kineticDriftMoment8Coeff5Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff5).coeff 0=c} := by
  have he : (driftReader h clearMoment8KineticCoeff5).coeff 0=(driftReader h clearMoment8KineticCoeff5).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff5Norm.property]
    dsimp only [clearMoment8KineticCoeff5Norm]
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

def kineticDriftMoment8Coeff5Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff5).coeff 1=c} := by
  have he : (driftReader h clearMoment8KineticCoeff5).coeff 1=(driftReader h clearMoment8KineticCoeff5).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff5Norm.property]
    dsimp only [clearMoment8KineticCoeff5Norm]
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

def kineticDriftMoment8Coeff5Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff5).coeff 2=c} := by
  have he : (driftReader h clearMoment8KineticCoeff5).coeff 2=(driftReader h clearMoment8KineticCoeff5).coeff 2 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff5Norm.property]
    dsimp only [clearMoment8KineticCoeff5Norm]
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

def kineticDriftMoment8Coeff5Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff5).coeff 3=c} := by
  have he : (driftReader h clearMoment8KineticCoeff5).coeff 3=(driftReader h clearMoment8KineticCoeff5).coeff 3 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff5Norm.property]
    dsimp only [clearMoment8KineticCoeff5Norm]
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

def kineticDriftMoment8Coeff5Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff5).coeff 4=c} := by
  have he : (driftReader h clearMoment8KineticCoeff5).coeff 4=(driftReader h clearMoment8KineticCoeff5).coeff 4 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff5Norm.property]
    dsimp only [clearMoment8KineticCoeff5Norm]
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

def kineticDriftMoment8Coeff6Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff6).coeff 0=c} := by
  have he : (driftReader h clearMoment8KineticCoeff6).coeff 0=(driftReader h clearMoment8KineticCoeff6).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff6Norm.property]
    dsimp only [clearMoment8KineticCoeff6Norm]
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

def kineticDriftMoment8Coeff6Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff6).coeff 1=c} := by
  have he : (driftReader h clearMoment8KineticCoeff6).coeff 1=(driftReader h clearMoment8KineticCoeff6).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff6Norm.property]
    dsimp only [clearMoment8KineticCoeff6Norm]
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

def kineticDriftMoment8Coeff6Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff6).coeff 2=c} := by
  have he : (driftReader h clearMoment8KineticCoeff6).coeff 2=(driftReader h clearMoment8KineticCoeff6).coeff 2 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff6Norm.property]
    dsimp only [clearMoment8KineticCoeff6Norm]
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

def kineticDriftMoment8Coeff6Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff6).coeff 3=c} := by
  have he : (driftReader h clearMoment8KineticCoeff6).coeff 3=(driftReader h clearMoment8KineticCoeff6).coeff 3 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff6Norm.property]
    dsimp only [clearMoment8KineticCoeff6Norm]
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

def kineticDriftMoment8Coeff6Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff6).coeff 4=c} := by
  have he : (driftReader h clearMoment8KineticCoeff6).coeff 4=(driftReader h clearMoment8KineticCoeff6).coeff 4 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff6Norm.property]
    dsimp only [clearMoment8KineticCoeff6Norm]
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

def kineticDriftMoment8Coeff7Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff7).coeff 0=c} := by
  have he : (driftReader h clearMoment8KineticCoeff7).coeff 0=(driftReader h clearMoment8KineticCoeff7).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff7Norm.property]
    dsimp only [clearMoment8KineticCoeff7Norm]
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

def kineticDriftMoment8Coeff7Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff7).coeff 1=c} := by
  have he : (driftReader h clearMoment8KineticCoeff7).coeff 1=(driftReader h clearMoment8KineticCoeff7).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff7Norm.property]
    dsimp only [clearMoment8KineticCoeff7Norm]
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

def kineticDriftMoment8Coeff7Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff7).coeff 2=c} := by
  have he : (driftReader h clearMoment8KineticCoeff7).coeff 2=(driftReader h clearMoment8KineticCoeff7).coeff 2 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff7Norm.property]
    dsimp only [clearMoment8KineticCoeff7Norm]
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

def kineticDriftMoment8Coeff7Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff7).coeff 3=c} := by
  have he : (driftReader h clearMoment8KineticCoeff7).coeff 3=(driftReader h clearMoment8KineticCoeff7).coeff 3 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff7Norm.property]
    dsimp only [clearMoment8KineticCoeff7Norm]
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

def kineticDriftMoment8Coeff7Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff7).coeff 4=c} := by
  have he : (driftReader h clearMoment8KineticCoeff7).coeff 4=(driftReader h clearMoment8KineticCoeff7).coeff 4 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff7Norm.property]
    dsimp only [clearMoment8KineticCoeff7Norm]
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

def kineticDriftMoment8Coeff8Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff8).coeff 0=c} := by
  have he : (driftReader h clearMoment8KineticCoeff8).coeff 0=(driftReader h clearMoment8KineticCoeff8).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff8Norm.property]
    dsimp only [clearMoment8KineticCoeff8Norm]
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

def kineticDriftMoment8Coeff8Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff8).coeff 1=c} := by
  have he : (driftReader h clearMoment8KineticCoeff8).coeff 1=(driftReader h clearMoment8KineticCoeff8).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff8Norm.property]
    dsimp only [clearMoment8KineticCoeff8Norm]
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

def kineticDriftMoment8Coeff8Row2Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff8).coeff 2=c} := by
  have he : (driftReader h clearMoment8KineticCoeff8).coeff 2=(driftReader h clearMoment8KineticCoeff8).coeff 2 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff8Norm.property]
    dsimp only [clearMoment8KineticCoeff8Norm]
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

def kineticDriftMoment8Coeff8Row3Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff8).coeff 3=c} := by
  have he : (driftReader h clearMoment8KineticCoeff8).coeff 3=(driftReader h clearMoment8KineticCoeff8).coeff 3 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff8Norm.property]
    dsimp only [clearMoment8KineticCoeff8Norm]
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

def kineticDriftMoment8Coeff8Row4Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment8KineticCoeff8).coeff 4=c} := by
  have he : (driftReader h clearMoment8KineticCoeff8).coeff 4=(driftReader h clearMoment8KineticCoeff8).coeff 4 := rfl
  conv at he =>
    rhs
    rw [clearMoment8KineticCoeff8Norm.property]
    dsimp only [clearMoment8KineticCoeff8Norm]
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

theorem clearMoment8KineticCoeff0_drift_degree (h : ℂ) :
    (driftReader h clearMoment8KineticCoeff0).natDegree≤4 := by
  rw [clearMoment8KineticCoeff0Norm.property]
  dsimp only [clearMoment8KineticCoeff0Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment8KineticCoeff0_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment8KineticCoeff0=
      ∑ b ∈ Finset.range 5, (driftReader h clearMoment8KineticCoeff0).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment8KineticCoeff0_drift_degree h; omega) v

theorem clearMoment8KineticCoeff1_drift_degree (h : ℂ) :
    (driftReader h clearMoment8KineticCoeff1).natDegree≤4 := by
  rw [clearMoment8KineticCoeff1Norm.property]
  dsimp only [clearMoment8KineticCoeff1Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment8KineticCoeff1_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment8KineticCoeff1=
      ∑ b ∈ Finset.range 5, (driftReader h clearMoment8KineticCoeff1).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment8KineticCoeff1_drift_degree h; omega) v

theorem clearMoment8KineticCoeff2_drift_degree (h : ℂ) :
    (driftReader h clearMoment8KineticCoeff2).natDegree≤4 := by
  rw [clearMoment8KineticCoeff2Norm.property]
  dsimp only [clearMoment8KineticCoeff2Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment8KineticCoeff2_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment8KineticCoeff2=
      ∑ b ∈ Finset.range 5, (driftReader h clearMoment8KineticCoeff2).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment8KineticCoeff2_drift_degree h; omega) v

theorem clearMoment8KineticCoeff3_drift_degree (h : ℂ) :
    (driftReader h clearMoment8KineticCoeff3).natDegree≤4 := by
  rw [clearMoment8KineticCoeff3Norm.property]
  dsimp only [clearMoment8KineticCoeff3Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment8KineticCoeff3_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment8KineticCoeff3=
      ∑ b ∈ Finset.range 5, (driftReader h clearMoment8KineticCoeff3).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment8KineticCoeff3_drift_degree h; omega) v

theorem clearMoment8KineticCoeff4_drift_degree (h : ℂ) :
    (driftReader h clearMoment8KineticCoeff4).natDegree≤4 := by
  rw [clearMoment8KineticCoeff4Norm.property]
  dsimp only [clearMoment8KineticCoeff4Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment8KineticCoeff4_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment8KineticCoeff4=
      ∑ b ∈ Finset.range 5, (driftReader h clearMoment8KineticCoeff4).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment8KineticCoeff4_drift_degree h; omega) v

theorem clearMoment8KineticCoeff5_drift_degree (h : ℂ) :
    (driftReader h clearMoment8KineticCoeff5).natDegree≤4 := by
  rw [clearMoment8KineticCoeff5Norm.property]
  dsimp only [clearMoment8KineticCoeff5Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment8KineticCoeff5_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment8KineticCoeff5=
      ∑ b ∈ Finset.range 5, (driftReader h clearMoment8KineticCoeff5).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment8KineticCoeff5_drift_degree h; omega) v

theorem clearMoment8KineticCoeff6_drift_degree (h : ℂ) :
    (driftReader h clearMoment8KineticCoeff6).natDegree≤4 := by
  rw [clearMoment8KineticCoeff6Norm.property]
  dsimp only [clearMoment8KineticCoeff6Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment8KineticCoeff6_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment8KineticCoeff6=
      ∑ b ∈ Finset.range 5, (driftReader h clearMoment8KineticCoeff6).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment8KineticCoeff6_drift_degree h; omega) v

theorem clearMoment8KineticCoeff7_drift_degree (h : ℂ) :
    (driftReader h clearMoment8KineticCoeff7).natDegree≤4 := by
  rw [clearMoment8KineticCoeff7Norm.property]
  dsimp only [clearMoment8KineticCoeff7Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment8KineticCoeff7_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment8KineticCoeff7=
      ∑ b ∈ Finset.range 5, (driftReader h clearMoment8KineticCoeff7).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment8KineticCoeff7_drift_degree h; omega) v

theorem clearMoment8KineticCoeff8_drift_degree (h : ℂ) :
    (driftReader h clearMoment8KineticCoeff8).natDegree≤4 := by
  rw [clearMoment8KineticCoeff8Norm.property]
  dsimp only [clearMoment8KineticCoeff8Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment8KineticCoeff8_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment8KineticCoeff8=
      ∑ b ∈ Finset.range 5, (driftReader h clearMoment8KineticCoeff8).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment8KineticCoeff8_drift_degree h; omega) v

end
end HTGeometry.ThetaRatioKineticContraction
