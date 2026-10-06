import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticDriftReader
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticDegree
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def kineticDriftMoment2Coeff0Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment2KineticCoeff0).coeff 0=c} := by
  have he : (driftReader h clearMoment2KineticCoeff0).coeff 0=(driftReader h clearMoment2KineticCoeff0).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment2KineticCoeff0Norm.property]
    dsimp only [clearMoment2KineticCoeff0Norm]
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

def kineticDriftMoment2Coeff0Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment2KineticCoeff0).coeff 1=c} := by
  have he : (driftReader h clearMoment2KineticCoeff0).coeff 1=(driftReader h clearMoment2KineticCoeff0).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment2KineticCoeff0Norm.property]
    dsimp only [clearMoment2KineticCoeff0Norm]
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

def kineticDriftMoment2Coeff1Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment2KineticCoeff1).coeff 0=c} := by
  have he : (driftReader h clearMoment2KineticCoeff1).coeff 0=(driftReader h clearMoment2KineticCoeff1).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment2KineticCoeff1Norm.property]
    dsimp only [clearMoment2KineticCoeff1Norm]
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

def kineticDriftMoment2Coeff1Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment2KineticCoeff1).coeff 1=c} := by
  have he : (driftReader h clearMoment2KineticCoeff1).coeff 1=(driftReader h clearMoment2KineticCoeff1).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment2KineticCoeff1Norm.property]
    dsimp only [clearMoment2KineticCoeff1Norm]
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

def kineticDriftMoment2Coeff2Row0Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment2KineticCoeff2).coeff 0=c} := by
  have he : (driftReader h clearMoment2KineticCoeff2).coeff 0=(driftReader h clearMoment2KineticCoeff2).coeff 0 := rfl
  conv at he =>
    rhs
    rw [clearMoment2KineticCoeff2Norm.property]
    dsimp only [clearMoment2KineticCoeff2Norm]
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

def kineticDriftMoment2Coeff2Row1Norm (h : ℂ) :
    {c : ℂ // (driftReader h clearMoment2KineticCoeff2).coeff 1=c} := by
  have he : (driftReader h clearMoment2KineticCoeff2).coeff 1=(driftReader h clearMoment2KineticCoeff2).coeff 1 := rfl
  conv at he =>
    rhs
    rw [clearMoment2KineticCoeff2Norm.property]
    dsimp only [clearMoment2KineticCoeff2Norm]
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

theorem clearMoment2KineticCoeff0_drift_degree (h : ℂ) :
    (driftReader h clearMoment2KineticCoeff0).natDegree≤1 := by
  rw [clearMoment2KineticCoeff0Norm.property]
  dsimp only [clearMoment2KineticCoeff0Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment2KineticCoeff0_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment2KineticCoeff0=
      ∑ b ∈ Finset.range 2, (driftReader h clearMoment2KineticCoeff0).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment2KineticCoeff0_drift_degree h; omega) v

theorem clearMoment2KineticCoeff1_drift_degree (h : ℂ) :
    (driftReader h clearMoment2KineticCoeff1).natDegree≤1 := by
  rw [clearMoment2KineticCoeff1Norm.property]
  dsimp only [clearMoment2KineticCoeff1Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment2KineticCoeff1_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment2KineticCoeff1=
      ∑ b ∈ Finset.range 2, (driftReader h clearMoment2KineticCoeff1).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment2KineticCoeff1_drift_degree h; omega) v

theorem clearMoment2KineticCoeff2_drift_degree (h : ℂ) :
    (driftReader h clearMoment2KineticCoeff2).natDegree≤1 := by
  rw [clearMoment2KineticCoeff2Norm.property]
  dsimp only [clearMoment2KineticCoeff2Norm]
  norm_num only [Nat.rawCast,Int.rawCast,map_add,map_sub,map_mul,map_pow,map_neg,_root_.map_ofNat,_root_.map_natCast,_root_.map_intCast,
    driftReader_C,driftReader_X,driftReaderCoord]
  compute_degree!

theorem clearMoment2KineticCoeff2_drift_expansion (h v : ℂ) :
    eval (basePoint h v 0) clearMoment2KineticCoeff2=
      ∑ b ∈ Finset.range 2, (driftReader h clearMoment2KineticCoeff2).coeff b*v^b := by
  rw [←driftReader_eval]
  exact Polynomial.eval_eq_sum_range' (by have := clearMoment2KineticCoeff2_drift_degree h; omega) v

end
end HTGeometry.ThetaRatioKineticContraction
