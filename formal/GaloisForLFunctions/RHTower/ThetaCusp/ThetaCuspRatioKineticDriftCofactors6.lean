import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticDriftSupport
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def kineticDriftCof6Coeff0Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 0 0=c} := by
  have he : kineticDriftCell h kineticCof6 0 0=kineticDriftCell h kineticCof6 0 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment10Coeff0Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff0Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 0 1=c} := by
  have he : kineticDriftCell h kineticCof6 0 1=kineticDriftCell h kineticCof6 0 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment10Coeff0Row0Norm,kineticDriftMoment10Coeff0Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff0Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 0 2=c} := by
  have he : kineticDriftCell h kineticCof6 0 2=kineticDriftCell h kineticCof6 0 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment10Coeff0Row1Norm,kineticDriftMoment10Coeff0Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff0Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 0 3=c} := by
  have he : kineticDriftCell h kineticCof6 0 3=kineticDriftCell h kineticCof6 0 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment10Coeff0Row2Norm,kineticDriftMoment10Coeff0Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff0Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 0 4=c} := by
  have he : kineticDriftCell h kineticCof6 0 4=kineticDriftCell h kineticCof6 0 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment10Coeff0Row3Norm,kineticDriftMoment10Coeff0Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff0Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 0 5=c} := by
  have he : kineticDriftCell h kineticCof6 0 5=kineticDriftCell h kineticCof6 0 5 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment10Coeff0Row4Norm,kineticDriftMoment10Coeff0Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff0Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 0 6=c} := by
  have he : kineticDriftCell h kineticCof6 0 6=kineticDriftCell h kineticCof6 0 6 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment10Coeff0Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff1Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 1 0=c} := by
  have he : kineticDriftCell h kineticCof6 1 0=kineticDriftCell h kineticCof6 1 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment10Coeff0Row0Norm,kineticDriftMoment10Coeff1Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff1Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 1 1=c} := by
  have he : kineticDriftCell h kineticCof6 1 1=kineticDriftCell h kineticCof6 1 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment10Coeff0Row0Norm,kineticDriftMoment10Coeff0Row1Norm,kineticDriftMoment10Coeff1Row0Norm,kineticDriftMoment10Coeff1Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff1Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 1 2=c} := by
  have he : kineticDriftCell h kineticCof6 1 2=kineticDriftCell h kineticCof6 1 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment10Coeff0Row1Norm,kineticDriftMoment10Coeff0Row2Norm,kineticDriftMoment10Coeff1Row1Norm,kineticDriftMoment10Coeff1Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff1Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 1 3=c} := by
  have he : kineticDriftCell h kineticCof6 1 3=kineticDriftCell h kineticCof6 1 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment10Coeff0Row2Norm,kineticDriftMoment10Coeff0Row3Norm,kineticDriftMoment10Coeff1Row2Norm,kineticDriftMoment10Coeff1Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff1Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 1 4=c} := by
  have he : kineticDriftCell h kineticCof6 1 4=kineticDriftCell h kineticCof6 1 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment10Coeff0Row3Norm,kineticDriftMoment10Coeff0Row4Norm,kineticDriftMoment10Coeff1Row3Norm,kineticDriftMoment10Coeff1Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff1Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 1 5=c} := by
  have he : kineticDriftCell h kineticCof6 1 5=kineticDriftCell h kineticCof6 1 5 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment10Coeff0Row4Norm,kineticDriftMoment10Coeff0Row5Norm,kineticDriftMoment10Coeff1Row4Norm,kineticDriftMoment10Coeff1Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff1Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 1 6=c} := by
  have he : kineticDriftCell h kineticCof6 1 6=kineticDriftCell h kineticCof6 1 6 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment10Coeff0Row5Norm,kineticDriftMoment10Coeff1Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff2Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 2 0=c} := by
  have he : kineticDriftCell h kineticCof6 2 0=kineticDriftCell h kineticCof6 2 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment10Coeff0Row0Norm,kineticDriftMoment10Coeff1Row0Norm,kineticDriftMoment10Coeff2Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff2Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 2 1=c} := by
  have he : kineticDriftCell h kineticCof6 2 1=kineticDriftCell h kineticCof6 2 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment10Coeff0Row0Norm,kineticDriftMoment10Coeff0Row1Norm,kineticDriftMoment10Coeff1Row0Norm,kineticDriftMoment10Coeff1Row1Norm,kineticDriftMoment10Coeff2Row0Norm,kineticDriftMoment10Coeff2Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff2Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 2 2=c} := by
  have he : kineticDriftCell h kineticCof6 2 2=kineticDriftCell h kineticCof6 2 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment10Coeff0Row1Norm,kineticDriftMoment10Coeff0Row2Norm,kineticDriftMoment10Coeff1Row1Norm,kineticDriftMoment10Coeff1Row2Norm,kineticDriftMoment10Coeff2Row1Norm,kineticDriftMoment10Coeff2Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff2Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 2 3=c} := by
  have he : kineticDriftCell h kineticCof6 2 3=kineticDriftCell h kineticCof6 2 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment10Coeff0Row2Norm,kineticDriftMoment10Coeff0Row3Norm,kineticDriftMoment10Coeff1Row2Norm,kineticDriftMoment10Coeff1Row3Norm,kineticDriftMoment10Coeff2Row2Norm,kineticDriftMoment10Coeff2Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff2Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 2 4=c} := by
  have he : kineticDriftCell h kineticCof6 2 4=kineticDriftCell h kineticCof6 2 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment10Coeff0Row3Norm,kineticDriftMoment10Coeff0Row4Norm,kineticDriftMoment10Coeff1Row3Norm,kineticDriftMoment10Coeff1Row4Norm,kineticDriftMoment10Coeff2Row3Norm,kineticDriftMoment10Coeff2Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff2Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 2 5=c} := by
  have he : kineticDriftCell h kineticCof6 2 5=kineticDriftCell h kineticCof6 2 5 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment10Coeff0Row4Norm,kineticDriftMoment10Coeff0Row5Norm,kineticDriftMoment10Coeff1Row4Norm,kineticDriftMoment10Coeff1Row5Norm,kineticDriftMoment10Coeff2Row4Norm,kineticDriftMoment10Coeff2Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff2Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 2 6=c} := by
  have he : kineticDriftCell h kineticCof6 2 6=kineticDriftCell h kineticCof6 2 6 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment10Coeff0Row5Norm,kineticDriftMoment10Coeff1Row5Norm,kineticDriftMoment10Coeff2Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff3Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 3 0=c} := by
  have he : kineticDriftCell h kineticCof6 3 0=kineticDriftCell h kineticCof6 3 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment10Coeff1Row0Norm,kineticDriftMoment10Coeff2Row0Norm,kineticDriftMoment10Coeff3Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff3Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 3 1=c} := by
  have he : kineticDriftCell h kineticCof6 3 1=kineticDriftCell h kineticCof6 3 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment10Coeff1Row0Norm,kineticDriftMoment10Coeff1Row1Norm,kineticDriftMoment10Coeff2Row0Norm,kineticDriftMoment10Coeff2Row1Norm,kineticDriftMoment10Coeff3Row0Norm,kineticDriftMoment10Coeff3Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff3Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 3 2=c} := by
  have he : kineticDriftCell h kineticCof6 3 2=kineticDriftCell h kineticCof6 3 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment10Coeff1Row1Norm,kineticDriftMoment10Coeff1Row2Norm,kineticDriftMoment10Coeff2Row1Norm,kineticDriftMoment10Coeff2Row2Norm,kineticDriftMoment10Coeff3Row1Norm,kineticDriftMoment10Coeff3Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff3Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 3 3=c} := by
  have he : kineticDriftCell h kineticCof6 3 3=kineticDriftCell h kineticCof6 3 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment10Coeff1Row2Norm,kineticDriftMoment10Coeff1Row3Norm,kineticDriftMoment10Coeff2Row2Norm,kineticDriftMoment10Coeff2Row3Norm,kineticDriftMoment10Coeff3Row2Norm,kineticDriftMoment10Coeff3Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff3Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 3 4=c} := by
  have he : kineticDriftCell h kineticCof6 3 4=kineticDriftCell h kineticCof6 3 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment10Coeff1Row3Norm,kineticDriftMoment10Coeff1Row4Norm,kineticDriftMoment10Coeff2Row3Norm,kineticDriftMoment10Coeff2Row4Norm,kineticDriftMoment10Coeff3Row3Norm,kineticDriftMoment10Coeff3Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff3Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 3 5=c} := by
  have he : kineticDriftCell h kineticCof6 3 5=kineticDriftCell h kineticCof6 3 5 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment10Coeff1Row4Norm,kineticDriftMoment10Coeff1Row5Norm,kineticDriftMoment10Coeff2Row4Norm,kineticDriftMoment10Coeff2Row5Norm,kineticDriftMoment10Coeff3Row4Norm,kineticDriftMoment10Coeff3Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff3Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 3 6=c} := by
  have he : kineticDriftCell h kineticCof6 3 6=kineticDriftCell h kineticCof6 3 6 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment10Coeff1Row5Norm,kineticDriftMoment10Coeff2Row5Norm,kineticDriftMoment10Coeff3Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff4Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 4 0=c} := by
  have he : kineticDriftCell h kineticCof6 4 0=kineticDriftCell h kineticCof6 4 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment10Coeff2Row0Norm,kineticDriftMoment10Coeff3Row0Norm,kineticDriftMoment10Coeff4Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff4Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 4 1=c} := by
  have he : kineticDriftCell h kineticCof6 4 1=kineticDriftCell h kineticCof6 4 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment10Coeff2Row0Norm,kineticDriftMoment10Coeff2Row1Norm,kineticDriftMoment10Coeff3Row0Norm,kineticDriftMoment10Coeff3Row1Norm,kineticDriftMoment10Coeff4Row0Norm,kineticDriftMoment10Coeff4Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff4Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 4 2=c} := by
  have he : kineticDriftCell h kineticCof6 4 2=kineticDriftCell h kineticCof6 4 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment10Coeff2Row1Norm,kineticDriftMoment10Coeff2Row2Norm,kineticDriftMoment10Coeff3Row1Norm,kineticDriftMoment10Coeff3Row2Norm,kineticDriftMoment10Coeff4Row1Norm,kineticDriftMoment10Coeff4Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff4Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 4 3=c} := by
  have he : kineticDriftCell h kineticCof6 4 3=kineticDriftCell h kineticCof6 4 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment10Coeff2Row2Norm,kineticDriftMoment10Coeff2Row3Norm,kineticDriftMoment10Coeff3Row2Norm,kineticDriftMoment10Coeff3Row3Norm,kineticDriftMoment10Coeff4Row2Norm,kineticDriftMoment10Coeff4Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff4Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 4 4=c} := by
  have he : kineticDriftCell h kineticCof6 4 4=kineticDriftCell h kineticCof6 4 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment10Coeff2Row3Norm,kineticDriftMoment10Coeff2Row4Norm,kineticDriftMoment10Coeff3Row3Norm,kineticDriftMoment10Coeff3Row4Norm,kineticDriftMoment10Coeff4Row3Norm,kineticDriftMoment10Coeff4Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff4Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 4 5=c} := by
  have he : kineticDriftCell h kineticCof6 4 5=kineticDriftCell h kineticCof6 4 5 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment10Coeff2Row4Norm,kineticDriftMoment10Coeff2Row5Norm,kineticDriftMoment10Coeff3Row4Norm,kineticDriftMoment10Coeff3Row5Norm,kineticDriftMoment10Coeff4Row4Norm,kineticDriftMoment10Coeff4Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff4Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 4 6=c} := by
  have he : kineticDriftCell h kineticCof6 4 6=kineticDriftCell h kineticCof6 4 6 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment10Coeff2Row5Norm,kineticDriftMoment10Coeff3Row5Norm,kineticDriftMoment10Coeff4Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff5Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 5 0=c} := by
  have he : kineticDriftCell h kineticCof6 5 0=kineticDriftCell h kineticCof6 5 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment10Coeff3Row0Norm,kineticDriftMoment10Coeff4Row0Norm,kineticDriftMoment10Coeff5Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff5Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 5 1=c} := by
  have he : kineticDriftCell h kineticCof6 5 1=kineticDriftCell h kineticCof6 5 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment10Coeff3Row0Norm,kineticDriftMoment10Coeff3Row1Norm,kineticDriftMoment10Coeff4Row0Norm,kineticDriftMoment10Coeff4Row1Norm,kineticDriftMoment10Coeff5Row0Norm,kineticDriftMoment10Coeff5Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff5Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 5 2=c} := by
  have he : kineticDriftCell h kineticCof6 5 2=kineticDriftCell h kineticCof6 5 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment10Coeff3Row1Norm,kineticDriftMoment10Coeff3Row2Norm,kineticDriftMoment10Coeff4Row1Norm,kineticDriftMoment10Coeff4Row2Norm,kineticDriftMoment10Coeff5Row1Norm,kineticDriftMoment10Coeff5Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff5Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 5 3=c} := by
  have he : kineticDriftCell h kineticCof6 5 3=kineticDriftCell h kineticCof6 5 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment10Coeff3Row2Norm,kineticDriftMoment10Coeff3Row3Norm,kineticDriftMoment10Coeff4Row2Norm,kineticDriftMoment10Coeff4Row3Norm,kineticDriftMoment10Coeff5Row2Norm,kineticDriftMoment10Coeff5Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff5Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 5 4=c} := by
  have he : kineticDriftCell h kineticCof6 5 4=kineticDriftCell h kineticCof6 5 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment10Coeff3Row3Norm,kineticDriftMoment10Coeff3Row4Norm,kineticDriftMoment10Coeff4Row3Norm,kineticDriftMoment10Coeff4Row4Norm,kineticDriftMoment10Coeff5Row3Norm,kineticDriftMoment10Coeff5Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff5Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 5 5=c} := by
  have he : kineticDriftCell h kineticCof6 5 5=kineticDriftCell h kineticCof6 5 5 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment10Coeff3Row4Norm,kineticDriftMoment10Coeff3Row5Norm,kineticDriftMoment10Coeff4Row4Norm,kineticDriftMoment10Coeff4Row5Norm,kineticDriftMoment10Coeff5Row4Norm,kineticDriftMoment10Coeff5Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff5Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 5 6=c} := by
  have he : kineticDriftCell h kineticCof6 5 6=kineticDriftCell h kineticCof6 5 6 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment10Coeff3Row5Norm,kineticDriftMoment10Coeff4Row5Norm,kineticDriftMoment10Coeff5Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff6Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 6 0=c} := by
  have he : kineticDriftCell h kineticCof6 6 0=kineticDriftCell h kineticCof6 6 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment10Coeff4Row0Norm,kineticDriftMoment10Coeff5Row0Norm,kineticDriftMoment10Coeff6Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff6Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 6 1=c} := by
  have he : kineticDriftCell h kineticCof6 6 1=kineticDriftCell h kineticCof6 6 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment10Coeff4Row0Norm,kineticDriftMoment10Coeff4Row1Norm,kineticDriftMoment10Coeff5Row0Norm,kineticDriftMoment10Coeff5Row1Norm,kineticDriftMoment10Coeff6Row0Norm,kineticDriftMoment10Coeff6Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff6Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 6 2=c} := by
  have he : kineticDriftCell h kineticCof6 6 2=kineticDriftCell h kineticCof6 6 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment10Coeff4Row1Norm,kineticDriftMoment10Coeff4Row2Norm,kineticDriftMoment10Coeff5Row1Norm,kineticDriftMoment10Coeff5Row2Norm,kineticDriftMoment10Coeff6Row1Norm,kineticDriftMoment10Coeff6Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff6Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 6 3=c} := by
  have he : kineticDriftCell h kineticCof6 6 3=kineticDriftCell h kineticCof6 6 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment10Coeff4Row2Norm,kineticDriftMoment10Coeff4Row3Norm,kineticDriftMoment10Coeff5Row2Norm,kineticDriftMoment10Coeff5Row3Norm,kineticDriftMoment10Coeff6Row2Norm,kineticDriftMoment10Coeff6Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff6Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 6 4=c} := by
  have he : kineticDriftCell h kineticCof6 6 4=kineticDriftCell h kineticCof6 6 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment10Coeff4Row3Norm,kineticDriftMoment10Coeff4Row4Norm,kineticDriftMoment10Coeff5Row3Norm,kineticDriftMoment10Coeff5Row4Norm,kineticDriftMoment10Coeff6Row3Norm,kineticDriftMoment10Coeff6Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff6Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 6 5=c} := by
  have he : kineticDriftCell h kineticCof6 6 5=kineticDriftCell h kineticCof6 6 5 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment10Coeff4Row4Norm,kineticDriftMoment10Coeff4Row5Norm,kineticDriftMoment10Coeff5Row4Norm,kineticDriftMoment10Coeff5Row5Norm,kineticDriftMoment10Coeff6Row4Norm,kineticDriftMoment10Coeff6Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff6Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 6 6=c} := by
  have he : kineticDriftCell h kineticCof6 6 6=kineticDriftCell h kineticCof6 6 6 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment10Coeff4Row5Norm,kineticDriftMoment10Coeff5Row5Norm,kineticDriftMoment10Coeff6Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff7Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 7 0=c} := by
  have he : kineticDriftCell h kineticCof6 7 0=kineticDriftCell h kineticCof6 7 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment10Coeff5Row0Norm,kineticDriftMoment10Coeff6Row0Norm,kineticDriftMoment10Coeff7Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff7Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 7 1=c} := by
  have he : kineticDriftCell h kineticCof6 7 1=kineticDriftCell h kineticCof6 7 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment10Coeff5Row0Norm,kineticDriftMoment10Coeff5Row1Norm,kineticDriftMoment10Coeff6Row0Norm,kineticDriftMoment10Coeff6Row1Norm,kineticDriftMoment10Coeff7Row0Norm,kineticDriftMoment10Coeff7Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff7Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 7 2=c} := by
  have he : kineticDriftCell h kineticCof6 7 2=kineticDriftCell h kineticCof6 7 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment10Coeff5Row1Norm,kineticDriftMoment10Coeff5Row2Norm,kineticDriftMoment10Coeff6Row1Norm,kineticDriftMoment10Coeff6Row2Norm,kineticDriftMoment10Coeff7Row1Norm,kineticDriftMoment10Coeff7Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff7Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 7 3=c} := by
  have he : kineticDriftCell h kineticCof6 7 3=kineticDriftCell h kineticCof6 7 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment10Coeff5Row2Norm,kineticDriftMoment10Coeff5Row3Norm,kineticDriftMoment10Coeff6Row2Norm,kineticDriftMoment10Coeff6Row3Norm,kineticDriftMoment10Coeff7Row2Norm,kineticDriftMoment10Coeff7Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff7Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 7 4=c} := by
  have he : kineticDriftCell h kineticCof6 7 4=kineticDriftCell h kineticCof6 7 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment10Coeff5Row3Norm,kineticDriftMoment10Coeff5Row4Norm,kineticDriftMoment10Coeff6Row3Norm,kineticDriftMoment10Coeff6Row4Norm,kineticDriftMoment10Coeff7Row3Norm,kineticDriftMoment10Coeff7Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff7Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 7 5=c} := by
  have he : kineticDriftCell h kineticCof6 7 5=kineticDriftCell h kineticCof6 7 5 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment10Coeff5Row4Norm,kineticDriftMoment10Coeff5Row5Norm,kineticDriftMoment10Coeff6Row4Norm,kineticDriftMoment10Coeff6Row5Norm,kineticDriftMoment10Coeff7Row4Norm,kineticDriftMoment10Coeff7Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff7Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 7 6=c} := by
  have he : kineticDriftCell h kineticCof6 7 6=kineticDriftCell h kineticCof6 7 6 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment10Coeff5Row5Norm,kineticDriftMoment10Coeff6Row5Norm,kineticDriftMoment10Coeff7Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff8Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 8 0=c} := by
  have he : kineticDriftCell h kineticCof6 8 0=kineticDriftCell h kineticCof6 8 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment10Coeff6Row0Norm,kineticDriftMoment10Coeff7Row0Norm,kineticDriftMoment10Coeff8Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff8Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 8 1=c} := by
  have he : kineticDriftCell h kineticCof6 8 1=kineticDriftCell h kineticCof6 8 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment10Coeff6Row0Norm,kineticDriftMoment10Coeff6Row1Norm,kineticDriftMoment10Coeff7Row0Norm,kineticDriftMoment10Coeff7Row1Norm,kineticDriftMoment10Coeff8Row0Norm,kineticDriftMoment10Coeff8Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff8Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 8 2=c} := by
  have he : kineticDriftCell h kineticCof6 8 2=kineticDriftCell h kineticCof6 8 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment10Coeff6Row1Norm,kineticDriftMoment10Coeff6Row2Norm,kineticDriftMoment10Coeff7Row1Norm,kineticDriftMoment10Coeff7Row2Norm,kineticDriftMoment10Coeff8Row1Norm,kineticDriftMoment10Coeff8Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff8Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 8 3=c} := by
  have he : kineticDriftCell h kineticCof6 8 3=kineticDriftCell h kineticCof6 8 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment10Coeff6Row2Norm,kineticDriftMoment10Coeff6Row3Norm,kineticDriftMoment10Coeff7Row2Norm,kineticDriftMoment10Coeff7Row3Norm,kineticDriftMoment10Coeff8Row2Norm,kineticDriftMoment10Coeff8Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff8Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 8 4=c} := by
  have he : kineticDriftCell h kineticCof6 8 4=kineticDriftCell h kineticCof6 8 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff6Row3Norm,kineticDriftMoment10Coeff6Row4Norm,kineticDriftMoment10Coeff7Row3Norm,kineticDriftMoment10Coeff7Row4Norm,kineticDriftMoment10Coeff8Row3Norm,kineticDriftMoment10Coeff8Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff8Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 8 5=c} := by
  have he : kineticDriftCell h kineticCof6 8 5=kineticDriftCell h kineticCof6 8 5 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff6Row4Norm,kineticDriftMoment10Coeff6Row5Norm,kineticDriftMoment10Coeff7Row4Norm,kineticDriftMoment10Coeff7Row5Norm,kineticDriftMoment10Coeff8Row4Norm,kineticDriftMoment10Coeff8Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff8Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 8 6=c} := by
  have he : kineticDriftCell h kineticCof6 8 6=kineticDriftCell h kineticCof6 8 6 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff6Row5Norm,kineticDriftMoment10Coeff7Row5Norm,kineticDriftMoment10Coeff8Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff9Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 9 0=c} := by
  have he : kineticDriftCell h kineticCof6 9 0=kineticDriftCell h kineticCof6 9 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment10Coeff7Row0Norm,kineticDriftMoment10Coeff8Row0Norm,kineticDriftMoment10Coeff9Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff9Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 9 1=c} := by
  have he : kineticDriftCell h kineticCof6 9 1=kineticDriftCell h kineticCof6 9 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment10Coeff7Row0Norm,kineticDriftMoment10Coeff7Row1Norm,kineticDriftMoment10Coeff8Row0Norm,kineticDriftMoment10Coeff8Row1Norm,kineticDriftMoment10Coeff9Row0Norm,kineticDriftMoment10Coeff9Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff9Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 9 2=c} := by
  have he : kineticDriftCell h kineticCof6 9 2=kineticDriftCell h kineticCof6 9 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment10Coeff7Row1Norm,kineticDriftMoment10Coeff7Row2Norm,kineticDriftMoment10Coeff8Row1Norm,kineticDriftMoment10Coeff8Row2Norm,kineticDriftMoment10Coeff9Row1Norm,kineticDriftMoment10Coeff9Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff9Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 9 3=c} := by
  have he : kineticDriftCell h kineticCof6 9 3=kineticDriftCell h kineticCof6 9 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment10Coeff7Row2Norm,kineticDriftMoment10Coeff7Row3Norm,kineticDriftMoment10Coeff8Row2Norm,kineticDriftMoment10Coeff8Row3Norm,kineticDriftMoment10Coeff9Row2Norm,kineticDriftMoment10Coeff9Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff9Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 9 4=c} := by
  have he : kineticDriftCell h kineticCof6 9 4=kineticDriftCell h kineticCof6 9 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff7Row3Norm,kineticDriftMoment10Coeff7Row4Norm,kineticDriftMoment10Coeff8Row3Norm,kineticDriftMoment10Coeff8Row4Norm,kineticDriftMoment10Coeff9Row3Norm,kineticDriftMoment10Coeff9Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff9Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 9 5=c} := by
  have he : kineticDriftCell h kineticCof6 9 5=kineticDriftCell h kineticCof6 9 5 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff7Row4Norm,kineticDriftMoment10Coeff7Row5Norm,kineticDriftMoment10Coeff8Row4Norm,kineticDriftMoment10Coeff8Row5Norm,kineticDriftMoment10Coeff9Row4Norm,kineticDriftMoment10Coeff9Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff9Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 9 6=c} := by
  have he : kineticDriftCell h kineticCof6 9 6=kineticDriftCell h kineticCof6 9 6 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff7Row5Norm,kineticDriftMoment10Coeff8Row5Norm,kineticDriftMoment10Coeff9Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff10Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 10 0=c} := by
  have he : kineticDriftCell h kineticCof6 10 0=kineticDriftCell h kineticCof6 10 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment10Coeff8Row0Norm,kineticDriftMoment10Coeff9Row0Norm,kineticDriftMoment10Coeff10Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff10Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 10 1=c} := by
  have he : kineticDriftCell h kineticCof6 10 1=kineticDriftCell h kineticCof6 10 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment10Coeff8Row0Norm,kineticDriftMoment10Coeff8Row1Norm,kineticDriftMoment10Coeff9Row0Norm,kineticDriftMoment10Coeff9Row1Norm,kineticDriftMoment10Coeff10Row0Norm,kineticDriftMoment10Coeff10Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff10Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 10 2=c} := by
  have he : kineticDriftCell h kineticCof6 10 2=kineticDriftCell h kineticCof6 10 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment10Coeff8Row1Norm,kineticDriftMoment10Coeff8Row2Norm,kineticDriftMoment10Coeff9Row1Norm,kineticDriftMoment10Coeff9Row2Norm,kineticDriftMoment10Coeff10Row1Norm,kineticDriftMoment10Coeff10Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff10Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 10 3=c} := by
  have he : kineticDriftCell h kineticCof6 10 3=kineticDriftCell h kineticCof6 10 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment10Coeff8Row2Norm,kineticDriftMoment10Coeff8Row3Norm,kineticDriftMoment10Coeff9Row2Norm,kineticDriftMoment10Coeff9Row3Norm,kineticDriftMoment10Coeff10Row2Norm,kineticDriftMoment10Coeff10Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff10Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 10 4=c} := by
  have he : kineticDriftCell h kineticCof6 10 4=kineticDriftCell h kineticCof6 10 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff8Row3Norm,kineticDriftMoment10Coeff8Row4Norm,kineticDriftMoment10Coeff9Row3Norm,kineticDriftMoment10Coeff9Row4Norm,kineticDriftMoment10Coeff10Row3Norm,kineticDriftMoment10Coeff10Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff10Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 10 5=c} := by
  have he : kineticDriftCell h kineticCof6 10 5=kineticDriftCell h kineticCof6 10 5 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff8Row4Norm,kineticDriftMoment10Coeff8Row5Norm,kineticDriftMoment10Coeff9Row4Norm,kineticDriftMoment10Coeff9Row5Norm,kineticDriftMoment10Coeff10Row4Norm,kineticDriftMoment10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff10Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 10 6=c} := by
  have he : kineticDriftCell h kineticCof6 10 6=kineticDriftCell h kineticCof6 10 6 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff8Row5Norm,kineticDriftMoment10Coeff9Row5Norm,kineticDriftMoment10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff11Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 11 0=c} := by
  have he : kineticDriftCell h kineticCof6 11 0=kineticDriftCell h kineticCof6 11 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment10Coeff9Row0Norm,kineticDriftMoment10Coeff10Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff11Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 11 1=c} := by
  have he : kineticDriftCell h kineticCof6 11 1=kineticDriftCell h kineticCof6 11 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment10Coeff9Row0Norm,kineticDriftMoment10Coeff9Row1Norm,kineticDriftMoment10Coeff10Row0Norm,kineticDriftMoment10Coeff10Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff11Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 11 2=c} := by
  have he : kineticDriftCell h kineticCof6 11 2=kineticDriftCell h kineticCof6 11 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment10Coeff9Row1Norm,kineticDriftMoment10Coeff9Row2Norm,kineticDriftMoment10Coeff10Row1Norm,kineticDriftMoment10Coeff10Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff11Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 11 3=c} := by
  have he : kineticDriftCell h kineticCof6 11 3=kineticDriftCell h kineticCof6 11 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment10Coeff9Row2Norm,kineticDriftMoment10Coeff9Row3Norm,kineticDriftMoment10Coeff10Row2Norm,kineticDriftMoment10Coeff10Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff11Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 11 4=c} := by
  have he : kineticDriftCell h kineticCof6 11 4=kineticDriftCell h kineticCof6 11 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff9Row3Norm,kineticDriftMoment10Coeff9Row4Norm,kineticDriftMoment10Coeff10Row3Norm,kineticDriftMoment10Coeff10Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff11Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 11 5=c} := by
  have he : kineticDriftCell h kineticCof6 11 5=kineticDriftCell h kineticCof6 11 5 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff9Row4Norm,kineticDriftMoment10Coeff9Row5Norm,kineticDriftMoment10Coeff10Row4Norm,kineticDriftMoment10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff11Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 11 6=c} := by
  have he : kineticDriftCell h kineticCof6 11 6=kineticDriftCell h kineticCof6 11 6 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff9Row5Norm,kineticDriftMoment10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff12Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 12 0=c} := by
  have he : kineticDriftCell h kineticCof6 12 0=kineticDriftCell h kineticCof6 12 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment10Coeff10Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff12Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 12 1=c} := by
  have he : kineticDriftCell h kineticCof6 12 1=kineticDriftCell h kineticCof6 12 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment10Coeff10Row0Norm,kineticDriftMoment10Coeff10Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff12Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 12 2=c} := by
  have he : kineticDriftCell h kineticCof6 12 2=kineticDriftCell h kineticCof6 12 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment10Coeff10Row1Norm,kineticDriftMoment10Coeff10Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff12Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 12 3=c} := by
  have he : kineticDriftCell h kineticCof6 12 3=kineticDriftCell h kineticCof6 12 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment10Coeff10Row2Norm,kineticDriftMoment10Coeff10Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff12Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 12 4=c} := by
  have he : kineticDriftCell h kineticCof6 12 4=kineticDriftCell h kineticCof6 12 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff10Row3Norm,kineticDriftMoment10Coeff10Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff12Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 12 5=c} := by
  have he : kineticDriftCell h kineticCof6 12 5=kineticDriftCell h kineticCof6 12 5 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff10Row4Norm,kineticDriftMoment10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof6Coeff12Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof6 12 6=c} := by
  have he : kineticDriftCell h kineticCof6 12 6=kineticDriftCell h kineticCof6 12 6 := rfl
  conv at he =>
    rhs
    rw [kineticCof6_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩


def kineticDriftCof6Row0 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof6Coeff0Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof6Coeff0Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof6Coeff0Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof6Coeff0Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof6Coeff0Row4Norm h).val else 0) + (if b=5 then (kineticDriftCof6Coeff0Row5Norm h).val else 0) + (if b=6 then (kineticDriftCof6Coeff0Row6Norm h).val else 0)

theorem kineticDriftCof6Coeff0_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof6 0 b=kineticDriftCof6Row0 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof6.coeff 0))
    (n := 7) (by have := kineticCof6_drift_degree h 0; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof6.coeff 0)).coeff 0=(kineticDriftCof6Coeff0Row0Norm h).val :=
    (kineticDriftCof6Coeff0Row0Norm h).property
  have h1 : (driftReader h (kineticCof6.coeff 0)).coeff 1=(kineticDriftCof6Coeff0Row1Norm h).val :=
    (kineticDriftCof6Coeff0Row1Norm h).property
  have h2 : (driftReader h (kineticCof6.coeff 0)).coeff 2=(kineticDriftCof6Coeff0Row2Norm h).val :=
    (kineticDriftCof6Coeff0Row2Norm h).property
  have h3 : (driftReader h (kineticCof6.coeff 0)).coeff 3=(kineticDriftCof6Coeff0Row3Norm h).val :=
    (kineticDriftCof6Coeff0Row3Norm h).property
  have h4 : (driftReader h (kineticCof6.coeff 0)).coeff 4=(kineticDriftCof6Coeff0Row4Norm h).val :=
    (kineticDriftCof6Coeff0Row4Norm h).property
  have h5 : (driftReader h (kineticCof6.coeff 0)).coeff 5=(kineticDriftCof6Coeff0Row5Norm h).val :=
    (kineticDriftCof6Coeff0Row5Norm h).property
  have h6 : (driftReader h (kineticCof6.coeff 0)).coeff 6=(kineticDriftCof6Coeff0Row6Norm h).val :=
    (kineticDriftCof6Coeff0Row6Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof6Row0,h0,h1,h2,h3,h4,h5,h6] using he

def kineticDriftCof6Row1 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof6Coeff1Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof6Coeff1Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof6Coeff1Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof6Coeff1Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof6Coeff1Row4Norm h).val else 0) + (if b=5 then (kineticDriftCof6Coeff1Row5Norm h).val else 0) + (if b=6 then (kineticDriftCof6Coeff1Row6Norm h).val else 0)

theorem kineticDriftCof6Coeff1_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof6 1 b=kineticDriftCof6Row1 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof6.coeff 1))
    (n := 7) (by have := kineticCof6_drift_degree h 1; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof6.coeff 1)).coeff 0=(kineticDriftCof6Coeff1Row0Norm h).val :=
    (kineticDriftCof6Coeff1Row0Norm h).property
  have h1 : (driftReader h (kineticCof6.coeff 1)).coeff 1=(kineticDriftCof6Coeff1Row1Norm h).val :=
    (kineticDriftCof6Coeff1Row1Norm h).property
  have h2 : (driftReader h (kineticCof6.coeff 1)).coeff 2=(kineticDriftCof6Coeff1Row2Norm h).val :=
    (kineticDriftCof6Coeff1Row2Norm h).property
  have h3 : (driftReader h (kineticCof6.coeff 1)).coeff 3=(kineticDriftCof6Coeff1Row3Norm h).val :=
    (kineticDriftCof6Coeff1Row3Norm h).property
  have h4 : (driftReader h (kineticCof6.coeff 1)).coeff 4=(kineticDriftCof6Coeff1Row4Norm h).val :=
    (kineticDriftCof6Coeff1Row4Norm h).property
  have h5 : (driftReader h (kineticCof6.coeff 1)).coeff 5=(kineticDriftCof6Coeff1Row5Norm h).val :=
    (kineticDriftCof6Coeff1Row5Norm h).property
  have h6 : (driftReader h (kineticCof6.coeff 1)).coeff 6=(kineticDriftCof6Coeff1Row6Norm h).val :=
    (kineticDriftCof6Coeff1Row6Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof6Row1,h0,h1,h2,h3,h4,h5,h6] using he

def kineticDriftCof6Row2 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof6Coeff2Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof6Coeff2Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof6Coeff2Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof6Coeff2Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof6Coeff2Row4Norm h).val else 0) + (if b=5 then (kineticDriftCof6Coeff2Row5Norm h).val else 0) + (if b=6 then (kineticDriftCof6Coeff2Row6Norm h).val else 0)

theorem kineticDriftCof6Coeff2_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof6 2 b=kineticDriftCof6Row2 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof6.coeff 2))
    (n := 7) (by have := kineticCof6_drift_degree h 2; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof6.coeff 2)).coeff 0=(kineticDriftCof6Coeff2Row0Norm h).val :=
    (kineticDriftCof6Coeff2Row0Norm h).property
  have h1 : (driftReader h (kineticCof6.coeff 2)).coeff 1=(kineticDriftCof6Coeff2Row1Norm h).val :=
    (kineticDriftCof6Coeff2Row1Norm h).property
  have h2 : (driftReader h (kineticCof6.coeff 2)).coeff 2=(kineticDriftCof6Coeff2Row2Norm h).val :=
    (kineticDriftCof6Coeff2Row2Norm h).property
  have h3 : (driftReader h (kineticCof6.coeff 2)).coeff 3=(kineticDriftCof6Coeff2Row3Norm h).val :=
    (kineticDriftCof6Coeff2Row3Norm h).property
  have h4 : (driftReader h (kineticCof6.coeff 2)).coeff 4=(kineticDriftCof6Coeff2Row4Norm h).val :=
    (kineticDriftCof6Coeff2Row4Norm h).property
  have h5 : (driftReader h (kineticCof6.coeff 2)).coeff 5=(kineticDriftCof6Coeff2Row5Norm h).val :=
    (kineticDriftCof6Coeff2Row5Norm h).property
  have h6 : (driftReader h (kineticCof6.coeff 2)).coeff 6=(kineticDriftCof6Coeff2Row6Norm h).val :=
    (kineticDriftCof6Coeff2Row6Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof6Row2,h0,h1,h2,h3,h4,h5,h6] using he

def kineticDriftCof6Row3 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof6Coeff3Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof6Coeff3Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof6Coeff3Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof6Coeff3Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof6Coeff3Row4Norm h).val else 0) + (if b=5 then (kineticDriftCof6Coeff3Row5Norm h).val else 0) + (if b=6 then (kineticDriftCof6Coeff3Row6Norm h).val else 0)

theorem kineticDriftCof6Coeff3_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof6 3 b=kineticDriftCof6Row3 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof6.coeff 3))
    (n := 7) (by have := kineticCof6_drift_degree h 3; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof6.coeff 3)).coeff 0=(kineticDriftCof6Coeff3Row0Norm h).val :=
    (kineticDriftCof6Coeff3Row0Norm h).property
  have h1 : (driftReader h (kineticCof6.coeff 3)).coeff 1=(kineticDriftCof6Coeff3Row1Norm h).val :=
    (kineticDriftCof6Coeff3Row1Norm h).property
  have h2 : (driftReader h (kineticCof6.coeff 3)).coeff 2=(kineticDriftCof6Coeff3Row2Norm h).val :=
    (kineticDriftCof6Coeff3Row2Norm h).property
  have h3 : (driftReader h (kineticCof6.coeff 3)).coeff 3=(kineticDriftCof6Coeff3Row3Norm h).val :=
    (kineticDriftCof6Coeff3Row3Norm h).property
  have h4 : (driftReader h (kineticCof6.coeff 3)).coeff 4=(kineticDriftCof6Coeff3Row4Norm h).val :=
    (kineticDriftCof6Coeff3Row4Norm h).property
  have h5 : (driftReader h (kineticCof6.coeff 3)).coeff 5=(kineticDriftCof6Coeff3Row5Norm h).val :=
    (kineticDriftCof6Coeff3Row5Norm h).property
  have h6 : (driftReader h (kineticCof6.coeff 3)).coeff 6=(kineticDriftCof6Coeff3Row6Norm h).val :=
    (kineticDriftCof6Coeff3Row6Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof6Row3,h0,h1,h2,h3,h4,h5,h6] using he

def kineticDriftCof6Row4 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof6Coeff4Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof6Coeff4Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof6Coeff4Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof6Coeff4Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof6Coeff4Row4Norm h).val else 0) + (if b=5 then (kineticDriftCof6Coeff4Row5Norm h).val else 0) + (if b=6 then (kineticDriftCof6Coeff4Row6Norm h).val else 0)

theorem kineticDriftCof6Coeff4_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof6 4 b=kineticDriftCof6Row4 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof6.coeff 4))
    (n := 7) (by have := kineticCof6_drift_degree h 4; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof6.coeff 4)).coeff 0=(kineticDriftCof6Coeff4Row0Norm h).val :=
    (kineticDriftCof6Coeff4Row0Norm h).property
  have h1 : (driftReader h (kineticCof6.coeff 4)).coeff 1=(kineticDriftCof6Coeff4Row1Norm h).val :=
    (kineticDriftCof6Coeff4Row1Norm h).property
  have h2 : (driftReader h (kineticCof6.coeff 4)).coeff 2=(kineticDriftCof6Coeff4Row2Norm h).val :=
    (kineticDriftCof6Coeff4Row2Norm h).property
  have h3 : (driftReader h (kineticCof6.coeff 4)).coeff 3=(kineticDriftCof6Coeff4Row3Norm h).val :=
    (kineticDriftCof6Coeff4Row3Norm h).property
  have h4 : (driftReader h (kineticCof6.coeff 4)).coeff 4=(kineticDriftCof6Coeff4Row4Norm h).val :=
    (kineticDriftCof6Coeff4Row4Norm h).property
  have h5 : (driftReader h (kineticCof6.coeff 4)).coeff 5=(kineticDriftCof6Coeff4Row5Norm h).val :=
    (kineticDriftCof6Coeff4Row5Norm h).property
  have h6 : (driftReader h (kineticCof6.coeff 4)).coeff 6=(kineticDriftCof6Coeff4Row6Norm h).val :=
    (kineticDriftCof6Coeff4Row6Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof6Row4,h0,h1,h2,h3,h4,h5,h6] using he

def kineticDriftCof6Row5 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof6Coeff5Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof6Coeff5Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof6Coeff5Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof6Coeff5Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof6Coeff5Row4Norm h).val else 0) + (if b=5 then (kineticDriftCof6Coeff5Row5Norm h).val else 0) + (if b=6 then (kineticDriftCof6Coeff5Row6Norm h).val else 0)

theorem kineticDriftCof6Coeff5_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof6 5 b=kineticDriftCof6Row5 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof6.coeff 5))
    (n := 7) (by have := kineticCof6_drift_degree h 5; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof6.coeff 5)).coeff 0=(kineticDriftCof6Coeff5Row0Norm h).val :=
    (kineticDriftCof6Coeff5Row0Norm h).property
  have h1 : (driftReader h (kineticCof6.coeff 5)).coeff 1=(kineticDriftCof6Coeff5Row1Norm h).val :=
    (kineticDriftCof6Coeff5Row1Norm h).property
  have h2 : (driftReader h (kineticCof6.coeff 5)).coeff 2=(kineticDriftCof6Coeff5Row2Norm h).val :=
    (kineticDriftCof6Coeff5Row2Norm h).property
  have h3 : (driftReader h (kineticCof6.coeff 5)).coeff 3=(kineticDriftCof6Coeff5Row3Norm h).val :=
    (kineticDriftCof6Coeff5Row3Norm h).property
  have h4 : (driftReader h (kineticCof6.coeff 5)).coeff 4=(kineticDriftCof6Coeff5Row4Norm h).val :=
    (kineticDriftCof6Coeff5Row4Norm h).property
  have h5 : (driftReader h (kineticCof6.coeff 5)).coeff 5=(kineticDriftCof6Coeff5Row5Norm h).val :=
    (kineticDriftCof6Coeff5Row5Norm h).property
  have h6 : (driftReader h (kineticCof6.coeff 5)).coeff 6=(kineticDriftCof6Coeff5Row6Norm h).val :=
    (kineticDriftCof6Coeff5Row6Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof6Row5,h0,h1,h2,h3,h4,h5,h6] using he

def kineticDriftCof6Row6 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof6Coeff6Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof6Coeff6Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof6Coeff6Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof6Coeff6Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof6Coeff6Row4Norm h).val else 0) + (if b=5 then (kineticDriftCof6Coeff6Row5Norm h).val else 0) + (if b=6 then (kineticDriftCof6Coeff6Row6Norm h).val else 0)

theorem kineticDriftCof6Coeff6_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof6 6 b=kineticDriftCof6Row6 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof6.coeff 6))
    (n := 7) (by have := kineticCof6_drift_degree h 6; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof6.coeff 6)).coeff 0=(kineticDriftCof6Coeff6Row0Norm h).val :=
    (kineticDriftCof6Coeff6Row0Norm h).property
  have h1 : (driftReader h (kineticCof6.coeff 6)).coeff 1=(kineticDriftCof6Coeff6Row1Norm h).val :=
    (kineticDriftCof6Coeff6Row1Norm h).property
  have h2 : (driftReader h (kineticCof6.coeff 6)).coeff 2=(kineticDriftCof6Coeff6Row2Norm h).val :=
    (kineticDriftCof6Coeff6Row2Norm h).property
  have h3 : (driftReader h (kineticCof6.coeff 6)).coeff 3=(kineticDriftCof6Coeff6Row3Norm h).val :=
    (kineticDriftCof6Coeff6Row3Norm h).property
  have h4 : (driftReader h (kineticCof6.coeff 6)).coeff 4=(kineticDriftCof6Coeff6Row4Norm h).val :=
    (kineticDriftCof6Coeff6Row4Norm h).property
  have h5 : (driftReader h (kineticCof6.coeff 6)).coeff 5=(kineticDriftCof6Coeff6Row5Norm h).val :=
    (kineticDriftCof6Coeff6Row5Norm h).property
  have h6 : (driftReader h (kineticCof6.coeff 6)).coeff 6=(kineticDriftCof6Coeff6Row6Norm h).val :=
    (kineticDriftCof6Coeff6Row6Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof6Row6,h0,h1,h2,h3,h4,h5,h6] using he

def kineticDriftCof6Row7 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof6Coeff7Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof6Coeff7Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof6Coeff7Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof6Coeff7Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof6Coeff7Row4Norm h).val else 0) + (if b=5 then (kineticDriftCof6Coeff7Row5Norm h).val else 0) + (if b=6 then (kineticDriftCof6Coeff7Row6Norm h).val else 0)

theorem kineticDriftCof6Coeff7_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof6 7 b=kineticDriftCof6Row7 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof6.coeff 7))
    (n := 7) (by have := kineticCof6_drift_degree h 7; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof6.coeff 7)).coeff 0=(kineticDriftCof6Coeff7Row0Norm h).val :=
    (kineticDriftCof6Coeff7Row0Norm h).property
  have h1 : (driftReader h (kineticCof6.coeff 7)).coeff 1=(kineticDriftCof6Coeff7Row1Norm h).val :=
    (kineticDriftCof6Coeff7Row1Norm h).property
  have h2 : (driftReader h (kineticCof6.coeff 7)).coeff 2=(kineticDriftCof6Coeff7Row2Norm h).val :=
    (kineticDriftCof6Coeff7Row2Norm h).property
  have h3 : (driftReader h (kineticCof6.coeff 7)).coeff 3=(kineticDriftCof6Coeff7Row3Norm h).val :=
    (kineticDriftCof6Coeff7Row3Norm h).property
  have h4 : (driftReader h (kineticCof6.coeff 7)).coeff 4=(kineticDriftCof6Coeff7Row4Norm h).val :=
    (kineticDriftCof6Coeff7Row4Norm h).property
  have h5 : (driftReader h (kineticCof6.coeff 7)).coeff 5=(kineticDriftCof6Coeff7Row5Norm h).val :=
    (kineticDriftCof6Coeff7Row5Norm h).property
  have h6 : (driftReader h (kineticCof6.coeff 7)).coeff 6=(kineticDriftCof6Coeff7Row6Norm h).val :=
    (kineticDriftCof6Coeff7Row6Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof6Row7,h0,h1,h2,h3,h4,h5,h6] using he

def kineticDriftCof6Row8 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof6Coeff8Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof6Coeff8Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof6Coeff8Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof6Coeff8Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof6Coeff8Row4Norm h).val else 0) + (if b=5 then (kineticDriftCof6Coeff8Row5Norm h).val else 0) + (if b=6 then (kineticDriftCof6Coeff8Row6Norm h).val else 0)

theorem kineticDriftCof6Coeff8_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof6 8 b=kineticDriftCof6Row8 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof6.coeff 8))
    (n := 7) (by have := kineticCof6_drift_degree h 8; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof6.coeff 8)).coeff 0=(kineticDriftCof6Coeff8Row0Norm h).val :=
    (kineticDriftCof6Coeff8Row0Norm h).property
  have h1 : (driftReader h (kineticCof6.coeff 8)).coeff 1=(kineticDriftCof6Coeff8Row1Norm h).val :=
    (kineticDriftCof6Coeff8Row1Norm h).property
  have h2 : (driftReader h (kineticCof6.coeff 8)).coeff 2=(kineticDriftCof6Coeff8Row2Norm h).val :=
    (kineticDriftCof6Coeff8Row2Norm h).property
  have h3 : (driftReader h (kineticCof6.coeff 8)).coeff 3=(kineticDriftCof6Coeff8Row3Norm h).val :=
    (kineticDriftCof6Coeff8Row3Norm h).property
  have h4 : (driftReader h (kineticCof6.coeff 8)).coeff 4=(kineticDriftCof6Coeff8Row4Norm h).val :=
    (kineticDriftCof6Coeff8Row4Norm h).property
  have h5 : (driftReader h (kineticCof6.coeff 8)).coeff 5=(kineticDriftCof6Coeff8Row5Norm h).val :=
    (kineticDriftCof6Coeff8Row5Norm h).property
  have h6 : (driftReader h (kineticCof6.coeff 8)).coeff 6=(kineticDriftCof6Coeff8Row6Norm h).val :=
    (kineticDriftCof6Coeff8Row6Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof6Row8,h0,h1,h2,h3,h4,h5,h6] using he

def kineticDriftCof6Row9 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof6Coeff9Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof6Coeff9Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof6Coeff9Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof6Coeff9Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof6Coeff9Row4Norm h).val else 0) + (if b=5 then (kineticDriftCof6Coeff9Row5Norm h).val else 0) + (if b=6 then (kineticDriftCof6Coeff9Row6Norm h).val else 0)

theorem kineticDriftCof6Coeff9_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof6 9 b=kineticDriftCof6Row9 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof6.coeff 9))
    (n := 7) (by have := kineticCof6_drift_degree h 9; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof6.coeff 9)).coeff 0=(kineticDriftCof6Coeff9Row0Norm h).val :=
    (kineticDriftCof6Coeff9Row0Norm h).property
  have h1 : (driftReader h (kineticCof6.coeff 9)).coeff 1=(kineticDriftCof6Coeff9Row1Norm h).val :=
    (kineticDriftCof6Coeff9Row1Norm h).property
  have h2 : (driftReader h (kineticCof6.coeff 9)).coeff 2=(kineticDriftCof6Coeff9Row2Norm h).val :=
    (kineticDriftCof6Coeff9Row2Norm h).property
  have h3 : (driftReader h (kineticCof6.coeff 9)).coeff 3=(kineticDriftCof6Coeff9Row3Norm h).val :=
    (kineticDriftCof6Coeff9Row3Norm h).property
  have h4 : (driftReader h (kineticCof6.coeff 9)).coeff 4=(kineticDriftCof6Coeff9Row4Norm h).val :=
    (kineticDriftCof6Coeff9Row4Norm h).property
  have h5 : (driftReader h (kineticCof6.coeff 9)).coeff 5=(kineticDriftCof6Coeff9Row5Norm h).val :=
    (kineticDriftCof6Coeff9Row5Norm h).property
  have h6 : (driftReader h (kineticCof6.coeff 9)).coeff 6=(kineticDriftCof6Coeff9Row6Norm h).val :=
    (kineticDriftCof6Coeff9Row6Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof6Row9,h0,h1,h2,h3,h4,h5,h6] using he

def kineticDriftCof6Row10 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof6Coeff10Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof6Coeff10Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof6Coeff10Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof6Coeff10Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof6Coeff10Row4Norm h).val else 0) + (if b=5 then (kineticDriftCof6Coeff10Row5Norm h).val else 0) + (if b=6 then (kineticDriftCof6Coeff10Row6Norm h).val else 0)

theorem kineticDriftCof6Coeff10_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof6 10 b=kineticDriftCof6Row10 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof6.coeff 10))
    (n := 7) (by have := kineticCof6_drift_degree h 10; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof6.coeff 10)).coeff 0=(kineticDriftCof6Coeff10Row0Norm h).val :=
    (kineticDriftCof6Coeff10Row0Norm h).property
  have h1 : (driftReader h (kineticCof6.coeff 10)).coeff 1=(kineticDriftCof6Coeff10Row1Norm h).val :=
    (kineticDriftCof6Coeff10Row1Norm h).property
  have h2 : (driftReader h (kineticCof6.coeff 10)).coeff 2=(kineticDriftCof6Coeff10Row2Norm h).val :=
    (kineticDriftCof6Coeff10Row2Norm h).property
  have h3 : (driftReader h (kineticCof6.coeff 10)).coeff 3=(kineticDriftCof6Coeff10Row3Norm h).val :=
    (kineticDriftCof6Coeff10Row3Norm h).property
  have h4 : (driftReader h (kineticCof6.coeff 10)).coeff 4=(kineticDriftCof6Coeff10Row4Norm h).val :=
    (kineticDriftCof6Coeff10Row4Norm h).property
  have h5 : (driftReader h (kineticCof6.coeff 10)).coeff 5=(kineticDriftCof6Coeff10Row5Norm h).val :=
    (kineticDriftCof6Coeff10Row5Norm h).property
  have h6 : (driftReader h (kineticCof6.coeff 10)).coeff 6=(kineticDriftCof6Coeff10Row6Norm h).val :=
    (kineticDriftCof6Coeff10Row6Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof6Row10,h0,h1,h2,h3,h4,h5,h6] using he

def kineticDriftCof6Row11 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof6Coeff11Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof6Coeff11Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof6Coeff11Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof6Coeff11Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof6Coeff11Row4Norm h).val else 0) + (if b=5 then (kineticDriftCof6Coeff11Row5Norm h).val else 0) + (if b=6 then (kineticDriftCof6Coeff11Row6Norm h).val else 0)

theorem kineticDriftCof6Coeff11_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof6 11 b=kineticDriftCof6Row11 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof6.coeff 11))
    (n := 7) (by have := kineticCof6_drift_degree h 11; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof6.coeff 11)).coeff 0=(kineticDriftCof6Coeff11Row0Norm h).val :=
    (kineticDriftCof6Coeff11Row0Norm h).property
  have h1 : (driftReader h (kineticCof6.coeff 11)).coeff 1=(kineticDriftCof6Coeff11Row1Norm h).val :=
    (kineticDriftCof6Coeff11Row1Norm h).property
  have h2 : (driftReader h (kineticCof6.coeff 11)).coeff 2=(kineticDriftCof6Coeff11Row2Norm h).val :=
    (kineticDriftCof6Coeff11Row2Norm h).property
  have h3 : (driftReader h (kineticCof6.coeff 11)).coeff 3=(kineticDriftCof6Coeff11Row3Norm h).val :=
    (kineticDriftCof6Coeff11Row3Norm h).property
  have h4 : (driftReader h (kineticCof6.coeff 11)).coeff 4=(kineticDriftCof6Coeff11Row4Norm h).val :=
    (kineticDriftCof6Coeff11Row4Norm h).property
  have h5 : (driftReader h (kineticCof6.coeff 11)).coeff 5=(kineticDriftCof6Coeff11Row5Norm h).val :=
    (kineticDriftCof6Coeff11Row5Norm h).property
  have h6 : (driftReader h (kineticCof6.coeff 11)).coeff 6=(kineticDriftCof6Coeff11Row6Norm h).val :=
    (kineticDriftCof6Coeff11Row6Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof6Row11,h0,h1,h2,h3,h4,h5,h6] using he

def kineticDriftCof6Row12 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof6Coeff12Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof6Coeff12Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof6Coeff12Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof6Coeff12Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof6Coeff12Row4Norm h).val else 0) + (if b=5 then (kineticDriftCof6Coeff12Row5Norm h).val else 0) + (if b=6 then (kineticDriftCof6Coeff12Row6Norm h).val else 0)

theorem kineticDriftCof6Coeff12_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof6 12 b=kineticDriftCof6Row12 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof6.coeff 12))
    (n := 7) (by have := kineticCof6_drift_degree h 12; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof6.coeff 12)).coeff 0=(kineticDriftCof6Coeff12Row0Norm h).val :=
    (kineticDriftCof6Coeff12Row0Norm h).property
  have h1 : (driftReader h (kineticCof6.coeff 12)).coeff 1=(kineticDriftCof6Coeff12Row1Norm h).val :=
    (kineticDriftCof6Coeff12Row1Norm h).property
  have h2 : (driftReader h (kineticCof6.coeff 12)).coeff 2=(kineticDriftCof6Coeff12Row2Norm h).val :=
    (kineticDriftCof6Coeff12Row2Norm h).property
  have h3 : (driftReader h (kineticCof6.coeff 12)).coeff 3=(kineticDriftCof6Coeff12Row3Norm h).val :=
    (kineticDriftCof6Coeff12Row3Norm h).property
  have h4 : (driftReader h (kineticCof6.coeff 12)).coeff 4=(kineticDriftCof6Coeff12Row4Norm h).val :=
    (kineticDriftCof6Coeff12Row4Norm h).property
  have h5 : (driftReader h (kineticCof6.coeff 12)).coeff 5=(kineticDriftCof6Coeff12Row5Norm h).val :=
    (kineticDriftCof6Coeff12Row5Norm h).property
  have h6 : (driftReader h (kineticCof6.coeff 12)).coeff 6=(kineticDriftCof6Coeff12Row6Norm h).val :=
    (kineticDriftCof6Coeff12Row6Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof6Row12,h0,h1,h2,h3,h4,h5,h6] using he

theorem kineticDriftCof6_rows (h : ℂ) (j b : ℕ) :
    kineticDriftCell h kineticCof6 j b=(if j=0 then kineticDriftCof6Row0 h b else 0) + (if j=1 then kineticDriftCof6Row1 h b else 0) + (if j=2 then kineticDriftCof6Row2 h b else 0) + (if j=3 then kineticDriftCof6Row3 h b else 0) + (if j=4 then kineticDriftCof6Row4 h b else 0) + (if j=5 then kineticDriftCof6Row5 h b else 0) + (if j=6 then kineticDriftCof6Row6 h b else 0) + (if j=7 then kineticDriftCof6Row7 h b else 0) + (if j=8 then kineticDriftCof6Row8 h b else 0) + (if j=9 then kineticDriftCof6Row9 h b else 0) + (if j=10 then kineticDriftCof6Row10 h b else 0) + (if j=11 then kineticDriftCof6Row11 h b else 0) + (if j=12 then kineticDriftCof6Row12 h b else 0) := by
  by_cases hj : j≤12
  · interval_cases j
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof6Coeff0_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof6Coeff1_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof6Coeff2_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof6Coeff3_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof6Coeff4_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof6Coeff5_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof6Coeff6_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof6Coeff7_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof6Coeff8_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof6Coeff9_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof6Coeff10_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof6Coeff11_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof6Coeff12_rows h b
  · have hp : kineticCof6.coeff j=0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (kineticCof6_degree.trans_lt (by omega))
    simp only [kineticDriftCell,hp,map_zero,Polynomial.coeff_zero,if_neg (show j≠0 by omega),if_neg (show j≠1 by omega),if_neg (show j≠2 by omega),if_neg (show j≠3 by omega),if_neg (show j≠4 by omega),if_neg (show j≠5 by omega),if_neg (show j≠6 by omega),if_neg (show j≠7 by omega),if_neg (show j≠8 by omega),if_neg (show j≠9 by omega),if_neg (show j≠10 by omega),if_neg (show j≠11 by omega),if_neg (show j≠12 by omega),zero_add]

end
end HTGeometry.ThetaRatioKineticContraction
