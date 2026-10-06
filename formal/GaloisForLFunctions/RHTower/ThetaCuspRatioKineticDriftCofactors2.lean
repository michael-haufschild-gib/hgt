import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticDriftSupport
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def kineticDriftCof2Coeff0Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 0 0=c} := by
  have he : kineticDriftCell h kineticCof2 0 0=kineticDriftCell h kineticCof2 0 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment10Coeff0Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff0Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 0 1=c} := by
  have he : kineticDriftCell h kineticCof2 0 1=kineticDriftCell h kineticCof2 0 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment10Coeff0Row0Norm,kineticDriftMoment10Coeff0Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff0Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 0 2=c} := by
  have he : kineticDriftCell h kineticCof2 0 2=kineticDriftCell h kineticCof2 0 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment10Coeff0Row0Norm,kineticDriftMoment10Coeff0Row1Norm,kineticDriftMoment10Coeff0Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff0Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 0 3=c} := by
  have he : kineticDriftCell h kineticCof2 0 3=kineticDriftCell h kineticCof2 0 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment10Coeff0Row0Norm,kineticDriftMoment10Coeff0Row1Norm,kineticDriftMoment10Coeff0Row2Norm,kineticDriftMoment10Coeff0Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff0Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 0 4=c} := by
  have he : kineticDriftCell h kineticCof2 0 4=kineticDriftCell h kineticCof2 0 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment10Coeff0Row1Norm,kineticDriftMoment10Coeff0Row2Norm,kineticDriftMoment10Coeff0Row3Norm,kineticDriftMoment10Coeff0Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff0Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 0 5=c} := by
  have he : kineticDriftCell h kineticCof2 0 5=kineticDriftCell h kineticCof2 0 5 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment10Coeff0Row2Norm,kineticDriftMoment10Coeff0Row3Norm,kineticDriftMoment10Coeff0Row4Norm,kineticDriftMoment10Coeff0Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff0Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 0 6=c} := by
  have he : kineticDriftCell h kineticCof2 0 6=kineticDriftCell h kineticCof2 0 6 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment10Coeff0Row3Norm,kineticDriftMoment10Coeff0Row4Norm,kineticDriftMoment10Coeff0Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff0Row7Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 0 7=c} := by
  have he : kineticDriftCell h kineticCof2 0 7=kineticDriftCell h kineticCof2 0 7 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment10Coeff0Row4Norm,kineticDriftMoment10Coeff0Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff0Row8Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 0 8=c} := by
  have he : kineticDriftCell h kineticCof2 0 8=kineticDriftCell h kineticCof2 0 8 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment10Coeff0Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff1Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 1 0=c} := by
  have he : kineticDriftCell h kineticCof2 1 0=kineticDriftCell h kineticCof2 1 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment10Coeff0Row0Norm,kineticDriftMoment10Coeff1Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff1Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 1 1=c} := by
  have he : kineticDriftCell h kineticCof2 1 1=kineticDriftCell h kineticCof2 1 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment10Coeff0Row0Norm,kineticDriftMoment10Coeff0Row1Norm,kineticDriftMoment10Coeff1Row0Norm,kineticDriftMoment10Coeff1Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff1Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 1 2=c} := by
  have he : kineticDriftCell h kineticCof2 1 2=kineticDriftCell h kineticCof2 1 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment10Coeff0Row0Norm,kineticDriftMoment10Coeff0Row1Norm,kineticDriftMoment10Coeff0Row2Norm,kineticDriftMoment10Coeff1Row0Norm,kineticDriftMoment10Coeff1Row1Norm,kineticDriftMoment10Coeff1Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff1Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 1 3=c} := by
  have he : kineticDriftCell h kineticCof2 1 3=kineticDriftCell h kineticCof2 1 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment10Coeff0Row0Norm,kineticDriftMoment10Coeff0Row1Norm,kineticDriftMoment10Coeff0Row2Norm,kineticDriftMoment10Coeff0Row3Norm,kineticDriftMoment10Coeff1Row0Norm,kineticDriftMoment10Coeff1Row1Norm,kineticDriftMoment10Coeff1Row2Norm,kineticDriftMoment10Coeff1Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff1Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 1 4=c} := by
  have he : kineticDriftCell h kineticCof2 1 4=kineticDriftCell h kineticCof2 1 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment10Coeff0Row1Norm,kineticDriftMoment10Coeff0Row2Norm,kineticDriftMoment10Coeff0Row3Norm,kineticDriftMoment10Coeff0Row4Norm,kineticDriftMoment10Coeff1Row1Norm,kineticDriftMoment10Coeff1Row2Norm,kineticDriftMoment10Coeff1Row3Norm,kineticDriftMoment10Coeff1Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff1Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 1 5=c} := by
  have he : kineticDriftCell h kineticCof2 1 5=kineticDriftCell h kineticCof2 1 5 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment10Coeff0Row2Norm,kineticDriftMoment10Coeff0Row3Norm,kineticDriftMoment10Coeff0Row4Norm,kineticDriftMoment10Coeff0Row5Norm,kineticDriftMoment10Coeff1Row2Norm,kineticDriftMoment10Coeff1Row3Norm,kineticDriftMoment10Coeff1Row4Norm,kineticDriftMoment10Coeff1Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff1Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 1 6=c} := by
  have he : kineticDriftCell h kineticCof2 1 6=kineticDriftCell h kineticCof2 1 6 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment10Coeff0Row3Norm,kineticDriftMoment10Coeff0Row4Norm,kineticDriftMoment10Coeff0Row5Norm,kineticDriftMoment10Coeff1Row3Norm,kineticDriftMoment10Coeff1Row4Norm,kineticDriftMoment10Coeff1Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff1Row7Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 1 7=c} := by
  have he : kineticDriftCell h kineticCof2 1 7=kineticDriftCell h kineticCof2 1 7 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment10Coeff0Row4Norm,kineticDriftMoment10Coeff0Row5Norm,kineticDriftMoment10Coeff1Row4Norm,kineticDriftMoment10Coeff1Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff1Row8Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 1 8=c} := by
  have he : kineticDriftCell h kineticCof2 1 8=kineticDriftCell h kineticCof2 1 8 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment10Coeff0Row5Norm,kineticDriftMoment10Coeff1Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff2Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 2 0=c} := by
  have he : kineticDriftCell h kineticCof2 2 0=kineticDriftCell h kineticCof2 2 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment10Coeff0Row0Norm,kineticDriftMoment10Coeff1Row0Norm,kineticDriftMoment10Coeff2Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff2Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 2 1=c} := by
  have he : kineticDriftCell h kineticCof2 2 1=kineticDriftCell h kineticCof2 2 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment10Coeff0Row0Norm,kineticDriftMoment10Coeff0Row1Norm,kineticDriftMoment10Coeff1Row0Norm,kineticDriftMoment10Coeff1Row1Norm,kineticDriftMoment10Coeff2Row0Norm,kineticDriftMoment10Coeff2Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff2Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 2 2=c} := by
  have he : kineticDriftCell h kineticCof2 2 2=kineticDriftCell h kineticCof2 2 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment10Coeff0Row0Norm,kineticDriftMoment10Coeff0Row1Norm,kineticDriftMoment10Coeff0Row2Norm,kineticDriftMoment10Coeff1Row0Norm,kineticDriftMoment10Coeff1Row1Norm,kineticDriftMoment10Coeff1Row2Norm,kineticDriftMoment10Coeff2Row0Norm,kineticDriftMoment10Coeff2Row1Norm,kineticDriftMoment10Coeff2Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff2Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 2 3=c} := by
  have he : kineticDriftCell h kineticCof2 2 3=kineticDriftCell h kineticCof2 2 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment10Coeff0Row0Norm,kineticDriftMoment10Coeff0Row1Norm,kineticDriftMoment10Coeff0Row2Norm,kineticDriftMoment10Coeff0Row3Norm,kineticDriftMoment10Coeff1Row0Norm,kineticDriftMoment10Coeff1Row1Norm,kineticDriftMoment10Coeff1Row2Norm,kineticDriftMoment10Coeff1Row3Norm,kineticDriftMoment10Coeff2Row0Norm,kineticDriftMoment10Coeff2Row1Norm,kineticDriftMoment10Coeff2Row2Norm,kineticDriftMoment10Coeff2Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff2Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 2 4=c} := by
  have he : kineticDriftCell h kineticCof2 2 4=kineticDriftCell h kineticCof2 2 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment10Coeff0Row1Norm,kineticDriftMoment10Coeff0Row2Norm,kineticDriftMoment10Coeff0Row3Norm,kineticDriftMoment10Coeff0Row4Norm,kineticDriftMoment10Coeff1Row1Norm,kineticDriftMoment10Coeff1Row2Norm,kineticDriftMoment10Coeff1Row3Norm,kineticDriftMoment10Coeff1Row4Norm,kineticDriftMoment10Coeff2Row1Norm,kineticDriftMoment10Coeff2Row2Norm,kineticDriftMoment10Coeff2Row3Norm,kineticDriftMoment10Coeff2Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff2Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 2 5=c} := by
  have he : kineticDriftCell h kineticCof2 2 5=kineticDriftCell h kineticCof2 2 5 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment10Coeff0Row2Norm,kineticDriftMoment10Coeff0Row3Norm,kineticDriftMoment10Coeff0Row4Norm,kineticDriftMoment10Coeff0Row5Norm,kineticDriftMoment10Coeff1Row2Norm,kineticDriftMoment10Coeff1Row3Norm,kineticDriftMoment10Coeff1Row4Norm,kineticDriftMoment10Coeff1Row5Norm,kineticDriftMoment10Coeff2Row2Norm,kineticDriftMoment10Coeff2Row3Norm,kineticDriftMoment10Coeff2Row4Norm,kineticDriftMoment10Coeff2Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff2Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 2 6=c} := by
  have he : kineticDriftCell h kineticCof2 2 6=kineticDriftCell h kineticCof2 2 6 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment10Coeff0Row3Norm,kineticDriftMoment10Coeff0Row4Norm,kineticDriftMoment10Coeff0Row5Norm,kineticDriftMoment10Coeff1Row3Norm,kineticDriftMoment10Coeff1Row4Norm,kineticDriftMoment10Coeff1Row5Norm,kineticDriftMoment10Coeff2Row3Norm,kineticDriftMoment10Coeff2Row4Norm,kineticDriftMoment10Coeff2Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff2Row7Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 2 7=c} := by
  have he : kineticDriftCell h kineticCof2 2 7=kineticDriftCell h kineticCof2 2 7 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment10Coeff0Row4Norm,kineticDriftMoment10Coeff0Row5Norm,kineticDriftMoment10Coeff1Row4Norm,kineticDriftMoment10Coeff1Row5Norm,kineticDriftMoment10Coeff2Row4Norm,kineticDriftMoment10Coeff2Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff2Row8Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 2 8=c} := by
  have he : kineticDriftCell h kineticCof2 2 8=kineticDriftCell h kineticCof2 2 8 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment10Coeff0Row5Norm,kineticDriftMoment10Coeff1Row5Norm,kineticDriftMoment10Coeff2Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff3Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 3 0=c} := by
  have he : kineticDriftCell h kineticCof2 3 0=kineticDriftCell h kineticCof2 3 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment10Coeff0Row0Norm,kineticDriftMoment10Coeff1Row0Norm,kineticDriftMoment10Coeff2Row0Norm,kineticDriftMoment10Coeff3Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff3Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 3 1=c} := by
  have he : kineticDriftCell h kineticCof2 3 1=kineticDriftCell h kineticCof2 3 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment10Coeff0Row0Norm,kineticDriftMoment10Coeff0Row1Norm,kineticDriftMoment10Coeff1Row0Norm,kineticDriftMoment10Coeff1Row1Norm,kineticDriftMoment10Coeff2Row0Norm,kineticDriftMoment10Coeff2Row1Norm,kineticDriftMoment10Coeff3Row0Norm,kineticDriftMoment10Coeff3Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff3Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 3 2=c} := by
  have he : kineticDriftCell h kineticCof2 3 2=kineticDriftCell h kineticCof2 3 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment10Coeff0Row0Norm,kineticDriftMoment10Coeff0Row1Norm,kineticDriftMoment10Coeff0Row2Norm,kineticDriftMoment10Coeff1Row0Norm,kineticDriftMoment10Coeff1Row1Norm,kineticDriftMoment10Coeff1Row2Norm,kineticDriftMoment10Coeff2Row0Norm,kineticDriftMoment10Coeff2Row1Norm,kineticDriftMoment10Coeff2Row2Norm,kineticDriftMoment10Coeff3Row0Norm,kineticDriftMoment10Coeff3Row1Norm,kineticDriftMoment10Coeff3Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff3Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 3 3=c} := by
  have he : kineticDriftCell h kineticCof2 3 3=kineticDriftCell h kineticCof2 3 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment10Coeff0Row0Norm,kineticDriftMoment10Coeff0Row1Norm,kineticDriftMoment10Coeff0Row2Norm,kineticDriftMoment10Coeff0Row3Norm,kineticDriftMoment10Coeff1Row0Norm,kineticDriftMoment10Coeff1Row1Norm,kineticDriftMoment10Coeff1Row2Norm,kineticDriftMoment10Coeff1Row3Norm,kineticDriftMoment10Coeff2Row0Norm,kineticDriftMoment10Coeff2Row1Norm,kineticDriftMoment10Coeff2Row2Norm,kineticDriftMoment10Coeff2Row3Norm,kineticDriftMoment10Coeff3Row0Norm,kineticDriftMoment10Coeff3Row1Norm,kineticDriftMoment10Coeff3Row2Norm,kineticDriftMoment10Coeff3Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff3Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 3 4=c} := by
  have he : kineticDriftCell h kineticCof2 3 4=kineticDriftCell h kineticCof2 3 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment10Coeff0Row1Norm,kineticDriftMoment10Coeff0Row2Norm,kineticDriftMoment10Coeff0Row3Norm,kineticDriftMoment10Coeff0Row4Norm,kineticDriftMoment10Coeff1Row1Norm,kineticDriftMoment10Coeff1Row2Norm,kineticDriftMoment10Coeff1Row3Norm,kineticDriftMoment10Coeff1Row4Norm,kineticDriftMoment10Coeff2Row1Norm,kineticDriftMoment10Coeff2Row2Norm,kineticDriftMoment10Coeff2Row3Norm,kineticDriftMoment10Coeff2Row4Norm,kineticDriftMoment10Coeff3Row1Norm,kineticDriftMoment10Coeff3Row2Norm,kineticDriftMoment10Coeff3Row3Norm,kineticDriftMoment10Coeff3Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff3Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 3 5=c} := by
  have he : kineticDriftCell h kineticCof2 3 5=kineticDriftCell h kineticCof2 3 5 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment10Coeff0Row2Norm,kineticDriftMoment10Coeff0Row3Norm,kineticDriftMoment10Coeff0Row4Norm,kineticDriftMoment10Coeff0Row5Norm,kineticDriftMoment10Coeff1Row2Norm,kineticDriftMoment10Coeff1Row3Norm,kineticDriftMoment10Coeff1Row4Norm,kineticDriftMoment10Coeff1Row5Norm,kineticDriftMoment10Coeff2Row2Norm,kineticDriftMoment10Coeff2Row3Norm,kineticDriftMoment10Coeff2Row4Norm,kineticDriftMoment10Coeff2Row5Norm,kineticDriftMoment10Coeff3Row2Norm,kineticDriftMoment10Coeff3Row3Norm,kineticDriftMoment10Coeff3Row4Norm,kineticDriftMoment10Coeff3Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff3Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 3 6=c} := by
  have he : kineticDriftCell h kineticCof2 3 6=kineticDriftCell h kineticCof2 3 6 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment10Coeff0Row3Norm,kineticDriftMoment10Coeff0Row4Norm,kineticDriftMoment10Coeff0Row5Norm,kineticDriftMoment10Coeff1Row3Norm,kineticDriftMoment10Coeff1Row4Norm,kineticDriftMoment10Coeff1Row5Norm,kineticDriftMoment10Coeff2Row3Norm,kineticDriftMoment10Coeff2Row4Norm,kineticDriftMoment10Coeff2Row5Norm,kineticDriftMoment10Coeff3Row3Norm,kineticDriftMoment10Coeff3Row4Norm,kineticDriftMoment10Coeff3Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff3Row7Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 3 7=c} := by
  have he : kineticDriftCell h kineticCof2 3 7=kineticDriftCell h kineticCof2 3 7 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment10Coeff0Row4Norm,kineticDriftMoment10Coeff0Row5Norm,kineticDriftMoment10Coeff1Row4Norm,kineticDriftMoment10Coeff1Row5Norm,kineticDriftMoment10Coeff2Row4Norm,kineticDriftMoment10Coeff2Row5Norm,kineticDriftMoment10Coeff3Row4Norm,kineticDriftMoment10Coeff3Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff3Row8Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 3 8=c} := by
  have he : kineticDriftCell h kineticCof2 3 8=kineticDriftCell h kineticCof2 3 8 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment10Coeff0Row5Norm,kineticDriftMoment10Coeff1Row5Norm,kineticDriftMoment10Coeff2Row5Norm,kineticDriftMoment10Coeff3Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff4Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 4 0=c} := by
  have he : kineticDriftCell h kineticCof2 4 0=kineticDriftCell h kineticCof2 4 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment10Coeff0Row0Norm,kineticDriftMoment10Coeff1Row0Norm,kineticDriftMoment10Coeff2Row0Norm,kineticDriftMoment10Coeff3Row0Norm,kineticDriftMoment10Coeff4Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff4Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 4 1=c} := by
  have he : kineticDriftCell h kineticCof2 4 1=kineticDriftCell h kineticCof2 4 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment10Coeff0Row0Norm,kineticDriftMoment10Coeff0Row1Norm,kineticDriftMoment10Coeff1Row0Norm,kineticDriftMoment10Coeff1Row1Norm,kineticDriftMoment10Coeff2Row0Norm,kineticDriftMoment10Coeff2Row1Norm,kineticDriftMoment10Coeff3Row0Norm,kineticDriftMoment10Coeff3Row1Norm,kineticDriftMoment10Coeff4Row0Norm,kineticDriftMoment10Coeff4Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff4Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 4 2=c} := by
  have he : kineticDriftCell h kineticCof2 4 2=kineticDriftCell h kineticCof2 4 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment10Coeff0Row0Norm,kineticDriftMoment10Coeff0Row1Norm,kineticDriftMoment10Coeff0Row2Norm,kineticDriftMoment10Coeff1Row0Norm,kineticDriftMoment10Coeff1Row1Norm,kineticDriftMoment10Coeff1Row2Norm,kineticDriftMoment10Coeff2Row0Norm,kineticDriftMoment10Coeff2Row1Norm,kineticDriftMoment10Coeff2Row2Norm,kineticDriftMoment10Coeff3Row0Norm,kineticDriftMoment10Coeff3Row1Norm,kineticDriftMoment10Coeff3Row2Norm,kineticDriftMoment10Coeff4Row0Norm,kineticDriftMoment10Coeff4Row1Norm,kineticDriftMoment10Coeff4Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff4Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 4 3=c} := by
  have he : kineticDriftCell h kineticCof2 4 3=kineticDriftCell h kineticCof2 4 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment10Coeff0Row0Norm,kineticDriftMoment10Coeff0Row1Norm,kineticDriftMoment10Coeff0Row2Norm,kineticDriftMoment10Coeff0Row3Norm,kineticDriftMoment10Coeff1Row0Norm,kineticDriftMoment10Coeff1Row1Norm,kineticDriftMoment10Coeff1Row2Norm,kineticDriftMoment10Coeff1Row3Norm,kineticDriftMoment10Coeff2Row0Norm,kineticDriftMoment10Coeff2Row1Norm,kineticDriftMoment10Coeff2Row2Norm,kineticDriftMoment10Coeff2Row3Norm,kineticDriftMoment10Coeff3Row0Norm,kineticDriftMoment10Coeff3Row1Norm,kineticDriftMoment10Coeff3Row2Norm,kineticDriftMoment10Coeff3Row3Norm,kineticDriftMoment10Coeff4Row0Norm,kineticDriftMoment10Coeff4Row1Norm,kineticDriftMoment10Coeff4Row2Norm,kineticDriftMoment10Coeff4Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff4Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 4 4=c} := by
  have he : kineticDriftCell h kineticCof2 4 4=kineticDriftCell h kineticCof2 4 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment10Coeff0Row1Norm,kineticDriftMoment10Coeff0Row2Norm,kineticDriftMoment10Coeff0Row3Norm,kineticDriftMoment10Coeff0Row4Norm,kineticDriftMoment10Coeff1Row1Norm,kineticDriftMoment10Coeff1Row2Norm,kineticDriftMoment10Coeff1Row3Norm,kineticDriftMoment10Coeff1Row4Norm,kineticDriftMoment10Coeff2Row1Norm,kineticDriftMoment10Coeff2Row2Norm,kineticDriftMoment10Coeff2Row3Norm,kineticDriftMoment10Coeff2Row4Norm,kineticDriftMoment10Coeff3Row1Norm,kineticDriftMoment10Coeff3Row2Norm,kineticDriftMoment10Coeff3Row3Norm,kineticDriftMoment10Coeff3Row4Norm,kineticDriftMoment10Coeff4Row1Norm,kineticDriftMoment10Coeff4Row2Norm,kineticDriftMoment10Coeff4Row3Norm,kineticDriftMoment10Coeff4Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff4Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 4 5=c} := by
  have he : kineticDriftCell h kineticCof2 4 5=kineticDriftCell h kineticCof2 4 5 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment10Coeff0Row2Norm,kineticDriftMoment10Coeff0Row3Norm,kineticDriftMoment10Coeff0Row4Norm,kineticDriftMoment10Coeff0Row5Norm,kineticDriftMoment10Coeff1Row2Norm,kineticDriftMoment10Coeff1Row3Norm,kineticDriftMoment10Coeff1Row4Norm,kineticDriftMoment10Coeff1Row5Norm,kineticDriftMoment10Coeff2Row2Norm,kineticDriftMoment10Coeff2Row3Norm,kineticDriftMoment10Coeff2Row4Norm,kineticDriftMoment10Coeff2Row5Norm,kineticDriftMoment10Coeff3Row2Norm,kineticDriftMoment10Coeff3Row3Norm,kineticDriftMoment10Coeff3Row4Norm,kineticDriftMoment10Coeff3Row5Norm,kineticDriftMoment10Coeff4Row2Norm,kineticDriftMoment10Coeff4Row3Norm,kineticDriftMoment10Coeff4Row4Norm,kineticDriftMoment10Coeff4Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff4Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 4 6=c} := by
  have he : kineticDriftCell h kineticCof2 4 6=kineticDriftCell h kineticCof2 4 6 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment10Coeff0Row3Norm,kineticDriftMoment10Coeff0Row4Norm,kineticDriftMoment10Coeff0Row5Norm,kineticDriftMoment10Coeff1Row3Norm,kineticDriftMoment10Coeff1Row4Norm,kineticDriftMoment10Coeff1Row5Norm,kineticDriftMoment10Coeff2Row3Norm,kineticDriftMoment10Coeff2Row4Norm,kineticDriftMoment10Coeff2Row5Norm,kineticDriftMoment10Coeff3Row3Norm,kineticDriftMoment10Coeff3Row4Norm,kineticDriftMoment10Coeff3Row5Norm,kineticDriftMoment10Coeff4Row3Norm,kineticDriftMoment10Coeff4Row4Norm,kineticDriftMoment10Coeff4Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff4Row7Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 4 7=c} := by
  have he : kineticDriftCell h kineticCof2 4 7=kineticDriftCell h kineticCof2 4 7 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment10Coeff0Row4Norm,kineticDriftMoment10Coeff0Row5Norm,kineticDriftMoment10Coeff1Row4Norm,kineticDriftMoment10Coeff1Row5Norm,kineticDriftMoment10Coeff2Row4Norm,kineticDriftMoment10Coeff2Row5Norm,kineticDriftMoment10Coeff3Row4Norm,kineticDriftMoment10Coeff3Row5Norm,kineticDriftMoment10Coeff4Row4Norm,kineticDriftMoment10Coeff4Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff4Row8Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 4 8=c} := by
  have he : kineticDriftCell h kineticCof2 4 8=kineticDriftCell h kineticCof2 4 8 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment10Coeff0Row5Norm,kineticDriftMoment10Coeff1Row5Norm,kineticDriftMoment10Coeff2Row5Norm,kineticDriftMoment10Coeff3Row5Norm,kineticDriftMoment10Coeff4Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff5Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 5 0=c} := by
  have he : kineticDriftCell h kineticCof2 5 0=kineticDriftCell h kineticCof2 5 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment10Coeff0Row0Norm,kineticDriftMoment10Coeff1Row0Norm,kineticDriftMoment10Coeff2Row0Norm,kineticDriftMoment10Coeff3Row0Norm,kineticDriftMoment10Coeff4Row0Norm,kineticDriftMoment10Coeff5Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff5Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 5 1=c} := by
  have he : kineticDriftCell h kineticCof2 5 1=kineticDriftCell h kineticCof2 5 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment10Coeff0Row0Norm,kineticDriftMoment10Coeff0Row1Norm,kineticDriftMoment10Coeff1Row0Norm,kineticDriftMoment10Coeff1Row1Norm,kineticDriftMoment10Coeff2Row0Norm,kineticDriftMoment10Coeff2Row1Norm,kineticDriftMoment10Coeff3Row0Norm,kineticDriftMoment10Coeff3Row1Norm,kineticDriftMoment10Coeff4Row0Norm,kineticDriftMoment10Coeff4Row1Norm,kineticDriftMoment10Coeff5Row0Norm,kineticDriftMoment10Coeff5Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff5Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 5 2=c} := by
  have he : kineticDriftCell h kineticCof2 5 2=kineticDriftCell h kineticCof2 5 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment10Coeff0Row0Norm,kineticDriftMoment10Coeff0Row1Norm,kineticDriftMoment10Coeff0Row2Norm,kineticDriftMoment10Coeff1Row0Norm,kineticDriftMoment10Coeff1Row1Norm,kineticDriftMoment10Coeff1Row2Norm,kineticDriftMoment10Coeff2Row0Norm,kineticDriftMoment10Coeff2Row1Norm,kineticDriftMoment10Coeff2Row2Norm,kineticDriftMoment10Coeff3Row0Norm,kineticDriftMoment10Coeff3Row1Norm,kineticDriftMoment10Coeff3Row2Norm,kineticDriftMoment10Coeff4Row0Norm,kineticDriftMoment10Coeff4Row1Norm,kineticDriftMoment10Coeff4Row2Norm,kineticDriftMoment10Coeff5Row0Norm,kineticDriftMoment10Coeff5Row1Norm,kineticDriftMoment10Coeff5Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff5Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 5 3=c} := by
  have he : kineticDriftCell h kineticCof2 5 3=kineticDriftCell h kineticCof2 5 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment10Coeff0Row0Norm,kineticDriftMoment10Coeff0Row1Norm,kineticDriftMoment10Coeff0Row2Norm,kineticDriftMoment10Coeff0Row3Norm,kineticDriftMoment10Coeff1Row0Norm,kineticDriftMoment10Coeff1Row1Norm,kineticDriftMoment10Coeff1Row2Norm,kineticDriftMoment10Coeff1Row3Norm,kineticDriftMoment10Coeff2Row0Norm,kineticDriftMoment10Coeff2Row1Norm,kineticDriftMoment10Coeff2Row2Norm,kineticDriftMoment10Coeff2Row3Norm,kineticDriftMoment10Coeff3Row0Norm,kineticDriftMoment10Coeff3Row1Norm,kineticDriftMoment10Coeff3Row2Norm,kineticDriftMoment10Coeff3Row3Norm,kineticDriftMoment10Coeff4Row0Norm,kineticDriftMoment10Coeff4Row1Norm,kineticDriftMoment10Coeff4Row2Norm,kineticDriftMoment10Coeff4Row3Norm,kineticDriftMoment10Coeff5Row0Norm,kineticDriftMoment10Coeff5Row1Norm,kineticDriftMoment10Coeff5Row2Norm,kineticDriftMoment10Coeff5Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff5Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 5 4=c} := by
  have he : kineticDriftCell h kineticCof2 5 4=kineticDriftCell h kineticCof2 5 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment10Coeff0Row1Norm,kineticDriftMoment10Coeff0Row2Norm,kineticDriftMoment10Coeff0Row3Norm,kineticDriftMoment10Coeff0Row4Norm,kineticDriftMoment10Coeff1Row1Norm,kineticDriftMoment10Coeff1Row2Norm,kineticDriftMoment10Coeff1Row3Norm,kineticDriftMoment10Coeff1Row4Norm,kineticDriftMoment10Coeff2Row1Norm,kineticDriftMoment10Coeff2Row2Norm,kineticDriftMoment10Coeff2Row3Norm,kineticDriftMoment10Coeff2Row4Norm,kineticDriftMoment10Coeff3Row1Norm,kineticDriftMoment10Coeff3Row2Norm,kineticDriftMoment10Coeff3Row3Norm,kineticDriftMoment10Coeff3Row4Norm,kineticDriftMoment10Coeff4Row1Norm,kineticDriftMoment10Coeff4Row2Norm,kineticDriftMoment10Coeff4Row3Norm,kineticDriftMoment10Coeff4Row4Norm,kineticDriftMoment10Coeff5Row1Norm,kineticDriftMoment10Coeff5Row2Norm,kineticDriftMoment10Coeff5Row3Norm,kineticDriftMoment10Coeff5Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff5Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 5 5=c} := by
  have he : kineticDriftCell h kineticCof2 5 5=kineticDriftCell h kineticCof2 5 5 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment10Coeff0Row2Norm,kineticDriftMoment10Coeff0Row3Norm,kineticDriftMoment10Coeff0Row4Norm,kineticDriftMoment10Coeff0Row5Norm,kineticDriftMoment10Coeff1Row2Norm,kineticDriftMoment10Coeff1Row3Norm,kineticDriftMoment10Coeff1Row4Norm,kineticDriftMoment10Coeff1Row5Norm,kineticDriftMoment10Coeff2Row2Norm,kineticDriftMoment10Coeff2Row3Norm,kineticDriftMoment10Coeff2Row4Norm,kineticDriftMoment10Coeff2Row5Norm,kineticDriftMoment10Coeff3Row2Norm,kineticDriftMoment10Coeff3Row3Norm,kineticDriftMoment10Coeff3Row4Norm,kineticDriftMoment10Coeff3Row5Norm,kineticDriftMoment10Coeff4Row2Norm,kineticDriftMoment10Coeff4Row3Norm,kineticDriftMoment10Coeff4Row4Norm,kineticDriftMoment10Coeff4Row5Norm,kineticDriftMoment10Coeff5Row2Norm,kineticDriftMoment10Coeff5Row3Norm,kineticDriftMoment10Coeff5Row4Norm,kineticDriftMoment10Coeff5Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff5Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 5 6=c} := by
  have he : kineticDriftCell h kineticCof2 5 6=kineticDriftCell h kineticCof2 5 6 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment10Coeff0Row3Norm,kineticDriftMoment10Coeff0Row4Norm,kineticDriftMoment10Coeff0Row5Norm,kineticDriftMoment10Coeff1Row3Norm,kineticDriftMoment10Coeff1Row4Norm,kineticDriftMoment10Coeff1Row5Norm,kineticDriftMoment10Coeff2Row3Norm,kineticDriftMoment10Coeff2Row4Norm,kineticDriftMoment10Coeff2Row5Norm,kineticDriftMoment10Coeff3Row3Norm,kineticDriftMoment10Coeff3Row4Norm,kineticDriftMoment10Coeff3Row5Norm,kineticDriftMoment10Coeff4Row3Norm,kineticDriftMoment10Coeff4Row4Norm,kineticDriftMoment10Coeff4Row5Norm,kineticDriftMoment10Coeff5Row3Norm,kineticDriftMoment10Coeff5Row4Norm,kineticDriftMoment10Coeff5Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff5Row7Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 5 7=c} := by
  have he : kineticDriftCell h kineticCof2 5 7=kineticDriftCell h kineticCof2 5 7 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment10Coeff0Row4Norm,kineticDriftMoment10Coeff0Row5Norm,kineticDriftMoment10Coeff1Row4Norm,kineticDriftMoment10Coeff1Row5Norm,kineticDriftMoment10Coeff2Row4Norm,kineticDriftMoment10Coeff2Row5Norm,kineticDriftMoment10Coeff3Row4Norm,kineticDriftMoment10Coeff3Row5Norm,kineticDriftMoment10Coeff4Row4Norm,kineticDriftMoment10Coeff4Row5Norm,kineticDriftMoment10Coeff5Row4Norm,kineticDriftMoment10Coeff5Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff5Row8Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 5 8=c} := by
  have he : kineticDriftCell h kineticCof2 5 8=kineticDriftCell h kineticCof2 5 8 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment10Coeff0Row5Norm,kineticDriftMoment10Coeff1Row5Norm,kineticDriftMoment10Coeff2Row5Norm,kineticDriftMoment10Coeff3Row5Norm,kineticDriftMoment10Coeff4Row5Norm,kineticDriftMoment10Coeff5Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff6Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 6 0=c} := by
  have he : kineticDriftCell h kineticCof2 6 0=kineticDriftCell h kineticCof2 6 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment10Coeff0Row0Norm,kineticDriftMoment10Coeff1Row0Norm,kineticDriftMoment10Coeff2Row0Norm,kineticDriftMoment10Coeff3Row0Norm,kineticDriftMoment10Coeff4Row0Norm,kineticDriftMoment10Coeff5Row0Norm,kineticDriftMoment10Coeff6Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff6Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 6 1=c} := by
  have he : kineticDriftCell h kineticCof2 6 1=kineticDriftCell h kineticCof2 6 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment10Coeff0Row0Norm,kineticDriftMoment10Coeff0Row1Norm,kineticDriftMoment10Coeff1Row0Norm,kineticDriftMoment10Coeff1Row1Norm,kineticDriftMoment10Coeff2Row0Norm,kineticDriftMoment10Coeff2Row1Norm,kineticDriftMoment10Coeff3Row0Norm,kineticDriftMoment10Coeff3Row1Norm,kineticDriftMoment10Coeff4Row0Norm,kineticDriftMoment10Coeff4Row1Norm,kineticDriftMoment10Coeff5Row0Norm,kineticDriftMoment10Coeff5Row1Norm,kineticDriftMoment10Coeff6Row0Norm,kineticDriftMoment10Coeff6Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff6Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 6 2=c} := by
  have he : kineticDriftCell h kineticCof2 6 2=kineticDriftCell h kineticCof2 6 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment10Coeff0Row0Norm,kineticDriftMoment10Coeff0Row1Norm,kineticDriftMoment10Coeff0Row2Norm,kineticDriftMoment10Coeff1Row0Norm,kineticDriftMoment10Coeff1Row1Norm,kineticDriftMoment10Coeff1Row2Norm,kineticDriftMoment10Coeff2Row0Norm,kineticDriftMoment10Coeff2Row1Norm,kineticDriftMoment10Coeff2Row2Norm,kineticDriftMoment10Coeff3Row0Norm,kineticDriftMoment10Coeff3Row1Norm,kineticDriftMoment10Coeff3Row2Norm,kineticDriftMoment10Coeff4Row0Norm,kineticDriftMoment10Coeff4Row1Norm,kineticDriftMoment10Coeff4Row2Norm,kineticDriftMoment10Coeff5Row0Norm,kineticDriftMoment10Coeff5Row1Norm,kineticDriftMoment10Coeff5Row2Norm,kineticDriftMoment10Coeff6Row0Norm,kineticDriftMoment10Coeff6Row1Norm,kineticDriftMoment10Coeff6Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff6Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 6 3=c} := by
  have he : kineticDriftCell h kineticCof2 6 3=kineticDriftCell h kineticCof2 6 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment10Coeff0Row0Norm,kineticDriftMoment10Coeff0Row1Norm,kineticDriftMoment10Coeff0Row2Norm,kineticDriftMoment10Coeff0Row3Norm,kineticDriftMoment10Coeff1Row0Norm,kineticDriftMoment10Coeff1Row1Norm,kineticDriftMoment10Coeff1Row2Norm,kineticDriftMoment10Coeff1Row3Norm,kineticDriftMoment10Coeff2Row0Norm,kineticDriftMoment10Coeff2Row1Norm,kineticDriftMoment10Coeff2Row2Norm,kineticDriftMoment10Coeff2Row3Norm,kineticDriftMoment10Coeff3Row0Norm,kineticDriftMoment10Coeff3Row1Norm,kineticDriftMoment10Coeff3Row2Norm,kineticDriftMoment10Coeff3Row3Norm,kineticDriftMoment10Coeff4Row0Norm,kineticDriftMoment10Coeff4Row1Norm,kineticDriftMoment10Coeff4Row2Norm,kineticDriftMoment10Coeff4Row3Norm,kineticDriftMoment10Coeff5Row0Norm,kineticDriftMoment10Coeff5Row1Norm,kineticDriftMoment10Coeff5Row2Norm,kineticDriftMoment10Coeff5Row3Norm,kineticDriftMoment10Coeff6Row0Norm,kineticDriftMoment10Coeff6Row1Norm,kineticDriftMoment10Coeff6Row2Norm,kineticDriftMoment10Coeff6Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff6Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 6 4=c} := by
  have he : kineticDriftCell h kineticCof2 6 4=kineticDriftCell h kineticCof2 6 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment10Coeff0Row1Norm,kineticDriftMoment10Coeff0Row2Norm,kineticDriftMoment10Coeff0Row3Norm,kineticDriftMoment10Coeff0Row4Norm,kineticDriftMoment10Coeff1Row1Norm,kineticDriftMoment10Coeff1Row2Norm,kineticDriftMoment10Coeff1Row3Norm,kineticDriftMoment10Coeff1Row4Norm,kineticDriftMoment10Coeff2Row1Norm,kineticDriftMoment10Coeff2Row2Norm,kineticDriftMoment10Coeff2Row3Norm,kineticDriftMoment10Coeff2Row4Norm,kineticDriftMoment10Coeff3Row1Norm,kineticDriftMoment10Coeff3Row2Norm,kineticDriftMoment10Coeff3Row3Norm,kineticDriftMoment10Coeff3Row4Norm,kineticDriftMoment10Coeff4Row1Norm,kineticDriftMoment10Coeff4Row2Norm,kineticDriftMoment10Coeff4Row3Norm,kineticDriftMoment10Coeff4Row4Norm,kineticDriftMoment10Coeff5Row1Norm,kineticDriftMoment10Coeff5Row2Norm,kineticDriftMoment10Coeff5Row3Norm,kineticDriftMoment10Coeff5Row4Norm,kineticDriftMoment10Coeff6Row1Norm,kineticDriftMoment10Coeff6Row2Norm,kineticDriftMoment10Coeff6Row3Norm,kineticDriftMoment10Coeff6Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff6Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 6 5=c} := by
  have he : kineticDriftCell h kineticCof2 6 5=kineticDriftCell h kineticCof2 6 5 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment10Coeff0Row2Norm,kineticDriftMoment10Coeff0Row3Norm,kineticDriftMoment10Coeff0Row4Norm,kineticDriftMoment10Coeff0Row5Norm,kineticDriftMoment10Coeff1Row2Norm,kineticDriftMoment10Coeff1Row3Norm,kineticDriftMoment10Coeff1Row4Norm,kineticDriftMoment10Coeff1Row5Norm,kineticDriftMoment10Coeff2Row2Norm,kineticDriftMoment10Coeff2Row3Norm,kineticDriftMoment10Coeff2Row4Norm,kineticDriftMoment10Coeff2Row5Norm,kineticDriftMoment10Coeff3Row2Norm,kineticDriftMoment10Coeff3Row3Norm,kineticDriftMoment10Coeff3Row4Norm,kineticDriftMoment10Coeff3Row5Norm,kineticDriftMoment10Coeff4Row2Norm,kineticDriftMoment10Coeff4Row3Norm,kineticDriftMoment10Coeff4Row4Norm,kineticDriftMoment10Coeff4Row5Norm,kineticDriftMoment10Coeff5Row2Norm,kineticDriftMoment10Coeff5Row3Norm,kineticDriftMoment10Coeff5Row4Norm,kineticDriftMoment10Coeff5Row5Norm,kineticDriftMoment10Coeff6Row2Norm,kineticDriftMoment10Coeff6Row3Norm,kineticDriftMoment10Coeff6Row4Norm,kineticDriftMoment10Coeff6Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff6Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 6 6=c} := by
  have he : kineticDriftCell h kineticCof2 6 6=kineticDriftCell h kineticCof2 6 6 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment10Coeff0Row3Norm,kineticDriftMoment10Coeff0Row4Norm,kineticDriftMoment10Coeff0Row5Norm,kineticDriftMoment10Coeff1Row3Norm,kineticDriftMoment10Coeff1Row4Norm,kineticDriftMoment10Coeff1Row5Norm,kineticDriftMoment10Coeff2Row3Norm,kineticDriftMoment10Coeff2Row4Norm,kineticDriftMoment10Coeff2Row5Norm,kineticDriftMoment10Coeff3Row3Norm,kineticDriftMoment10Coeff3Row4Norm,kineticDriftMoment10Coeff3Row5Norm,kineticDriftMoment10Coeff4Row3Norm,kineticDriftMoment10Coeff4Row4Norm,kineticDriftMoment10Coeff4Row5Norm,kineticDriftMoment10Coeff5Row3Norm,kineticDriftMoment10Coeff5Row4Norm,kineticDriftMoment10Coeff5Row5Norm,kineticDriftMoment10Coeff6Row3Norm,kineticDriftMoment10Coeff6Row4Norm,kineticDriftMoment10Coeff6Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff6Row7Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 6 7=c} := by
  have he : kineticDriftCell h kineticCof2 6 7=kineticDriftCell h kineticCof2 6 7 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment10Coeff0Row4Norm,kineticDriftMoment10Coeff0Row5Norm,kineticDriftMoment10Coeff1Row4Norm,kineticDriftMoment10Coeff1Row5Norm,kineticDriftMoment10Coeff2Row4Norm,kineticDriftMoment10Coeff2Row5Norm,kineticDriftMoment10Coeff3Row4Norm,kineticDriftMoment10Coeff3Row5Norm,kineticDriftMoment10Coeff4Row4Norm,kineticDriftMoment10Coeff4Row5Norm,kineticDriftMoment10Coeff5Row4Norm,kineticDriftMoment10Coeff5Row5Norm,kineticDriftMoment10Coeff6Row4Norm,kineticDriftMoment10Coeff6Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff6Row8Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 6 8=c} := by
  have he : kineticDriftCell h kineticCof2 6 8=kineticDriftCell h kineticCof2 6 8 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment10Coeff0Row5Norm,kineticDriftMoment10Coeff1Row5Norm,kineticDriftMoment10Coeff2Row5Norm,kineticDriftMoment10Coeff3Row5Norm,kineticDriftMoment10Coeff4Row5Norm,kineticDriftMoment10Coeff5Row5Norm,kineticDriftMoment10Coeff6Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff7Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 7 0=c} := by
  have he : kineticDriftCell h kineticCof2 7 0=kineticDriftCell h kineticCof2 7 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment10Coeff1Row0Norm,kineticDriftMoment10Coeff2Row0Norm,kineticDriftMoment10Coeff3Row0Norm,kineticDriftMoment10Coeff4Row0Norm,kineticDriftMoment10Coeff5Row0Norm,kineticDriftMoment10Coeff6Row0Norm,kineticDriftMoment10Coeff7Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff7Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 7 1=c} := by
  have he : kineticDriftCell h kineticCof2 7 1=kineticDriftCell h kineticCof2 7 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment10Coeff1Row0Norm,kineticDriftMoment10Coeff1Row1Norm,kineticDriftMoment10Coeff2Row0Norm,kineticDriftMoment10Coeff2Row1Norm,kineticDriftMoment10Coeff3Row0Norm,kineticDriftMoment10Coeff3Row1Norm,kineticDriftMoment10Coeff4Row0Norm,kineticDriftMoment10Coeff4Row1Norm,kineticDriftMoment10Coeff5Row0Norm,kineticDriftMoment10Coeff5Row1Norm,kineticDriftMoment10Coeff6Row0Norm,kineticDriftMoment10Coeff6Row1Norm,kineticDriftMoment10Coeff7Row0Norm,kineticDriftMoment10Coeff7Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff7Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 7 2=c} := by
  have he : kineticDriftCell h kineticCof2 7 2=kineticDriftCell h kineticCof2 7 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment10Coeff1Row0Norm,kineticDriftMoment10Coeff1Row1Norm,kineticDriftMoment10Coeff1Row2Norm,kineticDriftMoment10Coeff2Row0Norm,kineticDriftMoment10Coeff2Row1Norm,kineticDriftMoment10Coeff2Row2Norm,kineticDriftMoment10Coeff3Row0Norm,kineticDriftMoment10Coeff3Row1Norm,kineticDriftMoment10Coeff3Row2Norm,kineticDriftMoment10Coeff4Row0Norm,kineticDriftMoment10Coeff4Row1Norm,kineticDriftMoment10Coeff4Row2Norm,kineticDriftMoment10Coeff5Row0Norm,kineticDriftMoment10Coeff5Row1Norm,kineticDriftMoment10Coeff5Row2Norm,kineticDriftMoment10Coeff6Row0Norm,kineticDriftMoment10Coeff6Row1Norm,kineticDriftMoment10Coeff6Row2Norm,kineticDriftMoment10Coeff7Row0Norm,kineticDriftMoment10Coeff7Row1Norm,kineticDriftMoment10Coeff7Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff7Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 7 3=c} := by
  have he : kineticDriftCell h kineticCof2 7 3=kineticDriftCell h kineticCof2 7 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment10Coeff1Row0Norm,kineticDriftMoment10Coeff1Row1Norm,kineticDriftMoment10Coeff1Row2Norm,kineticDriftMoment10Coeff1Row3Norm,kineticDriftMoment10Coeff2Row0Norm,kineticDriftMoment10Coeff2Row1Norm,kineticDriftMoment10Coeff2Row2Norm,kineticDriftMoment10Coeff2Row3Norm,kineticDriftMoment10Coeff3Row0Norm,kineticDriftMoment10Coeff3Row1Norm,kineticDriftMoment10Coeff3Row2Norm,kineticDriftMoment10Coeff3Row3Norm,kineticDriftMoment10Coeff4Row0Norm,kineticDriftMoment10Coeff4Row1Norm,kineticDriftMoment10Coeff4Row2Norm,kineticDriftMoment10Coeff4Row3Norm,kineticDriftMoment10Coeff5Row0Norm,kineticDriftMoment10Coeff5Row1Norm,kineticDriftMoment10Coeff5Row2Norm,kineticDriftMoment10Coeff5Row3Norm,kineticDriftMoment10Coeff6Row0Norm,kineticDriftMoment10Coeff6Row1Norm,kineticDriftMoment10Coeff6Row2Norm,kineticDriftMoment10Coeff6Row3Norm,kineticDriftMoment10Coeff7Row0Norm,kineticDriftMoment10Coeff7Row1Norm,kineticDriftMoment10Coeff7Row2Norm,kineticDriftMoment10Coeff7Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff7Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 7 4=c} := by
  have he : kineticDriftCell h kineticCof2 7 4=kineticDriftCell h kineticCof2 7 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment10Coeff1Row1Norm,kineticDriftMoment10Coeff1Row2Norm,kineticDriftMoment10Coeff1Row3Norm,kineticDriftMoment10Coeff1Row4Norm,kineticDriftMoment10Coeff2Row1Norm,kineticDriftMoment10Coeff2Row2Norm,kineticDriftMoment10Coeff2Row3Norm,kineticDriftMoment10Coeff2Row4Norm,kineticDriftMoment10Coeff3Row1Norm,kineticDriftMoment10Coeff3Row2Norm,kineticDriftMoment10Coeff3Row3Norm,kineticDriftMoment10Coeff3Row4Norm,kineticDriftMoment10Coeff4Row1Norm,kineticDriftMoment10Coeff4Row2Norm,kineticDriftMoment10Coeff4Row3Norm,kineticDriftMoment10Coeff4Row4Norm,kineticDriftMoment10Coeff5Row1Norm,kineticDriftMoment10Coeff5Row2Norm,kineticDriftMoment10Coeff5Row3Norm,kineticDriftMoment10Coeff5Row4Norm,kineticDriftMoment10Coeff6Row1Norm,kineticDriftMoment10Coeff6Row2Norm,kineticDriftMoment10Coeff6Row3Norm,kineticDriftMoment10Coeff6Row4Norm,kineticDriftMoment10Coeff7Row1Norm,kineticDriftMoment10Coeff7Row2Norm,kineticDriftMoment10Coeff7Row3Norm,kineticDriftMoment10Coeff7Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff7Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 7 5=c} := by
  have he : kineticDriftCell h kineticCof2 7 5=kineticDriftCell h kineticCof2 7 5 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment10Coeff1Row2Norm,kineticDriftMoment10Coeff1Row3Norm,kineticDriftMoment10Coeff1Row4Norm,kineticDriftMoment10Coeff1Row5Norm,kineticDriftMoment10Coeff2Row2Norm,kineticDriftMoment10Coeff2Row3Norm,kineticDriftMoment10Coeff2Row4Norm,kineticDriftMoment10Coeff2Row5Norm,kineticDriftMoment10Coeff3Row2Norm,kineticDriftMoment10Coeff3Row3Norm,kineticDriftMoment10Coeff3Row4Norm,kineticDriftMoment10Coeff3Row5Norm,kineticDriftMoment10Coeff4Row2Norm,kineticDriftMoment10Coeff4Row3Norm,kineticDriftMoment10Coeff4Row4Norm,kineticDriftMoment10Coeff4Row5Norm,kineticDriftMoment10Coeff5Row2Norm,kineticDriftMoment10Coeff5Row3Norm,kineticDriftMoment10Coeff5Row4Norm,kineticDriftMoment10Coeff5Row5Norm,kineticDriftMoment10Coeff6Row2Norm,kineticDriftMoment10Coeff6Row3Norm,kineticDriftMoment10Coeff6Row4Norm,kineticDriftMoment10Coeff6Row5Norm,kineticDriftMoment10Coeff7Row2Norm,kineticDriftMoment10Coeff7Row3Norm,kineticDriftMoment10Coeff7Row4Norm,kineticDriftMoment10Coeff7Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff7Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 7 6=c} := by
  have he : kineticDriftCell h kineticCof2 7 6=kineticDriftCell h kineticCof2 7 6 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment10Coeff1Row3Norm,kineticDriftMoment10Coeff1Row4Norm,kineticDriftMoment10Coeff1Row5Norm,kineticDriftMoment10Coeff2Row3Norm,kineticDriftMoment10Coeff2Row4Norm,kineticDriftMoment10Coeff2Row5Norm,kineticDriftMoment10Coeff3Row3Norm,kineticDriftMoment10Coeff3Row4Norm,kineticDriftMoment10Coeff3Row5Norm,kineticDriftMoment10Coeff4Row3Norm,kineticDriftMoment10Coeff4Row4Norm,kineticDriftMoment10Coeff4Row5Norm,kineticDriftMoment10Coeff5Row3Norm,kineticDriftMoment10Coeff5Row4Norm,kineticDriftMoment10Coeff5Row5Norm,kineticDriftMoment10Coeff6Row3Norm,kineticDriftMoment10Coeff6Row4Norm,kineticDriftMoment10Coeff6Row5Norm,kineticDriftMoment10Coeff7Row3Norm,kineticDriftMoment10Coeff7Row4Norm,kineticDriftMoment10Coeff7Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff7Row7Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 7 7=c} := by
  have he : kineticDriftCell h kineticCof2 7 7=kineticDriftCell h kineticCof2 7 7 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment10Coeff1Row4Norm,kineticDriftMoment10Coeff1Row5Norm,kineticDriftMoment10Coeff2Row4Norm,kineticDriftMoment10Coeff2Row5Norm,kineticDriftMoment10Coeff3Row4Norm,kineticDriftMoment10Coeff3Row5Norm,kineticDriftMoment10Coeff4Row4Norm,kineticDriftMoment10Coeff4Row5Norm,kineticDriftMoment10Coeff5Row4Norm,kineticDriftMoment10Coeff5Row5Norm,kineticDriftMoment10Coeff6Row4Norm,kineticDriftMoment10Coeff6Row5Norm,kineticDriftMoment10Coeff7Row4Norm,kineticDriftMoment10Coeff7Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff7Row8Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 7 8=c} := by
  have he : kineticDriftCell h kineticCof2 7 8=kineticDriftCell h kineticCof2 7 8 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment10Coeff1Row5Norm,kineticDriftMoment10Coeff2Row5Norm,kineticDriftMoment10Coeff3Row5Norm,kineticDriftMoment10Coeff4Row5Norm,kineticDriftMoment10Coeff5Row5Norm,kineticDriftMoment10Coeff6Row5Norm,kineticDriftMoment10Coeff7Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff8Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 8 0=c} := by
  have he : kineticDriftCell h kineticCof2 8 0=kineticDriftCell h kineticCof2 8 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment10Coeff2Row0Norm,kineticDriftMoment10Coeff3Row0Norm,kineticDriftMoment10Coeff4Row0Norm,kineticDriftMoment10Coeff5Row0Norm,kineticDriftMoment10Coeff6Row0Norm,kineticDriftMoment10Coeff7Row0Norm,kineticDriftMoment10Coeff8Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff8Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 8 1=c} := by
  have he : kineticDriftCell h kineticCof2 8 1=kineticDriftCell h kineticCof2 8 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment10Coeff2Row0Norm,kineticDriftMoment10Coeff2Row1Norm,kineticDriftMoment10Coeff3Row0Norm,kineticDriftMoment10Coeff3Row1Norm,kineticDriftMoment10Coeff4Row0Norm,kineticDriftMoment10Coeff4Row1Norm,kineticDriftMoment10Coeff5Row0Norm,kineticDriftMoment10Coeff5Row1Norm,kineticDriftMoment10Coeff6Row0Norm,kineticDriftMoment10Coeff6Row1Norm,kineticDriftMoment10Coeff7Row0Norm,kineticDriftMoment10Coeff7Row1Norm,kineticDriftMoment10Coeff8Row0Norm,kineticDriftMoment10Coeff8Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff8Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 8 2=c} := by
  have he : kineticDriftCell h kineticCof2 8 2=kineticDriftCell h kineticCof2 8 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment10Coeff2Row0Norm,kineticDriftMoment10Coeff2Row1Norm,kineticDriftMoment10Coeff2Row2Norm,kineticDriftMoment10Coeff3Row0Norm,kineticDriftMoment10Coeff3Row1Norm,kineticDriftMoment10Coeff3Row2Norm,kineticDriftMoment10Coeff4Row0Norm,kineticDriftMoment10Coeff4Row1Norm,kineticDriftMoment10Coeff4Row2Norm,kineticDriftMoment10Coeff5Row0Norm,kineticDriftMoment10Coeff5Row1Norm,kineticDriftMoment10Coeff5Row2Norm,kineticDriftMoment10Coeff6Row0Norm,kineticDriftMoment10Coeff6Row1Norm,kineticDriftMoment10Coeff6Row2Norm,kineticDriftMoment10Coeff7Row0Norm,kineticDriftMoment10Coeff7Row1Norm,kineticDriftMoment10Coeff7Row2Norm,kineticDriftMoment10Coeff8Row0Norm,kineticDriftMoment10Coeff8Row1Norm,kineticDriftMoment10Coeff8Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff8Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 8 3=c} := by
  have he : kineticDriftCell h kineticCof2 8 3=kineticDriftCell h kineticCof2 8 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment10Coeff2Row0Norm,kineticDriftMoment10Coeff2Row1Norm,kineticDriftMoment10Coeff2Row2Norm,kineticDriftMoment10Coeff2Row3Norm,kineticDriftMoment10Coeff3Row0Norm,kineticDriftMoment10Coeff3Row1Norm,kineticDriftMoment10Coeff3Row2Norm,kineticDriftMoment10Coeff3Row3Norm,kineticDriftMoment10Coeff4Row0Norm,kineticDriftMoment10Coeff4Row1Norm,kineticDriftMoment10Coeff4Row2Norm,kineticDriftMoment10Coeff4Row3Norm,kineticDriftMoment10Coeff5Row0Norm,kineticDriftMoment10Coeff5Row1Norm,kineticDriftMoment10Coeff5Row2Norm,kineticDriftMoment10Coeff5Row3Norm,kineticDriftMoment10Coeff6Row0Norm,kineticDriftMoment10Coeff6Row1Norm,kineticDriftMoment10Coeff6Row2Norm,kineticDriftMoment10Coeff6Row3Norm,kineticDriftMoment10Coeff7Row0Norm,kineticDriftMoment10Coeff7Row1Norm,kineticDriftMoment10Coeff7Row2Norm,kineticDriftMoment10Coeff7Row3Norm,kineticDriftMoment10Coeff8Row0Norm,kineticDriftMoment10Coeff8Row1Norm,kineticDriftMoment10Coeff8Row2Norm,kineticDriftMoment10Coeff8Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff8Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 8 4=c} := by
  have he : kineticDriftCell h kineticCof2 8 4=kineticDriftCell h kineticCof2 8 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff0Row0Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff2Row1Norm,kineticDriftMoment10Coeff2Row2Norm,kineticDriftMoment10Coeff2Row3Norm,kineticDriftMoment10Coeff2Row4Norm,kineticDriftMoment10Coeff3Row1Norm,kineticDriftMoment10Coeff3Row2Norm,kineticDriftMoment10Coeff3Row3Norm,kineticDriftMoment10Coeff3Row4Norm,kineticDriftMoment10Coeff4Row1Norm,kineticDriftMoment10Coeff4Row2Norm,kineticDriftMoment10Coeff4Row3Norm,kineticDriftMoment10Coeff4Row4Norm,kineticDriftMoment10Coeff5Row1Norm,kineticDriftMoment10Coeff5Row2Norm,kineticDriftMoment10Coeff5Row3Norm,kineticDriftMoment10Coeff5Row4Norm,kineticDriftMoment10Coeff6Row1Norm,kineticDriftMoment10Coeff6Row2Norm,kineticDriftMoment10Coeff6Row3Norm,kineticDriftMoment10Coeff6Row4Norm,kineticDriftMoment10Coeff7Row1Norm,kineticDriftMoment10Coeff7Row2Norm,kineticDriftMoment10Coeff7Row3Norm,kineticDriftMoment10Coeff7Row4Norm,kineticDriftMoment10Coeff8Row1Norm,kineticDriftMoment10Coeff8Row2Norm,kineticDriftMoment10Coeff8Row3Norm,kineticDriftMoment10Coeff8Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff8Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 8 5=c} := by
  have he : kineticDriftCell h kineticCof2 8 5=kineticDriftCell h kineticCof2 8 5 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff0Row1Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff2Row2Norm,kineticDriftMoment10Coeff2Row3Norm,kineticDriftMoment10Coeff2Row4Norm,kineticDriftMoment10Coeff2Row5Norm,kineticDriftMoment10Coeff3Row2Norm,kineticDriftMoment10Coeff3Row3Norm,kineticDriftMoment10Coeff3Row4Norm,kineticDriftMoment10Coeff3Row5Norm,kineticDriftMoment10Coeff4Row2Norm,kineticDriftMoment10Coeff4Row3Norm,kineticDriftMoment10Coeff4Row4Norm,kineticDriftMoment10Coeff4Row5Norm,kineticDriftMoment10Coeff5Row2Norm,kineticDriftMoment10Coeff5Row3Norm,kineticDriftMoment10Coeff5Row4Norm,kineticDriftMoment10Coeff5Row5Norm,kineticDriftMoment10Coeff6Row2Norm,kineticDriftMoment10Coeff6Row3Norm,kineticDriftMoment10Coeff6Row4Norm,kineticDriftMoment10Coeff6Row5Norm,kineticDriftMoment10Coeff7Row2Norm,kineticDriftMoment10Coeff7Row3Norm,kineticDriftMoment10Coeff7Row4Norm,kineticDriftMoment10Coeff7Row5Norm,kineticDriftMoment10Coeff8Row2Norm,kineticDriftMoment10Coeff8Row3Norm,kineticDriftMoment10Coeff8Row4Norm,kineticDriftMoment10Coeff8Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff8Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 8 6=c} := by
  have he : kineticDriftCell h kineticCof2 8 6=kineticDriftCell h kineticCof2 8 6 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff0Row2Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff2Row3Norm,kineticDriftMoment10Coeff2Row4Norm,kineticDriftMoment10Coeff2Row5Norm,kineticDriftMoment10Coeff3Row3Norm,kineticDriftMoment10Coeff3Row4Norm,kineticDriftMoment10Coeff3Row5Norm,kineticDriftMoment10Coeff4Row3Norm,kineticDriftMoment10Coeff4Row4Norm,kineticDriftMoment10Coeff4Row5Norm,kineticDriftMoment10Coeff5Row3Norm,kineticDriftMoment10Coeff5Row4Norm,kineticDriftMoment10Coeff5Row5Norm,kineticDriftMoment10Coeff6Row3Norm,kineticDriftMoment10Coeff6Row4Norm,kineticDriftMoment10Coeff6Row5Norm,kineticDriftMoment10Coeff7Row3Norm,kineticDriftMoment10Coeff7Row4Norm,kineticDriftMoment10Coeff7Row5Norm,kineticDriftMoment10Coeff8Row3Norm,kineticDriftMoment10Coeff8Row4Norm,kineticDriftMoment10Coeff8Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff8Row7Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 8 7=c} := by
  have he : kineticDriftCell h kineticCof2 8 7=kineticDriftCell h kineticCof2 8 7 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff0Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff2Row4Norm,kineticDriftMoment10Coeff2Row5Norm,kineticDriftMoment10Coeff3Row4Norm,kineticDriftMoment10Coeff3Row5Norm,kineticDriftMoment10Coeff4Row4Norm,kineticDriftMoment10Coeff4Row5Norm,kineticDriftMoment10Coeff5Row4Norm,kineticDriftMoment10Coeff5Row5Norm,kineticDriftMoment10Coeff6Row4Norm,kineticDriftMoment10Coeff6Row5Norm,kineticDriftMoment10Coeff7Row4Norm,kineticDriftMoment10Coeff7Row5Norm,kineticDriftMoment10Coeff8Row4Norm,kineticDriftMoment10Coeff8Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff8Row8Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 8 8=c} := by
  have he : kineticDriftCell h kineticCof2 8 8=kineticDriftCell h kineticCof2 8 8 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff0Row4Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff2Row5Norm,kineticDriftMoment10Coeff3Row5Norm,kineticDriftMoment10Coeff4Row5Norm,kineticDriftMoment10Coeff5Row5Norm,kineticDriftMoment10Coeff6Row5Norm,kineticDriftMoment10Coeff7Row5Norm,kineticDriftMoment10Coeff8Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff9Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 9 0=c} := by
  have he : kineticDriftCell h kineticCof2 9 0=kineticDriftCell h kineticCof2 9 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment10Coeff3Row0Norm,kineticDriftMoment10Coeff4Row0Norm,kineticDriftMoment10Coeff5Row0Norm,kineticDriftMoment10Coeff6Row0Norm,kineticDriftMoment10Coeff7Row0Norm,kineticDriftMoment10Coeff8Row0Norm,kineticDriftMoment10Coeff9Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff9Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 9 1=c} := by
  have he : kineticDriftCell h kineticCof2 9 1=kineticDriftCell h kineticCof2 9 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment10Coeff3Row0Norm,kineticDriftMoment10Coeff3Row1Norm,kineticDriftMoment10Coeff4Row0Norm,kineticDriftMoment10Coeff4Row1Norm,kineticDriftMoment10Coeff5Row0Norm,kineticDriftMoment10Coeff5Row1Norm,kineticDriftMoment10Coeff6Row0Norm,kineticDriftMoment10Coeff6Row1Norm,kineticDriftMoment10Coeff7Row0Norm,kineticDriftMoment10Coeff7Row1Norm,kineticDriftMoment10Coeff8Row0Norm,kineticDriftMoment10Coeff8Row1Norm,kineticDriftMoment10Coeff9Row0Norm,kineticDriftMoment10Coeff9Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff9Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 9 2=c} := by
  have he : kineticDriftCell h kineticCof2 9 2=kineticDriftCell h kineticCof2 9 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment10Coeff3Row0Norm,kineticDriftMoment10Coeff3Row1Norm,kineticDriftMoment10Coeff3Row2Norm,kineticDriftMoment10Coeff4Row0Norm,kineticDriftMoment10Coeff4Row1Norm,kineticDriftMoment10Coeff4Row2Norm,kineticDriftMoment10Coeff5Row0Norm,kineticDriftMoment10Coeff5Row1Norm,kineticDriftMoment10Coeff5Row2Norm,kineticDriftMoment10Coeff6Row0Norm,kineticDriftMoment10Coeff6Row1Norm,kineticDriftMoment10Coeff6Row2Norm,kineticDriftMoment10Coeff7Row0Norm,kineticDriftMoment10Coeff7Row1Norm,kineticDriftMoment10Coeff7Row2Norm,kineticDriftMoment10Coeff8Row0Norm,kineticDriftMoment10Coeff8Row1Norm,kineticDriftMoment10Coeff8Row2Norm,kineticDriftMoment10Coeff9Row0Norm,kineticDriftMoment10Coeff9Row1Norm,kineticDriftMoment10Coeff9Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff9Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 9 3=c} := by
  have he : kineticDriftCell h kineticCof2 9 3=kineticDriftCell h kineticCof2 9 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment10Coeff3Row0Norm,kineticDriftMoment10Coeff3Row1Norm,kineticDriftMoment10Coeff3Row2Norm,kineticDriftMoment10Coeff3Row3Norm,kineticDriftMoment10Coeff4Row0Norm,kineticDriftMoment10Coeff4Row1Norm,kineticDriftMoment10Coeff4Row2Norm,kineticDriftMoment10Coeff4Row3Norm,kineticDriftMoment10Coeff5Row0Norm,kineticDriftMoment10Coeff5Row1Norm,kineticDriftMoment10Coeff5Row2Norm,kineticDriftMoment10Coeff5Row3Norm,kineticDriftMoment10Coeff6Row0Norm,kineticDriftMoment10Coeff6Row1Norm,kineticDriftMoment10Coeff6Row2Norm,kineticDriftMoment10Coeff6Row3Norm,kineticDriftMoment10Coeff7Row0Norm,kineticDriftMoment10Coeff7Row1Norm,kineticDriftMoment10Coeff7Row2Norm,kineticDriftMoment10Coeff7Row3Norm,kineticDriftMoment10Coeff8Row0Norm,kineticDriftMoment10Coeff8Row1Norm,kineticDriftMoment10Coeff8Row2Norm,kineticDriftMoment10Coeff8Row3Norm,kineticDriftMoment10Coeff9Row0Norm,kineticDriftMoment10Coeff9Row1Norm,kineticDriftMoment10Coeff9Row2Norm,kineticDriftMoment10Coeff9Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff9Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 9 4=c} := by
  have he : kineticDriftCell h kineticCof2 9 4=kineticDriftCell h kineticCof2 9 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff1Row0Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff3Row1Norm,kineticDriftMoment10Coeff3Row2Norm,kineticDriftMoment10Coeff3Row3Norm,kineticDriftMoment10Coeff3Row4Norm,kineticDriftMoment10Coeff4Row1Norm,kineticDriftMoment10Coeff4Row2Norm,kineticDriftMoment10Coeff4Row3Norm,kineticDriftMoment10Coeff4Row4Norm,kineticDriftMoment10Coeff5Row1Norm,kineticDriftMoment10Coeff5Row2Norm,kineticDriftMoment10Coeff5Row3Norm,kineticDriftMoment10Coeff5Row4Norm,kineticDriftMoment10Coeff6Row1Norm,kineticDriftMoment10Coeff6Row2Norm,kineticDriftMoment10Coeff6Row3Norm,kineticDriftMoment10Coeff6Row4Norm,kineticDriftMoment10Coeff7Row1Norm,kineticDriftMoment10Coeff7Row2Norm,kineticDriftMoment10Coeff7Row3Norm,kineticDriftMoment10Coeff7Row4Norm,kineticDriftMoment10Coeff8Row1Norm,kineticDriftMoment10Coeff8Row2Norm,kineticDriftMoment10Coeff8Row3Norm,kineticDriftMoment10Coeff8Row4Norm,kineticDriftMoment10Coeff9Row1Norm,kineticDriftMoment10Coeff9Row2Norm,kineticDriftMoment10Coeff9Row3Norm,kineticDriftMoment10Coeff9Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff9Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 9 5=c} := by
  have he : kineticDriftCell h kineticCof2 9 5=kineticDriftCell h kineticCof2 9 5 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff1Row1Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff3Row2Norm,kineticDriftMoment10Coeff3Row3Norm,kineticDriftMoment10Coeff3Row4Norm,kineticDriftMoment10Coeff3Row5Norm,kineticDriftMoment10Coeff4Row2Norm,kineticDriftMoment10Coeff4Row3Norm,kineticDriftMoment10Coeff4Row4Norm,kineticDriftMoment10Coeff4Row5Norm,kineticDriftMoment10Coeff5Row2Norm,kineticDriftMoment10Coeff5Row3Norm,kineticDriftMoment10Coeff5Row4Norm,kineticDriftMoment10Coeff5Row5Norm,kineticDriftMoment10Coeff6Row2Norm,kineticDriftMoment10Coeff6Row3Norm,kineticDriftMoment10Coeff6Row4Norm,kineticDriftMoment10Coeff6Row5Norm,kineticDriftMoment10Coeff7Row2Norm,kineticDriftMoment10Coeff7Row3Norm,kineticDriftMoment10Coeff7Row4Norm,kineticDriftMoment10Coeff7Row5Norm,kineticDriftMoment10Coeff8Row2Norm,kineticDriftMoment10Coeff8Row3Norm,kineticDriftMoment10Coeff8Row4Norm,kineticDriftMoment10Coeff8Row5Norm,kineticDriftMoment10Coeff9Row2Norm,kineticDriftMoment10Coeff9Row3Norm,kineticDriftMoment10Coeff9Row4Norm,kineticDriftMoment10Coeff9Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff9Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 9 6=c} := by
  have he : kineticDriftCell h kineticCof2 9 6=kineticDriftCell h kineticCof2 9 6 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff1Row2Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff3Row3Norm,kineticDriftMoment10Coeff3Row4Norm,kineticDriftMoment10Coeff3Row5Norm,kineticDriftMoment10Coeff4Row3Norm,kineticDriftMoment10Coeff4Row4Norm,kineticDriftMoment10Coeff4Row5Norm,kineticDriftMoment10Coeff5Row3Norm,kineticDriftMoment10Coeff5Row4Norm,kineticDriftMoment10Coeff5Row5Norm,kineticDriftMoment10Coeff6Row3Norm,kineticDriftMoment10Coeff6Row4Norm,kineticDriftMoment10Coeff6Row5Norm,kineticDriftMoment10Coeff7Row3Norm,kineticDriftMoment10Coeff7Row4Norm,kineticDriftMoment10Coeff7Row5Norm,kineticDriftMoment10Coeff8Row3Norm,kineticDriftMoment10Coeff8Row4Norm,kineticDriftMoment10Coeff8Row5Norm,kineticDriftMoment10Coeff9Row3Norm,kineticDriftMoment10Coeff9Row4Norm,kineticDriftMoment10Coeff9Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff9Row7Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 9 7=c} := by
  have he : kineticDriftCell h kineticCof2 9 7=kineticDriftCell h kineticCof2 9 7 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff1Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff3Row4Norm,kineticDriftMoment10Coeff3Row5Norm,kineticDriftMoment10Coeff4Row4Norm,kineticDriftMoment10Coeff4Row5Norm,kineticDriftMoment10Coeff5Row4Norm,kineticDriftMoment10Coeff5Row5Norm,kineticDriftMoment10Coeff6Row4Norm,kineticDriftMoment10Coeff6Row5Norm,kineticDriftMoment10Coeff7Row4Norm,kineticDriftMoment10Coeff7Row5Norm,kineticDriftMoment10Coeff8Row4Norm,kineticDriftMoment10Coeff8Row5Norm,kineticDriftMoment10Coeff9Row4Norm,kineticDriftMoment10Coeff9Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff9Row8Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 9 8=c} := by
  have he : kineticDriftCell h kineticCof2 9 8=kineticDriftCell h kineticCof2 9 8 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff1Row4Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff3Row5Norm,kineticDriftMoment10Coeff4Row5Norm,kineticDriftMoment10Coeff5Row5Norm,kineticDriftMoment10Coeff6Row5Norm,kineticDriftMoment10Coeff7Row5Norm,kineticDriftMoment10Coeff8Row5Norm,kineticDriftMoment10Coeff9Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff10Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 10 0=c} := by
  have he : kineticDriftCell h kineticCof2 10 0=kineticDriftCell h kineticCof2 10 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment10Coeff4Row0Norm,kineticDriftMoment10Coeff5Row0Norm,kineticDriftMoment10Coeff6Row0Norm,kineticDriftMoment10Coeff7Row0Norm,kineticDriftMoment10Coeff8Row0Norm,kineticDriftMoment10Coeff9Row0Norm,kineticDriftMoment10Coeff10Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff10Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 10 1=c} := by
  have he : kineticDriftCell h kineticCof2 10 1=kineticDriftCell h kineticCof2 10 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment10Coeff4Row0Norm,kineticDriftMoment10Coeff4Row1Norm,kineticDriftMoment10Coeff5Row0Norm,kineticDriftMoment10Coeff5Row1Norm,kineticDriftMoment10Coeff6Row0Norm,kineticDriftMoment10Coeff6Row1Norm,kineticDriftMoment10Coeff7Row0Norm,kineticDriftMoment10Coeff7Row1Norm,kineticDriftMoment10Coeff8Row0Norm,kineticDriftMoment10Coeff8Row1Norm,kineticDriftMoment10Coeff9Row0Norm,kineticDriftMoment10Coeff9Row1Norm,kineticDriftMoment10Coeff10Row0Norm,kineticDriftMoment10Coeff10Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff10Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 10 2=c} := by
  have he : kineticDriftCell h kineticCof2 10 2=kineticDriftCell h kineticCof2 10 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment10Coeff4Row0Norm,kineticDriftMoment10Coeff4Row1Norm,kineticDriftMoment10Coeff4Row2Norm,kineticDriftMoment10Coeff5Row0Norm,kineticDriftMoment10Coeff5Row1Norm,kineticDriftMoment10Coeff5Row2Norm,kineticDriftMoment10Coeff6Row0Norm,kineticDriftMoment10Coeff6Row1Norm,kineticDriftMoment10Coeff6Row2Norm,kineticDriftMoment10Coeff7Row0Norm,kineticDriftMoment10Coeff7Row1Norm,kineticDriftMoment10Coeff7Row2Norm,kineticDriftMoment10Coeff8Row0Norm,kineticDriftMoment10Coeff8Row1Norm,kineticDriftMoment10Coeff8Row2Norm,kineticDriftMoment10Coeff9Row0Norm,kineticDriftMoment10Coeff9Row1Norm,kineticDriftMoment10Coeff9Row2Norm,kineticDriftMoment10Coeff10Row0Norm,kineticDriftMoment10Coeff10Row1Norm,kineticDriftMoment10Coeff10Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff10Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 10 3=c} := by
  have he : kineticDriftCell h kineticCof2 10 3=kineticDriftCell h kineticCof2 10 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment10Coeff4Row0Norm,kineticDriftMoment10Coeff4Row1Norm,kineticDriftMoment10Coeff4Row2Norm,kineticDriftMoment10Coeff4Row3Norm,kineticDriftMoment10Coeff5Row0Norm,kineticDriftMoment10Coeff5Row1Norm,kineticDriftMoment10Coeff5Row2Norm,kineticDriftMoment10Coeff5Row3Norm,kineticDriftMoment10Coeff6Row0Norm,kineticDriftMoment10Coeff6Row1Norm,kineticDriftMoment10Coeff6Row2Norm,kineticDriftMoment10Coeff6Row3Norm,kineticDriftMoment10Coeff7Row0Norm,kineticDriftMoment10Coeff7Row1Norm,kineticDriftMoment10Coeff7Row2Norm,kineticDriftMoment10Coeff7Row3Norm,kineticDriftMoment10Coeff8Row0Norm,kineticDriftMoment10Coeff8Row1Norm,kineticDriftMoment10Coeff8Row2Norm,kineticDriftMoment10Coeff8Row3Norm,kineticDriftMoment10Coeff9Row0Norm,kineticDriftMoment10Coeff9Row1Norm,kineticDriftMoment10Coeff9Row2Norm,kineticDriftMoment10Coeff9Row3Norm,kineticDriftMoment10Coeff10Row0Norm,kineticDriftMoment10Coeff10Row1Norm,kineticDriftMoment10Coeff10Row2Norm,kineticDriftMoment10Coeff10Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff10Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 10 4=c} := by
  have he : kineticDriftCell h kineticCof2 10 4=kineticDriftCell h kineticCof2 10 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff2Row0Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff4Row1Norm,kineticDriftMoment10Coeff4Row2Norm,kineticDriftMoment10Coeff4Row3Norm,kineticDriftMoment10Coeff4Row4Norm,kineticDriftMoment10Coeff5Row1Norm,kineticDriftMoment10Coeff5Row2Norm,kineticDriftMoment10Coeff5Row3Norm,kineticDriftMoment10Coeff5Row4Norm,kineticDriftMoment10Coeff6Row1Norm,kineticDriftMoment10Coeff6Row2Norm,kineticDriftMoment10Coeff6Row3Norm,kineticDriftMoment10Coeff6Row4Norm,kineticDriftMoment10Coeff7Row1Norm,kineticDriftMoment10Coeff7Row2Norm,kineticDriftMoment10Coeff7Row3Norm,kineticDriftMoment10Coeff7Row4Norm,kineticDriftMoment10Coeff8Row1Norm,kineticDriftMoment10Coeff8Row2Norm,kineticDriftMoment10Coeff8Row3Norm,kineticDriftMoment10Coeff8Row4Norm,kineticDriftMoment10Coeff9Row1Norm,kineticDriftMoment10Coeff9Row2Norm,kineticDriftMoment10Coeff9Row3Norm,kineticDriftMoment10Coeff9Row4Norm,kineticDriftMoment10Coeff10Row1Norm,kineticDriftMoment10Coeff10Row2Norm,kineticDriftMoment10Coeff10Row3Norm,kineticDriftMoment10Coeff10Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff10Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 10 5=c} := by
  have he : kineticDriftCell h kineticCof2 10 5=kineticDriftCell h kineticCof2 10 5 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff2Row1Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff4Row2Norm,kineticDriftMoment10Coeff4Row3Norm,kineticDriftMoment10Coeff4Row4Norm,kineticDriftMoment10Coeff4Row5Norm,kineticDriftMoment10Coeff5Row2Norm,kineticDriftMoment10Coeff5Row3Norm,kineticDriftMoment10Coeff5Row4Norm,kineticDriftMoment10Coeff5Row5Norm,kineticDriftMoment10Coeff6Row2Norm,kineticDriftMoment10Coeff6Row3Norm,kineticDriftMoment10Coeff6Row4Norm,kineticDriftMoment10Coeff6Row5Norm,kineticDriftMoment10Coeff7Row2Norm,kineticDriftMoment10Coeff7Row3Norm,kineticDriftMoment10Coeff7Row4Norm,kineticDriftMoment10Coeff7Row5Norm,kineticDriftMoment10Coeff8Row2Norm,kineticDriftMoment10Coeff8Row3Norm,kineticDriftMoment10Coeff8Row4Norm,kineticDriftMoment10Coeff8Row5Norm,kineticDriftMoment10Coeff9Row2Norm,kineticDriftMoment10Coeff9Row3Norm,kineticDriftMoment10Coeff9Row4Norm,kineticDriftMoment10Coeff9Row5Norm,kineticDriftMoment10Coeff10Row2Norm,kineticDriftMoment10Coeff10Row3Norm,kineticDriftMoment10Coeff10Row4Norm,kineticDriftMoment10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff10Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 10 6=c} := by
  have he : kineticDriftCell h kineticCof2 10 6=kineticDriftCell h kineticCof2 10 6 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff2Row2Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff4Row3Norm,kineticDriftMoment10Coeff4Row4Norm,kineticDriftMoment10Coeff4Row5Norm,kineticDriftMoment10Coeff5Row3Norm,kineticDriftMoment10Coeff5Row4Norm,kineticDriftMoment10Coeff5Row5Norm,kineticDriftMoment10Coeff6Row3Norm,kineticDriftMoment10Coeff6Row4Norm,kineticDriftMoment10Coeff6Row5Norm,kineticDriftMoment10Coeff7Row3Norm,kineticDriftMoment10Coeff7Row4Norm,kineticDriftMoment10Coeff7Row5Norm,kineticDriftMoment10Coeff8Row3Norm,kineticDriftMoment10Coeff8Row4Norm,kineticDriftMoment10Coeff8Row5Norm,kineticDriftMoment10Coeff9Row3Norm,kineticDriftMoment10Coeff9Row4Norm,kineticDriftMoment10Coeff9Row5Norm,kineticDriftMoment10Coeff10Row3Norm,kineticDriftMoment10Coeff10Row4Norm,kineticDriftMoment10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff10Row7Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 10 7=c} := by
  have he : kineticDriftCell h kineticCof2 10 7=kineticDriftCell h kineticCof2 10 7 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff2Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff4Row4Norm,kineticDriftMoment10Coeff4Row5Norm,kineticDriftMoment10Coeff5Row4Norm,kineticDriftMoment10Coeff5Row5Norm,kineticDriftMoment10Coeff6Row4Norm,kineticDriftMoment10Coeff6Row5Norm,kineticDriftMoment10Coeff7Row4Norm,kineticDriftMoment10Coeff7Row5Norm,kineticDriftMoment10Coeff8Row4Norm,kineticDriftMoment10Coeff8Row5Norm,kineticDriftMoment10Coeff9Row4Norm,kineticDriftMoment10Coeff9Row5Norm,kineticDriftMoment10Coeff10Row4Norm,kineticDriftMoment10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff10Row8Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 10 8=c} := by
  have he : kineticDriftCell h kineticCof2 10 8=kineticDriftCell h kineticCof2 10 8 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff2Row4Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff4Row5Norm,kineticDriftMoment10Coeff5Row5Norm,kineticDriftMoment10Coeff6Row5Norm,kineticDriftMoment10Coeff7Row5Norm,kineticDriftMoment10Coeff8Row5Norm,kineticDriftMoment10Coeff9Row5Norm,kineticDriftMoment10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff11Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 11 0=c} := by
  have he : kineticDriftCell h kineticCof2 11 0=kineticDriftCell h kineticCof2 11 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment10Coeff5Row0Norm,kineticDriftMoment10Coeff6Row0Norm,kineticDriftMoment10Coeff7Row0Norm,kineticDriftMoment10Coeff8Row0Norm,kineticDriftMoment10Coeff9Row0Norm,kineticDriftMoment10Coeff10Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff11Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 11 1=c} := by
  have he : kineticDriftCell h kineticCof2 11 1=kineticDriftCell h kineticCof2 11 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment10Coeff5Row0Norm,kineticDriftMoment10Coeff5Row1Norm,kineticDriftMoment10Coeff6Row0Norm,kineticDriftMoment10Coeff6Row1Norm,kineticDriftMoment10Coeff7Row0Norm,kineticDriftMoment10Coeff7Row1Norm,kineticDriftMoment10Coeff8Row0Norm,kineticDriftMoment10Coeff8Row1Norm,kineticDriftMoment10Coeff9Row0Norm,kineticDriftMoment10Coeff9Row1Norm,kineticDriftMoment10Coeff10Row0Norm,kineticDriftMoment10Coeff10Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff11Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 11 2=c} := by
  have he : kineticDriftCell h kineticCof2 11 2=kineticDriftCell h kineticCof2 11 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment10Coeff5Row0Norm,kineticDriftMoment10Coeff5Row1Norm,kineticDriftMoment10Coeff5Row2Norm,kineticDriftMoment10Coeff6Row0Norm,kineticDriftMoment10Coeff6Row1Norm,kineticDriftMoment10Coeff6Row2Norm,kineticDriftMoment10Coeff7Row0Norm,kineticDriftMoment10Coeff7Row1Norm,kineticDriftMoment10Coeff7Row2Norm,kineticDriftMoment10Coeff8Row0Norm,kineticDriftMoment10Coeff8Row1Norm,kineticDriftMoment10Coeff8Row2Norm,kineticDriftMoment10Coeff9Row0Norm,kineticDriftMoment10Coeff9Row1Norm,kineticDriftMoment10Coeff9Row2Norm,kineticDriftMoment10Coeff10Row0Norm,kineticDriftMoment10Coeff10Row1Norm,kineticDriftMoment10Coeff10Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff11Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 11 3=c} := by
  have he : kineticDriftCell h kineticCof2 11 3=kineticDriftCell h kineticCof2 11 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment10Coeff5Row0Norm,kineticDriftMoment10Coeff5Row1Norm,kineticDriftMoment10Coeff5Row2Norm,kineticDriftMoment10Coeff5Row3Norm,kineticDriftMoment10Coeff6Row0Norm,kineticDriftMoment10Coeff6Row1Norm,kineticDriftMoment10Coeff6Row2Norm,kineticDriftMoment10Coeff6Row3Norm,kineticDriftMoment10Coeff7Row0Norm,kineticDriftMoment10Coeff7Row1Norm,kineticDriftMoment10Coeff7Row2Norm,kineticDriftMoment10Coeff7Row3Norm,kineticDriftMoment10Coeff8Row0Norm,kineticDriftMoment10Coeff8Row1Norm,kineticDriftMoment10Coeff8Row2Norm,kineticDriftMoment10Coeff8Row3Norm,kineticDriftMoment10Coeff9Row0Norm,kineticDriftMoment10Coeff9Row1Norm,kineticDriftMoment10Coeff9Row2Norm,kineticDriftMoment10Coeff9Row3Norm,kineticDriftMoment10Coeff10Row0Norm,kineticDriftMoment10Coeff10Row1Norm,kineticDriftMoment10Coeff10Row2Norm,kineticDriftMoment10Coeff10Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff11Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 11 4=c} := by
  have he : kineticDriftCell h kineticCof2 11 4=kineticDriftCell h kineticCof2 11 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff3Row0Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff5Row1Norm,kineticDriftMoment10Coeff5Row2Norm,kineticDriftMoment10Coeff5Row3Norm,kineticDriftMoment10Coeff5Row4Norm,kineticDriftMoment10Coeff6Row1Norm,kineticDriftMoment10Coeff6Row2Norm,kineticDriftMoment10Coeff6Row3Norm,kineticDriftMoment10Coeff6Row4Norm,kineticDriftMoment10Coeff7Row1Norm,kineticDriftMoment10Coeff7Row2Norm,kineticDriftMoment10Coeff7Row3Norm,kineticDriftMoment10Coeff7Row4Norm,kineticDriftMoment10Coeff8Row1Norm,kineticDriftMoment10Coeff8Row2Norm,kineticDriftMoment10Coeff8Row3Norm,kineticDriftMoment10Coeff8Row4Norm,kineticDriftMoment10Coeff9Row1Norm,kineticDriftMoment10Coeff9Row2Norm,kineticDriftMoment10Coeff9Row3Norm,kineticDriftMoment10Coeff9Row4Norm,kineticDriftMoment10Coeff10Row1Norm,kineticDriftMoment10Coeff10Row2Norm,kineticDriftMoment10Coeff10Row3Norm,kineticDriftMoment10Coeff10Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff11Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 11 5=c} := by
  have he : kineticDriftCell h kineticCof2 11 5=kineticDriftCell h kineticCof2 11 5 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff3Row1Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff5Row2Norm,kineticDriftMoment10Coeff5Row3Norm,kineticDriftMoment10Coeff5Row4Norm,kineticDriftMoment10Coeff5Row5Norm,kineticDriftMoment10Coeff6Row2Norm,kineticDriftMoment10Coeff6Row3Norm,kineticDriftMoment10Coeff6Row4Norm,kineticDriftMoment10Coeff6Row5Norm,kineticDriftMoment10Coeff7Row2Norm,kineticDriftMoment10Coeff7Row3Norm,kineticDriftMoment10Coeff7Row4Norm,kineticDriftMoment10Coeff7Row5Norm,kineticDriftMoment10Coeff8Row2Norm,kineticDriftMoment10Coeff8Row3Norm,kineticDriftMoment10Coeff8Row4Norm,kineticDriftMoment10Coeff8Row5Norm,kineticDriftMoment10Coeff9Row2Norm,kineticDriftMoment10Coeff9Row3Norm,kineticDriftMoment10Coeff9Row4Norm,kineticDriftMoment10Coeff9Row5Norm,kineticDriftMoment10Coeff10Row2Norm,kineticDriftMoment10Coeff10Row3Norm,kineticDriftMoment10Coeff10Row4Norm,kineticDriftMoment10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff11Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 11 6=c} := by
  have he : kineticDriftCell h kineticCof2 11 6=kineticDriftCell h kineticCof2 11 6 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff3Row2Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff5Row3Norm,kineticDriftMoment10Coeff5Row4Norm,kineticDriftMoment10Coeff5Row5Norm,kineticDriftMoment10Coeff6Row3Norm,kineticDriftMoment10Coeff6Row4Norm,kineticDriftMoment10Coeff6Row5Norm,kineticDriftMoment10Coeff7Row3Norm,kineticDriftMoment10Coeff7Row4Norm,kineticDriftMoment10Coeff7Row5Norm,kineticDriftMoment10Coeff8Row3Norm,kineticDriftMoment10Coeff8Row4Norm,kineticDriftMoment10Coeff8Row5Norm,kineticDriftMoment10Coeff9Row3Norm,kineticDriftMoment10Coeff9Row4Norm,kineticDriftMoment10Coeff9Row5Norm,kineticDriftMoment10Coeff10Row3Norm,kineticDriftMoment10Coeff10Row4Norm,kineticDriftMoment10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff11Row7Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 11 7=c} := by
  have he : kineticDriftCell h kineticCof2 11 7=kineticDriftCell h kineticCof2 11 7 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff3Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff5Row4Norm,kineticDriftMoment10Coeff5Row5Norm,kineticDriftMoment10Coeff6Row4Norm,kineticDriftMoment10Coeff6Row5Norm,kineticDriftMoment10Coeff7Row4Norm,kineticDriftMoment10Coeff7Row5Norm,kineticDriftMoment10Coeff8Row4Norm,kineticDriftMoment10Coeff8Row5Norm,kineticDriftMoment10Coeff9Row4Norm,kineticDriftMoment10Coeff9Row5Norm,kineticDriftMoment10Coeff10Row4Norm,kineticDriftMoment10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff11Row8Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 11 8=c} := by
  have he : kineticDriftCell h kineticCof2 11 8=kineticDriftCell h kineticCof2 11 8 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff3Row4Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff5Row5Norm,kineticDriftMoment10Coeff6Row5Norm,kineticDriftMoment10Coeff7Row5Norm,kineticDriftMoment10Coeff8Row5Norm,kineticDriftMoment10Coeff9Row5Norm,kineticDriftMoment10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff12Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 12 0=c} := by
  have he : kineticDriftCell h kineticCof2 12 0=kineticDriftCell h kineticCof2 12 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment10Coeff6Row0Norm,kineticDriftMoment10Coeff7Row0Norm,kineticDriftMoment10Coeff8Row0Norm,kineticDriftMoment10Coeff9Row0Norm,kineticDriftMoment10Coeff10Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff12Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 12 1=c} := by
  have he : kineticDriftCell h kineticCof2 12 1=kineticDriftCell h kineticCof2 12 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment10Coeff6Row0Norm,kineticDriftMoment10Coeff6Row1Norm,kineticDriftMoment10Coeff7Row0Norm,kineticDriftMoment10Coeff7Row1Norm,kineticDriftMoment10Coeff8Row0Norm,kineticDriftMoment10Coeff8Row1Norm,kineticDriftMoment10Coeff9Row0Norm,kineticDriftMoment10Coeff9Row1Norm,kineticDriftMoment10Coeff10Row0Norm,kineticDriftMoment10Coeff10Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff12Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 12 2=c} := by
  have he : kineticDriftCell h kineticCof2 12 2=kineticDriftCell h kineticCof2 12 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment10Coeff6Row0Norm,kineticDriftMoment10Coeff6Row1Norm,kineticDriftMoment10Coeff6Row2Norm,kineticDriftMoment10Coeff7Row0Norm,kineticDriftMoment10Coeff7Row1Norm,kineticDriftMoment10Coeff7Row2Norm,kineticDriftMoment10Coeff8Row0Norm,kineticDriftMoment10Coeff8Row1Norm,kineticDriftMoment10Coeff8Row2Norm,kineticDriftMoment10Coeff9Row0Norm,kineticDriftMoment10Coeff9Row1Norm,kineticDriftMoment10Coeff9Row2Norm,kineticDriftMoment10Coeff10Row0Norm,kineticDriftMoment10Coeff10Row1Norm,kineticDriftMoment10Coeff10Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff12Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 12 3=c} := by
  have he : kineticDriftCell h kineticCof2 12 3=kineticDriftCell h kineticCof2 12 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment10Coeff6Row0Norm,kineticDriftMoment10Coeff6Row1Norm,kineticDriftMoment10Coeff6Row2Norm,kineticDriftMoment10Coeff6Row3Norm,kineticDriftMoment10Coeff7Row0Norm,kineticDriftMoment10Coeff7Row1Norm,kineticDriftMoment10Coeff7Row2Norm,kineticDriftMoment10Coeff7Row3Norm,kineticDriftMoment10Coeff8Row0Norm,kineticDriftMoment10Coeff8Row1Norm,kineticDriftMoment10Coeff8Row2Norm,kineticDriftMoment10Coeff8Row3Norm,kineticDriftMoment10Coeff9Row0Norm,kineticDriftMoment10Coeff9Row1Norm,kineticDriftMoment10Coeff9Row2Norm,kineticDriftMoment10Coeff9Row3Norm,kineticDriftMoment10Coeff10Row0Norm,kineticDriftMoment10Coeff10Row1Norm,kineticDriftMoment10Coeff10Row2Norm,kineticDriftMoment10Coeff10Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff12Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 12 4=c} := by
  have he : kineticDriftCell h kineticCof2 12 4=kineticDriftCell h kineticCof2 12 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff4Row0Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff6Row1Norm,kineticDriftMoment10Coeff6Row2Norm,kineticDriftMoment10Coeff6Row3Norm,kineticDriftMoment10Coeff6Row4Norm,kineticDriftMoment10Coeff7Row1Norm,kineticDriftMoment10Coeff7Row2Norm,kineticDriftMoment10Coeff7Row3Norm,kineticDriftMoment10Coeff7Row4Norm,kineticDriftMoment10Coeff8Row1Norm,kineticDriftMoment10Coeff8Row2Norm,kineticDriftMoment10Coeff8Row3Norm,kineticDriftMoment10Coeff8Row4Norm,kineticDriftMoment10Coeff9Row1Norm,kineticDriftMoment10Coeff9Row2Norm,kineticDriftMoment10Coeff9Row3Norm,kineticDriftMoment10Coeff9Row4Norm,kineticDriftMoment10Coeff10Row1Norm,kineticDriftMoment10Coeff10Row2Norm,kineticDriftMoment10Coeff10Row3Norm,kineticDriftMoment10Coeff10Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff12Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 12 5=c} := by
  have he : kineticDriftCell h kineticCof2 12 5=kineticDriftCell h kineticCof2 12 5 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff4Row1Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff6Row2Norm,kineticDriftMoment10Coeff6Row3Norm,kineticDriftMoment10Coeff6Row4Norm,kineticDriftMoment10Coeff6Row5Norm,kineticDriftMoment10Coeff7Row2Norm,kineticDriftMoment10Coeff7Row3Norm,kineticDriftMoment10Coeff7Row4Norm,kineticDriftMoment10Coeff7Row5Norm,kineticDriftMoment10Coeff8Row2Norm,kineticDriftMoment10Coeff8Row3Norm,kineticDriftMoment10Coeff8Row4Norm,kineticDriftMoment10Coeff8Row5Norm,kineticDriftMoment10Coeff9Row2Norm,kineticDriftMoment10Coeff9Row3Norm,kineticDriftMoment10Coeff9Row4Norm,kineticDriftMoment10Coeff9Row5Norm,kineticDriftMoment10Coeff10Row2Norm,kineticDriftMoment10Coeff10Row3Norm,kineticDriftMoment10Coeff10Row4Norm,kineticDriftMoment10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff12Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 12 6=c} := by
  have he : kineticDriftCell h kineticCof2 12 6=kineticDriftCell h kineticCof2 12 6 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff4Row2Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff6Row3Norm,kineticDriftMoment10Coeff6Row4Norm,kineticDriftMoment10Coeff6Row5Norm,kineticDriftMoment10Coeff7Row3Norm,kineticDriftMoment10Coeff7Row4Norm,kineticDriftMoment10Coeff7Row5Norm,kineticDriftMoment10Coeff8Row3Norm,kineticDriftMoment10Coeff8Row4Norm,kineticDriftMoment10Coeff8Row5Norm,kineticDriftMoment10Coeff9Row3Norm,kineticDriftMoment10Coeff9Row4Norm,kineticDriftMoment10Coeff9Row5Norm,kineticDriftMoment10Coeff10Row3Norm,kineticDriftMoment10Coeff10Row4Norm,kineticDriftMoment10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff12Row7Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 12 7=c} := by
  have he : kineticDriftCell h kineticCof2 12 7=kineticDriftCell h kineticCof2 12 7 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff4Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff6Row4Norm,kineticDriftMoment10Coeff6Row5Norm,kineticDriftMoment10Coeff7Row4Norm,kineticDriftMoment10Coeff7Row5Norm,kineticDriftMoment10Coeff8Row4Norm,kineticDriftMoment10Coeff8Row5Norm,kineticDriftMoment10Coeff9Row4Norm,kineticDriftMoment10Coeff9Row5Norm,kineticDriftMoment10Coeff10Row4Norm,kineticDriftMoment10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff12Row8Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 12 8=c} := by
  have he : kineticDriftCell h kineticCof2 12 8=kineticDriftCell h kineticCof2 12 8 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff4Row4Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff6Row5Norm,kineticDriftMoment10Coeff7Row5Norm,kineticDriftMoment10Coeff8Row5Norm,kineticDriftMoment10Coeff9Row5Norm,kineticDriftMoment10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff13Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 13 0=c} := by
  have he : kineticDriftCell h kineticCof2 13 0=kineticDriftCell h kineticCof2 13 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment10Coeff7Row0Norm,kineticDriftMoment10Coeff8Row0Norm,kineticDriftMoment10Coeff9Row0Norm,kineticDriftMoment10Coeff10Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff13Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 13 1=c} := by
  have he : kineticDriftCell h kineticCof2 13 1=kineticDriftCell h kineticCof2 13 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment10Coeff7Row0Norm,kineticDriftMoment10Coeff7Row1Norm,kineticDriftMoment10Coeff8Row0Norm,kineticDriftMoment10Coeff8Row1Norm,kineticDriftMoment10Coeff9Row0Norm,kineticDriftMoment10Coeff9Row1Norm,kineticDriftMoment10Coeff10Row0Norm,kineticDriftMoment10Coeff10Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff13Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 13 2=c} := by
  have he : kineticDriftCell h kineticCof2 13 2=kineticDriftCell h kineticCof2 13 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment10Coeff7Row0Norm,kineticDriftMoment10Coeff7Row1Norm,kineticDriftMoment10Coeff7Row2Norm,kineticDriftMoment10Coeff8Row0Norm,kineticDriftMoment10Coeff8Row1Norm,kineticDriftMoment10Coeff8Row2Norm,kineticDriftMoment10Coeff9Row0Norm,kineticDriftMoment10Coeff9Row1Norm,kineticDriftMoment10Coeff9Row2Norm,kineticDriftMoment10Coeff10Row0Norm,kineticDriftMoment10Coeff10Row1Norm,kineticDriftMoment10Coeff10Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff13Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 13 3=c} := by
  have he : kineticDriftCell h kineticCof2 13 3=kineticDriftCell h kineticCof2 13 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment10Coeff7Row0Norm,kineticDriftMoment10Coeff7Row1Norm,kineticDriftMoment10Coeff7Row2Norm,kineticDriftMoment10Coeff7Row3Norm,kineticDriftMoment10Coeff8Row0Norm,kineticDriftMoment10Coeff8Row1Norm,kineticDriftMoment10Coeff8Row2Norm,kineticDriftMoment10Coeff8Row3Norm,kineticDriftMoment10Coeff9Row0Norm,kineticDriftMoment10Coeff9Row1Norm,kineticDriftMoment10Coeff9Row2Norm,kineticDriftMoment10Coeff9Row3Norm,kineticDriftMoment10Coeff10Row0Norm,kineticDriftMoment10Coeff10Row1Norm,kineticDriftMoment10Coeff10Row2Norm,kineticDriftMoment10Coeff10Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff13Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 13 4=c} := by
  have he : kineticDriftCell h kineticCof2 13 4=kineticDriftCell h kineticCof2 13 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff5Row0Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff7Row1Norm,kineticDriftMoment10Coeff7Row2Norm,kineticDriftMoment10Coeff7Row3Norm,kineticDriftMoment10Coeff7Row4Norm,kineticDriftMoment10Coeff8Row1Norm,kineticDriftMoment10Coeff8Row2Norm,kineticDriftMoment10Coeff8Row3Norm,kineticDriftMoment10Coeff8Row4Norm,kineticDriftMoment10Coeff9Row1Norm,kineticDriftMoment10Coeff9Row2Norm,kineticDriftMoment10Coeff9Row3Norm,kineticDriftMoment10Coeff9Row4Norm,kineticDriftMoment10Coeff10Row1Norm,kineticDriftMoment10Coeff10Row2Norm,kineticDriftMoment10Coeff10Row3Norm,kineticDriftMoment10Coeff10Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff13Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 13 5=c} := by
  have he : kineticDriftCell h kineticCof2 13 5=kineticDriftCell h kineticCof2 13 5 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff5Row1Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff7Row2Norm,kineticDriftMoment10Coeff7Row3Norm,kineticDriftMoment10Coeff7Row4Norm,kineticDriftMoment10Coeff7Row5Norm,kineticDriftMoment10Coeff8Row2Norm,kineticDriftMoment10Coeff8Row3Norm,kineticDriftMoment10Coeff8Row4Norm,kineticDriftMoment10Coeff8Row5Norm,kineticDriftMoment10Coeff9Row2Norm,kineticDriftMoment10Coeff9Row3Norm,kineticDriftMoment10Coeff9Row4Norm,kineticDriftMoment10Coeff9Row5Norm,kineticDriftMoment10Coeff10Row2Norm,kineticDriftMoment10Coeff10Row3Norm,kineticDriftMoment10Coeff10Row4Norm,kineticDriftMoment10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff13Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 13 6=c} := by
  have he : kineticDriftCell h kineticCof2 13 6=kineticDriftCell h kineticCof2 13 6 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff5Row2Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff7Row3Norm,kineticDriftMoment10Coeff7Row4Norm,kineticDriftMoment10Coeff7Row5Norm,kineticDriftMoment10Coeff8Row3Norm,kineticDriftMoment10Coeff8Row4Norm,kineticDriftMoment10Coeff8Row5Norm,kineticDriftMoment10Coeff9Row3Norm,kineticDriftMoment10Coeff9Row4Norm,kineticDriftMoment10Coeff9Row5Norm,kineticDriftMoment10Coeff10Row3Norm,kineticDriftMoment10Coeff10Row4Norm,kineticDriftMoment10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff13Row7Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 13 7=c} := by
  have he : kineticDriftCell h kineticCof2 13 7=kineticDriftCell h kineticCof2 13 7 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff5Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff7Row4Norm,kineticDriftMoment10Coeff7Row5Norm,kineticDriftMoment10Coeff8Row4Norm,kineticDriftMoment10Coeff8Row5Norm,kineticDriftMoment10Coeff9Row4Norm,kineticDriftMoment10Coeff9Row5Norm,kineticDriftMoment10Coeff10Row4Norm,kineticDriftMoment10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff13Row8Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 13 8=c} := by
  have he : kineticDriftCell h kineticCof2 13 8=kineticDriftCell h kineticCof2 13 8 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff5Row4Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff7Row5Norm,kineticDriftMoment10Coeff8Row5Norm,kineticDriftMoment10Coeff9Row5Norm,kineticDriftMoment10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff14Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 14 0=c} := by
  have he : kineticDriftCell h kineticCof2 14 0=kineticDriftCell h kineticCof2 14 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment10Coeff8Row0Norm,kineticDriftMoment10Coeff9Row0Norm,kineticDriftMoment10Coeff10Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff14Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 14 1=c} := by
  have he : kineticDriftCell h kineticCof2 14 1=kineticDriftCell h kineticCof2 14 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment10Coeff8Row0Norm,kineticDriftMoment10Coeff8Row1Norm,kineticDriftMoment10Coeff9Row0Norm,kineticDriftMoment10Coeff9Row1Norm,kineticDriftMoment10Coeff10Row0Norm,kineticDriftMoment10Coeff10Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff14Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 14 2=c} := by
  have he : kineticDriftCell h kineticCof2 14 2=kineticDriftCell h kineticCof2 14 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment10Coeff8Row0Norm,kineticDriftMoment10Coeff8Row1Norm,kineticDriftMoment10Coeff8Row2Norm,kineticDriftMoment10Coeff9Row0Norm,kineticDriftMoment10Coeff9Row1Norm,kineticDriftMoment10Coeff9Row2Norm,kineticDriftMoment10Coeff10Row0Norm,kineticDriftMoment10Coeff10Row1Norm,kineticDriftMoment10Coeff10Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff14Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 14 3=c} := by
  have he : kineticDriftCell h kineticCof2 14 3=kineticDriftCell h kineticCof2 14 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment10Coeff8Row0Norm,kineticDriftMoment10Coeff8Row1Norm,kineticDriftMoment10Coeff8Row2Norm,kineticDriftMoment10Coeff8Row3Norm,kineticDriftMoment10Coeff9Row0Norm,kineticDriftMoment10Coeff9Row1Norm,kineticDriftMoment10Coeff9Row2Norm,kineticDriftMoment10Coeff9Row3Norm,kineticDriftMoment10Coeff10Row0Norm,kineticDriftMoment10Coeff10Row1Norm,kineticDriftMoment10Coeff10Row2Norm,kineticDriftMoment10Coeff10Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff14Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 14 4=c} := by
  have he : kineticDriftCell h kineticCof2 14 4=kineticDriftCell h kineticCof2 14 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff6Row0Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff8Row1Norm,kineticDriftMoment10Coeff8Row2Norm,kineticDriftMoment10Coeff8Row3Norm,kineticDriftMoment10Coeff8Row4Norm,kineticDriftMoment10Coeff9Row1Norm,kineticDriftMoment10Coeff9Row2Norm,kineticDriftMoment10Coeff9Row3Norm,kineticDriftMoment10Coeff9Row4Norm,kineticDriftMoment10Coeff10Row1Norm,kineticDriftMoment10Coeff10Row2Norm,kineticDriftMoment10Coeff10Row3Norm,kineticDriftMoment10Coeff10Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff14Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 14 5=c} := by
  have he : kineticDriftCell h kineticCof2 14 5=kineticDriftCell h kineticCof2 14 5 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff6Row1Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff8Row2Norm,kineticDriftMoment10Coeff8Row3Norm,kineticDriftMoment10Coeff8Row4Norm,kineticDriftMoment10Coeff8Row5Norm,kineticDriftMoment10Coeff9Row2Norm,kineticDriftMoment10Coeff9Row3Norm,kineticDriftMoment10Coeff9Row4Norm,kineticDriftMoment10Coeff9Row5Norm,kineticDriftMoment10Coeff10Row2Norm,kineticDriftMoment10Coeff10Row3Norm,kineticDriftMoment10Coeff10Row4Norm,kineticDriftMoment10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff14Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 14 6=c} := by
  have he : kineticDriftCell h kineticCof2 14 6=kineticDriftCell h kineticCof2 14 6 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff6Row2Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff8Row3Norm,kineticDriftMoment10Coeff8Row4Norm,kineticDriftMoment10Coeff8Row5Norm,kineticDriftMoment10Coeff9Row3Norm,kineticDriftMoment10Coeff9Row4Norm,kineticDriftMoment10Coeff9Row5Norm,kineticDriftMoment10Coeff10Row3Norm,kineticDriftMoment10Coeff10Row4Norm,kineticDriftMoment10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff14Row7Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 14 7=c} := by
  have he : kineticDriftCell h kineticCof2 14 7=kineticDriftCell h kineticCof2 14 7 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff8Row4Norm,kineticDriftMoment10Coeff8Row5Norm,kineticDriftMoment10Coeff9Row4Norm,kineticDriftMoment10Coeff9Row5Norm,kineticDriftMoment10Coeff10Row4Norm,kineticDriftMoment10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff14Row8Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 14 8=c} := by
  have he : kineticDriftCell h kineticCof2 14 8=kineticDriftCell h kineticCof2 14 8 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff6Row4Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff8Row5Norm,kineticDriftMoment10Coeff9Row5Norm,kineticDriftMoment10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff15Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 15 0=c} := by
  have he : kineticDriftCell h kineticCof2 15 0=kineticDriftCell h kineticCof2 15 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment10Coeff9Row0Norm,kineticDriftMoment10Coeff10Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff15Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 15 1=c} := by
  have he : kineticDriftCell h kineticCof2 15 1=kineticDriftCell h kineticCof2 15 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment10Coeff9Row0Norm,kineticDriftMoment10Coeff9Row1Norm,kineticDriftMoment10Coeff10Row0Norm,kineticDriftMoment10Coeff10Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff15Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 15 2=c} := by
  have he : kineticDriftCell h kineticCof2 15 2=kineticDriftCell h kineticCof2 15 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment10Coeff9Row0Norm,kineticDriftMoment10Coeff9Row1Norm,kineticDriftMoment10Coeff9Row2Norm,kineticDriftMoment10Coeff10Row0Norm,kineticDriftMoment10Coeff10Row1Norm,kineticDriftMoment10Coeff10Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff15Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 15 3=c} := by
  have he : kineticDriftCell h kineticCof2 15 3=kineticDriftCell h kineticCof2 15 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment10Coeff9Row0Norm,kineticDriftMoment10Coeff9Row1Norm,kineticDriftMoment10Coeff9Row2Norm,kineticDriftMoment10Coeff9Row3Norm,kineticDriftMoment10Coeff10Row0Norm,kineticDriftMoment10Coeff10Row1Norm,kineticDriftMoment10Coeff10Row2Norm,kineticDriftMoment10Coeff10Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff15Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 15 4=c} := by
  have he : kineticDriftCell h kineticCof2 15 4=kineticDriftCell h kineticCof2 15 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff7Row0Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff9Row1Norm,kineticDriftMoment10Coeff9Row2Norm,kineticDriftMoment10Coeff9Row3Norm,kineticDriftMoment10Coeff9Row4Norm,kineticDriftMoment10Coeff10Row1Norm,kineticDriftMoment10Coeff10Row2Norm,kineticDriftMoment10Coeff10Row3Norm,kineticDriftMoment10Coeff10Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff15Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 15 5=c} := by
  have he : kineticDriftCell h kineticCof2 15 5=kineticDriftCell h kineticCof2 15 5 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff7Row1Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff9Row2Norm,kineticDriftMoment10Coeff9Row3Norm,kineticDriftMoment10Coeff9Row4Norm,kineticDriftMoment10Coeff9Row5Norm,kineticDriftMoment10Coeff10Row2Norm,kineticDriftMoment10Coeff10Row3Norm,kineticDriftMoment10Coeff10Row4Norm,kineticDriftMoment10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff15Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 15 6=c} := by
  have he : kineticDriftCell h kineticCof2 15 6=kineticDriftCell h kineticCof2 15 6 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff7Row2Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff9Row3Norm,kineticDriftMoment10Coeff9Row4Norm,kineticDriftMoment10Coeff9Row5Norm,kineticDriftMoment10Coeff10Row3Norm,kineticDriftMoment10Coeff10Row4Norm,kineticDriftMoment10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff15Row7Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 15 7=c} := by
  have he : kineticDriftCell h kineticCof2 15 7=kineticDriftCell h kineticCof2 15 7 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff7Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff9Row4Norm,kineticDriftMoment10Coeff9Row5Norm,kineticDriftMoment10Coeff10Row4Norm,kineticDriftMoment10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff15Row8Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 15 8=c} := by
  have he : kineticDriftCell h kineticCof2 15 8=kineticDriftCell h kineticCof2 15 8 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff7Row4Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff9Row5Norm,kineticDriftMoment10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff16Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 16 0=c} := by
  have he : kineticDriftCell h kineticCof2 16 0=kineticDriftCell h kineticCof2 16 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment10Coeff10Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff16Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 16 1=c} := by
  have he : kineticDriftCell h kineticCof2 16 1=kineticDriftCell h kineticCof2 16 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment10Coeff10Row0Norm,kineticDriftMoment10Coeff10Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff16Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 16 2=c} := by
  have he : kineticDriftCell h kineticCof2 16 2=kineticDriftCell h kineticCof2 16 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment10Coeff10Row0Norm,kineticDriftMoment10Coeff10Row1Norm,kineticDriftMoment10Coeff10Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff16Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 16 3=c} := by
  have he : kineticDriftCell h kineticCof2 16 3=kineticDriftCell h kineticCof2 16 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment10Coeff10Row0Norm,kineticDriftMoment10Coeff10Row1Norm,kineticDriftMoment10Coeff10Row2Norm,kineticDriftMoment10Coeff10Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff16Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 16 4=c} := by
  have he : kineticDriftCell h kineticCof2 16 4=kineticDriftCell h kineticCof2 16 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff8Row0Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff10Row1Norm,kineticDriftMoment10Coeff10Row2Norm,kineticDriftMoment10Coeff10Row3Norm,kineticDriftMoment10Coeff10Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff16Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 16 5=c} := by
  have he : kineticDriftCell h kineticCof2 16 5=kineticDriftCell h kineticCof2 16 5 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff8Row1Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff10Row2Norm,kineticDriftMoment10Coeff10Row3Norm,kineticDriftMoment10Coeff10Row4Norm,kineticDriftMoment10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff16Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 16 6=c} := by
  have he : kineticDriftCell h kineticCof2 16 6=kineticDriftCell h kineticCof2 16 6 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff8Row2Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff10Row3Norm,kineticDriftMoment10Coeff10Row4Norm,kineticDriftMoment10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff16Row7Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 16 7=c} := by
  have he : kineticDriftCell h kineticCof2 16 7=kineticDriftCell h kineticCof2 16 7 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff8Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff10Row4Norm,kineticDriftMoment10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof2Coeff16Row8Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof2 16 8=c} := by
  have he : kineticDriftCell h kineticCof2 16 8=kineticDriftCell h kineticCof2 16 8 := rfl
  conv at he =>
    rhs
    rw [kineticCof2_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment6_coeff,kineticMoment8_coeff,kineticMoment10_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows,kineticDriftMoment8Coeff0_rows,kineticDriftMoment8Coeff1_rows,kineticDriftMoment8Coeff2_rows,kineticDriftMoment8Coeff3_rows,kineticDriftMoment8Coeff4_rows,kineticDriftMoment8Coeff5_rows,kineticDriftMoment8Coeff6_rows,kineticDriftMoment8Coeff7_rows,kineticDriftMoment8Coeff8_rows,kineticDriftMoment10Coeff0_rows,kineticDriftMoment10Coeff1_rows,kineticDriftMoment10Coeff2_rows,kineticDriftMoment10Coeff3_rows,kineticDriftMoment10Coeff4_rows,kineticDriftMoment10Coeff5_rows,kineticDriftMoment10Coeff6_rows,kineticDriftMoment10Coeff7_rows,kineticDriftMoment10Coeff8_rows,kineticDriftMoment10Coeff9_rows,kineticDriftMoment10Coeff10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment6Coeff6Row3Norm,kineticDriftMoment8Coeff8Row4Norm,kineticDriftMoment10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩


def kineticDriftCof2Row0 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof2Coeff0Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof2Coeff0Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof2Coeff0Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof2Coeff0Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof2Coeff0Row4Norm h).val else 0) + (if b=5 then (kineticDriftCof2Coeff0Row5Norm h).val else 0) + (if b=6 then (kineticDriftCof2Coeff0Row6Norm h).val else 0) + (if b=7 then (kineticDriftCof2Coeff0Row7Norm h).val else 0) + (if b=8 then (kineticDriftCof2Coeff0Row8Norm h).val else 0)

theorem kineticDriftCof2Coeff0_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof2 0 b=kineticDriftCof2Row0 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof2.coeff 0))
    (n := 9) (by have := kineticCof2_drift_degree h 0; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof2.coeff 0)).coeff 0=(kineticDriftCof2Coeff0Row0Norm h).val :=
    (kineticDriftCof2Coeff0Row0Norm h).property
  have h1 : (driftReader h (kineticCof2.coeff 0)).coeff 1=(kineticDriftCof2Coeff0Row1Norm h).val :=
    (kineticDriftCof2Coeff0Row1Norm h).property
  have h2 : (driftReader h (kineticCof2.coeff 0)).coeff 2=(kineticDriftCof2Coeff0Row2Norm h).val :=
    (kineticDriftCof2Coeff0Row2Norm h).property
  have h3 : (driftReader h (kineticCof2.coeff 0)).coeff 3=(kineticDriftCof2Coeff0Row3Norm h).val :=
    (kineticDriftCof2Coeff0Row3Norm h).property
  have h4 : (driftReader h (kineticCof2.coeff 0)).coeff 4=(kineticDriftCof2Coeff0Row4Norm h).val :=
    (kineticDriftCof2Coeff0Row4Norm h).property
  have h5 : (driftReader h (kineticCof2.coeff 0)).coeff 5=(kineticDriftCof2Coeff0Row5Norm h).val :=
    (kineticDriftCof2Coeff0Row5Norm h).property
  have h6 : (driftReader h (kineticCof2.coeff 0)).coeff 6=(kineticDriftCof2Coeff0Row6Norm h).val :=
    (kineticDriftCof2Coeff0Row6Norm h).property
  have h7 : (driftReader h (kineticCof2.coeff 0)).coeff 7=(kineticDriftCof2Coeff0Row7Norm h).val :=
    (kineticDriftCof2Coeff0Row7Norm h).property
  have h8 : (driftReader h (kineticCof2.coeff 0)).coeff 8=(kineticDriftCof2Coeff0Row8Norm h).val :=
    (kineticDriftCof2Coeff0Row8Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof2Row0,h0,h1,h2,h3,h4,h5,h6,h7,h8] using he

def kineticDriftCof2Row1 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof2Coeff1Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof2Coeff1Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof2Coeff1Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof2Coeff1Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof2Coeff1Row4Norm h).val else 0) + (if b=5 then (kineticDriftCof2Coeff1Row5Norm h).val else 0) + (if b=6 then (kineticDriftCof2Coeff1Row6Norm h).val else 0) + (if b=7 then (kineticDriftCof2Coeff1Row7Norm h).val else 0) + (if b=8 then (kineticDriftCof2Coeff1Row8Norm h).val else 0)

theorem kineticDriftCof2Coeff1_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof2 1 b=kineticDriftCof2Row1 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof2.coeff 1))
    (n := 9) (by have := kineticCof2_drift_degree h 1; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof2.coeff 1)).coeff 0=(kineticDriftCof2Coeff1Row0Norm h).val :=
    (kineticDriftCof2Coeff1Row0Norm h).property
  have h1 : (driftReader h (kineticCof2.coeff 1)).coeff 1=(kineticDriftCof2Coeff1Row1Norm h).val :=
    (kineticDriftCof2Coeff1Row1Norm h).property
  have h2 : (driftReader h (kineticCof2.coeff 1)).coeff 2=(kineticDriftCof2Coeff1Row2Norm h).val :=
    (kineticDriftCof2Coeff1Row2Norm h).property
  have h3 : (driftReader h (kineticCof2.coeff 1)).coeff 3=(kineticDriftCof2Coeff1Row3Norm h).val :=
    (kineticDriftCof2Coeff1Row3Norm h).property
  have h4 : (driftReader h (kineticCof2.coeff 1)).coeff 4=(kineticDriftCof2Coeff1Row4Norm h).val :=
    (kineticDriftCof2Coeff1Row4Norm h).property
  have h5 : (driftReader h (kineticCof2.coeff 1)).coeff 5=(kineticDriftCof2Coeff1Row5Norm h).val :=
    (kineticDriftCof2Coeff1Row5Norm h).property
  have h6 : (driftReader h (kineticCof2.coeff 1)).coeff 6=(kineticDriftCof2Coeff1Row6Norm h).val :=
    (kineticDriftCof2Coeff1Row6Norm h).property
  have h7 : (driftReader h (kineticCof2.coeff 1)).coeff 7=(kineticDriftCof2Coeff1Row7Norm h).val :=
    (kineticDriftCof2Coeff1Row7Norm h).property
  have h8 : (driftReader h (kineticCof2.coeff 1)).coeff 8=(kineticDriftCof2Coeff1Row8Norm h).val :=
    (kineticDriftCof2Coeff1Row8Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof2Row1,h0,h1,h2,h3,h4,h5,h6,h7,h8] using he

def kineticDriftCof2Row2 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof2Coeff2Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof2Coeff2Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof2Coeff2Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof2Coeff2Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof2Coeff2Row4Norm h).val else 0) + (if b=5 then (kineticDriftCof2Coeff2Row5Norm h).val else 0) + (if b=6 then (kineticDriftCof2Coeff2Row6Norm h).val else 0) + (if b=7 then (kineticDriftCof2Coeff2Row7Norm h).val else 0) + (if b=8 then (kineticDriftCof2Coeff2Row8Norm h).val else 0)

theorem kineticDriftCof2Coeff2_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof2 2 b=kineticDriftCof2Row2 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof2.coeff 2))
    (n := 9) (by have := kineticCof2_drift_degree h 2; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof2.coeff 2)).coeff 0=(kineticDriftCof2Coeff2Row0Norm h).val :=
    (kineticDriftCof2Coeff2Row0Norm h).property
  have h1 : (driftReader h (kineticCof2.coeff 2)).coeff 1=(kineticDriftCof2Coeff2Row1Norm h).val :=
    (kineticDriftCof2Coeff2Row1Norm h).property
  have h2 : (driftReader h (kineticCof2.coeff 2)).coeff 2=(kineticDriftCof2Coeff2Row2Norm h).val :=
    (kineticDriftCof2Coeff2Row2Norm h).property
  have h3 : (driftReader h (kineticCof2.coeff 2)).coeff 3=(kineticDriftCof2Coeff2Row3Norm h).val :=
    (kineticDriftCof2Coeff2Row3Norm h).property
  have h4 : (driftReader h (kineticCof2.coeff 2)).coeff 4=(kineticDriftCof2Coeff2Row4Norm h).val :=
    (kineticDriftCof2Coeff2Row4Norm h).property
  have h5 : (driftReader h (kineticCof2.coeff 2)).coeff 5=(kineticDriftCof2Coeff2Row5Norm h).val :=
    (kineticDriftCof2Coeff2Row5Norm h).property
  have h6 : (driftReader h (kineticCof2.coeff 2)).coeff 6=(kineticDriftCof2Coeff2Row6Norm h).val :=
    (kineticDriftCof2Coeff2Row6Norm h).property
  have h7 : (driftReader h (kineticCof2.coeff 2)).coeff 7=(kineticDriftCof2Coeff2Row7Norm h).val :=
    (kineticDriftCof2Coeff2Row7Norm h).property
  have h8 : (driftReader h (kineticCof2.coeff 2)).coeff 8=(kineticDriftCof2Coeff2Row8Norm h).val :=
    (kineticDriftCof2Coeff2Row8Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof2Row2,h0,h1,h2,h3,h4,h5,h6,h7,h8] using he

def kineticDriftCof2Row3 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof2Coeff3Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof2Coeff3Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof2Coeff3Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof2Coeff3Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof2Coeff3Row4Norm h).val else 0) + (if b=5 then (kineticDriftCof2Coeff3Row5Norm h).val else 0) + (if b=6 then (kineticDriftCof2Coeff3Row6Norm h).val else 0) + (if b=7 then (kineticDriftCof2Coeff3Row7Norm h).val else 0) + (if b=8 then (kineticDriftCof2Coeff3Row8Norm h).val else 0)

theorem kineticDriftCof2Coeff3_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof2 3 b=kineticDriftCof2Row3 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof2.coeff 3))
    (n := 9) (by have := kineticCof2_drift_degree h 3; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof2.coeff 3)).coeff 0=(kineticDriftCof2Coeff3Row0Norm h).val :=
    (kineticDriftCof2Coeff3Row0Norm h).property
  have h1 : (driftReader h (kineticCof2.coeff 3)).coeff 1=(kineticDriftCof2Coeff3Row1Norm h).val :=
    (kineticDriftCof2Coeff3Row1Norm h).property
  have h2 : (driftReader h (kineticCof2.coeff 3)).coeff 2=(kineticDriftCof2Coeff3Row2Norm h).val :=
    (kineticDriftCof2Coeff3Row2Norm h).property
  have h3 : (driftReader h (kineticCof2.coeff 3)).coeff 3=(kineticDriftCof2Coeff3Row3Norm h).val :=
    (kineticDriftCof2Coeff3Row3Norm h).property
  have h4 : (driftReader h (kineticCof2.coeff 3)).coeff 4=(kineticDriftCof2Coeff3Row4Norm h).val :=
    (kineticDriftCof2Coeff3Row4Norm h).property
  have h5 : (driftReader h (kineticCof2.coeff 3)).coeff 5=(kineticDriftCof2Coeff3Row5Norm h).val :=
    (kineticDriftCof2Coeff3Row5Norm h).property
  have h6 : (driftReader h (kineticCof2.coeff 3)).coeff 6=(kineticDriftCof2Coeff3Row6Norm h).val :=
    (kineticDriftCof2Coeff3Row6Norm h).property
  have h7 : (driftReader h (kineticCof2.coeff 3)).coeff 7=(kineticDriftCof2Coeff3Row7Norm h).val :=
    (kineticDriftCof2Coeff3Row7Norm h).property
  have h8 : (driftReader h (kineticCof2.coeff 3)).coeff 8=(kineticDriftCof2Coeff3Row8Norm h).val :=
    (kineticDriftCof2Coeff3Row8Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof2Row3,h0,h1,h2,h3,h4,h5,h6,h7,h8] using he

def kineticDriftCof2Row4 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof2Coeff4Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof2Coeff4Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof2Coeff4Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof2Coeff4Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof2Coeff4Row4Norm h).val else 0) + (if b=5 then (kineticDriftCof2Coeff4Row5Norm h).val else 0) + (if b=6 then (kineticDriftCof2Coeff4Row6Norm h).val else 0) + (if b=7 then (kineticDriftCof2Coeff4Row7Norm h).val else 0) + (if b=8 then (kineticDriftCof2Coeff4Row8Norm h).val else 0)

theorem kineticDriftCof2Coeff4_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof2 4 b=kineticDriftCof2Row4 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof2.coeff 4))
    (n := 9) (by have := kineticCof2_drift_degree h 4; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof2.coeff 4)).coeff 0=(kineticDriftCof2Coeff4Row0Norm h).val :=
    (kineticDriftCof2Coeff4Row0Norm h).property
  have h1 : (driftReader h (kineticCof2.coeff 4)).coeff 1=(kineticDriftCof2Coeff4Row1Norm h).val :=
    (kineticDriftCof2Coeff4Row1Norm h).property
  have h2 : (driftReader h (kineticCof2.coeff 4)).coeff 2=(kineticDriftCof2Coeff4Row2Norm h).val :=
    (kineticDriftCof2Coeff4Row2Norm h).property
  have h3 : (driftReader h (kineticCof2.coeff 4)).coeff 3=(kineticDriftCof2Coeff4Row3Norm h).val :=
    (kineticDriftCof2Coeff4Row3Norm h).property
  have h4 : (driftReader h (kineticCof2.coeff 4)).coeff 4=(kineticDriftCof2Coeff4Row4Norm h).val :=
    (kineticDriftCof2Coeff4Row4Norm h).property
  have h5 : (driftReader h (kineticCof2.coeff 4)).coeff 5=(kineticDriftCof2Coeff4Row5Norm h).val :=
    (kineticDriftCof2Coeff4Row5Norm h).property
  have h6 : (driftReader h (kineticCof2.coeff 4)).coeff 6=(kineticDriftCof2Coeff4Row6Norm h).val :=
    (kineticDriftCof2Coeff4Row6Norm h).property
  have h7 : (driftReader h (kineticCof2.coeff 4)).coeff 7=(kineticDriftCof2Coeff4Row7Norm h).val :=
    (kineticDriftCof2Coeff4Row7Norm h).property
  have h8 : (driftReader h (kineticCof2.coeff 4)).coeff 8=(kineticDriftCof2Coeff4Row8Norm h).val :=
    (kineticDriftCof2Coeff4Row8Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof2Row4,h0,h1,h2,h3,h4,h5,h6,h7,h8] using he

def kineticDriftCof2Row5 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof2Coeff5Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof2Coeff5Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof2Coeff5Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof2Coeff5Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof2Coeff5Row4Norm h).val else 0) + (if b=5 then (kineticDriftCof2Coeff5Row5Norm h).val else 0) + (if b=6 then (kineticDriftCof2Coeff5Row6Norm h).val else 0) + (if b=7 then (kineticDriftCof2Coeff5Row7Norm h).val else 0) + (if b=8 then (kineticDriftCof2Coeff5Row8Norm h).val else 0)

theorem kineticDriftCof2Coeff5_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof2 5 b=kineticDriftCof2Row5 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof2.coeff 5))
    (n := 9) (by have := kineticCof2_drift_degree h 5; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof2.coeff 5)).coeff 0=(kineticDriftCof2Coeff5Row0Norm h).val :=
    (kineticDriftCof2Coeff5Row0Norm h).property
  have h1 : (driftReader h (kineticCof2.coeff 5)).coeff 1=(kineticDriftCof2Coeff5Row1Norm h).val :=
    (kineticDriftCof2Coeff5Row1Norm h).property
  have h2 : (driftReader h (kineticCof2.coeff 5)).coeff 2=(kineticDriftCof2Coeff5Row2Norm h).val :=
    (kineticDriftCof2Coeff5Row2Norm h).property
  have h3 : (driftReader h (kineticCof2.coeff 5)).coeff 3=(kineticDriftCof2Coeff5Row3Norm h).val :=
    (kineticDriftCof2Coeff5Row3Norm h).property
  have h4 : (driftReader h (kineticCof2.coeff 5)).coeff 4=(kineticDriftCof2Coeff5Row4Norm h).val :=
    (kineticDriftCof2Coeff5Row4Norm h).property
  have h5 : (driftReader h (kineticCof2.coeff 5)).coeff 5=(kineticDriftCof2Coeff5Row5Norm h).val :=
    (kineticDriftCof2Coeff5Row5Norm h).property
  have h6 : (driftReader h (kineticCof2.coeff 5)).coeff 6=(kineticDriftCof2Coeff5Row6Norm h).val :=
    (kineticDriftCof2Coeff5Row6Norm h).property
  have h7 : (driftReader h (kineticCof2.coeff 5)).coeff 7=(kineticDriftCof2Coeff5Row7Norm h).val :=
    (kineticDriftCof2Coeff5Row7Norm h).property
  have h8 : (driftReader h (kineticCof2.coeff 5)).coeff 8=(kineticDriftCof2Coeff5Row8Norm h).val :=
    (kineticDriftCof2Coeff5Row8Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof2Row5,h0,h1,h2,h3,h4,h5,h6,h7,h8] using he

def kineticDriftCof2Row6 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof2Coeff6Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof2Coeff6Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof2Coeff6Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof2Coeff6Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof2Coeff6Row4Norm h).val else 0) + (if b=5 then (kineticDriftCof2Coeff6Row5Norm h).val else 0) + (if b=6 then (kineticDriftCof2Coeff6Row6Norm h).val else 0) + (if b=7 then (kineticDriftCof2Coeff6Row7Norm h).val else 0) + (if b=8 then (kineticDriftCof2Coeff6Row8Norm h).val else 0)

theorem kineticDriftCof2Coeff6_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof2 6 b=kineticDriftCof2Row6 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof2.coeff 6))
    (n := 9) (by have := kineticCof2_drift_degree h 6; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof2.coeff 6)).coeff 0=(kineticDriftCof2Coeff6Row0Norm h).val :=
    (kineticDriftCof2Coeff6Row0Norm h).property
  have h1 : (driftReader h (kineticCof2.coeff 6)).coeff 1=(kineticDriftCof2Coeff6Row1Norm h).val :=
    (kineticDriftCof2Coeff6Row1Norm h).property
  have h2 : (driftReader h (kineticCof2.coeff 6)).coeff 2=(kineticDriftCof2Coeff6Row2Norm h).val :=
    (kineticDriftCof2Coeff6Row2Norm h).property
  have h3 : (driftReader h (kineticCof2.coeff 6)).coeff 3=(kineticDriftCof2Coeff6Row3Norm h).val :=
    (kineticDriftCof2Coeff6Row3Norm h).property
  have h4 : (driftReader h (kineticCof2.coeff 6)).coeff 4=(kineticDriftCof2Coeff6Row4Norm h).val :=
    (kineticDriftCof2Coeff6Row4Norm h).property
  have h5 : (driftReader h (kineticCof2.coeff 6)).coeff 5=(kineticDriftCof2Coeff6Row5Norm h).val :=
    (kineticDriftCof2Coeff6Row5Norm h).property
  have h6 : (driftReader h (kineticCof2.coeff 6)).coeff 6=(kineticDriftCof2Coeff6Row6Norm h).val :=
    (kineticDriftCof2Coeff6Row6Norm h).property
  have h7 : (driftReader h (kineticCof2.coeff 6)).coeff 7=(kineticDriftCof2Coeff6Row7Norm h).val :=
    (kineticDriftCof2Coeff6Row7Norm h).property
  have h8 : (driftReader h (kineticCof2.coeff 6)).coeff 8=(kineticDriftCof2Coeff6Row8Norm h).val :=
    (kineticDriftCof2Coeff6Row8Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof2Row6,h0,h1,h2,h3,h4,h5,h6,h7,h8] using he

def kineticDriftCof2Row7 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof2Coeff7Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof2Coeff7Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof2Coeff7Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof2Coeff7Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof2Coeff7Row4Norm h).val else 0) + (if b=5 then (kineticDriftCof2Coeff7Row5Norm h).val else 0) + (if b=6 then (kineticDriftCof2Coeff7Row6Norm h).val else 0) + (if b=7 then (kineticDriftCof2Coeff7Row7Norm h).val else 0) + (if b=8 then (kineticDriftCof2Coeff7Row8Norm h).val else 0)

theorem kineticDriftCof2Coeff7_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof2 7 b=kineticDriftCof2Row7 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof2.coeff 7))
    (n := 9) (by have := kineticCof2_drift_degree h 7; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof2.coeff 7)).coeff 0=(kineticDriftCof2Coeff7Row0Norm h).val :=
    (kineticDriftCof2Coeff7Row0Norm h).property
  have h1 : (driftReader h (kineticCof2.coeff 7)).coeff 1=(kineticDriftCof2Coeff7Row1Norm h).val :=
    (kineticDriftCof2Coeff7Row1Norm h).property
  have h2 : (driftReader h (kineticCof2.coeff 7)).coeff 2=(kineticDriftCof2Coeff7Row2Norm h).val :=
    (kineticDriftCof2Coeff7Row2Norm h).property
  have h3 : (driftReader h (kineticCof2.coeff 7)).coeff 3=(kineticDriftCof2Coeff7Row3Norm h).val :=
    (kineticDriftCof2Coeff7Row3Norm h).property
  have h4 : (driftReader h (kineticCof2.coeff 7)).coeff 4=(kineticDriftCof2Coeff7Row4Norm h).val :=
    (kineticDriftCof2Coeff7Row4Norm h).property
  have h5 : (driftReader h (kineticCof2.coeff 7)).coeff 5=(kineticDriftCof2Coeff7Row5Norm h).val :=
    (kineticDriftCof2Coeff7Row5Norm h).property
  have h6 : (driftReader h (kineticCof2.coeff 7)).coeff 6=(kineticDriftCof2Coeff7Row6Norm h).val :=
    (kineticDriftCof2Coeff7Row6Norm h).property
  have h7 : (driftReader h (kineticCof2.coeff 7)).coeff 7=(kineticDriftCof2Coeff7Row7Norm h).val :=
    (kineticDriftCof2Coeff7Row7Norm h).property
  have h8 : (driftReader h (kineticCof2.coeff 7)).coeff 8=(kineticDriftCof2Coeff7Row8Norm h).val :=
    (kineticDriftCof2Coeff7Row8Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof2Row7,h0,h1,h2,h3,h4,h5,h6,h7,h8] using he

def kineticDriftCof2Row8 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof2Coeff8Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof2Coeff8Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof2Coeff8Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof2Coeff8Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof2Coeff8Row4Norm h).val else 0) + (if b=5 then (kineticDriftCof2Coeff8Row5Norm h).val else 0) + (if b=6 then (kineticDriftCof2Coeff8Row6Norm h).val else 0) + (if b=7 then (kineticDriftCof2Coeff8Row7Norm h).val else 0) + (if b=8 then (kineticDriftCof2Coeff8Row8Norm h).val else 0)

theorem kineticDriftCof2Coeff8_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof2 8 b=kineticDriftCof2Row8 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof2.coeff 8))
    (n := 9) (by have := kineticCof2_drift_degree h 8; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof2.coeff 8)).coeff 0=(kineticDriftCof2Coeff8Row0Norm h).val :=
    (kineticDriftCof2Coeff8Row0Norm h).property
  have h1 : (driftReader h (kineticCof2.coeff 8)).coeff 1=(kineticDriftCof2Coeff8Row1Norm h).val :=
    (kineticDriftCof2Coeff8Row1Norm h).property
  have h2 : (driftReader h (kineticCof2.coeff 8)).coeff 2=(kineticDriftCof2Coeff8Row2Norm h).val :=
    (kineticDriftCof2Coeff8Row2Norm h).property
  have h3 : (driftReader h (kineticCof2.coeff 8)).coeff 3=(kineticDriftCof2Coeff8Row3Norm h).val :=
    (kineticDriftCof2Coeff8Row3Norm h).property
  have h4 : (driftReader h (kineticCof2.coeff 8)).coeff 4=(kineticDriftCof2Coeff8Row4Norm h).val :=
    (kineticDriftCof2Coeff8Row4Norm h).property
  have h5 : (driftReader h (kineticCof2.coeff 8)).coeff 5=(kineticDriftCof2Coeff8Row5Norm h).val :=
    (kineticDriftCof2Coeff8Row5Norm h).property
  have h6 : (driftReader h (kineticCof2.coeff 8)).coeff 6=(kineticDriftCof2Coeff8Row6Norm h).val :=
    (kineticDriftCof2Coeff8Row6Norm h).property
  have h7 : (driftReader h (kineticCof2.coeff 8)).coeff 7=(kineticDriftCof2Coeff8Row7Norm h).val :=
    (kineticDriftCof2Coeff8Row7Norm h).property
  have h8 : (driftReader h (kineticCof2.coeff 8)).coeff 8=(kineticDriftCof2Coeff8Row8Norm h).val :=
    (kineticDriftCof2Coeff8Row8Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof2Row8,h0,h1,h2,h3,h4,h5,h6,h7,h8] using he

def kineticDriftCof2Row9 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof2Coeff9Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof2Coeff9Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof2Coeff9Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof2Coeff9Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof2Coeff9Row4Norm h).val else 0) + (if b=5 then (kineticDriftCof2Coeff9Row5Norm h).val else 0) + (if b=6 then (kineticDriftCof2Coeff9Row6Norm h).val else 0) + (if b=7 then (kineticDriftCof2Coeff9Row7Norm h).val else 0) + (if b=8 then (kineticDriftCof2Coeff9Row8Norm h).val else 0)

theorem kineticDriftCof2Coeff9_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof2 9 b=kineticDriftCof2Row9 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof2.coeff 9))
    (n := 9) (by have := kineticCof2_drift_degree h 9; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof2.coeff 9)).coeff 0=(kineticDriftCof2Coeff9Row0Norm h).val :=
    (kineticDriftCof2Coeff9Row0Norm h).property
  have h1 : (driftReader h (kineticCof2.coeff 9)).coeff 1=(kineticDriftCof2Coeff9Row1Norm h).val :=
    (kineticDriftCof2Coeff9Row1Norm h).property
  have h2 : (driftReader h (kineticCof2.coeff 9)).coeff 2=(kineticDriftCof2Coeff9Row2Norm h).val :=
    (kineticDriftCof2Coeff9Row2Norm h).property
  have h3 : (driftReader h (kineticCof2.coeff 9)).coeff 3=(kineticDriftCof2Coeff9Row3Norm h).val :=
    (kineticDriftCof2Coeff9Row3Norm h).property
  have h4 : (driftReader h (kineticCof2.coeff 9)).coeff 4=(kineticDriftCof2Coeff9Row4Norm h).val :=
    (kineticDriftCof2Coeff9Row4Norm h).property
  have h5 : (driftReader h (kineticCof2.coeff 9)).coeff 5=(kineticDriftCof2Coeff9Row5Norm h).val :=
    (kineticDriftCof2Coeff9Row5Norm h).property
  have h6 : (driftReader h (kineticCof2.coeff 9)).coeff 6=(kineticDriftCof2Coeff9Row6Norm h).val :=
    (kineticDriftCof2Coeff9Row6Norm h).property
  have h7 : (driftReader h (kineticCof2.coeff 9)).coeff 7=(kineticDriftCof2Coeff9Row7Norm h).val :=
    (kineticDriftCof2Coeff9Row7Norm h).property
  have h8 : (driftReader h (kineticCof2.coeff 9)).coeff 8=(kineticDriftCof2Coeff9Row8Norm h).val :=
    (kineticDriftCof2Coeff9Row8Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof2Row9,h0,h1,h2,h3,h4,h5,h6,h7,h8] using he

def kineticDriftCof2Row10 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof2Coeff10Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof2Coeff10Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof2Coeff10Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof2Coeff10Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof2Coeff10Row4Norm h).val else 0) + (if b=5 then (kineticDriftCof2Coeff10Row5Norm h).val else 0) + (if b=6 then (kineticDriftCof2Coeff10Row6Norm h).val else 0) + (if b=7 then (kineticDriftCof2Coeff10Row7Norm h).val else 0) + (if b=8 then (kineticDriftCof2Coeff10Row8Norm h).val else 0)

theorem kineticDriftCof2Coeff10_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof2 10 b=kineticDriftCof2Row10 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof2.coeff 10))
    (n := 9) (by have := kineticCof2_drift_degree h 10; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof2.coeff 10)).coeff 0=(kineticDriftCof2Coeff10Row0Norm h).val :=
    (kineticDriftCof2Coeff10Row0Norm h).property
  have h1 : (driftReader h (kineticCof2.coeff 10)).coeff 1=(kineticDriftCof2Coeff10Row1Norm h).val :=
    (kineticDriftCof2Coeff10Row1Norm h).property
  have h2 : (driftReader h (kineticCof2.coeff 10)).coeff 2=(kineticDriftCof2Coeff10Row2Norm h).val :=
    (kineticDriftCof2Coeff10Row2Norm h).property
  have h3 : (driftReader h (kineticCof2.coeff 10)).coeff 3=(kineticDriftCof2Coeff10Row3Norm h).val :=
    (kineticDriftCof2Coeff10Row3Norm h).property
  have h4 : (driftReader h (kineticCof2.coeff 10)).coeff 4=(kineticDriftCof2Coeff10Row4Norm h).val :=
    (kineticDriftCof2Coeff10Row4Norm h).property
  have h5 : (driftReader h (kineticCof2.coeff 10)).coeff 5=(kineticDriftCof2Coeff10Row5Norm h).val :=
    (kineticDriftCof2Coeff10Row5Norm h).property
  have h6 : (driftReader h (kineticCof2.coeff 10)).coeff 6=(kineticDriftCof2Coeff10Row6Norm h).val :=
    (kineticDriftCof2Coeff10Row6Norm h).property
  have h7 : (driftReader h (kineticCof2.coeff 10)).coeff 7=(kineticDriftCof2Coeff10Row7Norm h).val :=
    (kineticDriftCof2Coeff10Row7Norm h).property
  have h8 : (driftReader h (kineticCof2.coeff 10)).coeff 8=(kineticDriftCof2Coeff10Row8Norm h).val :=
    (kineticDriftCof2Coeff10Row8Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof2Row10,h0,h1,h2,h3,h4,h5,h6,h7,h8] using he

def kineticDriftCof2Row11 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof2Coeff11Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof2Coeff11Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof2Coeff11Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof2Coeff11Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof2Coeff11Row4Norm h).val else 0) + (if b=5 then (kineticDriftCof2Coeff11Row5Norm h).val else 0) + (if b=6 then (kineticDriftCof2Coeff11Row6Norm h).val else 0) + (if b=7 then (kineticDriftCof2Coeff11Row7Norm h).val else 0) + (if b=8 then (kineticDriftCof2Coeff11Row8Norm h).val else 0)

theorem kineticDriftCof2Coeff11_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof2 11 b=kineticDriftCof2Row11 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof2.coeff 11))
    (n := 9) (by have := kineticCof2_drift_degree h 11; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof2.coeff 11)).coeff 0=(kineticDriftCof2Coeff11Row0Norm h).val :=
    (kineticDriftCof2Coeff11Row0Norm h).property
  have h1 : (driftReader h (kineticCof2.coeff 11)).coeff 1=(kineticDriftCof2Coeff11Row1Norm h).val :=
    (kineticDriftCof2Coeff11Row1Norm h).property
  have h2 : (driftReader h (kineticCof2.coeff 11)).coeff 2=(kineticDriftCof2Coeff11Row2Norm h).val :=
    (kineticDriftCof2Coeff11Row2Norm h).property
  have h3 : (driftReader h (kineticCof2.coeff 11)).coeff 3=(kineticDriftCof2Coeff11Row3Norm h).val :=
    (kineticDriftCof2Coeff11Row3Norm h).property
  have h4 : (driftReader h (kineticCof2.coeff 11)).coeff 4=(kineticDriftCof2Coeff11Row4Norm h).val :=
    (kineticDriftCof2Coeff11Row4Norm h).property
  have h5 : (driftReader h (kineticCof2.coeff 11)).coeff 5=(kineticDriftCof2Coeff11Row5Norm h).val :=
    (kineticDriftCof2Coeff11Row5Norm h).property
  have h6 : (driftReader h (kineticCof2.coeff 11)).coeff 6=(kineticDriftCof2Coeff11Row6Norm h).val :=
    (kineticDriftCof2Coeff11Row6Norm h).property
  have h7 : (driftReader h (kineticCof2.coeff 11)).coeff 7=(kineticDriftCof2Coeff11Row7Norm h).val :=
    (kineticDriftCof2Coeff11Row7Norm h).property
  have h8 : (driftReader h (kineticCof2.coeff 11)).coeff 8=(kineticDriftCof2Coeff11Row8Norm h).val :=
    (kineticDriftCof2Coeff11Row8Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof2Row11,h0,h1,h2,h3,h4,h5,h6,h7,h8] using he

def kineticDriftCof2Row12 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof2Coeff12Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof2Coeff12Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof2Coeff12Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof2Coeff12Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof2Coeff12Row4Norm h).val else 0) + (if b=5 then (kineticDriftCof2Coeff12Row5Norm h).val else 0) + (if b=6 then (kineticDriftCof2Coeff12Row6Norm h).val else 0) + (if b=7 then (kineticDriftCof2Coeff12Row7Norm h).val else 0) + (if b=8 then (kineticDriftCof2Coeff12Row8Norm h).val else 0)

theorem kineticDriftCof2Coeff12_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof2 12 b=kineticDriftCof2Row12 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof2.coeff 12))
    (n := 9) (by have := kineticCof2_drift_degree h 12; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof2.coeff 12)).coeff 0=(kineticDriftCof2Coeff12Row0Norm h).val :=
    (kineticDriftCof2Coeff12Row0Norm h).property
  have h1 : (driftReader h (kineticCof2.coeff 12)).coeff 1=(kineticDriftCof2Coeff12Row1Norm h).val :=
    (kineticDriftCof2Coeff12Row1Norm h).property
  have h2 : (driftReader h (kineticCof2.coeff 12)).coeff 2=(kineticDriftCof2Coeff12Row2Norm h).val :=
    (kineticDriftCof2Coeff12Row2Norm h).property
  have h3 : (driftReader h (kineticCof2.coeff 12)).coeff 3=(kineticDriftCof2Coeff12Row3Norm h).val :=
    (kineticDriftCof2Coeff12Row3Norm h).property
  have h4 : (driftReader h (kineticCof2.coeff 12)).coeff 4=(kineticDriftCof2Coeff12Row4Norm h).val :=
    (kineticDriftCof2Coeff12Row4Norm h).property
  have h5 : (driftReader h (kineticCof2.coeff 12)).coeff 5=(kineticDriftCof2Coeff12Row5Norm h).val :=
    (kineticDriftCof2Coeff12Row5Norm h).property
  have h6 : (driftReader h (kineticCof2.coeff 12)).coeff 6=(kineticDriftCof2Coeff12Row6Norm h).val :=
    (kineticDriftCof2Coeff12Row6Norm h).property
  have h7 : (driftReader h (kineticCof2.coeff 12)).coeff 7=(kineticDriftCof2Coeff12Row7Norm h).val :=
    (kineticDriftCof2Coeff12Row7Norm h).property
  have h8 : (driftReader h (kineticCof2.coeff 12)).coeff 8=(kineticDriftCof2Coeff12Row8Norm h).val :=
    (kineticDriftCof2Coeff12Row8Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof2Row12,h0,h1,h2,h3,h4,h5,h6,h7,h8] using he

def kineticDriftCof2Row13 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof2Coeff13Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof2Coeff13Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof2Coeff13Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof2Coeff13Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof2Coeff13Row4Norm h).val else 0) + (if b=5 then (kineticDriftCof2Coeff13Row5Norm h).val else 0) + (if b=6 then (kineticDriftCof2Coeff13Row6Norm h).val else 0) + (if b=7 then (kineticDriftCof2Coeff13Row7Norm h).val else 0) + (if b=8 then (kineticDriftCof2Coeff13Row8Norm h).val else 0)

theorem kineticDriftCof2Coeff13_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof2 13 b=kineticDriftCof2Row13 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof2.coeff 13))
    (n := 9) (by have := kineticCof2_drift_degree h 13; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof2.coeff 13)).coeff 0=(kineticDriftCof2Coeff13Row0Norm h).val :=
    (kineticDriftCof2Coeff13Row0Norm h).property
  have h1 : (driftReader h (kineticCof2.coeff 13)).coeff 1=(kineticDriftCof2Coeff13Row1Norm h).val :=
    (kineticDriftCof2Coeff13Row1Norm h).property
  have h2 : (driftReader h (kineticCof2.coeff 13)).coeff 2=(kineticDriftCof2Coeff13Row2Norm h).val :=
    (kineticDriftCof2Coeff13Row2Norm h).property
  have h3 : (driftReader h (kineticCof2.coeff 13)).coeff 3=(kineticDriftCof2Coeff13Row3Norm h).val :=
    (kineticDriftCof2Coeff13Row3Norm h).property
  have h4 : (driftReader h (kineticCof2.coeff 13)).coeff 4=(kineticDriftCof2Coeff13Row4Norm h).val :=
    (kineticDriftCof2Coeff13Row4Norm h).property
  have h5 : (driftReader h (kineticCof2.coeff 13)).coeff 5=(kineticDriftCof2Coeff13Row5Norm h).val :=
    (kineticDriftCof2Coeff13Row5Norm h).property
  have h6 : (driftReader h (kineticCof2.coeff 13)).coeff 6=(kineticDriftCof2Coeff13Row6Norm h).val :=
    (kineticDriftCof2Coeff13Row6Norm h).property
  have h7 : (driftReader h (kineticCof2.coeff 13)).coeff 7=(kineticDriftCof2Coeff13Row7Norm h).val :=
    (kineticDriftCof2Coeff13Row7Norm h).property
  have h8 : (driftReader h (kineticCof2.coeff 13)).coeff 8=(kineticDriftCof2Coeff13Row8Norm h).val :=
    (kineticDriftCof2Coeff13Row8Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof2Row13,h0,h1,h2,h3,h4,h5,h6,h7,h8] using he

def kineticDriftCof2Row14 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof2Coeff14Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof2Coeff14Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof2Coeff14Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof2Coeff14Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof2Coeff14Row4Norm h).val else 0) + (if b=5 then (kineticDriftCof2Coeff14Row5Norm h).val else 0) + (if b=6 then (kineticDriftCof2Coeff14Row6Norm h).val else 0) + (if b=7 then (kineticDriftCof2Coeff14Row7Norm h).val else 0) + (if b=8 then (kineticDriftCof2Coeff14Row8Norm h).val else 0)

theorem kineticDriftCof2Coeff14_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof2 14 b=kineticDriftCof2Row14 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof2.coeff 14))
    (n := 9) (by have := kineticCof2_drift_degree h 14; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof2.coeff 14)).coeff 0=(kineticDriftCof2Coeff14Row0Norm h).val :=
    (kineticDriftCof2Coeff14Row0Norm h).property
  have h1 : (driftReader h (kineticCof2.coeff 14)).coeff 1=(kineticDriftCof2Coeff14Row1Norm h).val :=
    (kineticDriftCof2Coeff14Row1Norm h).property
  have h2 : (driftReader h (kineticCof2.coeff 14)).coeff 2=(kineticDriftCof2Coeff14Row2Norm h).val :=
    (kineticDriftCof2Coeff14Row2Norm h).property
  have h3 : (driftReader h (kineticCof2.coeff 14)).coeff 3=(kineticDriftCof2Coeff14Row3Norm h).val :=
    (kineticDriftCof2Coeff14Row3Norm h).property
  have h4 : (driftReader h (kineticCof2.coeff 14)).coeff 4=(kineticDriftCof2Coeff14Row4Norm h).val :=
    (kineticDriftCof2Coeff14Row4Norm h).property
  have h5 : (driftReader h (kineticCof2.coeff 14)).coeff 5=(kineticDriftCof2Coeff14Row5Norm h).val :=
    (kineticDriftCof2Coeff14Row5Norm h).property
  have h6 : (driftReader h (kineticCof2.coeff 14)).coeff 6=(kineticDriftCof2Coeff14Row6Norm h).val :=
    (kineticDriftCof2Coeff14Row6Norm h).property
  have h7 : (driftReader h (kineticCof2.coeff 14)).coeff 7=(kineticDriftCof2Coeff14Row7Norm h).val :=
    (kineticDriftCof2Coeff14Row7Norm h).property
  have h8 : (driftReader h (kineticCof2.coeff 14)).coeff 8=(kineticDriftCof2Coeff14Row8Norm h).val :=
    (kineticDriftCof2Coeff14Row8Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof2Row14,h0,h1,h2,h3,h4,h5,h6,h7,h8] using he

def kineticDriftCof2Row15 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof2Coeff15Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof2Coeff15Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof2Coeff15Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof2Coeff15Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof2Coeff15Row4Norm h).val else 0) + (if b=5 then (kineticDriftCof2Coeff15Row5Norm h).val else 0) + (if b=6 then (kineticDriftCof2Coeff15Row6Norm h).val else 0) + (if b=7 then (kineticDriftCof2Coeff15Row7Norm h).val else 0) + (if b=8 then (kineticDriftCof2Coeff15Row8Norm h).val else 0)

theorem kineticDriftCof2Coeff15_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof2 15 b=kineticDriftCof2Row15 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof2.coeff 15))
    (n := 9) (by have := kineticCof2_drift_degree h 15; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof2.coeff 15)).coeff 0=(kineticDriftCof2Coeff15Row0Norm h).val :=
    (kineticDriftCof2Coeff15Row0Norm h).property
  have h1 : (driftReader h (kineticCof2.coeff 15)).coeff 1=(kineticDriftCof2Coeff15Row1Norm h).val :=
    (kineticDriftCof2Coeff15Row1Norm h).property
  have h2 : (driftReader h (kineticCof2.coeff 15)).coeff 2=(kineticDriftCof2Coeff15Row2Norm h).val :=
    (kineticDriftCof2Coeff15Row2Norm h).property
  have h3 : (driftReader h (kineticCof2.coeff 15)).coeff 3=(kineticDriftCof2Coeff15Row3Norm h).val :=
    (kineticDriftCof2Coeff15Row3Norm h).property
  have h4 : (driftReader h (kineticCof2.coeff 15)).coeff 4=(kineticDriftCof2Coeff15Row4Norm h).val :=
    (kineticDriftCof2Coeff15Row4Norm h).property
  have h5 : (driftReader h (kineticCof2.coeff 15)).coeff 5=(kineticDriftCof2Coeff15Row5Norm h).val :=
    (kineticDriftCof2Coeff15Row5Norm h).property
  have h6 : (driftReader h (kineticCof2.coeff 15)).coeff 6=(kineticDriftCof2Coeff15Row6Norm h).val :=
    (kineticDriftCof2Coeff15Row6Norm h).property
  have h7 : (driftReader h (kineticCof2.coeff 15)).coeff 7=(kineticDriftCof2Coeff15Row7Norm h).val :=
    (kineticDriftCof2Coeff15Row7Norm h).property
  have h8 : (driftReader h (kineticCof2.coeff 15)).coeff 8=(kineticDriftCof2Coeff15Row8Norm h).val :=
    (kineticDriftCof2Coeff15Row8Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof2Row15,h0,h1,h2,h3,h4,h5,h6,h7,h8] using he

def kineticDriftCof2Row16 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof2Coeff16Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof2Coeff16Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof2Coeff16Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof2Coeff16Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof2Coeff16Row4Norm h).val else 0) + (if b=5 then (kineticDriftCof2Coeff16Row5Norm h).val else 0) + (if b=6 then (kineticDriftCof2Coeff16Row6Norm h).val else 0) + (if b=7 then (kineticDriftCof2Coeff16Row7Norm h).val else 0) + (if b=8 then (kineticDriftCof2Coeff16Row8Norm h).val else 0)

theorem kineticDriftCof2Coeff16_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof2 16 b=kineticDriftCof2Row16 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof2.coeff 16))
    (n := 9) (by have := kineticCof2_drift_degree h 16; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof2.coeff 16)).coeff 0=(kineticDriftCof2Coeff16Row0Norm h).val :=
    (kineticDriftCof2Coeff16Row0Norm h).property
  have h1 : (driftReader h (kineticCof2.coeff 16)).coeff 1=(kineticDriftCof2Coeff16Row1Norm h).val :=
    (kineticDriftCof2Coeff16Row1Norm h).property
  have h2 : (driftReader h (kineticCof2.coeff 16)).coeff 2=(kineticDriftCof2Coeff16Row2Norm h).val :=
    (kineticDriftCof2Coeff16Row2Norm h).property
  have h3 : (driftReader h (kineticCof2.coeff 16)).coeff 3=(kineticDriftCof2Coeff16Row3Norm h).val :=
    (kineticDriftCof2Coeff16Row3Norm h).property
  have h4 : (driftReader h (kineticCof2.coeff 16)).coeff 4=(kineticDriftCof2Coeff16Row4Norm h).val :=
    (kineticDriftCof2Coeff16Row4Norm h).property
  have h5 : (driftReader h (kineticCof2.coeff 16)).coeff 5=(kineticDriftCof2Coeff16Row5Norm h).val :=
    (kineticDriftCof2Coeff16Row5Norm h).property
  have h6 : (driftReader h (kineticCof2.coeff 16)).coeff 6=(kineticDriftCof2Coeff16Row6Norm h).val :=
    (kineticDriftCof2Coeff16Row6Norm h).property
  have h7 : (driftReader h (kineticCof2.coeff 16)).coeff 7=(kineticDriftCof2Coeff16Row7Norm h).val :=
    (kineticDriftCof2Coeff16Row7Norm h).property
  have h8 : (driftReader h (kineticCof2.coeff 16)).coeff 8=(kineticDriftCof2Coeff16Row8Norm h).val :=
    (kineticDriftCof2Coeff16Row8Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof2Row16,h0,h1,h2,h3,h4,h5,h6,h7,h8] using he

theorem kineticDriftCof2_rows (h : ℂ) (j b : ℕ) :
    kineticDriftCell h kineticCof2 j b=(if j=0 then kineticDriftCof2Row0 h b else 0) + (if j=1 then kineticDriftCof2Row1 h b else 0) + (if j=2 then kineticDriftCof2Row2 h b else 0) + (if j=3 then kineticDriftCof2Row3 h b else 0) + (if j=4 then kineticDriftCof2Row4 h b else 0) + (if j=5 then kineticDriftCof2Row5 h b else 0) + (if j=6 then kineticDriftCof2Row6 h b else 0) + (if j=7 then kineticDriftCof2Row7 h b else 0) + (if j=8 then kineticDriftCof2Row8 h b else 0) + (if j=9 then kineticDriftCof2Row9 h b else 0) + (if j=10 then kineticDriftCof2Row10 h b else 0) + (if j=11 then kineticDriftCof2Row11 h b else 0) + (if j=12 then kineticDriftCof2Row12 h b else 0) + (if j=13 then kineticDriftCof2Row13 h b else 0) + (if j=14 then kineticDriftCof2Row14 h b else 0) + (if j=15 then kineticDriftCof2Row15 h b else 0) + (if j=16 then kineticDriftCof2Row16 h b else 0) := by
  by_cases hj : j≤16
  · interval_cases j
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof2Coeff0_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof2Coeff1_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof2Coeff2_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof2Coeff3_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof2Coeff4_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof2Coeff5_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof2Coeff6_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof2Coeff7_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof2Coeff8_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof2Coeff9_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof2Coeff10_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof2Coeff11_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof2Coeff12_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof2Coeff13_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof2Coeff14_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof2Coeff15_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof2Coeff16_rows h b
  · have hp : kineticCof2.coeff j=0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (kineticCof2_degree.trans_lt (by omega))
    simp only [kineticDriftCell,hp,map_zero,Polynomial.coeff_zero,if_neg (show j≠0 by omega),if_neg (show j≠1 by omega),if_neg (show j≠2 by omega),if_neg (show j≠3 by omega),if_neg (show j≠4 by omega),if_neg (show j≠5 by omega),if_neg (show j≠6 by omega),if_neg (show j≠7 by omega),if_neg (show j≠8 by omega),if_neg (show j≠9 by omega),if_neg (show j≠10 by omega),if_neg (show j≠11 by omega),if_neg (show j≠12 by omega),if_neg (show j≠13 by omega),if_neg (show j≠14 by omega),if_neg (show j≠15 by omega),if_neg (show j≠16 by omega),zero_add]

end
end HTGeometry.ThetaRatioKineticContraction
