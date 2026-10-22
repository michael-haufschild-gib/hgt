import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticDriftSupport
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def kineticDriftCof10Coeff0Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 0 0=c} := by
  have he : kineticDriftCell h kineticCof10 0 0=kineticDriftCell h kineticCof10 0 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment6Coeff0Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff0Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 0 1=c} := by
  have he : kineticDriftCell h kineticCof10 0 1=kineticDriftCell h kineticCof10 0 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff0Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 0 2=c} := by
  have he : kineticDriftCell h kineticCof10 0 2=kineticDriftCell h kineticCof10 0 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff0Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 0 3=c} := by
  have he : kineticDriftCell h kineticCof10 0 3=kineticDriftCell h kineticCof10 0 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff0Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 0 4=c} := by
  have he : kineticDriftCell h kineticCof10 0 4=kineticDriftCell h kineticCof10 0 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff1Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 1 0=c} := by
  have he : kineticDriftCell h kineticCof10 1 0=kineticDriftCell h kineticCof10 1 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff1Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff1Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 1 1=c} := by
  have he : kineticDriftCell h kineticCof10 1 1=kineticDriftCell h kineticCof10 1 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff1Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 1 2=c} := by
  have he : kineticDriftCell h kineticCof10 1 2=kineticDriftCell h kineticCof10 1 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff1Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 1 3=c} := by
  have he : kineticDriftCell h kineticCof10 1 3=kineticDriftCell h kineticCof10 1 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff1Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 1 4=c} := by
  have he : kineticDriftCell h kineticCof10 1 4=kineticDriftCell h kineticCof10 1 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff2Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 2 0=c} := by
  have he : kineticDriftCell h kineticCof10 2 0=kineticDriftCell h kineticCof10 2 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff2Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff2Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 2 1=c} := by
  have he : kineticDriftCell h kineticCof10 2 1=kineticDriftCell h kineticCof10 2 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment6Coeff0Row0Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff2Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 2 2=c} := by
  have he : kineticDriftCell h kineticCof10 2 2=kineticDriftCell h kineticCof10 2 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment6Coeff0Row1Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff2Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 2 3=c} := by
  have he : kineticDriftCell h kineticCof10 2 3=kineticDriftCell h kineticCof10 2 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment6Coeff0Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff2Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 2 4=c} := by
  have he : kineticDriftCell h kineticCof10 2 4=kineticDriftCell h kineticCof10 2 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment6Coeff0Row3Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff3Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 3 0=c} := by
  have he : kineticDriftCell h kineticCof10 3 0=kineticDriftCell h kineticCof10 3 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff3Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff3Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 3 1=c} := by
  have he : kineticDriftCell h kineticCof10 3 1=kineticDriftCell h kineticCof10 3 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment6Coeff1Row0Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff3Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 3 2=c} := by
  have he : kineticDriftCell h kineticCof10 3 2=kineticDriftCell h kineticCof10 3 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment6Coeff1Row1Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff3Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 3 3=c} := by
  have he : kineticDriftCell h kineticCof10 3 3=kineticDriftCell h kineticCof10 3 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment6Coeff1Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff3Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 3 4=c} := by
  have he : kineticDriftCell h kineticCof10 3 4=kineticDriftCell h kineticCof10 3 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment6Coeff1Row3Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff4Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 4 0=c} := by
  have he : kineticDriftCell h kineticCof10 4 0=kineticDriftCell h kineticCof10 4 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff4Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff4Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 4 1=c} := by
  have he : kineticDriftCell h kineticCof10 4 1=kineticDriftCell h kineticCof10 4 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment6Coeff2Row0Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff4Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 4 2=c} := by
  have he : kineticDriftCell h kineticCof10 4 2=kineticDriftCell h kineticCof10 4 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row0Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff2Row1Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff4Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 4 3=c} := by
  have he : kineticDriftCell h kineticCof10 4 3=kineticDriftCell h kineticCof10 4 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff2Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff4Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 4 4=c} := by
  have he : kineticDriftCell h kineticCof10 4 4=kineticDriftCell h kineticCof10 4 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff0Row2Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff2Row3Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff5Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 5 0=c} := by
  have he : kineticDriftCell h kineticCof10 5 0=kineticDriftCell h kineticCof10 5 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff5Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff5Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 5 1=c} := by
  have he : kineticDriftCell h kineticCof10 5 1=kineticDriftCell h kineticCof10 5 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment6Coeff3Row0Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff5Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 5 2=c} := by
  have he : kineticDriftCell h kineticCof10 5 2=kineticDriftCell h kineticCof10 5 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff1Row0Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff3Row1Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff5Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 5 3=c} := by
  have he : kineticDriftCell h kineticCof10 5 3=kineticDriftCell h kineticCof10 5 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff1Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff3Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff5Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 5 4=c} := by
  have he : kineticDriftCell h kineticCof10 5 4=kineticDriftCell h kineticCof10 5 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff1Row2Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff3Row3Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff6Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 6 0=c} := by
  have he : kineticDriftCell h kineticCof10 6 0=kineticDriftCell h kineticCof10 6 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff6Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff6Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 6 1=c} := by
  have he : kineticDriftCell h kineticCof10 6 1=kineticDriftCell h kineticCof10 6 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment6Coeff4Row0Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff6Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 6 2=c} := by
  have he : kineticDriftCell h kineticCof10 6 2=kineticDriftCell h kineticCof10 6 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff2Row0Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff4Row1Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff6Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 6 3=c} := by
  have he : kineticDriftCell h kineticCof10 6 3=kineticDriftCell h kineticCof10 6 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row0Norm,kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff6Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 6 4=c} := by
  have he : kineticDriftCell h kineticCof10 6 4=kineticDriftCell h kineticCof10 6 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff0Row1Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff2Row2Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff4Row3Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff7Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 7 0=c} := by
  have he : kineticDriftCell h kineticCof10 7 0=kineticDriftCell h kineticCof10 7 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff6Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff7Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 7 1=c} := by
  have he : kineticDriftCell h kineticCof10 7 1=kineticDriftCell h kineticCof10 7 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment6Coeff5Row0Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff7Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 7 2=c} := by
  have he : kineticDriftCell h kineticCof10 7 2=kineticDriftCell h kineticCof10 7 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff3Row0Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff5Row1Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff7Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 7 3=c} := by
  have he : kineticDriftCell h kineticCof10 7 3=kineticDriftCell h kineticCof10 7 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff1Row0Norm,kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff3Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff5Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff7Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 7 4=c} := by
  have he : kineticDriftCell h kineticCof10 7 4=kineticDriftCell h kineticCof10 7 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff1Row1Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff3Row2Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff5Row3Norm,kineticDriftMoment6Coeff6Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff8Row0Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 8 0=c} := by
  have he : kineticDriftCell h kineticCof10 8 0=kineticDriftCell h kineticCof10 8 0 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment6Coeff6Row0Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff8Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 8 1=c} := by
  have he : kineticDriftCell h kineticCof10 8 1=kineticDriftCell h kineticCof10 8 1 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment6Coeff6Row0Norm,kineticDriftMoment6Coeff6Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff8Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 8 2=c} := by
  have he : kineticDriftCell h kineticCof10 8 2=kineticDriftCell h kineticCof10 8 2 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff4Row0Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff6Row1Norm,kineticDriftMoment6Coeff6Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff8Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 8 3=c} := by
  have he : kineticDriftCell h kineticCof10 8 3=kineticDriftCell h kineticCof10 8 3 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff2Row0Norm,kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff4Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff6Row2Norm,kineticDriftMoment6Coeff6Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticDriftCof10Coeff8Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h kineticCof10 8 4=c} := by
  have he : kineticDriftCell h kineticCof10 8 4=kineticDriftCell h kineticCof10 8 4 := rfl
  conv at he =>
    rhs
    rw [kineticCof10_tensor_form]
    simp only [kineticDriftCell_add,kineticDriftCell_sub,kineticDriftCell_neg,kineticDriftCell_nat_mul]
    simp only [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,kineticDriftCell,kineticMoment2_coeff,kineticMoment4_coeff,kineticMoment6_coeff]
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero,map_add,map_zero,
      Polynomial.coeff_add,Polynomial.coeff_zero]
    simp only [kineticDriftMoment2Coeff0_rows,kineticDriftMoment2Coeff1_rows,kineticDriftMoment2Coeff2_rows,kineticDriftMoment4Coeff0_rows,kineticDriftMoment4Coeff1_rows,kineticDriftMoment4Coeff2_rows,kineticDriftMoment4Coeff3_rows,kineticDriftMoment4Coeff4_rows,kineticDriftMoment6Coeff0_rows,kineticDriftMoment6Coeff1_rows,kineticDriftMoment6Coeff2_rows,kineticDriftMoment6Coeff3_rows,kineticDriftMoment6Coeff4_rows,kineticDriftMoment6Coeff5_rows,kineticDriftMoment6Coeff6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftMoment2Coeff2Row1Norm,kineticDriftMoment4Coeff4Row2Norm,kineticDriftMoment6Coeff6Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩


def kineticDriftCof10Row0 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof10Coeff0Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof10Coeff0Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof10Coeff0Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof10Coeff0Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof10Coeff0Row4Norm h).val else 0)

theorem kineticDriftCof10Coeff0_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof10 0 b=kineticDriftCof10Row0 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof10.coeff 0))
    (n := 5) (by have := kineticCof10_drift_degree h 0; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof10.coeff 0)).coeff 0=(kineticDriftCof10Coeff0Row0Norm h).val :=
    (kineticDriftCof10Coeff0Row0Norm h).property
  have h1 : (driftReader h (kineticCof10.coeff 0)).coeff 1=(kineticDriftCof10Coeff0Row1Norm h).val :=
    (kineticDriftCof10Coeff0Row1Norm h).property
  have h2 : (driftReader h (kineticCof10.coeff 0)).coeff 2=(kineticDriftCof10Coeff0Row2Norm h).val :=
    (kineticDriftCof10Coeff0Row2Norm h).property
  have h3 : (driftReader h (kineticCof10.coeff 0)).coeff 3=(kineticDriftCof10Coeff0Row3Norm h).val :=
    (kineticDriftCof10Coeff0Row3Norm h).property
  have h4 : (driftReader h (kineticCof10.coeff 0)).coeff 4=(kineticDriftCof10Coeff0Row4Norm h).val :=
    (kineticDriftCof10Coeff0Row4Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof10Row0,h0,h1,h2,h3,h4] using he

def kineticDriftCof10Row1 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof10Coeff1Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof10Coeff1Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof10Coeff1Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof10Coeff1Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof10Coeff1Row4Norm h).val else 0)

theorem kineticDriftCof10Coeff1_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof10 1 b=kineticDriftCof10Row1 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof10.coeff 1))
    (n := 5) (by have := kineticCof10_drift_degree h 1; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof10.coeff 1)).coeff 0=(kineticDriftCof10Coeff1Row0Norm h).val :=
    (kineticDriftCof10Coeff1Row0Norm h).property
  have h1 : (driftReader h (kineticCof10.coeff 1)).coeff 1=(kineticDriftCof10Coeff1Row1Norm h).val :=
    (kineticDriftCof10Coeff1Row1Norm h).property
  have h2 : (driftReader h (kineticCof10.coeff 1)).coeff 2=(kineticDriftCof10Coeff1Row2Norm h).val :=
    (kineticDriftCof10Coeff1Row2Norm h).property
  have h3 : (driftReader h (kineticCof10.coeff 1)).coeff 3=(kineticDriftCof10Coeff1Row3Norm h).val :=
    (kineticDriftCof10Coeff1Row3Norm h).property
  have h4 : (driftReader h (kineticCof10.coeff 1)).coeff 4=(kineticDriftCof10Coeff1Row4Norm h).val :=
    (kineticDriftCof10Coeff1Row4Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof10Row1,h0,h1,h2,h3,h4] using he

def kineticDriftCof10Row2 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof10Coeff2Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof10Coeff2Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof10Coeff2Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof10Coeff2Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof10Coeff2Row4Norm h).val else 0)

theorem kineticDriftCof10Coeff2_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof10 2 b=kineticDriftCof10Row2 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof10.coeff 2))
    (n := 5) (by have := kineticCof10_drift_degree h 2; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof10.coeff 2)).coeff 0=(kineticDriftCof10Coeff2Row0Norm h).val :=
    (kineticDriftCof10Coeff2Row0Norm h).property
  have h1 : (driftReader h (kineticCof10.coeff 2)).coeff 1=(kineticDriftCof10Coeff2Row1Norm h).val :=
    (kineticDriftCof10Coeff2Row1Norm h).property
  have h2 : (driftReader h (kineticCof10.coeff 2)).coeff 2=(kineticDriftCof10Coeff2Row2Norm h).val :=
    (kineticDriftCof10Coeff2Row2Norm h).property
  have h3 : (driftReader h (kineticCof10.coeff 2)).coeff 3=(kineticDriftCof10Coeff2Row3Norm h).val :=
    (kineticDriftCof10Coeff2Row3Norm h).property
  have h4 : (driftReader h (kineticCof10.coeff 2)).coeff 4=(kineticDriftCof10Coeff2Row4Norm h).val :=
    (kineticDriftCof10Coeff2Row4Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof10Row2,h0,h1,h2,h3,h4] using he

def kineticDriftCof10Row3 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof10Coeff3Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof10Coeff3Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof10Coeff3Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof10Coeff3Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof10Coeff3Row4Norm h).val else 0)

theorem kineticDriftCof10Coeff3_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof10 3 b=kineticDriftCof10Row3 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof10.coeff 3))
    (n := 5) (by have := kineticCof10_drift_degree h 3; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof10.coeff 3)).coeff 0=(kineticDriftCof10Coeff3Row0Norm h).val :=
    (kineticDriftCof10Coeff3Row0Norm h).property
  have h1 : (driftReader h (kineticCof10.coeff 3)).coeff 1=(kineticDriftCof10Coeff3Row1Norm h).val :=
    (kineticDriftCof10Coeff3Row1Norm h).property
  have h2 : (driftReader h (kineticCof10.coeff 3)).coeff 2=(kineticDriftCof10Coeff3Row2Norm h).val :=
    (kineticDriftCof10Coeff3Row2Norm h).property
  have h3 : (driftReader h (kineticCof10.coeff 3)).coeff 3=(kineticDriftCof10Coeff3Row3Norm h).val :=
    (kineticDriftCof10Coeff3Row3Norm h).property
  have h4 : (driftReader h (kineticCof10.coeff 3)).coeff 4=(kineticDriftCof10Coeff3Row4Norm h).val :=
    (kineticDriftCof10Coeff3Row4Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof10Row3,h0,h1,h2,h3,h4] using he

def kineticDriftCof10Row4 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof10Coeff4Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof10Coeff4Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof10Coeff4Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof10Coeff4Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof10Coeff4Row4Norm h).val else 0)

theorem kineticDriftCof10Coeff4_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof10 4 b=kineticDriftCof10Row4 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof10.coeff 4))
    (n := 5) (by have := kineticCof10_drift_degree h 4; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof10.coeff 4)).coeff 0=(kineticDriftCof10Coeff4Row0Norm h).val :=
    (kineticDriftCof10Coeff4Row0Norm h).property
  have h1 : (driftReader h (kineticCof10.coeff 4)).coeff 1=(kineticDriftCof10Coeff4Row1Norm h).val :=
    (kineticDriftCof10Coeff4Row1Norm h).property
  have h2 : (driftReader h (kineticCof10.coeff 4)).coeff 2=(kineticDriftCof10Coeff4Row2Norm h).val :=
    (kineticDriftCof10Coeff4Row2Norm h).property
  have h3 : (driftReader h (kineticCof10.coeff 4)).coeff 3=(kineticDriftCof10Coeff4Row3Norm h).val :=
    (kineticDriftCof10Coeff4Row3Norm h).property
  have h4 : (driftReader h (kineticCof10.coeff 4)).coeff 4=(kineticDriftCof10Coeff4Row4Norm h).val :=
    (kineticDriftCof10Coeff4Row4Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof10Row4,h0,h1,h2,h3,h4] using he

def kineticDriftCof10Row5 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof10Coeff5Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof10Coeff5Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof10Coeff5Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof10Coeff5Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof10Coeff5Row4Norm h).val else 0)

theorem kineticDriftCof10Coeff5_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof10 5 b=kineticDriftCof10Row5 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof10.coeff 5))
    (n := 5) (by have := kineticCof10_drift_degree h 5; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof10.coeff 5)).coeff 0=(kineticDriftCof10Coeff5Row0Norm h).val :=
    (kineticDriftCof10Coeff5Row0Norm h).property
  have h1 : (driftReader h (kineticCof10.coeff 5)).coeff 1=(kineticDriftCof10Coeff5Row1Norm h).val :=
    (kineticDriftCof10Coeff5Row1Norm h).property
  have h2 : (driftReader h (kineticCof10.coeff 5)).coeff 2=(kineticDriftCof10Coeff5Row2Norm h).val :=
    (kineticDriftCof10Coeff5Row2Norm h).property
  have h3 : (driftReader h (kineticCof10.coeff 5)).coeff 3=(kineticDriftCof10Coeff5Row3Norm h).val :=
    (kineticDriftCof10Coeff5Row3Norm h).property
  have h4 : (driftReader h (kineticCof10.coeff 5)).coeff 4=(kineticDriftCof10Coeff5Row4Norm h).val :=
    (kineticDriftCof10Coeff5Row4Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof10Row5,h0,h1,h2,h3,h4] using he

def kineticDriftCof10Row6 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof10Coeff6Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof10Coeff6Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof10Coeff6Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof10Coeff6Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof10Coeff6Row4Norm h).val else 0)

theorem kineticDriftCof10Coeff6_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof10 6 b=kineticDriftCof10Row6 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof10.coeff 6))
    (n := 5) (by have := kineticCof10_drift_degree h 6; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof10.coeff 6)).coeff 0=(kineticDriftCof10Coeff6Row0Norm h).val :=
    (kineticDriftCof10Coeff6Row0Norm h).property
  have h1 : (driftReader h (kineticCof10.coeff 6)).coeff 1=(kineticDriftCof10Coeff6Row1Norm h).val :=
    (kineticDriftCof10Coeff6Row1Norm h).property
  have h2 : (driftReader h (kineticCof10.coeff 6)).coeff 2=(kineticDriftCof10Coeff6Row2Norm h).val :=
    (kineticDriftCof10Coeff6Row2Norm h).property
  have h3 : (driftReader h (kineticCof10.coeff 6)).coeff 3=(kineticDriftCof10Coeff6Row3Norm h).val :=
    (kineticDriftCof10Coeff6Row3Norm h).property
  have h4 : (driftReader h (kineticCof10.coeff 6)).coeff 4=(kineticDriftCof10Coeff6Row4Norm h).val :=
    (kineticDriftCof10Coeff6Row4Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof10Row6,h0,h1,h2,h3,h4] using he

def kineticDriftCof10Row7 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof10Coeff7Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof10Coeff7Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof10Coeff7Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof10Coeff7Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof10Coeff7Row4Norm h).val else 0)

theorem kineticDriftCof10Coeff7_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof10 7 b=kineticDriftCof10Row7 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof10.coeff 7))
    (n := 5) (by have := kineticCof10_drift_degree h 7; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof10.coeff 7)).coeff 0=(kineticDriftCof10Coeff7Row0Norm h).val :=
    (kineticDriftCof10Coeff7Row0Norm h).property
  have h1 : (driftReader h (kineticCof10.coeff 7)).coeff 1=(kineticDriftCof10Coeff7Row1Norm h).val :=
    (kineticDriftCof10Coeff7Row1Norm h).property
  have h2 : (driftReader h (kineticCof10.coeff 7)).coeff 2=(kineticDriftCof10Coeff7Row2Norm h).val :=
    (kineticDriftCof10Coeff7Row2Norm h).property
  have h3 : (driftReader h (kineticCof10.coeff 7)).coeff 3=(kineticDriftCof10Coeff7Row3Norm h).val :=
    (kineticDriftCof10Coeff7Row3Norm h).property
  have h4 : (driftReader h (kineticCof10.coeff 7)).coeff 4=(kineticDriftCof10Coeff7Row4Norm h).val :=
    (kineticDriftCof10Coeff7Row4Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof10Row7,h0,h1,h2,h3,h4] using he

def kineticDriftCof10Row8 (h : ℂ) (b : ℕ) : ℂ :=
  (if b=0 then (kineticDriftCof10Coeff8Row0Norm h).val else 0) + (if b=1 then (kineticDriftCof10Coeff8Row1Norm h).val else 0) + (if b=2 then (kineticDriftCof10Coeff8Row2Norm h).val else 0) + (if b=3 then (kineticDriftCof10Coeff8Row3Norm h).val else 0) + (if b=4 then (kineticDriftCof10Coeff8Row4Norm h).val else 0)

theorem kineticDriftCof10Coeff8_rows (h : ℂ) (b : ℕ) :
    kineticDriftCell h kineticCof10 8 b=kineticDriftCof10Row8 h b := by
  have hp := Polynomial.as_sum_range_C_mul_X_pow' (driftReader h (kineticCof10.coeff 8))
    (n := 5) (by have := kineticCof10_drift_degree h 8; omega)
  have he := congrArg (fun P : Polynomial ℂ => P.coeff b) hp
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow] at he
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have h0 : (driftReader h (kineticCof10.coeff 8)).coeff 0=(kineticDriftCof10Coeff8Row0Norm h).val :=
    (kineticDriftCof10Coeff8Row0Norm h).property
  have h1 : (driftReader h (kineticCof10.coeff 8)).coeff 1=(kineticDriftCof10Coeff8Row1Norm h).val :=
    (kineticDriftCof10Coeff8Row1Norm h).property
  have h2 : (driftReader h (kineticCof10.coeff 8)).coeff 2=(kineticDriftCof10Coeff8Row2Norm h).val :=
    (kineticDriftCof10Coeff8Row2Norm h).property
  have h3 : (driftReader h (kineticCof10.coeff 8)).coeff 3=(kineticDriftCof10Coeff8Row3Norm h).val :=
    (kineticDriftCof10Coeff8Row3Norm h).property
  have h4 : (driftReader h (kineticCof10.coeff 8)).coeff 4=(kineticDriftCof10Coeff8Row4Norm h).val :=
    (kineticDriftCof10Coeff8Row4Norm h).property
  simpa only [kineticDriftCell,kineticDriftCof10Row8,h0,h1,h2,h3,h4] using he

theorem kineticDriftCof10_rows (h : ℂ) (j b : ℕ) :
    kineticDriftCell h kineticCof10 j b=(if j=0 then kineticDriftCof10Row0 h b else 0) + (if j=1 then kineticDriftCof10Row1 h b else 0) + (if j=2 then kineticDriftCof10Row2 h b else 0) + (if j=3 then kineticDriftCof10Row3 h b else 0) + (if j=4 then kineticDriftCof10Row4 h b else 0) + (if j=5 then kineticDriftCof10Row5 h b else 0) + (if j=6 then kineticDriftCof10Row6 h b else 0) + (if j=7 then kineticDriftCof10Row7 h b else 0) + (if j=8 then kineticDriftCof10Row8 h b else 0) := by
  by_cases hj : j≤8
  · interval_cases j
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof10Coeff0_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof10Coeff1_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof10Coeff2_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof10Coeff3_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof10Coeff4_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof10Coeff5_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof10Coeff6_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof10Coeff7_rows h b
    · norm_num only
      simpa only [ite_true,ite_false,zero_add,add_zero] using kineticDriftCof10Coeff8_rows h b
  · have hp : kineticCof10.coeff j=0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (kineticCof10_degree.trans_lt (by omega))
    simp only [kineticDriftCell,hp,map_zero,Polynomial.coeff_zero,if_neg (show j≠0 by omega),if_neg (show j≠1 by omega),if_neg (show j≠2 by omega),if_neg (show j≠3 by omega),if_neg (show j≠4 by omega),if_neg (show j≠5 by omega),if_neg (show j≠6 by omega),if_neg (show j≠7 by omega),if_neg (show j≠8 by omega),zero_add]

end
end HTGeometry.ThetaRatioKineticContraction
