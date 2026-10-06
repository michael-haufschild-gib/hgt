import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSecondSource
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def kineticSourcePart2Coeff2Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 2 1=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 2 1=kineticDriftCell h (kineticCof2*kineticBlock2) 2 1 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff2Row0Norm,kineticDriftCof2Coeff2Row1Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff2Row0Norm,kineticDriftBlock2Coeff2Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff2Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 2 1=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 2 1=kineticDriftCell h (kineticCof4*kineticBlock4) 2 1 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff2Row0Norm,kineticDriftCof4Coeff2Row1Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff2Row0Norm,kineticDriftBlock4Coeff2Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff2Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 2 1=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 2 1=kineticDriftCell h (kineticCof6*kineticBlock6) 2 1 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff2Row0Norm,kineticDriftCof6Coeff2Row1Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff2Row0Norm,kineticDriftBlock6Coeff2Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff2Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 2 1=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 2 1=kineticDriftCell h (kineticCof8*kineticBlock8) 2 1 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff2Row0Norm,kineticDriftCof8Coeff2Row1Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff2Row0Norm,kineticDriftBlock8Coeff2Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff2Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 2 1=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 2 1=kineticDriftCell h (kineticCof10*kineticBlock10) 2 1 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff2Row0Norm,kineticDriftCof10Coeff2Row1Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff2Row0Norm,kineticDriftBlock10Coeff2Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff2Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 2 2=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 2 2=kineticDriftCell h (kineticCof2*kineticBlock2) 2 2 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff2Row0Norm,kineticDriftCof2Coeff2Row1Norm,kineticDriftCof2Coeff2Row2Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm,kineticDriftBlock2Coeff2Row0Norm,kineticDriftBlock2Coeff2Row1Norm,kineticDriftBlock2Coeff2Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff2Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 2 2=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 2 2=kineticDriftCell h (kineticCof4*kineticBlock4) 2 2 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff2Row0Norm,kineticDriftCof4Coeff2Row1Norm,kineticDriftCof4Coeff2Row2Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff2Row0Norm,kineticDriftBlock4Coeff2Row1Norm,kineticDriftBlock4Coeff2Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff2Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 2 2=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 2 2=kineticDriftCell h (kineticCof6*kineticBlock6) 2 2 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff2Row0Norm,kineticDriftCof6Coeff2Row1Norm,kineticDriftCof6Coeff2Row2Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff2Row0Norm,kineticDriftBlock6Coeff2Row1Norm,kineticDriftBlock6Coeff2Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff2Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 2 2=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 2 2=kineticDriftCell h (kineticCof8*kineticBlock8) 2 2 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff2Row0Norm,kineticDriftCof8Coeff2Row1Norm,kineticDriftCof8Coeff2Row2Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff2Row0Norm,kineticDriftBlock8Coeff2Row1Norm,kineticDriftBlock8Coeff2Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff2Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 2 2=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 2 2=kineticDriftCell h (kineticCof10*kineticBlock10) 2 2 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff2Row0Norm,kineticDriftCof10Coeff2Row1Norm,kineticDriftCof10Coeff2Row2Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff2Row0Norm,kineticDriftBlock10Coeff2Row1Norm,kineticDriftBlock10Coeff2Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff2Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 2 3=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 2 3=kineticDriftCell h (kineticCof2*kineticBlock2) 2 3 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff1Row3Norm,kineticDriftCof2Coeff2Row0Norm,kineticDriftCof2Coeff2Row1Norm,kineticDriftCof2Coeff2Row2Norm,kineticDriftCof2Coeff2Row3Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm,kineticDriftBlock2Coeff2Row0Norm,kineticDriftBlock2Coeff2Row1Norm,kineticDriftBlock2Coeff2Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff2Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 2 3=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 2 3=kineticDriftCell h (kineticCof4*kineticBlock4) 2 3 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff1Row3Norm,kineticDriftCof4Coeff2Row0Norm,kineticDriftCof4Coeff2Row1Norm,kineticDriftCof4Coeff2Row2Norm,kineticDriftCof4Coeff2Row3Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff1Row3Norm,kineticDriftBlock4Coeff2Row0Norm,kineticDriftBlock4Coeff2Row1Norm,kineticDriftBlock4Coeff2Row2Norm,kineticDriftBlock4Coeff2Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff2Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 2 3=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 2 3=kineticDriftCell h (kineticCof6*kineticBlock6) 2 3 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff1Row3Norm,kineticDriftCof6Coeff2Row0Norm,kineticDriftCof6Coeff2Row1Norm,kineticDriftCof6Coeff2Row2Norm,kineticDriftCof6Coeff2Row3Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff1Row3Norm,kineticDriftBlock6Coeff2Row0Norm,kineticDriftBlock6Coeff2Row1Norm,kineticDriftBlock6Coeff2Row2Norm,kineticDriftBlock6Coeff2Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff2Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 2 3=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 2 3=kineticDriftCell h (kineticCof8*kineticBlock8) 2 3 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff1Row3Norm,kineticDriftCof8Coeff2Row0Norm,kineticDriftCof8Coeff2Row1Norm,kineticDriftCof8Coeff2Row2Norm,kineticDriftCof8Coeff2Row3Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff1Row3Norm,kineticDriftBlock8Coeff2Row0Norm,kineticDriftBlock8Coeff2Row1Norm,kineticDriftBlock8Coeff2Row2Norm,kineticDriftBlock8Coeff2Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff2Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 2 3=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 2 3=kineticDriftCell h (kineticCof10*kineticBlock10) 2 3 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff1Row3Norm,kineticDriftCof10Coeff2Row0Norm,kineticDriftCof10Coeff2Row1Norm,kineticDriftCof10Coeff2Row2Norm,kineticDriftCof10Coeff2Row3Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff1Row3Norm,kineticDriftBlock10Coeff2Row0Norm,kineticDriftBlock10Coeff2Row1Norm,kineticDriftBlock10Coeff2Row2Norm,kineticDriftBlock10Coeff2Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff2Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 2 4=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 2 4=kineticDriftCell h (kineticCof2*kineticBlock2) 2 4 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm,kineticDriftCof2Coeff0Row4Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff1Row3Norm,kineticDriftCof2Coeff1Row4Norm,kineticDriftCof2Coeff2Row0Norm,kineticDriftCof2Coeff2Row1Norm,kineticDriftCof2Coeff2Row2Norm,kineticDriftCof2Coeff2Row3Norm,kineticDriftCof2Coeff2Row4Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm,kineticDriftBlock2Coeff2Row0Norm,kineticDriftBlock2Coeff2Row1Norm,kineticDriftBlock2Coeff2Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff2Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 2 4=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 2 4=kineticDriftCell h (kineticCof4*kineticBlock4) 2 4 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff0Row4Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff1Row3Norm,kineticDriftCof4Coeff1Row4Norm,kineticDriftCof4Coeff2Row0Norm,kineticDriftCof4Coeff2Row1Norm,kineticDriftCof4Coeff2Row2Norm,kineticDriftCof4Coeff2Row3Norm,kineticDriftCof4Coeff2Row4Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff1Row3Norm,kineticDriftBlock4Coeff2Row0Norm,kineticDriftBlock4Coeff2Row1Norm,kineticDriftBlock4Coeff2Row2Norm,kineticDriftBlock4Coeff2Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff2Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 2 4=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 2 4=kineticDriftCell h (kineticCof6*kineticBlock6) 2 4 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff0Row4Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff1Row3Norm,kineticDriftCof6Coeff1Row4Norm,kineticDriftCof6Coeff2Row0Norm,kineticDriftCof6Coeff2Row1Norm,kineticDriftCof6Coeff2Row2Norm,kineticDriftCof6Coeff2Row3Norm,kineticDriftCof6Coeff2Row4Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff0Row4Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff1Row3Norm,kineticDriftBlock6Coeff1Row4Norm,kineticDriftBlock6Coeff2Row0Norm,kineticDriftBlock6Coeff2Row1Norm,kineticDriftBlock6Coeff2Row2Norm,kineticDriftBlock6Coeff2Row3Norm,kineticDriftBlock6Coeff2Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff2Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 2 4=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 2 4=kineticDriftCell h (kineticCof8*kineticBlock8) 2 4 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff0Row4Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff1Row3Norm,kineticDriftCof8Coeff1Row4Norm,kineticDriftCof8Coeff2Row0Norm,kineticDriftCof8Coeff2Row1Norm,kineticDriftCof8Coeff2Row2Norm,kineticDriftCof8Coeff2Row3Norm,kineticDriftCof8Coeff2Row4Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff0Row4Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff1Row3Norm,kineticDriftBlock8Coeff1Row4Norm,kineticDriftBlock8Coeff2Row0Norm,kineticDriftBlock8Coeff2Row1Norm,kineticDriftBlock8Coeff2Row2Norm,kineticDriftBlock8Coeff2Row3Norm,kineticDriftBlock8Coeff2Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff2Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 2 4=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 2 4=kineticDriftCell h (kineticCof10*kineticBlock10) 2 4 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff0Row4Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff1Row3Norm,kineticDriftCof10Coeff1Row4Norm,kineticDriftCof10Coeff2Row0Norm,kineticDriftCof10Coeff2Row1Norm,kineticDriftCof10Coeff2Row2Norm,kineticDriftCof10Coeff2Row3Norm,kineticDriftCof10Coeff2Row4Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff0Row4Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff1Row3Norm,kineticDriftBlock10Coeff1Row4Norm,kineticDriftBlock10Coeff2Row0Norm,kineticDriftBlock10Coeff2Row1Norm,kineticDriftBlock10Coeff2Row2Norm,kineticDriftBlock10Coeff2Row3Norm,kineticDriftBlock10Coeff2Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff2Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 2 5=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 2 5=kineticDriftCell h (kineticCof2*kineticBlock2) 2 5 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm,kineticDriftCof2Coeff0Row4Norm,kineticDriftCof2Coeff0Row5Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff1Row3Norm,kineticDriftCof2Coeff1Row4Norm,kineticDriftCof2Coeff1Row5Norm,kineticDriftCof2Coeff2Row0Norm,kineticDriftCof2Coeff2Row1Norm,kineticDriftCof2Coeff2Row2Norm,kineticDriftCof2Coeff2Row3Norm,kineticDriftCof2Coeff2Row4Norm,kineticDriftCof2Coeff2Row5Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm,kineticDriftBlock2Coeff2Row0Norm,kineticDriftBlock2Coeff2Row1Norm,kineticDriftBlock2Coeff2Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff2Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 2 5=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 2 5=kineticDriftCell h (kineticCof4*kineticBlock4) 2 5 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff0Row4Norm,kineticDriftCof4Coeff0Row5Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff1Row3Norm,kineticDriftCof4Coeff1Row4Norm,kineticDriftCof4Coeff1Row5Norm,kineticDriftCof4Coeff2Row0Norm,kineticDriftCof4Coeff2Row1Norm,kineticDriftCof4Coeff2Row2Norm,kineticDriftCof4Coeff2Row3Norm,kineticDriftCof4Coeff2Row4Norm,kineticDriftCof4Coeff2Row5Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff1Row3Norm,kineticDriftBlock4Coeff2Row0Norm,kineticDriftBlock4Coeff2Row1Norm,kineticDriftBlock4Coeff2Row2Norm,kineticDriftBlock4Coeff2Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff2Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 2 5=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 2 5=kineticDriftCell h (kineticCof6*kineticBlock6) 2 5 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff0Row4Norm,kineticDriftCof6Coeff0Row5Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff1Row3Norm,kineticDriftCof6Coeff1Row4Norm,kineticDriftCof6Coeff1Row5Norm,kineticDriftCof6Coeff2Row0Norm,kineticDriftCof6Coeff2Row1Norm,kineticDriftCof6Coeff2Row2Norm,kineticDriftCof6Coeff2Row3Norm,kineticDriftCof6Coeff2Row4Norm,kineticDriftCof6Coeff2Row5Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff0Row4Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff1Row3Norm,kineticDriftBlock6Coeff1Row4Norm,kineticDriftBlock6Coeff2Row0Norm,kineticDriftBlock6Coeff2Row1Norm,kineticDriftBlock6Coeff2Row2Norm,kineticDriftBlock6Coeff2Row3Norm,kineticDriftBlock6Coeff2Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff2Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 2 5=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 2 5=kineticDriftCell h (kineticCof8*kineticBlock8) 2 5 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff0Row4Norm,kineticDriftCof8Coeff0Row5Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff1Row3Norm,kineticDriftCof8Coeff1Row4Norm,kineticDriftCof8Coeff1Row5Norm,kineticDriftCof8Coeff2Row0Norm,kineticDriftCof8Coeff2Row1Norm,kineticDriftCof8Coeff2Row2Norm,kineticDriftCof8Coeff2Row3Norm,kineticDriftCof8Coeff2Row4Norm,kineticDriftCof8Coeff2Row5Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff0Row4Norm,kineticDriftBlock8Coeff0Row5Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff1Row3Norm,kineticDriftBlock8Coeff1Row4Norm,kineticDriftBlock8Coeff1Row5Norm,kineticDriftBlock8Coeff2Row0Norm,kineticDriftBlock8Coeff2Row1Norm,kineticDriftBlock8Coeff2Row2Norm,kineticDriftBlock8Coeff2Row3Norm,kineticDriftBlock8Coeff2Row4Norm,kineticDriftBlock8Coeff2Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff2Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 2 5=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 2 5=kineticDriftCell h (kineticCof10*kineticBlock10) 2 5 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff0Row4Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff1Row3Norm,kineticDriftCof10Coeff1Row4Norm,kineticDriftCof10Coeff2Row0Norm,kineticDriftCof10Coeff2Row1Norm,kineticDriftCof10Coeff2Row2Norm,kineticDriftCof10Coeff2Row3Norm,kineticDriftCof10Coeff2Row4Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff0Row4Norm,kineticDriftBlock10Coeff0Row5Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff1Row3Norm,kineticDriftBlock10Coeff1Row4Norm,kineticDriftBlock10Coeff1Row5Norm,kineticDriftBlock10Coeff2Row0Norm,kineticDriftBlock10Coeff2Row1Norm,kineticDriftBlock10Coeff2Row2Norm,kineticDriftBlock10Coeff2Row3Norm,kineticDriftBlock10Coeff2Row4Norm,kineticDriftBlock10Coeff2Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff2Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 2 6=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 2 6=kineticDriftCell h (kineticCof2*kineticBlock2) 2 6 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm,kineticDriftCof2Coeff0Row4Norm,kineticDriftCof2Coeff0Row5Norm,kineticDriftCof2Coeff0Row6Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff1Row3Norm,kineticDriftCof2Coeff1Row4Norm,kineticDriftCof2Coeff1Row5Norm,kineticDriftCof2Coeff1Row6Norm,kineticDriftCof2Coeff2Row0Norm,kineticDriftCof2Coeff2Row1Norm,kineticDriftCof2Coeff2Row2Norm,kineticDriftCof2Coeff2Row3Norm,kineticDriftCof2Coeff2Row4Norm,kineticDriftCof2Coeff2Row5Norm,kineticDriftCof2Coeff2Row6Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm,kineticDriftBlock2Coeff2Row0Norm,kineticDriftBlock2Coeff2Row1Norm,kineticDriftBlock2Coeff2Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff2Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 2 6=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 2 6=kineticDriftCell h (kineticCof4*kineticBlock4) 2 6 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff0Row4Norm,kineticDriftCof4Coeff0Row5Norm,kineticDriftCof4Coeff0Row6Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff1Row3Norm,kineticDriftCof4Coeff1Row4Norm,kineticDriftCof4Coeff1Row5Norm,kineticDriftCof4Coeff1Row6Norm,kineticDriftCof4Coeff2Row0Norm,kineticDriftCof4Coeff2Row1Norm,kineticDriftCof4Coeff2Row2Norm,kineticDriftCof4Coeff2Row3Norm,kineticDriftCof4Coeff2Row4Norm,kineticDriftCof4Coeff2Row5Norm,kineticDriftCof4Coeff2Row6Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff1Row3Norm,kineticDriftBlock4Coeff2Row0Norm,kineticDriftBlock4Coeff2Row1Norm,kineticDriftBlock4Coeff2Row2Norm,kineticDriftBlock4Coeff2Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff2Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 2 6=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 2 6=kineticDriftCell h (kineticCof6*kineticBlock6) 2 6 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff0Row4Norm,kineticDriftCof6Coeff0Row5Norm,kineticDriftCof6Coeff0Row6Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff1Row3Norm,kineticDriftCof6Coeff1Row4Norm,kineticDriftCof6Coeff1Row5Norm,kineticDriftCof6Coeff1Row6Norm,kineticDriftCof6Coeff2Row0Norm,kineticDriftCof6Coeff2Row1Norm,kineticDriftCof6Coeff2Row2Norm,kineticDriftCof6Coeff2Row3Norm,kineticDriftCof6Coeff2Row4Norm,kineticDriftCof6Coeff2Row5Norm,kineticDriftCof6Coeff2Row6Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff0Row4Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff1Row3Norm,kineticDriftBlock6Coeff1Row4Norm,kineticDriftBlock6Coeff2Row0Norm,kineticDriftBlock6Coeff2Row1Norm,kineticDriftBlock6Coeff2Row2Norm,kineticDriftBlock6Coeff2Row3Norm,kineticDriftBlock6Coeff2Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff2Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 2 6=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 2 6=kineticDriftCell h (kineticCof8*kineticBlock8) 2 6 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff0Row4Norm,kineticDriftCof8Coeff0Row5Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff1Row3Norm,kineticDriftCof8Coeff1Row4Norm,kineticDriftCof8Coeff1Row5Norm,kineticDriftCof8Coeff2Row0Norm,kineticDriftCof8Coeff2Row1Norm,kineticDriftCof8Coeff2Row2Norm,kineticDriftCof8Coeff2Row3Norm,kineticDriftCof8Coeff2Row4Norm,kineticDriftCof8Coeff2Row5Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff0Row4Norm,kineticDriftBlock8Coeff0Row5Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff1Row3Norm,kineticDriftBlock8Coeff1Row4Norm,kineticDriftBlock8Coeff1Row5Norm,kineticDriftBlock8Coeff2Row0Norm,kineticDriftBlock8Coeff2Row1Norm,kineticDriftBlock8Coeff2Row2Norm,kineticDriftBlock8Coeff2Row3Norm,kineticDriftBlock8Coeff2Row4Norm,kineticDriftBlock8Coeff2Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff2Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 2 6=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 2 6=kineticDriftCell h (kineticCof10*kineticBlock10) 2 6 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff0Row4Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff1Row3Norm,kineticDriftCof10Coeff1Row4Norm,kineticDriftCof10Coeff2Row0Norm,kineticDriftCof10Coeff2Row1Norm,kineticDriftCof10Coeff2Row2Norm,kineticDriftCof10Coeff2Row3Norm,kineticDriftCof10Coeff2Row4Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff0Row4Norm,kineticDriftBlock10Coeff0Row5Norm,kineticDriftBlock10Coeff0Row6Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff1Row3Norm,kineticDriftBlock10Coeff1Row4Norm,kineticDriftBlock10Coeff1Row5Norm,kineticDriftBlock10Coeff1Row6Norm,kineticDriftBlock10Coeff2Row0Norm,kineticDriftBlock10Coeff2Row1Norm,kineticDriftBlock10Coeff2Row2Norm,kineticDriftBlock10Coeff2Row3Norm,kineticDriftBlock10Coeff2Row4Norm,kineticDriftBlock10Coeff2Row5Norm,kineticDriftBlock10Coeff2Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff2Row7Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 2 7=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 2 7=kineticDriftCell h (kineticCof2*kineticBlock2) 2 7 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm,kineticDriftCof2Coeff0Row4Norm,kineticDriftCof2Coeff0Row5Norm,kineticDriftCof2Coeff0Row6Norm,kineticDriftCof2Coeff0Row7Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff1Row3Norm,kineticDriftCof2Coeff1Row4Norm,kineticDriftCof2Coeff1Row5Norm,kineticDriftCof2Coeff1Row6Norm,kineticDriftCof2Coeff1Row7Norm,kineticDriftCof2Coeff2Row0Norm,kineticDriftCof2Coeff2Row1Norm,kineticDriftCof2Coeff2Row2Norm,kineticDriftCof2Coeff2Row3Norm,kineticDriftCof2Coeff2Row4Norm,kineticDriftCof2Coeff2Row5Norm,kineticDriftCof2Coeff2Row6Norm,kineticDriftCof2Coeff2Row7Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm,kineticDriftBlock2Coeff2Row0Norm,kineticDriftBlock2Coeff2Row1Norm,kineticDriftBlock2Coeff2Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff2Row7Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 2 7=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 2 7=kineticDriftCell h (kineticCof4*kineticBlock4) 2 7 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff0Row4Norm,kineticDriftCof4Coeff0Row5Norm,kineticDriftCof4Coeff0Row6Norm,kineticDriftCof4Coeff0Row7Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff1Row3Norm,kineticDriftCof4Coeff1Row4Norm,kineticDriftCof4Coeff1Row5Norm,kineticDriftCof4Coeff1Row6Norm,kineticDriftCof4Coeff1Row7Norm,kineticDriftCof4Coeff2Row0Norm,kineticDriftCof4Coeff2Row1Norm,kineticDriftCof4Coeff2Row2Norm,kineticDriftCof4Coeff2Row3Norm,kineticDriftCof4Coeff2Row4Norm,kineticDriftCof4Coeff2Row5Norm,kineticDriftCof4Coeff2Row6Norm,kineticDriftCof4Coeff2Row7Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff1Row3Norm,kineticDriftBlock4Coeff2Row0Norm,kineticDriftBlock4Coeff2Row1Norm,kineticDriftBlock4Coeff2Row2Norm,kineticDriftBlock4Coeff2Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff2Row7Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 2 7=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 2 7=kineticDriftCell h (kineticCof6*kineticBlock6) 2 7 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff0Row4Norm,kineticDriftCof6Coeff0Row5Norm,kineticDriftCof6Coeff0Row6Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff1Row3Norm,kineticDriftCof6Coeff1Row4Norm,kineticDriftCof6Coeff1Row5Norm,kineticDriftCof6Coeff1Row6Norm,kineticDriftCof6Coeff2Row0Norm,kineticDriftCof6Coeff2Row1Norm,kineticDriftCof6Coeff2Row2Norm,kineticDriftCof6Coeff2Row3Norm,kineticDriftCof6Coeff2Row4Norm,kineticDriftCof6Coeff2Row5Norm,kineticDriftCof6Coeff2Row6Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff0Row4Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff1Row3Norm,kineticDriftBlock6Coeff1Row4Norm,kineticDriftBlock6Coeff2Row0Norm,kineticDriftBlock6Coeff2Row1Norm,kineticDriftBlock6Coeff2Row2Norm,kineticDriftBlock6Coeff2Row3Norm,kineticDriftBlock6Coeff2Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff2Row7Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 2 7=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 2 7=kineticDriftCell h (kineticCof8*kineticBlock8) 2 7 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff0Row4Norm,kineticDriftCof8Coeff0Row5Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff1Row3Norm,kineticDriftCof8Coeff1Row4Norm,kineticDriftCof8Coeff1Row5Norm,kineticDriftCof8Coeff2Row0Norm,kineticDriftCof8Coeff2Row1Norm,kineticDriftCof8Coeff2Row2Norm,kineticDriftCof8Coeff2Row3Norm,kineticDriftCof8Coeff2Row4Norm,kineticDriftCof8Coeff2Row5Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff0Row4Norm,kineticDriftBlock8Coeff0Row5Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff1Row3Norm,kineticDriftBlock8Coeff1Row4Norm,kineticDriftBlock8Coeff1Row5Norm,kineticDriftBlock8Coeff2Row0Norm,kineticDriftBlock8Coeff2Row1Norm,kineticDriftBlock8Coeff2Row2Norm,kineticDriftBlock8Coeff2Row3Norm,kineticDriftBlock8Coeff2Row4Norm,kineticDriftBlock8Coeff2Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff2Row7Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 2 7=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 2 7=kineticDriftCell h (kineticCof10*kineticBlock10) 2 7 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff0Row4Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff1Row3Norm,kineticDriftCof10Coeff1Row4Norm,kineticDriftCof10Coeff2Row0Norm,kineticDriftCof10Coeff2Row1Norm,kineticDriftCof10Coeff2Row2Norm,kineticDriftCof10Coeff2Row3Norm,kineticDriftCof10Coeff2Row4Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff0Row4Norm,kineticDriftBlock10Coeff0Row5Norm,kineticDriftBlock10Coeff0Row6Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff1Row3Norm,kineticDriftBlock10Coeff1Row4Norm,kineticDriftBlock10Coeff1Row5Norm,kineticDriftBlock10Coeff1Row6Norm,kineticDriftBlock10Coeff2Row0Norm,kineticDriftBlock10Coeff2Row1Norm,kineticDriftBlock10Coeff2Row2Norm,kineticDriftBlock10Coeff2Row3Norm,kineticDriftBlock10Coeff2Row4Norm,kineticDriftBlock10Coeff2Row5Norm,kineticDriftBlock10Coeff2Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff2Row8Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 2 8=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 2 8=kineticDriftCell h (kineticCof2*kineticBlock2) 2 8 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm,kineticDriftCof2Coeff0Row4Norm,kineticDriftCof2Coeff0Row5Norm,kineticDriftCof2Coeff0Row6Norm,kineticDriftCof2Coeff0Row7Norm,kineticDriftCof2Coeff0Row8Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff1Row3Norm,kineticDriftCof2Coeff1Row4Norm,kineticDriftCof2Coeff1Row5Norm,kineticDriftCof2Coeff1Row6Norm,kineticDriftCof2Coeff1Row7Norm,kineticDriftCof2Coeff1Row8Norm,kineticDriftCof2Coeff2Row0Norm,kineticDriftCof2Coeff2Row1Norm,kineticDriftCof2Coeff2Row2Norm,kineticDriftCof2Coeff2Row3Norm,kineticDriftCof2Coeff2Row4Norm,kineticDriftCof2Coeff2Row5Norm,kineticDriftCof2Coeff2Row6Norm,kineticDriftCof2Coeff2Row7Norm,kineticDriftCof2Coeff2Row8Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm,kineticDriftBlock2Coeff2Row0Norm,kineticDriftBlock2Coeff2Row1Norm,kineticDriftBlock2Coeff2Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff2Row8Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 2 8=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 2 8=kineticDriftCell h (kineticCof4*kineticBlock4) 2 8 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff0Row4Norm,kineticDriftCof4Coeff0Row5Norm,kineticDriftCof4Coeff0Row6Norm,kineticDriftCof4Coeff0Row7Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff1Row3Norm,kineticDriftCof4Coeff1Row4Norm,kineticDriftCof4Coeff1Row5Norm,kineticDriftCof4Coeff1Row6Norm,kineticDriftCof4Coeff1Row7Norm,kineticDriftCof4Coeff2Row0Norm,kineticDriftCof4Coeff2Row1Norm,kineticDriftCof4Coeff2Row2Norm,kineticDriftCof4Coeff2Row3Norm,kineticDriftCof4Coeff2Row4Norm,kineticDriftCof4Coeff2Row5Norm,kineticDriftCof4Coeff2Row6Norm,kineticDriftCof4Coeff2Row7Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff1Row3Norm,kineticDriftBlock4Coeff2Row0Norm,kineticDriftBlock4Coeff2Row1Norm,kineticDriftBlock4Coeff2Row2Norm,kineticDriftBlock4Coeff2Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff2Row8Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 2 8=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 2 8=kineticDriftCell h (kineticCof6*kineticBlock6) 2 8 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff0Row4Norm,kineticDriftCof6Coeff0Row5Norm,kineticDriftCof6Coeff0Row6Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff1Row3Norm,kineticDriftCof6Coeff1Row4Norm,kineticDriftCof6Coeff1Row5Norm,kineticDriftCof6Coeff1Row6Norm,kineticDriftCof6Coeff2Row0Norm,kineticDriftCof6Coeff2Row1Norm,kineticDriftCof6Coeff2Row2Norm,kineticDriftCof6Coeff2Row3Norm,kineticDriftCof6Coeff2Row4Norm,kineticDriftCof6Coeff2Row5Norm,kineticDriftCof6Coeff2Row6Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff0Row4Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff1Row3Norm,kineticDriftBlock6Coeff1Row4Norm,kineticDriftBlock6Coeff2Row0Norm,kineticDriftBlock6Coeff2Row1Norm,kineticDriftBlock6Coeff2Row2Norm,kineticDriftBlock6Coeff2Row3Norm,kineticDriftBlock6Coeff2Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff2Row8Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 2 8=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 2 8=kineticDriftCell h (kineticCof8*kineticBlock8) 2 8 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff0Row4Norm,kineticDriftCof8Coeff0Row5Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff1Row3Norm,kineticDriftCof8Coeff1Row4Norm,kineticDriftCof8Coeff1Row5Norm,kineticDriftCof8Coeff2Row0Norm,kineticDriftCof8Coeff2Row1Norm,kineticDriftCof8Coeff2Row2Norm,kineticDriftCof8Coeff2Row3Norm,kineticDriftCof8Coeff2Row4Norm,kineticDriftCof8Coeff2Row5Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff0Row4Norm,kineticDriftBlock8Coeff0Row5Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff1Row3Norm,kineticDriftBlock8Coeff1Row4Norm,kineticDriftBlock8Coeff1Row5Norm,kineticDriftBlock8Coeff2Row0Norm,kineticDriftBlock8Coeff2Row1Norm,kineticDriftBlock8Coeff2Row2Norm,kineticDriftBlock8Coeff2Row3Norm,kineticDriftBlock8Coeff2Row4Norm,kineticDriftBlock8Coeff2Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff2Row8Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 2 8=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 2 8=kineticDriftCell h (kineticCof10*kineticBlock10) 2 8 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff0Row4Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff1Row3Norm,kineticDriftCof10Coeff1Row4Norm,kineticDriftCof10Coeff2Row0Norm,kineticDriftCof10Coeff2Row1Norm,kineticDriftCof10Coeff2Row2Norm,kineticDriftCof10Coeff2Row3Norm,kineticDriftCof10Coeff2Row4Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff0Row4Norm,kineticDriftBlock10Coeff0Row5Norm,kineticDriftBlock10Coeff0Row6Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff1Row3Norm,kineticDriftBlock10Coeff1Row4Norm,kineticDriftBlock10Coeff1Row5Norm,kineticDriftBlock10Coeff1Row6Norm,kineticDriftBlock10Coeff2Row0Norm,kineticDriftBlock10Coeff2Row1Norm,kineticDriftBlock10Coeff2Row2Norm,kineticDriftBlock10Coeff2Row3Norm,kineticDriftBlock10Coeff2Row4Norm,kineticDriftBlock10Coeff2Row5Norm,kineticDriftBlock10Coeff2Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff2Row9Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 2 9=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 2 9=kineticDriftCell h (kineticCof2*kineticBlock2) 2 9 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm,kineticDriftCof2Coeff0Row4Norm,kineticDriftCof2Coeff0Row5Norm,kineticDriftCof2Coeff0Row6Norm,kineticDriftCof2Coeff0Row7Norm,kineticDriftCof2Coeff0Row8Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff1Row3Norm,kineticDriftCof2Coeff1Row4Norm,kineticDriftCof2Coeff1Row5Norm,kineticDriftCof2Coeff1Row6Norm,kineticDriftCof2Coeff1Row7Norm,kineticDriftCof2Coeff1Row8Norm,kineticDriftCof2Coeff2Row0Norm,kineticDriftCof2Coeff2Row1Norm,kineticDriftCof2Coeff2Row2Norm,kineticDriftCof2Coeff2Row3Norm,kineticDriftCof2Coeff2Row4Norm,kineticDriftCof2Coeff2Row5Norm,kineticDriftCof2Coeff2Row6Norm,kineticDriftCof2Coeff2Row7Norm,kineticDriftCof2Coeff2Row8Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm,kineticDriftBlock2Coeff2Row0Norm,kineticDriftBlock2Coeff2Row1Norm,kineticDriftBlock2Coeff2Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff2Row9Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 2 9=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 2 9=kineticDriftCell h (kineticCof4*kineticBlock4) 2 9 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff0Row4Norm,kineticDriftCof4Coeff0Row5Norm,kineticDriftCof4Coeff0Row6Norm,kineticDriftCof4Coeff0Row7Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff1Row3Norm,kineticDriftCof4Coeff1Row4Norm,kineticDriftCof4Coeff1Row5Norm,kineticDriftCof4Coeff1Row6Norm,kineticDriftCof4Coeff1Row7Norm,kineticDriftCof4Coeff2Row0Norm,kineticDriftCof4Coeff2Row1Norm,kineticDriftCof4Coeff2Row2Norm,kineticDriftCof4Coeff2Row3Norm,kineticDriftCof4Coeff2Row4Norm,kineticDriftCof4Coeff2Row5Norm,kineticDriftCof4Coeff2Row6Norm,kineticDriftCof4Coeff2Row7Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff1Row3Norm,kineticDriftBlock4Coeff2Row0Norm,kineticDriftBlock4Coeff2Row1Norm,kineticDriftBlock4Coeff2Row2Norm,kineticDriftBlock4Coeff2Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff2Row9Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 2 9=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 2 9=kineticDriftCell h (kineticCof6*kineticBlock6) 2 9 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff0Row4Norm,kineticDriftCof6Coeff0Row5Norm,kineticDriftCof6Coeff0Row6Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff1Row3Norm,kineticDriftCof6Coeff1Row4Norm,kineticDriftCof6Coeff1Row5Norm,kineticDriftCof6Coeff1Row6Norm,kineticDriftCof6Coeff2Row0Norm,kineticDriftCof6Coeff2Row1Norm,kineticDriftCof6Coeff2Row2Norm,kineticDriftCof6Coeff2Row3Norm,kineticDriftCof6Coeff2Row4Norm,kineticDriftCof6Coeff2Row5Norm,kineticDriftCof6Coeff2Row6Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff0Row4Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff1Row3Norm,kineticDriftBlock6Coeff1Row4Norm,kineticDriftBlock6Coeff2Row0Norm,kineticDriftBlock6Coeff2Row1Norm,kineticDriftBlock6Coeff2Row2Norm,kineticDriftBlock6Coeff2Row3Norm,kineticDriftBlock6Coeff2Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff2Row9Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 2 9=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 2 9=kineticDriftCell h (kineticCof8*kineticBlock8) 2 9 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff0Row4Norm,kineticDriftCof8Coeff0Row5Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff1Row3Norm,kineticDriftCof8Coeff1Row4Norm,kineticDriftCof8Coeff1Row5Norm,kineticDriftCof8Coeff2Row0Norm,kineticDriftCof8Coeff2Row1Norm,kineticDriftCof8Coeff2Row2Norm,kineticDriftCof8Coeff2Row3Norm,kineticDriftCof8Coeff2Row4Norm,kineticDriftCof8Coeff2Row5Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff0Row4Norm,kineticDriftBlock8Coeff0Row5Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff1Row3Norm,kineticDriftBlock8Coeff1Row4Norm,kineticDriftBlock8Coeff1Row5Norm,kineticDriftBlock8Coeff2Row0Norm,kineticDriftBlock8Coeff2Row1Norm,kineticDriftBlock8Coeff2Row2Norm,kineticDriftBlock8Coeff2Row3Norm,kineticDriftBlock8Coeff2Row4Norm,kineticDriftBlock8Coeff2Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff2Row9Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 2 9=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 2 9=kineticDriftCell h (kineticCof10*kineticBlock10) 2 9 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff0Row4Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff1Row3Norm,kineticDriftCof10Coeff1Row4Norm,kineticDriftCof10Coeff2Row0Norm,kineticDriftCof10Coeff2Row1Norm,kineticDriftCof10Coeff2Row2Norm,kineticDriftCof10Coeff2Row3Norm,kineticDriftCof10Coeff2Row4Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff0Row4Norm,kineticDriftBlock10Coeff0Row5Norm,kineticDriftBlock10Coeff0Row6Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff1Row3Norm,kineticDriftBlock10Coeff1Row4Norm,kineticDriftBlock10Coeff1Row5Norm,kineticDriftBlock10Coeff1Row6Norm,kineticDriftBlock10Coeff2Row0Norm,kineticDriftBlock10Coeff2Row1Norm,kineticDriftBlock10Coeff2Row2Norm,kineticDriftBlock10Coeff2Row3Norm,kineticDriftBlock10Coeff2Row4Norm,kineticDriftBlock10Coeff2Row5Norm,kineticDriftBlock10Coeff2Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff2Row10Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 2 10=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 2 10=kineticDriftCell h (kineticCof2*kineticBlock2) 2 10 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm,kineticDriftCof2Coeff0Row4Norm,kineticDriftCof2Coeff0Row5Norm,kineticDriftCof2Coeff0Row6Norm,kineticDriftCof2Coeff0Row7Norm,kineticDriftCof2Coeff0Row8Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff1Row3Norm,kineticDriftCof2Coeff1Row4Norm,kineticDriftCof2Coeff1Row5Norm,kineticDriftCof2Coeff1Row6Norm,kineticDriftCof2Coeff1Row7Norm,kineticDriftCof2Coeff1Row8Norm,kineticDriftCof2Coeff2Row0Norm,kineticDriftCof2Coeff2Row1Norm,kineticDriftCof2Coeff2Row2Norm,kineticDriftCof2Coeff2Row3Norm,kineticDriftCof2Coeff2Row4Norm,kineticDriftCof2Coeff2Row5Norm,kineticDriftCof2Coeff2Row6Norm,kineticDriftCof2Coeff2Row7Norm,kineticDriftCof2Coeff2Row8Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm,kineticDriftBlock2Coeff2Row0Norm,kineticDriftBlock2Coeff2Row1Norm,kineticDriftBlock2Coeff2Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff2Row10Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 2 10=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 2 10=kineticDriftCell h (kineticCof4*kineticBlock4) 2 10 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff0Row4Norm,kineticDriftCof4Coeff0Row5Norm,kineticDriftCof4Coeff0Row6Norm,kineticDriftCof4Coeff0Row7Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff1Row3Norm,kineticDriftCof4Coeff1Row4Norm,kineticDriftCof4Coeff1Row5Norm,kineticDriftCof4Coeff1Row6Norm,kineticDriftCof4Coeff1Row7Norm,kineticDriftCof4Coeff2Row0Norm,kineticDriftCof4Coeff2Row1Norm,kineticDriftCof4Coeff2Row2Norm,kineticDriftCof4Coeff2Row3Norm,kineticDriftCof4Coeff2Row4Norm,kineticDriftCof4Coeff2Row5Norm,kineticDriftCof4Coeff2Row6Norm,kineticDriftCof4Coeff2Row7Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff1Row3Norm,kineticDriftBlock4Coeff2Row0Norm,kineticDriftBlock4Coeff2Row1Norm,kineticDriftBlock4Coeff2Row2Norm,kineticDriftBlock4Coeff2Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff2Row10Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 2 10=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 2 10=kineticDriftCell h (kineticCof6*kineticBlock6) 2 10 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff0Row4Norm,kineticDriftCof6Coeff0Row5Norm,kineticDriftCof6Coeff0Row6Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff1Row3Norm,kineticDriftCof6Coeff1Row4Norm,kineticDriftCof6Coeff1Row5Norm,kineticDriftCof6Coeff1Row6Norm,kineticDriftCof6Coeff2Row0Norm,kineticDriftCof6Coeff2Row1Norm,kineticDriftCof6Coeff2Row2Norm,kineticDriftCof6Coeff2Row3Norm,kineticDriftCof6Coeff2Row4Norm,kineticDriftCof6Coeff2Row5Norm,kineticDriftCof6Coeff2Row6Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff0Row4Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff1Row3Norm,kineticDriftBlock6Coeff1Row4Norm,kineticDriftBlock6Coeff2Row0Norm,kineticDriftBlock6Coeff2Row1Norm,kineticDriftBlock6Coeff2Row2Norm,kineticDriftBlock6Coeff2Row3Norm,kineticDriftBlock6Coeff2Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff2Row10Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 2 10=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 2 10=kineticDriftCell h (kineticCof8*kineticBlock8) 2 10 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff0Row4Norm,kineticDriftCof8Coeff0Row5Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff1Row3Norm,kineticDriftCof8Coeff1Row4Norm,kineticDriftCof8Coeff1Row5Norm,kineticDriftCof8Coeff2Row0Norm,kineticDriftCof8Coeff2Row1Norm,kineticDriftCof8Coeff2Row2Norm,kineticDriftCof8Coeff2Row3Norm,kineticDriftCof8Coeff2Row4Norm,kineticDriftCof8Coeff2Row5Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff0Row4Norm,kineticDriftBlock8Coeff0Row5Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff1Row3Norm,kineticDriftBlock8Coeff1Row4Norm,kineticDriftBlock8Coeff1Row5Norm,kineticDriftBlock8Coeff2Row0Norm,kineticDriftBlock8Coeff2Row1Norm,kineticDriftBlock8Coeff2Row2Norm,kineticDriftBlock8Coeff2Row3Norm,kineticDriftBlock8Coeff2Row4Norm,kineticDriftBlock8Coeff2Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff2Row10Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 2 10=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 2 10=kineticDriftCell h (kineticCof10*kineticBlock10) 2 10 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff0Row4Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff1Row3Norm,kineticDriftCof10Coeff1Row4Norm,kineticDriftCof10Coeff2Row0Norm,kineticDriftCof10Coeff2Row1Norm,kineticDriftCof10Coeff2Row2Norm,kineticDriftCof10Coeff2Row3Norm,kineticDriftCof10Coeff2Row4Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff0Row4Norm,kineticDriftBlock10Coeff0Row5Norm,kineticDriftBlock10Coeff0Row6Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff1Row3Norm,kineticDriftBlock10Coeff1Row4Norm,kineticDriftBlock10Coeff1Row5Norm,kineticDriftBlock10Coeff1Row6Norm,kineticDriftBlock10Coeff2Row0Norm,kineticDriftBlock10Coeff2Row1Norm,kineticDriftBlock10Coeff2Row2Norm,kineticDriftBlock10Coeff2Row3Norm,kineticDriftBlock10Coeff2Row4Norm,kineticDriftBlock10Coeff2Row5Norm,kineticDriftBlock10Coeff2Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

end
end HTGeometry.ThetaRatioKineticContraction

