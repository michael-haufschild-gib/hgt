import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSecondSource
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def kineticSourcePart2Coeff4Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 4 1=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 4 1=kineticDriftCell h (kineticCof2*kineticBlock2) 4 1 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftCof2Row3,kineticDriftCof2Row4,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2,kineticDriftBlock2Row3]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff2Row0Norm,kineticDriftCof2Coeff2Row1Norm,kineticDriftCof2Coeff3Row0Norm,kineticDriftCof2Coeff3Row1Norm,kineticDriftCof2Coeff4Row0Norm,kineticDriftCof2Coeff4Row1Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff2Row0Norm,kineticDriftBlock2Coeff2Row1Norm,kineticDriftBlock2Coeff3Row0Norm,kineticDriftBlock2Coeff3Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff4Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 4 1=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 4 1=kineticDriftCell h (kineticCof4*kineticBlock4) 4 1 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftCof4Row3,kineticDriftCof4Row4,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2,kineticDriftBlock4Row3,kineticDriftBlock4Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff2Row0Norm,kineticDriftCof4Coeff2Row1Norm,kineticDriftCof4Coeff3Row0Norm,kineticDriftCof4Coeff3Row1Norm,kineticDriftCof4Coeff4Row0Norm,kineticDriftCof4Coeff4Row1Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff2Row0Norm,kineticDriftBlock4Coeff2Row1Norm,kineticDriftBlock4Coeff3Row0Norm,kineticDriftBlock4Coeff3Row1Norm,kineticDriftBlock4Coeff4Row0Norm,kineticDriftBlock4Coeff4Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff4Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 4 1=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 4 1=kineticDriftCell h (kineticCof6*kineticBlock6) 4 1 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftCof6Row3,kineticDriftCof6Row4,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2,kineticDriftBlock6Row3,kineticDriftBlock6Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff2Row0Norm,kineticDriftCof6Coeff2Row1Norm,kineticDriftCof6Coeff3Row0Norm,kineticDriftCof6Coeff3Row1Norm,kineticDriftCof6Coeff4Row0Norm,kineticDriftCof6Coeff4Row1Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff2Row0Norm,kineticDriftBlock6Coeff2Row1Norm,kineticDriftBlock6Coeff3Row0Norm,kineticDriftBlock6Coeff3Row1Norm,kineticDriftBlock6Coeff4Row0Norm,kineticDriftBlock6Coeff4Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff4Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 4 1=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 4 1=kineticDriftCell h (kineticCof8*kineticBlock8) 4 1 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftCof8Row3,kineticDriftCof8Row4,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2,kineticDriftBlock8Row3,kineticDriftBlock8Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff2Row0Norm,kineticDriftCof8Coeff2Row1Norm,kineticDriftCof8Coeff3Row0Norm,kineticDriftCof8Coeff3Row1Norm,kineticDriftCof8Coeff4Row0Norm,kineticDriftCof8Coeff4Row1Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff2Row0Norm,kineticDriftBlock8Coeff2Row1Norm,kineticDriftBlock8Coeff3Row0Norm,kineticDriftBlock8Coeff3Row1Norm,kineticDriftBlock8Coeff4Row0Norm,kineticDriftBlock8Coeff4Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff4Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 4 1=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 4 1=kineticDriftCell h (kineticCof10*kineticBlock10) 4 1 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftCof10Row3,kineticDriftCof10Row4,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2,kineticDriftBlock10Row3,kineticDriftBlock10Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff2Row0Norm,kineticDriftCof10Coeff2Row1Norm,kineticDriftCof10Coeff3Row0Norm,kineticDriftCof10Coeff3Row1Norm,kineticDriftCof10Coeff4Row0Norm,kineticDriftCof10Coeff4Row1Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff2Row0Norm,kineticDriftBlock10Coeff2Row1Norm,kineticDriftBlock10Coeff3Row0Norm,kineticDriftBlock10Coeff3Row1Norm,kineticDriftBlock10Coeff4Row0Norm,kineticDriftBlock10Coeff4Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff4Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 4 2=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 4 2=kineticDriftCell h (kineticCof2*kineticBlock2) 4 2 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftCof2Row3,kineticDriftCof2Row4,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2,kineticDriftBlock2Row3]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff2Row0Norm,kineticDriftCof2Coeff2Row1Norm,kineticDriftCof2Coeff2Row2Norm,kineticDriftCof2Coeff3Row0Norm,kineticDriftCof2Coeff3Row1Norm,kineticDriftCof2Coeff3Row2Norm,kineticDriftCof2Coeff4Row0Norm,kineticDriftCof2Coeff4Row1Norm,kineticDriftCof2Coeff4Row2Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm,kineticDriftBlock2Coeff2Row0Norm,kineticDriftBlock2Coeff2Row1Norm,kineticDriftBlock2Coeff2Row2Norm,kineticDriftBlock2Coeff3Row0Norm,kineticDriftBlock2Coeff3Row1Norm,kineticDriftBlock2Coeff3Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff4Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 4 2=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 4 2=kineticDriftCell h (kineticCof4*kineticBlock4) 4 2 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftCof4Row3,kineticDriftCof4Row4,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2,kineticDriftBlock4Row3,kineticDriftBlock4Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff2Row0Norm,kineticDriftCof4Coeff2Row1Norm,kineticDriftCof4Coeff2Row2Norm,kineticDriftCof4Coeff3Row0Norm,kineticDriftCof4Coeff3Row1Norm,kineticDriftCof4Coeff3Row2Norm,kineticDriftCof4Coeff4Row0Norm,kineticDriftCof4Coeff4Row1Norm,kineticDriftCof4Coeff4Row2Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff2Row0Norm,kineticDriftBlock4Coeff2Row1Norm,kineticDriftBlock4Coeff2Row2Norm,kineticDriftBlock4Coeff3Row0Norm,kineticDriftBlock4Coeff3Row1Norm,kineticDriftBlock4Coeff3Row2Norm,kineticDriftBlock4Coeff4Row0Norm,kineticDriftBlock4Coeff4Row1Norm,kineticDriftBlock4Coeff4Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff4Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 4 2=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 4 2=kineticDriftCell h (kineticCof6*kineticBlock6) 4 2 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftCof6Row3,kineticDriftCof6Row4,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2,kineticDriftBlock6Row3,kineticDriftBlock6Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff2Row0Norm,kineticDriftCof6Coeff2Row1Norm,kineticDriftCof6Coeff2Row2Norm,kineticDriftCof6Coeff3Row0Norm,kineticDriftCof6Coeff3Row1Norm,kineticDriftCof6Coeff3Row2Norm,kineticDriftCof6Coeff4Row0Norm,kineticDriftCof6Coeff4Row1Norm,kineticDriftCof6Coeff4Row2Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff2Row0Norm,kineticDriftBlock6Coeff2Row1Norm,kineticDriftBlock6Coeff2Row2Norm,kineticDriftBlock6Coeff3Row0Norm,kineticDriftBlock6Coeff3Row1Norm,kineticDriftBlock6Coeff3Row2Norm,kineticDriftBlock6Coeff4Row0Norm,kineticDriftBlock6Coeff4Row1Norm,kineticDriftBlock6Coeff4Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff4Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 4 2=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 4 2=kineticDriftCell h (kineticCof8*kineticBlock8) 4 2 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftCof8Row3,kineticDriftCof8Row4,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2,kineticDriftBlock8Row3,kineticDriftBlock8Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff2Row0Norm,kineticDriftCof8Coeff2Row1Norm,kineticDriftCof8Coeff2Row2Norm,kineticDriftCof8Coeff3Row0Norm,kineticDriftCof8Coeff3Row1Norm,kineticDriftCof8Coeff3Row2Norm,kineticDriftCof8Coeff4Row0Norm,kineticDriftCof8Coeff4Row1Norm,kineticDriftCof8Coeff4Row2Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff2Row0Norm,kineticDriftBlock8Coeff2Row1Norm,kineticDriftBlock8Coeff2Row2Norm,kineticDriftBlock8Coeff3Row0Norm,kineticDriftBlock8Coeff3Row1Norm,kineticDriftBlock8Coeff3Row2Norm,kineticDriftBlock8Coeff4Row0Norm,kineticDriftBlock8Coeff4Row1Norm,kineticDriftBlock8Coeff4Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff4Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 4 2=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 4 2=kineticDriftCell h (kineticCof10*kineticBlock10) 4 2 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftCof10Row3,kineticDriftCof10Row4,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2,kineticDriftBlock10Row3,kineticDriftBlock10Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff2Row0Norm,kineticDriftCof10Coeff2Row1Norm,kineticDriftCof10Coeff2Row2Norm,kineticDriftCof10Coeff3Row0Norm,kineticDriftCof10Coeff3Row1Norm,kineticDriftCof10Coeff3Row2Norm,kineticDriftCof10Coeff4Row0Norm,kineticDriftCof10Coeff4Row1Norm,kineticDriftCof10Coeff4Row2Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff2Row0Norm,kineticDriftBlock10Coeff2Row1Norm,kineticDriftBlock10Coeff2Row2Norm,kineticDriftBlock10Coeff3Row0Norm,kineticDriftBlock10Coeff3Row1Norm,kineticDriftBlock10Coeff3Row2Norm,kineticDriftBlock10Coeff4Row0Norm,kineticDriftBlock10Coeff4Row1Norm,kineticDriftBlock10Coeff4Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff4Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 4 3=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 4 3=kineticDriftCell h (kineticCof2*kineticBlock2) 4 3 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftCof2Row3,kineticDriftCof2Row4,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2,kineticDriftBlock2Row3]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff1Row3Norm,kineticDriftCof2Coeff2Row0Norm,kineticDriftCof2Coeff2Row1Norm,kineticDriftCof2Coeff2Row2Norm,kineticDriftCof2Coeff2Row3Norm,kineticDriftCof2Coeff3Row0Norm,kineticDriftCof2Coeff3Row1Norm,kineticDriftCof2Coeff3Row2Norm,kineticDriftCof2Coeff3Row3Norm,kineticDriftCof2Coeff4Row0Norm,kineticDriftCof2Coeff4Row1Norm,kineticDriftCof2Coeff4Row2Norm,kineticDriftCof2Coeff4Row3Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm,kineticDriftBlock2Coeff2Row0Norm,kineticDriftBlock2Coeff2Row1Norm,kineticDriftBlock2Coeff2Row2Norm,kineticDriftBlock2Coeff3Row0Norm,kineticDriftBlock2Coeff3Row1Norm,kineticDriftBlock2Coeff3Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff4Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 4 3=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 4 3=kineticDriftCell h (kineticCof4*kineticBlock4) 4 3 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftCof4Row3,kineticDriftCof4Row4,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2,kineticDriftBlock4Row3,kineticDriftBlock4Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff1Row3Norm,kineticDriftCof4Coeff2Row0Norm,kineticDriftCof4Coeff2Row1Norm,kineticDriftCof4Coeff2Row2Norm,kineticDriftCof4Coeff2Row3Norm,kineticDriftCof4Coeff3Row0Norm,kineticDriftCof4Coeff3Row1Norm,kineticDriftCof4Coeff3Row2Norm,kineticDriftCof4Coeff3Row3Norm,kineticDriftCof4Coeff4Row0Norm,kineticDriftCof4Coeff4Row1Norm,kineticDriftCof4Coeff4Row2Norm,kineticDriftCof4Coeff4Row3Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff1Row3Norm,kineticDriftBlock4Coeff2Row0Norm,kineticDriftBlock4Coeff2Row1Norm,kineticDriftBlock4Coeff2Row2Norm,kineticDriftBlock4Coeff2Row3Norm,kineticDriftBlock4Coeff3Row0Norm,kineticDriftBlock4Coeff3Row1Norm,kineticDriftBlock4Coeff3Row2Norm,kineticDriftBlock4Coeff3Row3Norm,kineticDriftBlock4Coeff4Row0Norm,kineticDriftBlock4Coeff4Row1Norm,kineticDriftBlock4Coeff4Row2Norm,kineticDriftBlock4Coeff4Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff4Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 4 3=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 4 3=kineticDriftCell h (kineticCof6*kineticBlock6) 4 3 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftCof6Row3,kineticDriftCof6Row4,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2,kineticDriftBlock6Row3,kineticDriftBlock6Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff1Row3Norm,kineticDriftCof6Coeff2Row0Norm,kineticDriftCof6Coeff2Row1Norm,kineticDriftCof6Coeff2Row2Norm,kineticDriftCof6Coeff2Row3Norm,kineticDriftCof6Coeff3Row0Norm,kineticDriftCof6Coeff3Row1Norm,kineticDriftCof6Coeff3Row2Norm,kineticDriftCof6Coeff3Row3Norm,kineticDriftCof6Coeff4Row0Norm,kineticDriftCof6Coeff4Row1Norm,kineticDriftCof6Coeff4Row2Norm,kineticDriftCof6Coeff4Row3Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff1Row3Norm,kineticDriftBlock6Coeff2Row0Norm,kineticDriftBlock6Coeff2Row1Norm,kineticDriftBlock6Coeff2Row2Norm,kineticDriftBlock6Coeff2Row3Norm,kineticDriftBlock6Coeff3Row0Norm,kineticDriftBlock6Coeff3Row1Norm,kineticDriftBlock6Coeff3Row2Norm,kineticDriftBlock6Coeff3Row3Norm,kineticDriftBlock6Coeff4Row0Norm,kineticDriftBlock6Coeff4Row1Norm,kineticDriftBlock6Coeff4Row2Norm,kineticDriftBlock6Coeff4Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff4Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 4 3=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 4 3=kineticDriftCell h (kineticCof8*kineticBlock8) 4 3 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftCof8Row3,kineticDriftCof8Row4,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2,kineticDriftBlock8Row3,kineticDriftBlock8Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff1Row3Norm,kineticDriftCof8Coeff2Row0Norm,kineticDriftCof8Coeff2Row1Norm,kineticDriftCof8Coeff2Row2Norm,kineticDriftCof8Coeff2Row3Norm,kineticDriftCof8Coeff3Row0Norm,kineticDriftCof8Coeff3Row1Norm,kineticDriftCof8Coeff3Row2Norm,kineticDriftCof8Coeff3Row3Norm,kineticDriftCof8Coeff4Row0Norm,kineticDriftCof8Coeff4Row1Norm,kineticDriftCof8Coeff4Row2Norm,kineticDriftCof8Coeff4Row3Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff1Row3Norm,kineticDriftBlock8Coeff2Row0Norm,kineticDriftBlock8Coeff2Row1Norm,kineticDriftBlock8Coeff2Row2Norm,kineticDriftBlock8Coeff2Row3Norm,kineticDriftBlock8Coeff3Row0Norm,kineticDriftBlock8Coeff3Row1Norm,kineticDriftBlock8Coeff3Row2Norm,kineticDriftBlock8Coeff3Row3Norm,kineticDriftBlock8Coeff4Row0Norm,kineticDriftBlock8Coeff4Row1Norm,kineticDriftBlock8Coeff4Row2Norm,kineticDriftBlock8Coeff4Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff4Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 4 3=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 4 3=kineticDriftCell h (kineticCof10*kineticBlock10) 4 3 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftCof10Row3,kineticDriftCof10Row4,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2,kineticDriftBlock10Row3,kineticDriftBlock10Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff1Row3Norm,kineticDriftCof10Coeff2Row0Norm,kineticDriftCof10Coeff2Row1Norm,kineticDriftCof10Coeff2Row2Norm,kineticDriftCof10Coeff2Row3Norm,kineticDriftCof10Coeff3Row0Norm,kineticDriftCof10Coeff3Row1Norm,kineticDriftCof10Coeff3Row2Norm,kineticDriftCof10Coeff3Row3Norm,kineticDriftCof10Coeff4Row0Norm,kineticDriftCof10Coeff4Row1Norm,kineticDriftCof10Coeff4Row2Norm,kineticDriftCof10Coeff4Row3Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff1Row3Norm,kineticDriftBlock10Coeff2Row0Norm,kineticDriftBlock10Coeff2Row1Norm,kineticDriftBlock10Coeff2Row2Norm,kineticDriftBlock10Coeff2Row3Norm,kineticDriftBlock10Coeff3Row0Norm,kineticDriftBlock10Coeff3Row1Norm,kineticDriftBlock10Coeff3Row2Norm,kineticDriftBlock10Coeff3Row3Norm,kineticDriftBlock10Coeff4Row0Norm,kineticDriftBlock10Coeff4Row1Norm,kineticDriftBlock10Coeff4Row2Norm,kineticDriftBlock10Coeff4Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff4Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 4 4=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 4 4=kineticDriftCell h (kineticCof2*kineticBlock2) 4 4 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftCof2Row3,kineticDriftCof2Row4,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2,kineticDriftBlock2Row3]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm,kineticDriftCof2Coeff0Row4Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff1Row3Norm,kineticDriftCof2Coeff1Row4Norm,kineticDriftCof2Coeff2Row0Norm,kineticDriftCof2Coeff2Row1Norm,kineticDriftCof2Coeff2Row2Norm,kineticDriftCof2Coeff2Row3Norm,kineticDriftCof2Coeff2Row4Norm,kineticDriftCof2Coeff3Row0Norm,kineticDriftCof2Coeff3Row1Norm,kineticDriftCof2Coeff3Row2Norm,kineticDriftCof2Coeff3Row3Norm,kineticDriftCof2Coeff3Row4Norm,kineticDriftCof2Coeff4Row0Norm,kineticDriftCof2Coeff4Row1Norm,kineticDriftCof2Coeff4Row2Norm,kineticDriftCof2Coeff4Row3Norm,kineticDriftCof2Coeff4Row4Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm,kineticDriftBlock2Coeff2Row0Norm,kineticDriftBlock2Coeff2Row1Norm,kineticDriftBlock2Coeff2Row2Norm,kineticDriftBlock2Coeff3Row0Norm,kineticDriftBlock2Coeff3Row1Norm,kineticDriftBlock2Coeff3Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff4Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 4 4=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 4 4=kineticDriftCell h (kineticCof4*kineticBlock4) 4 4 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftCof4Row3,kineticDriftCof4Row4,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2,kineticDriftBlock4Row3,kineticDriftBlock4Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff0Row4Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff1Row3Norm,kineticDriftCof4Coeff1Row4Norm,kineticDriftCof4Coeff2Row0Norm,kineticDriftCof4Coeff2Row1Norm,kineticDriftCof4Coeff2Row2Norm,kineticDriftCof4Coeff2Row3Norm,kineticDriftCof4Coeff2Row4Norm,kineticDriftCof4Coeff3Row0Norm,kineticDriftCof4Coeff3Row1Norm,kineticDriftCof4Coeff3Row2Norm,kineticDriftCof4Coeff3Row3Norm,kineticDriftCof4Coeff3Row4Norm,kineticDriftCof4Coeff4Row0Norm,kineticDriftCof4Coeff4Row1Norm,kineticDriftCof4Coeff4Row2Norm,kineticDriftCof4Coeff4Row3Norm,kineticDriftCof4Coeff4Row4Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff1Row3Norm,kineticDriftBlock4Coeff2Row0Norm,kineticDriftBlock4Coeff2Row1Norm,kineticDriftBlock4Coeff2Row2Norm,kineticDriftBlock4Coeff2Row3Norm,kineticDriftBlock4Coeff3Row0Norm,kineticDriftBlock4Coeff3Row1Norm,kineticDriftBlock4Coeff3Row2Norm,kineticDriftBlock4Coeff3Row3Norm,kineticDriftBlock4Coeff4Row0Norm,kineticDriftBlock4Coeff4Row1Norm,kineticDriftBlock4Coeff4Row2Norm,kineticDriftBlock4Coeff4Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff4Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 4 4=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 4 4=kineticDriftCell h (kineticCof6*kineticBlock6) 4 4 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftCof6Row3,kineticDriftCof6Row4,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2,kineticDriftBlock6Row3,kineticDriftBlock6Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff0Row4Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff1Row3Norm,kineticDriftCof6Coeff1Row4Norm,kineticDriftCof6Coeff2Row0Norm,kineticDriftCof6Coeff2Row1Norm,kineticDriftCof6Coeff2Row2Norm,kineticDriftCof6Coeff2Row3Norm,kineticDriftCof6Coeff2Row4Norm,kineticDriftCof6Coeff3Row0Norm,kineticDriftCof6Coeff3Row1Norm,kineticDriftCof6Coeff3Row2Norm,kineticDriftCof6Coeff3Row3Norm,kineticDriftCof6Coeff3Row4Norm,kineticDriftCof6Coeff4Row0Norm,kineticDriftCof6Coeff4Row1Norm,kineticDriftCof6Coeff4Row2Norm,kineticDriftCof6Coeff4Row3Norm,kineticDriftCof6Coeff4Row4Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff0Row4Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff1Row3Norm,kineticDriftBlock6Coeff1Row4Norm,kineticDriftBlock6Coeff2Row0Norm,kineticDriftBlock6Coeff2Row1Norm,kineticDriftBlock6Coeff2Row2Norm,kineticDriftBlock6Coeff2Row3Norm,kineticDriftBlock6Coeff2Row4Norm,kineticDriftBlock6Coeff3Row0Norm,kineticDriftBlock6Coeff3Row1Norm,kineticDriftBlock6Coeff3Row2Norm,kineticDriftBlock6Coeff3Row3Norm,kineticDriftBlock6Coeff3Row4Norm,kineticDriftBlock6Coeff4Row0Norm,kineticDriftBlock6Coeff4Row1Norm,kineticDriftBlock6Coeff4Row2Norm,kineticDriftBlock6Coeff4Row3Norm,kineticDriftBlock6Coeff4Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff4Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 4 4=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 4 4=kineticDriftCell h (kineticCof8*kineticBlock8) 4 4 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftCof8Row3,kineticDriftCof8Row4,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2,kineticDriftBlock8Row3,kineticDriftBlock8Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff0Row4Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff1Row3Norm,kineticDriftCof8Coeff1Row4Norm,kineticDriftCof8Coeff2Row0Norm,kineticDriftCof8Coeff2Row1Norm,kineticDriftCof8Coeff2Row2Norm,kineticDriftCof8Coeff2Row3Norm,kineticDriftCof8Coeff2Row4Norm,kineticDriftCof8Coeff3Row0Norm,kineticDriftCof8Coeff3Row1Norm,kineticDriftCof8Coeff3Row2Norm,kineticDriftCof8Coeff3Row3Norm,kineticDriftCof8Coeff3Row4Norm,kineticDriftCof8Coeff4Row0Norm,kineticDriftCof8Coeff4Row1Norm,kineticDriftCof8Coeff4Row2Norm,kineticDriftCof8Coeff4Row3Norm,kineticDriftCof8Coeff4Row4Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff0Row4Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff1Row3Norm,kineticDriftBlock8Coeff1Row4Norm,kineticDriftBlock8Coeff2Row0Norm,kineticDriftBlock8Coeff2Row1Norm,kineticDriftBlock8Coeff2Row2Norm,kineticDriftBlock8Coeff2Row3Norm,kineticDriftBlock8Coeff2Row4Norm,kineticDriftBlock8Coeff3Row0Norm,kineticDriftBlock8Coeff3Row1Norm,kineticDriftBlock8Coeff3Row2Norm,kineticDriftBlock8Coeff3Row3Norm,kineticDriftBlock8Coeff3Row4Norm,kineticDriftBlock8Coeff4Row0Norm,kineticDriftBlock8Coeff4Row1Norm,kineticDriftBlock8Coeff4Row2Norm,kineticDriftBlock8Coeff4Row3Norm,kineticDriftBlock8Coeff4Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff4Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 4 4=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 4 4=kineticDriftCell h (kineticCof10*kineticBlock10) 4 4 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftCof10Row3,kineticDriftCof10Row4,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2,kineticDriftBlock10Row3,kineticDriftBlock10Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff0Row4Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff1Row3Norm,kineticDriftCof10Coeff1Row4Norm,kineticDriftCof10Coeff2Row0Norm,kineticDriftCof10Coeff2Row1Norm,kineticDriftCof10Coeff2Row2Norm,kineticDriftCof10Coeff2Row3Norm,kineticDriftCof10Coeff2Row4Norm,kineticDriftCof10Coeff3Row0Norm,kineticDriftCof10Coeff3Row1Norm,kineticDriftCof10Coeff3Row2Norm,kineticDriftCof10Coeff3Row3Norm,kineticDriftCof10Coeff3Row4Norm,kineticDriftCof10Coeff4Row0Norm,kineticDriftCof10Coeff4Row1Norm,kineticDriftCof10Coeff4Row2Norm,kineticDriftCof10Coeff4Row3Norm,kineticDriftCof10Coeff4Row4Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff0Row4Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff1Row3Norm,kineticDriftBlock10Coeff1Row4Norm,kineticDriftBlock10Coeff2Row0Norm,kineticDriftBlock10Coeff2Row1Norm,kineticDriftBlock10Coeff2Row2Norm,kineticDriftBlock10Coeff2Row3Norm,kineticDriftBlock10Coeff2Row4Norm,kineticDriftBlock10Coeff3Row0Norm,kineticDriftBlock10Coeff3Row1Norm,kineticDriftBlock10Coeff3Row2Norm,kineticDriftBlock10Coeff3Row3Norm,kineticDriftBlock10Coeff3Row4Norm,kineticDriftBlock10Coeff4Row0Norm,kineticDriftBlock10Coeff4Row1Norm,kineticDriftBlock10Coeff4Row2Norm,kineticDriftBlock10Coeff4Row3Norm,kineticDriftBlock10Coeff4Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff4Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 4 5=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 4 5=kineticDriftCell h (kineticCof2*kineticBlock2) 4 5 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftCof2Row3,kineticDriftCof2Row4,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2,kineticDriftBlock2Row3]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm,kineticDriftCof2Coeff0Row4Norm,kineticDriftCof2Coeff0Row5Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff1Row3Norm,kineticDriftCof2Coeff1Row4Norm,kineticDriftCof2Coeff1Row5Norm,kineticDriftCof2Coeff2Row0Norm,kineticDriftCof2Coeff2Row1Norm,kineticDriftCof2Coeff2Row2Norm,kineticDriftCof2Coeff2Row3Norm,kineticDriftCof2Coeff2Row4Norm,kineticDriftCof2Coeff2Row5Norm,kineticDriftCof2Coeff3Row0Norm,kineticDriftCof2Coeff3Row1Norm,kineticDriftCof2Coeff3Row2Norm,kineticDriftCof2Coeff3Row3Norm,kineticDriftCof2Coeff3Row4Norm,kineticDriftCof2Coeff3Row5Norm,kineticDriftCof2Coeff4Row0Norm,kineticDriftCof2Coeff4Row1Norm,kineticDriftCof2Coeff4Row2Norm,kineticDriftCof2Coeff4Row3Norm,kineticDriftCof2Coeff4Row4Norm,kineticDriftCof2Coeff4Row5Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm,kineticDriftBlock2Coeff2Row0Norm,kineticDriftBlock2Coeff2Row1Norm,kineticDriftBlock2Coeff2Row2Norm,kineticDriftBlock2Coeff3Row0Norm,kineticDriftBlock2Coeff3Row1Norm,kineticDriftBlock2Coeff3Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff4Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 4 5=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 4 5=kineticDriftCell h (kineticCof4*kineticBlock4) 4 5 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftCof4Row3,kineticDriftCof4Row4,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2,kineticDriftBlock4Row3,kineticDriftBlock4Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff0Row4Norm,kineticDriftCof4Coeff0Row5Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff1Row3Norm,kineticDriftCof4Coeff1Row4Norm,kineticDriftCof4Coeff1Row5Norm,kineticDriftCof4Coeff2Row0Norm,kineticDriftCof4Coeff2Row1Norm,kineticDriftCof4Coeff2Row2Norm,kineticDriftCof4Coeff2Row3Norm,kineticDriftCof4Coeff2Row4Norm,kineticDriftCof4Coeff2Row5Norm,kineticDriftCof4Coeff3Row0Norm,kineticDriftCof4Coeff3Row1Norm,kineticDriftCof4Coeff3Row2Norm,kineticDriftCof4Coeff3Row3Norm,kineticDriftCof4Coeff3Row4Norm,kineticDriftCof4Coeff3Row5Norm,kineticDriftCof4Coeff4Row0Norm,kineticDriftCof4Coeff4Row1Norm,kineticDriftCof4Coeff4Row2Norm,kineticDriftCof4Coeff4Row3Norm,kineticDriftCof4Coeff4Row4Norm,kineticDriftCof4Coeff4Row5Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff1Row3Norm,kineticDriftBlock4Coeff2Row0Norm,kineticDriftBlock4Coeff2Row1Norm,kineticDriftBlock4Coeff2Row2Norm,kineticDriftBlock4Coeff2Row3Norm,kineticDriftBlock4Coeff3Row0Norm,kineticDriftBlock4Coeff3Row1Norm,kineticDriftBlock4Coeff3Row2Norm,kineticDriftBlock4Coeff3Row3Norm,kineticDriftBlock4Coeff4Row0Norm,kineticDriftBlock4Coeff4Row1Norm,kineticDriftBlock4Coeff4Row2Norm,kineticDriftBlock4Coeff4Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff4Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 4 5=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 4 5=kineticDriftCell h (kineticCof6*kineticBlock6) 4 5 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftCof6Row3,kineticDriftCof6Row4,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2,kineticDriftBlock6Row3,kineticDriftBlock6Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff0Row4Norm,kineticDriftCof6Coeff0Row5Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff1Row3Norm,kineticDriftCof6Coeff1Row4Norm,kineticDriftCof6Coeff1Row5Norm,kineticDriftCof6Coeff2Row0Norm,kineticDriftCof6Coeff2Row1Norm,kineticDriftCof6Coeff2Row2Norm,kineticDriftCof6Coeff2Row3Norm,kineticDriftCof6Coeff2Row4Norm,kineticDriftCof6Coeff2Row5Norm,kineticDriftCof6Coeff3Row0Norm,kineticDriftCof6Coeff3Row1Norm,kineticDriftCof6Coeff3Row2Norm,kineticDriftCof6Coeff3Row3Norm,kineticDriftCof6Coeff3Row4Norm,kineticDriftCof6Coeff3Row5Norm,kineticDriftCof6Coeff4Row0Norm,kineticDriftCof6Coeff4Row1Norm,kineticDriftCof6Coeff4Row2Norm,kineticDriftCof6Coeff4Row3Norm,kineticDriftCof6Coeff4Row4Norm,kineticDriftCof6Coeff4Row5Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff0Row4Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff1Row3Norm,kineticDriftBlock6Coeff1Row4Norm,kineticDriftBlock6Coeff2Row0Norm,kineticDriftBlock6Coeff2Row1Norm,kineticDriftBlock6Coeff2Row2Norm,kineticDriftBlock6Coeff2Row3Norm,kineticDriftBlock6Coeff2Row4Norm,kineticDriftBlock6Coeff3Row0Norm,kineticDriftBlock6Coeff3Row1Norm,kineticDriftBlock6Coeff3Row2Norm,kineticDriftBlock6Coeff3Row3Norm,kineticDriftBlock6Coeff3Row4Norm,kineticDriftBlock6Coeff4Row0Norm,kineticDriftBlock6Coeff4Row1Norm,kineticDriftBlock6Coeff4Row2Norm,kineticDriftBlock6Coeff4Row3Norm,kineticDriftBlock6Coeff4Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff4Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 4 5=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 4 5=kineticDriftCell h (kineticCof8*kineticBlock8) 4 5 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftCof8Row3,kineticDriftCof8Row4,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2,kineticDriftBlock8Row3,kineticDriftBlock8Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff0Row4Norm,kineticDriftCof8Coeff0Row5Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff1Row3Norm,kineticDriftCof8Coeff1Row4Norm,kineticDriftCof8Coeff1Row5Norm,kineticDriftCof8Coeff2Row0Norm,kineticDriftCof8Coeff2Row1Norm,kineticDriftCof8Coeff2Row2Norm,kineticDriftCof8Coeff2Row3Norm,kineticDriftCof8Coeff2Row4Norm,kineticDriftCof8Coeff2Row5Norm,kineticDriftCof8Coeff3Row0Norm,kineticDriftCof8Coeff3Row1Norm,kineticDriftCof8Coeff3Row2Norm,kineticDriftCof8Coeff3Row3Norm,kineticDriftCof8Coeff3Row4Norm,kineticDriftCof8Coeff3Row5Norm,kineticDriftCof8Coeff4Row0Norm,kineticDriftCof8Coeff4Row1Norm,kineticDriftCof8Coeff4Row2Norm,kineticDriftCof8Coeff4Row3Norm,kineticDriftCof8Coeff4Row4Norm,kineticDriftCof8Coeff4Row5Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff0Row4Norm,kineticDriftBlock8Coeff0Row5Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff1Row3Norm,kineticDriftBlock8Coeff1Row4Norm,kineticDriftBlock8Coeff1Row5Norm,kineticDriftBlock8Coeff2Row0Norm,kineticDriftBlock8Coeff2Row1Norm,kineticDriftBlock8Coeff2Row2Norm,kineticDriftBlock8Coeff2Row3Norm,kineticDriftBlock8Coeff2Row4Norm,kineticDriftBlock8Coeff2Row5Norm,kineticDriftBlock8Coeff3Row0Norm,kineticDriftBlock8Coeff3Row1Norm,kineticDriftBlock8Coeff3Row2Norm,kineticDriftBlock8Coeff3Row3Norm,kineticDriftBlock8Coeff3Row4Norm,kineticDriftBlock8Coeff3Row5Norm,kineticDriftBlock8Coeff4Row0Norm,kineticDriftBlock8Coeff4Row1Norm,kineticDriftBlock8Coeff4Row2Norm,kineticDriftBlock8Coeff4Row3Norm,kineticDriftBlock8Coeff4Row4Norm,kineticDriftBlock8Coeff4Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff4Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 4 5=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 4 5=kineticDriftCell h (kineticCof10*kineticBlock10) 4 5 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftCof10Row3,kineticDriftCof10Row4,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2,kineticDriftBlock10Row3,kineticDriftBlock10Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff0Row4Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff1Row3Norm,kineticDriftCof10Coeff1Row4Norm,kineticDriftCof10Coeff2Row0Norm,kineticDriftCof10Coeff2Row1Norm,kineticDriftCof10Coeff2Row2Norm,kineticDriftCof10Coeff2Row3Norm,kineticDriftCof10Coeff2Row4Norm,kineticDriftCof10Coeff3Row0Norm,kineticDriftCof10Coeff3Row1Norm,kineticDriftCof10Coeff3Row2Norm,kineticDriftCof10Coeff3Row3Norm,kineticDriftCof10Coeff3Row4Norm,kineticDriftCof10Coeff4Row0Norm,kineticDriftCof10Coeff4Row1Norm,kineticDriftCof10Coeff4Row2Norm,kineticDriftCof10Coeff4Row3Norm,kineticDriftCof10Coeff4Row4Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff0Row4Norm,kineticDriftBlock10Coeff0Row5Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff1Row3Norm,kineticDriftBlock10Coeff1Row4Norm,kineticDriftBlock10Coeff1Row5Norm,kineticDriftBlock10Coeff2Row0Norm,kineticDriftBlock10Coeff2Row1Norm,kineticDriftBlock10Coeff2Row2Norm,kineticDriftBlock10Coeff2Row3Norm,kineticDriftBlock10Coeff2Row4Norm,kineticDriftBlock10Coeff2Row5Norm,kineticDriftBlock10Coeff3Row0Norm,kineticDriftBlock10Coeff3Row1Norm,kineticDriftBlock10Coeff3Row2Norm,kineticDriftBlock10Coeff3Row3Norm,kineticDriftBlock10Coeff3Row4Norm,kineticDriftBlock10Coeff3Row5Norm,kineticDriftBlock10Coeff4Row0Norm,kineticDriftBlock10Coeff4Row1Norm,kineticDriftBlock10Coeff4Row2Norm,kineticDriftBlock10Coeff4Row3Norm,kineticDriftBlock10Coeff4Row4Norm,kineticDriftBlock10Coeff4Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff4Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 4 6=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 4 6=kineticDriftCell h (kineticCof2*kineticBlock2) 4 6 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftCof2Row3,kineticDriftCof2Row4,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2,kineticDriftBlock2Row3]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm,kineticDriftCof2Coeff0Row4Norm,kineticDriftCof2Coeff0Row5Norm,kineticDriftCof2Coeff0Row6Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff1Row3Norm,kineticDriftCof2Coeff1Row4Norm,kineticDriftCof2Coeff1Row5Norm,kineticDriftCof2Coeff1Row6Norm,kineticDriftCof2Coeff2Row0Norm,kineticDriftCof2Coeff2Row1Norm,kineticDriftCof2Coeff2Row2Norm,kineticDriftCof2Coeff2Row3Norm,kineticDriftCof2Coeff2Row4Norm,kineticDriftCof2Coeff2Row5Norm,kineticDriftCof2Coeff2Row6Norm,kineticDriftCof2Coeff3Row0Norm,kineticDriftCof2Coeff3Row1Norm,kineticDriftCof2Coeff3Row2Norm,kineticDriftCof2Coeff3Row3Norm,kineticDriftCof2Coeff3Row4Norm,kineticDriftCof2Coeff3Row5Norm,kineticDriftCof2Coeff3Row6Norm,kineticDriftCof2Coeff4Row0Norm,kineticDriftCof2Coeff4Row1Norm,kineticDriftCof2Coeff4Row2Norm,kineticDriftCof2Coeff4Row3Norm,kineticDriftCof2Coeff4Row4Norm,kineticDriftCof2Coeff4Row5Norm,kineticDriftCof2Coeff4Row6Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm,kineticDriftBlock2Coeff2Row0Norm,kineticDriftBlock2Coeff2Row1Norm,kineticDriftBlock2Coeff2Row2Norm,kineticDriftBlock2Coeff3Row0Norm,kineticDriftBlock2Coeff3Row1Norm,kineticDriftBlock2Coeff3Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff4Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 4 6=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 4 6=kineticDriftCell h (kineticCof4*kineticBlock4) 4 6 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftCof4Row3,kineticDriftCof4Row4,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2,kineticDriftBlock4Row3,kineticDriftBlock4Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff0Row4Norm,kineticDriftCof4Coeff0Row5Norm,kineticDriftCof4Coeff0Row6Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff1Row3Norm,kineticDriftCof4Coeff1Row4Norm,kineticDriftCof4Coeff1Row5Norm,kineticDriftCof4Coeff1Row6Norm,kineticDriftCof4Coeff2Row0Norm,kineticDriftCof4Coeff2Row1Norm,kineticDriftCof4Coeff2Row2Norm,kineticDriftCof4Coeff2Row3Norm,kineticDriftCof4Coeff2Row4Norm,kineticDriftCof4Coeff2Row5Norm,kineticDriftCof4Coeff2Row6Norm,kineticDriftCof4Coeff3Row0Norm,kineticDriftCof4Coeff3Row1Norm,kineticDriftCof4Coeff3Row2Norm,kineticDriftCof4Coeff3Row3Norm,kineticDriftCof4Coeff3Row4Norm,kineticDriftCof4Coeff3Row5Norm,kineticDriftCof4Coeff3Row6Norm,kineticDriftCof4Coeff4Row0Norm,kineticDriftCof4Coeff4Row1Norm,kineticDriftCof4Coeff4Row2Norm,kineticDriftCof4Coeff4Row3Norm,kineticDriftCof4Coeff4Row4Norm,kineticDriftCof4Coeff4Row5Norm,kineticDriftCof4Coeff4Row6Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff1Row3Norm,kineticDriftBlock4Coeff2Row0Norm,kineticDriftBlock4Coeff2Row1Norm,kineticDriftBlock4Coeff2Row2Norm,kineticDriftBlock4Coeff2Row3Norm,kineticDriftBlock4Coeff3Row0Norm,kineticDriftBlock4Coeff3Row1Norm,kineticDriftBlock4Coeff3Row2Norm,kineticDriftBlock4Coeff3Row3Norm,kineticDriftBlock4Coeff4Row0Norm,kineticDriftBlock4Coeff4Row1Norm,kineticDriftBlock4Coeff4Row2Norm,kineticDriftBlock4Coeff4Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff4Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 4 6=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 4 6=kineticDriftCell h (kineticCof6*kineticBlock6) 4 6 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftCof6Row3,kineticDriftCof6Row4,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2,kineticDriftBlock6Row3,kineticDriftBlock6Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff0Row4Norm,kineticDriftCof6Coeff0Row5Norm,kineticDriftCof6Coeff0Row6Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff1Row3Norm,kineticDriftCof6Coeff1Row4Norm,kineticDriftCof6Coeff1Row5Norm,kineticDriftCof6Coeff1Row6Norm,kineticDriftCof6Coeff2Row0Norm,kineticDriftCof6Coeff2Row1Norm,kineticDriftCof6Coeff2Row2Norm,kineticDriftCof6Coeff2Row3Norm,kineticDriftCof6Coeff2Row4Norm,kineticDriftCof6Coeff2Row5Norm,kineticDriftCof6Coeff2Row6Norm,kineticDriftCof6Coeff3Row0Norm,kineticDriftCof6Coeff3Row1Norm,kineticDriftCof6Coeff3Row2Norm,kineticDriftCof6Coeff3Row3Norm,kineticDriftCof6Coeff3Row4Norm,kineticDriftCof6Coeff3Row5Norm,kineticDriftCof6Coeff3Row6Norm,kineticDriftCof6Coeff4Row0Norm,kineticDriftCof6Coeff4Row1Norm,kineticDriftCof6Coeff4Row2Norm,kineticDriftCof6Coeff4Row3Norm,kineticDriftCof6Coeff4Row4Norm,kineticDriftCof6Coeff4Row5Norm,kineticDriftCof6Coeff4Row6Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff0Row4Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff1Row3Norm,kineticDriftBlock6Coeff1Row4Norm,kineticDriftBlock6Coeff2Row0Norm,kineticDriftBlock6Coeff2Row1Norm,kineticDriftBlock6Coeff2Row2Norm,kineticDriftBlock6Coeff2Row3Norm,kineticDriftBlock6Coeff2Row4Norm,kineticDriftBlock6Coeff3Row0Norm,kineticDriftBlock6Coeff3Row1Norm,kineticDriftBlock6Coeff3Row2Norm,kineticDriftBlock6Coeff3Row3Norm,kineticDriftBlock6Coeff3Row4Norm,kineticDriftBlock6Coeff4Row0Norm,kineticDriftBlock6Coeff4Row1Norm,kineticDriftBlock6Coeff4Row2Norm,kineticDriftBlock6Coeff4Row3Norm,kineticDriftBlock6Coeff4Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff4Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 4 6=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 4 6=kineticDriftCell h (kineticCof8*kineticBlock8) 4 6 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftCof8Row3,kineticDriftCof8Row4,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2,kineticDriftBlock8Row3,kineticDriftBlock8Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff0Row4Norm,kineticDriftCof8Coeff0Row5Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff1Row3Norm,kineticDriftCof8Coeff1Row4Norm,kineticDriftCof8Coeff1Row5Norm,kineticDriftCof8Coeff2Row0Norm,kineticDriftCof8Coeff2Row1Norm,kineticDriftCof8Coeff2Row2Norm,kineticDriftCof8Coeff2Row3Norm,kineticDriftCof8Coeff2Row4Norm,kineticDriftCof8Coeff2Row5Norm,kineticDriftCof8Coeff3Row0Norm,kineticDriftCof8Coeff3Row1Norm,kineticDriftCof8Coeff3Row2Norm,kineticDriftCof8Coeff3Row3Norm,kineticDriftCof8Coeff3Row4Norm,kineticDriftCof8Coeff3Row5Norm,kineticDriftCof8Coeff4Row0Norm,kineticDriftCof8Coeff4Row1Norm,kineticDriftCof8Coeff4Row2Norm,kineticDriftCof8Coeff4Row3Norm,kineticDriftCof8Coeff4Row4Norm,kineticDriftCof8Coeff4Row5Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff0Row4Norm,kineticDriftBlock8Coeff0Row5Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff1Row3Norm,kineticDriftBlock8Coeff1Row4Norm,kineticDriftBlock8Coeff1Row5Norm,kineticDriftBlock8Coeff2Row0Norm,kineticDriftBlock8Coeff2Row1Norm,kineticDriftBlock8Coeff2Row2Norm,kineticDriftBlock8Coeff2Row3Norm,kineticDriftBlock8Coeff2Row4Norm,kineticDriftBlock8Coeff2Row5Norm,kineticDriftBlock8Coeff3Row0Norm,kineticDriftBlock8Coeff3Row1Norm,kineticDriftBlock8Coeff3Row2Norm,kineticDriftBlock8Coeff3Row3Norm,kineticDriftBlock8Coeff3Row4Norm,kineticDriftBlock8Coeff3Row5Norm,kineticDriftBlock8Coeff4Row0Norm,kineticDriftBlock8Coeff4Row1Norm,kineticDriftBlock8Coeff4Row2Norm,kineticDriftBlock8Coeff4Row3Norm,kineticDriftBlock8Coeff4Row4Norm,kineticDriftBlock8Coeff4Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff4Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 4 6=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 4 6=kineticDriftCell h (kineticCof10*kineticBlock10) 4 6 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftCof10Row3,kineticDriftCof10Row4,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2,kineticDriftBlock10Row3,kineticDriftBlock10Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff0Row4Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff1Row3Norm,kineticDriftCof10Coeff1Row4Norm,kineticDriftCof10Coeff2Row0Norm,kineticDriftCof10Coeff2Row1Norm,kineticDriftCof10Coeff2Row2Norm,kineticDriftCof10Coeff2Row3Norm,kineticDriftCof10Coeff2Row4Norm,kineticDriftCof10Coeff3Row0Norm,kineticDriftCof10Coeff3Row1Norm,kineticDriftCof10Coeff3Row2Norm,kineticDriftCof10Coeff3Row3Norm,kineticDriftCof10Coeff3Row4Norm,kineticDriftCof10Coeff4Row0Norm,kineticDriftCof10Coeff4Row1Norm,kineticDriftCof10Coeff4Row2Norm,kineticDriftCof10Coeff4Row3Norm,kineticDriftCof10Coeff4Row4Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff0Row4Norm,kineticDriftBlock10Coeff0Row5Norm,kineticDriftBlock10Coeff0Row6Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff1Row3Norm,kineticDriftBlock10Coeff1Row4Norm,kineticDriftBlock10Coeff1Row5Norm,kineticDriftBlock10Coeff1Row6Norm,kineticDriftBlock10Coeff2Row0Norm,kineticDriftBlock10Coeff2Row1Norm,kineticDriftBlock10Coeff2Row2Norm,kineticDriftBlock10Coeff2Row3Norm,kineticDriftBlock10Coeff2Row4Norm,kineticDriftBlock10Coeff2Row5Norm,kineticDriftBlock10Coeff2Row6Norm,kineticDriftBlock10Coeff3Row0Norm,kineticDriftBlock10Coeff3Row1Norm,kineticDriftBlock10Coeff3Row2Norm,kineticDriftBlock10Coeff3Row3Norm,kineticDriftBlock10Coeff3Row4Norm,kineticDriftBlock10Coeff3Row5Norm,kineticDriftBlock10Coeff3Row6Norm,kineticDriftBlock10Coeff4Row0Norm,kineticDriftBlock10Coeff4Row1Norm,kineticDriftBlock10Coeff4Row2Norm,kineticDriftBlock10Coeff4Row3Norm,kineticDriftBlock10Coeff4Row4Norm,kineticDriftBlock10Coeff4Row5Norm,kineticDriftBlock10Coeff4Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff4Row7Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 4 7=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 4 7=kineticDriftCell h (kineticCof2*kineticBlock2) 4 7 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftCof2Row3,kineticDriftCof2Row4,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2,kineticDriftBlock2Row3]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm,kineticDriftCof2Coeff0Row4Norm,kineticDriftCof2Coeff0Row5Norm,kineticDriftCof2Coeff0Row6Norm,kineticDriftCof2Coeff0Row7Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff1Row3Norm,kineticDriftCof2Coeff1Row4Norm,kineticDriftCof2Coeff1Row5Norm,kineticDriftCof2Coeff1Row6Norm,kineticDriftCof2Coeff1Row7Norm,kineticDriftCof2Coeff2Row0Norm,kineticDriftCof2Coeff2Row1Norm,kineticDriftCof2Coeff2Row2Norm,kineticDriftCof2Coeff2Row3Norm,kineticDriftCof2Coeff2Row4Norm,kineticDriftCof2Coeff2Row5Norm,kineticDriftCof2Coeff2Row6Norm,kineticDriftCof2Coeff2Row7Norm,kineticDriftCof2Coeff3Row0Norm,kineticDriftCof2Coeff3Row1Norm,kineticDriftCof2Coeff3Row2Norm,kineticDriftCof2Coeff3Row3Norm,kineticDriftCof2Coeff3Row4Norm,kineticDriftCof2Coeff3Row5Norm,kineticDriftCof2Coeff3Row6Norm,kineticDriftCof2Coeff3Row7Norm,kineticDriftCof2Coeff4Row0Norm,kineticDriftCof2Coeff4Row1Norm,kineticDriftCof2Coeff4Row2Norm,kineticDriftCof2Coeff4Row3Norm,kineticDriftCof2Coeff4Row4Norm,kineticDriftCof2Coeff4Row5Norm,kineticDriftCof2Coeff4Row6Norm,kineticDriftCof2Coeff4Row7Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm,kineticDriftBlock2Coeff2Row0Norm,kineticDriftBlock2Coeff2Row1Norm,kineticDriftBlock2Coeff2Row2Norm,kineticDriftBlock2Coeff3Row0Norm,kineticDriftBlock2Coeff3Row1Norm,kineticDriftBlock2Coeff3Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff4Row7Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 4 7=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 4 7=kineticDriftCell h (kineticCof4*kineticBlock4) 4 7 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftCof4Row3,kineticDriftCof4Row4,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2,kineticDriftBlock4Row3,kineticDriftBlock4Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff0Row4Norm,kineticDriftCof4Coeff0Row5Norm,kineticDriftCof4Coeff0Row6Norm,kineticDriftCof4Coeff0Row7Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff1Row3Norm,kineticDriftCof4Coeff1Row4Norm,kineticDriftCof4Coeff1Row5Norm,kineticDriftCof4Coeff1Row6Norm,kineticDriftCof4Coeff1Row7Norm,kineticDriftCof4Coeff2Row0Norm,kineticDriftCof4Coeff2Row1Norm,kineticDriftCof4Coeff2Row2Norm,kineticDriftCof4Coeff2Row3Norm,kineticDriftCof4Coeff2Row4Norm,kineticDriftCof4Coeff2Row5Norm,kineticDriftCof4Coeff2Row6Norm,kineticDriftCof4Coeff2Row7Norm,kineticDriftCof4Coeff3Row0Norm,kineticDriftCof4Coeff3Row1Norm,kineticDriftCof4Coeff3Row2Norm,kineticDriftCof4Coeff3Row3Norm,kineticDriftCof4Coeff3Row4Norm,kineticDriftCof4Coeff3Row5Norm,kineticDriftCof4Coeff3Row6Norm,kineticDriftCof4Coeff3Row7Norm,kineticDriftCof4Coeff4Row0Norm,kineticDriftCof4Coeff4Row1Norm,kineticDriftCof4Coeff4Row2Norm,kineticDriftCof4Coeff4Row3Norm,kineticDriftCof4Coeff4Row4Norm,kineticDriftCof4Coeff4Row5Norm,kineticDriftCof4Coeff4Row6Norm,kineticDriftCof4Coeff4Row7Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff1Row3Norm,kineticDriftBlock4Coeff2Row0Norm,kineticDriftBlock4Coeff2Row1Norm,kineticDriftBlock4Coeff2Row2Norm,kineticDriftBlock4Coeff2Row3Norm,kineticDriftBlock4Coeff3Row0Norm,kineticDriftBlock4Coeff3Row1Norm,kineticDriftBlock4Coeff3Row2Norm,kineticDriftBlock4Coeff3Row3Norm,kineticDriftBlock4Coeff4Row0Norm,kineticDriftBlock4Coeff4Row1Norm,kineticDriftBlock4Coeff4Row2Norm,kineticDriftBlock4Coeff4Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff4Row7Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 4 7=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 4 7=kineticDriftCell h (kineticCof6*kineticBlock6) 4 7 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftCof6Row3,kineticDriftCof6Row4,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2,kineticDriftBlock6Row3,kineticDriftBlock6Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff0Row4Norm,kineticDriftCof6Coeff0Row5Norm,kineticDriftCof6Coeff0Row6Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff1Row3Norm,kineticDriftCof6Coeff1Row4Norm,kineticDriftCof6Coeff1Row5Norm,kineticDriftCof6Coeff1Row6Norm,kineticDriftCof6Coeff2Row0Norm,kineticDriftCof6Coeff2Row1Norm,kineticDriftCof6Coeff2Row2Norm,kineticDriftCof6Coeff2Row3Norm,kineticDriftCof6Coeff2Row4Norm,kineticDriftCof6Coeff2Row5Norm,kineticDriftCof6Coeff2Row6Norm,kineticDriftCof6Coeff3Row0Norm,kineticDriftCof6Coeff3Row1Norm,kineticDriftCof6Coeff3Row2Norm,kineticDriftCof6Coeff3Row3Norm,kineticDriftCof6Coeff3Row4Norm,kineticDriftCof6Coeff3Row5Norm,kineticDriftCof6Coeff3Row6Norm,kineticDriftCof6Coeff4Row0Norm,kineticDriftCof6Coeff4Row1Norm,kineticDriftCof6Coeff4Row2Norm,kineticDriftCof6Coeff4Row3Norm,kineticDriftCof6Coeff4Row4Norm,kineticDriftCof6Coeff4Row5Norm,kineticDriftCof6Coeff4Row6Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff0Row4Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff1Row3Norm,kineticDriftBlock6Coeff1Row4Norm,kineticDriftBlock6Coeff2Row0Norm,kineticDriftBlock6Coeff2Row1Norm,kineticDriftBlock6Coeff2Row2Norm,kineticDriftBlock6Coeff2Row3Norm,kineticDriftBlock6Coeff2Row4Norm,kineticDriftBlock6Coeff3Row0Norm,kineticDriftBlock6Coeff3Row1Norm,kineticDriftBlock6Coeff3Row2Norm,kineticDriftBlock6Coeff3Row3Norm,kineticDriftBlock6Coeff3Row4Norm,kineticDriftBlock6Coeff4Row0Norm,kineticDriftBlock6Coeff4Row1Norm,kineticDriftBlock6Coeff4Row2Norm,kineticDriftBlock6Coeff4Row3Norm,kineticDriftBlock6Coeff4Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff4Row7Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 4 7=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 4 7=kineticDriftCell h (kineticCof8*kineticBlock8) 4 7 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftCof8Row3,kineticDriftCof8Row4,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2,kineticDriftBlock8Row3,kineticDriftBlock8Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff0Row4Norm,kineticDriftCof8Coeff0Row5Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff1Row3Norm,kineticDriftCof8Coeff1Row4Norm,kineticDriftCof8Coeff1Row5Norm,kineticDriftCof8Coeff2Row0Norm,kineticDriftCof8Coeff2Row1Norm,kineticDriftCof8Coeff2Row2Norm,kineticDriftCof8Coeff2Row3Norm,kineticDriftCof8Coeff2Row4Norm,kineticDriftCof8Coeff2Row5Norm,kineticDriftCof8Coeff3Row0Norm,kineticDriftCof8Coeff3Row1Norm,kineticDriftCof8Coeff3Row2Norm,kineticDriftCof8Coeff3Row3Norm,kineticDriftCof8Coeff3Row4Norm,kineticDriftCof8Coeff3Row5Norm,kineticDriftCof8Coeff4Row0Norm,kineticDriftCof8Coeff4Row1Norm,kineticDriftCof8Coeff4Row2Norm,kineticDriftCof8Coeff4Row3Norm,kineticDriftCof8Coeff4Row4Norm,kineticDriftCof8Coeff4Row5Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff0Row4Norm,kineticDriftBlock8Coeff0Row5Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff1Row3Norm,kineticDriftBlock8Coeff1Row4Norm,kineticDriftBlock8Coeff1Row5Norm,kineticDriftBlock8Coeff2Row0Norm,kineticDriftBlock8Coeff2Row1Norm,kineticDriftBlock8Coeff2Row2Norm,kineticDriftBlock8Coeff2Row3Norm,kineticDriftBlock8Coeff2Row4Norm,kineticDriftBlock8Coeff2Row5Norm,kineticDriftBlock8Coeff3Row0Norm,kineticDriftBlock8Coeff3Row1Norm,kineticDriftBlock8Coeff3Row2Norm,kineticDriftBlock8Coeff3Row3Norm,kineticDriftBlock8Coeff3Row4Norm,kineticDriftBlock8Coeff3Row5Norm,kineticDriftBlock8Coeff4Row0Norm,kineticDriftBlock8Coeff4Row1Norm,kineticDriftBlock8Coeff4Row2Norm,kineticDriftBlock8Coeff4Row3Norm,kineticDriftBlock8Coeff4Row4Norm,kineticDriftBlock8Coeff4Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff4Row7Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 4 7=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 4 7=kineticDriftCell h (kineticCof10*kineticBlock10) 4 7 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftCof10Row3,kineticDriftCof10Row4,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2,kineticDriftBlock10Row3,kineticDriftBlock10Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff0Row4Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff1Row3Norm,kineticDriftCof10Coeff1Row4Norm,kineticDriftCof10Coeff2Row0Norm,kineticDriftCof10Coeff2Row1Norm,kineticDriftCof10Coeff2Row2Norm,kineticDriftCof10Coeff2Row3Norm,kineticDriftCof10Coeff2Row4Norm,kineticDriftCof10Coeff3Row0Norm,kineticDriftCof10Coeff3Row1Norm,kineticDriftCof10Coeff3Row2Norm,kineticDriftCof10Coeff3Row3Norm,kineticDriftCof10Coeff3Row4Norm,kineticDriftCof10Coeff4Row0Norm,kineticDriftCof10Coeff4Row1Norm,kineticDriftCof10Coeff4Row2Norm,kineticDriftCof10Coeff4Row3Norm,kineticDriftCof10Coeff4Row4Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff0Row4Norm,kineticDriftBlock10Coeff0Row5Norm,kineticDriftBlock10Coeff0Row6Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff1Row3Norm,kineticDriftBlock10Coeff1Row4Norm,kineticDriftBlock10Coeff1Row5Norm,kineticDriftBlock10Coeff1Row6Norm,kineticDriftBlock10Coeff2Row0Norm,kineticDriftBlock10Coeff2Row1Norm,kineticDriftBlock10Coeff2Row2Norm,kineticDriftBlock10Coeff2Row3Norm,kineticDriftBlock10Coeff2Row4Norm,kineticDriftBlock10Coeff2Row5Norm,kineticDriftBlock10Coeff2Row6Norm,kineticDriftBlock10Coeff3Row0Norm,kineticDriftBlock10Coeff3Row1Norm,kineticDriftBlock10Coeff3Row2Norm,kineticDriftBlock10Coeff3Row3Norm,kineticDriftBlock10Coeff3Row4Norm,kineticDriftBlock10Coeff3Row5Norm,kineticDriftBlock10Coeff3Row6Norm,kineticDriftBlock10Coeff4Row0Norm,kineticDriftBlock10Coeff4Row1Norm,kineticDriftBlock10Coeff4Row2Norm,kineticDriftBlock10Coeff4Row3Norm,kineticDriftBlock10Coeff4Row4Norm,kineticDriftBlock10Coeff4Row5Norm,kineticDriftBlock10Coeff4Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff4Row8Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 4 8=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 4 8=kineticDriftCell h (kineticCof2*kineticBlock2) 4 8 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftCof2Row3,kineticDriftCof2Row4,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2,kineticDriftBlock2Row3]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm,kineticDriftCof2Coeff0Row4Norm,kineticDriftCof2Coeff0Row5Norm,kineticDriftCof2Coeff0Row6Norm,kineticDriftCof2Coeff0Row7Norm,kineticDriftCof2Coeff0Row8Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff1Row3Norm,kineticDriftCof2Coeff1Row4Norm,kineticDriftCof2Coeff1Row5Norm,kineticDriftCof2Coeff1Row6Norm,kineticDriftCof2Coeff1Row7Norm,kineticDriftCof2Coeff1Row8Norm,kineticDriftCof2Coeff2Row0Norm,kineticDriftCof2Coeff2Row1Norm,kineticDriftCof2Coeff2Row2Norm,kineticDriftCof2Coeff2Row3Norm,kineticDriftCof2Coeff2Row4Norm,kineticDriftCof2Coeff2Row5Norm,kineticDriftCof2Coeff2Row6Norm,kineticDriftCof2Coeff2Row7Norm,kineticDriftCof2Coeff2Row8Norm,kineticDriftCof2Coeff3Row0Norm,kineticDriftCof2Coeff3Row1Norm,kineticDriftCof2Coeff3Row2Norm,kineticDriftCof2Coeff3Row3Norm,kineticDriftCof2Coeff3Row4Norm,kineticDriftCof2Coeff3Row5Norm,kineticDriftCof2Coeff3Row6Norm,kineticDriftCof2Coeff3Row7Norm,kineticDriftCof2Coeff3Row8Norm,kineticDriftCof2Coeff4Row0Norm,kineticDriftCof2Coeff4Row1Norm,kineticDriftCof2Coeff4Row2Norm,kineticDriftCof2Coeff4Row3Norm,kineticDriftCof2Coeff4Row4Norm,kineticDriftCof2Coeff4Row5Norm,kineticDriftCof2Coeff4Row6Norm,kineticDriftCof2Coeff4Row7Norm,kineticDriftCof2Coeff4Row8Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm,kineticDriftBlock2Coeff2Row0Norm,kineticDriftBlock2Coeff2Row1Norm,kineticDriftBlock2Coeff2Row2Norm,kineticDriftBlock2Coeff3Row0Norm,kineticDriftBlock2Coeff3Row1Norm,kineticDriftBlock2Coeff3Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff4Row8Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 4 8=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 4 8=kineticDriftCell h (kineticCof4*kineticBlock4) 4 8 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftCof4Row3,kineticDriftCof4Row4,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2,kineticDriftBlock4Row3,kineticDriftBlock4Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff0Row4Norm,kineticDriftCof4Coeff0Row5Norm,kineticDriftCof4Coeff0Row6Norm,kineticDriftCof4Coeff0Row7Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff1Row3Norm,kineticDriftCof4Coeff1Row4Norm,kineticDriftCof4Coeff1Row5Norm,kineticDriftCof4Coeff1Row6Norm,kineticDriftCof4Coeff1Row7Norm,kineticDriftCof4Coeff2Row0Norm,kineticDriftCof4Coeff2Row1Norm,kineticDriftCof4Coeff2Row2Norm,kineticDriftCof4Coeff2Row3Norm,kineticDriftCof4Coeff2Row4Norm,kineticDriftCof4Coeff2Row5Norm,kineticDriftCof4Coeff2Row6Norm,kineticDriftCof4Coeff2Row7Norm,kineticDriftCof4Coeff3Row0Norm,kineticDriftCof4Coeff3Row1Norm,kineticDriftCof4Coeff3Row2Norm,kineticDriftCof4Coeff3Row3Norm,kineticDriftCof4Coeff3Row4Norm,kineticDriftCof4Coeff3Row5Norm,kineticDriftCof4Coeff3Row6Norm,kineticDriftCof4Coeff3Row7Norm,kineticDriftCof4Coeff4Row0Norm,kineticDriftCof4Coeff4Row1Norm,kineticDriftCof4Coeff4Row2Norm,kineticDriftCof4Coeff4Row3Norm,kineticDriftCof4Coeff4Row4Norm,kineticDriftCof4Coeff4Row5Norm,kineticDriftCof4Coeff4Row6Norm,kineticDriftCof4Coeff4Row7Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff1Row3Norm,kineticDriftBlock4Coeff2Row0Norm,kineticDriftBlock4Coeff2Row1Norm,kineticDriftBlock4Coeff2Row2Norm,kineticDriftBlock4Coeff2Row3Norm,kineticDriftBlock4Coeff3Row0Norm,kineticDriftBlock4Coeff3Row1Norm,kineticDriftBlock4Coeff3Row2Norm,kineticDriftBlock4Coeff3Row3Norm,kineticDriftBlock4Coeff4Row0Norm,kineticDriftBlock4Coeff4Row1Norm,kineticDriftBlock4Coeff4Row2Norm,kineticDriftBlock4Coeff4Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff4Row8Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 4 8=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 4 8=kineticDriftCell h (kineticCof6*kineticBlock6) 4 8 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftCof6Row3,kineticDriftCof6Row4,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2,kineticDriftBlock6Row3,kineticDriftBlock6Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff0Row4Norm,kineticDriftCof6Coeff0Row5Norm,kineticDriftCof6Coeff0Row6Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff1Row3Norm,kineticDriftCof6Coeff1Row4Norm,kineticDriftCof6Coeff1Row5Norm,kineticDriftCof6Coeff1Row6Norm,kineticDriftCof6Coeff2Row0Norm,kineticDriftCof6Coeff2Row1Norm,kineticDriftCof6Coeff2Row2Norm,kineticDriftCof6Coeff2Row3Norm,kineticDriftCof6Coeff2Row4Norm,kineticDriftCof6Coeff2Row5Norm,kineticDriftCof6Coeff2Row6Norm,kineticDriftCof6Coeff3Row0Norm,kineticDriftCof6Coeff3Row1Norm,kineticDriftCof6Coeff3Row2Norm,kineticDriftCof6Coeff3Row3Norm,kineticDriftCof6Coeff3Row4Norm,kineticDriftCof6Coeff3Row5Norm,kineticDriftCof6Coeff3Row6Norm,kineticDriftCof6Coeff4Row0Norm,kineticDriftCof6Coeff4Row1Norm,kineticDriftCof6Coeff4Row2Norm,kineticDriftCof6Coeff4Row3Norm,kineticDriftCof6Coeff4Row4Norm,kineticDriftCof6Coeff4Row5Norm,kineticDriftCof6Coeff4Row6Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff0Row4Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff1Row3Norm,kineticDriftBlock6Coeff1Row4Norm,kineticDriftBlock6Coeff2Row0Norm,kineticDriftBlock6Coeff2Row1Norm,kineticDriftBlock6Coeff2Row2Norm,kineticDriftBlock6Coeff2Row3Norm,kineticDriftBlock6Coeff2Row4Norm,kineticDriftBlock6Coeff3Row0Norm,kineticDriftBlock6Coeff3Row1Norm,kineticDriftBlock6Coeff3Row2Norm,kineticDriftBlock6Coeff3Row3Norm,kineticDriftBlock6Coeff3Row4Norm,kineticDriftBlock6Coeff4Row0Norm,kineticDriftBlock6Coeff4Row1Norm,kineticDriftBlock6Coeff4Row2Norm,kineticDriftBlock6Coeff4Row3Norm,kineticDriftBlock6Coeff4Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff4Row8Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 4 8=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 4 8=kineticDriftCell h (kineticCof8*kineticBlock8) 4 8 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftCof8Row3,kineticDriftCof8Row4,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2,kineticDriftBlock8Row3,kineticDriftBlock8Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff0Row4Norm,kineticDriftCof8Coeff0Row5Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff1Row3Norm,kineticDriftCof8Coeff1Row4Norm,kineticDriftCof8Coeff1Row5Norm,kineticDriftCof8Coeff2Row0Norm,kineticDriftCof8Coeff2Row1Norm,kineticDriftCof8Coeff2Row2Norm,kineticDriftCof8Coeff2Row3Norm,kineticDriftCof8Coeff2Row4Norm,kineticDriftCof8Coeff2Row5Norm,kineticDriftCof8Coeff3Row0Norm,kineticDriftCof8Coeff3Row1Norm,kineticDriftCof8Coeff3Row2Norm,kineticDriftCof8Coeff3Row3Norm,kineticDriftCof8Coeff3Row4Norm,kineticDriftCof8Coeff3Row5Norm,kineticDriftCof8Coeff4Row0Norm,kineticDriftCof8Coeff4Row1Norm,kineticDriftCof8Coeff4Row2Norm,kineticDriftCof8Coeff4Row3Norm,kineticDriftCof8Coeff4Row4Norm,kineticDriftCof8Coeff4Row5Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff0Row4Norm,kineticDriftBlock8Coeff0Row5Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff1Row3Norm,kineticDriftBlock8Coeff1Row4Norm,kineticDriftBlock8Coeff1Row5Norm,kineticDriftBlock8Coeff2Row0Norm,kineticDriftBlock8Coeff2Row1Norm,kineticDriftBlock8Coeff2Row2Norm,kineticDriftBlock8Coeff2Row3Norm,kineticDriftBlock8Coeff2Row4Norm,kineticDriftBlock8Coeff2Row5Norm,kineticDriftBlock8Coeff3Row0Norm,kineticDriftBlock8Coeff3Row1Norm,kineticDriftBlock8Coeff3Row2Norm,kineticDriftBlock8Coeff3Row3Norm,kineticDriftBlock8Coeff3Row4Norm,kineticDriftBlock8Coeff3Row5Norm,kineticDriftBlock8Coeff4Row0Norm,kineticDriftBlock8Coeff4Row1Norm,kineticDriftBlock8Coeff4Row2Norm,kineticDriftBlock8Coeff4Row3Norm,kineticDriftBlock8Coeff4Row4Norm,kineticDriftBlock8Coeff4Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff4Row8Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 4 8=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 4 8=kineticDriftCell h (kineticCof10*kineticBlock10) 4 8 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftCof10Row3,kineticDriftCof10Row4,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2,kineticDriftBlock10Row3,kineticDriftBlock10Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff0Row4Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff1Row3Norm,kineticDriftCof10Coeff1Row4Norm,kineticDriftCof10Coeff2Row0Norm,kineticDriftCof10Coeff2Row1Norm,kineticDriftCof10Coeff2Row2Norm,kineticDriftCof10Coeff2Row3Norm,kineticDriftCof10Coeff2Row4Norm,kineticDriftCof10Coeff3Row0Norm,kineticDriftCof10Coeff3Row1Norm,kineticDriftCof10Coeff3Row2Norm,kineticDriftCof10Coeff3Row3Norm,kineticDriftCof10Coeff3Row4Norm,kineticDriftCof10Coeff4Row0Norm,kineticDriftCof10Coeff4Row1Norm,kineticDriftCof10Coeff4Row2Norm,kineticDriftCof10Coeff4Row3Norm,kineticDriftCof10Coeff4Row4Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff0Row4Norm,kineticDriftBlock10Coeff0Row5Norm,kineticDriftBlock10Coeff0Row6Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff1Row3Norm,kineticDriftBlock10Coeff1Row4Norm,kineticDriftBlock10Coeff1Row5Norm,kineticDriftBlock10Coeff1Row6Norm,kineticDriftBlock10Coeff2Row0Norm,kineticDriftBlock10Coeff2Row1Norm,kineticDriftBlock10Coeff2Row2Norm,kineticDriftBlock10Coeff2Row3Norm,kineticDriftBlock10Coeff2Row4Norm,kineticDriftBlock10Coeff2Row5Norm,kineticDriftBlock10Coeff2Row6Norm,kineticDriftBlock10Coeff3Row0Norm,kineticDriftBlock10Coeff3Row1Norm,kineticDriftBlock10Coeff3Row2Norm,kineticDriftBlock10Coeff3Row3Norm,kineticDriftBlock10Coeff3Row4Norm,kineticDriftBlock10Coeff3Row5Norm,kineticDriftBlock10Coeff3Row6Norm,kineticDriftBlock10Coeff4Row0Norm,kineticDriftBlock10Coeff4Row1Norm,kineticDriftBlock10Coeff4Row2Norm,kineticDriftBlock10Coeff4Row3Norm,kineticDriftBlock10Coeff4Row4Norm,kineticDriftBlock10Coeff4Row5Norm,kineticDriftBlock10Coeff4Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff4Row9Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 4 9=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 4 9=kineticDriftCell h (kineticCof2*kineticBlock2) 4 9 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftCof2Row3,kineticDriftCof2Row4,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2,kineticDriftBlock2Row3]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm,kineticDriftCof2Coeff0Row4Norm,kineticDriftCof2Coeff0Row5Norm,kineticDriftCof2Coeff0Row6Norm,kineticDriftCof2Coeff0Row7Norm,kineticDriftCof2Coeff0Row8Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff1Row3Norm,kineticDriftCof2Coeff1Row4Norm,kineticDriftCof2Coeff1Row5Norm,kineticDriftCof2Coeff1Row6Norm,kineticDriftCof2Coeff1Row7Norm,kineticDriftCof2Coeff1Row8Norm,kineticDriftCof2Coeff2Row0Norm,kineticDriftCof2Coeff2Row1Norm,kineticDriftCof2Coeff2Row2Norm,kineticDriftCof2Coeff2Row3Norm,kineticDriftCof2Coeff2Row4Norm,kineticDriftCof2Coeff2Row5Norm,kineticDriftCof2Coeff2Row6Norm,kineticDriftCof2Coeff2Row7Norm,kineticDriftCof2Coeff2Row8Norm,kineticDriftCof2Coeff3Row0Norm,kineticDriftCof2Coeff3Row1Norm,kineticDriftCof2Coeff3Row2Norm,kineticDriftCof2Coeff3Row3Norm,kineticDriftCof2Coeff3Row4Norm,kineticDriftCof2Coeff3Row5Norm,kineticDriftCof2Coeff3Row6Norm,kineticDriftCof2Coeff3Row7Norm,kineticDriftCof2Coeff3Row8Norm,kineticDriftCof2Coeff4Row0Norm,kineticDriftCof2Coeff4Row1Norm,kineticDriftCof2Coeff4Row2Norm,kineticDriftCof2Coeff4Row3Norm,kineticDriftCof2Coeff4Row4Norm,kineticDriftCof2Coeff4Row5Norm,kineticDriftCof2Coeff4Row6Norm,kineticDriftCof2Coeff4Row7Norm,kineticDriftCof2Coeff4Row8Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm,kineticDriftBlock2Coeff2Row0Norm,kineticDriftBlock2Coeff2Row1Norm,kineticDriftBlock2Coeff2Row2Norm,kineticDriftBlock2Coeff3Row0Norm,kineticDriftBlock2Coeff3Row1Norm,kineticDriftBlock2Coeff3Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff4Row9Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 4 9=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 4 9=kineticDriftCell h (kineticCof4*kineticBlock4) 4 9 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftCof4Row3,kineticDriftCof4Row4,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2,kineticDriftBlock4Row3,kineticDriftBlock4Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff0Row4Norm,kineticDriftCof4Coeff0Row5Norm,kineticDriftCof4Coeff0Row6Norm,kineticDriftCof4Coeff0Row7Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff1Row3Norm,kineticDriftCof4Coeff1Row4Norm,kineticDriftCof4Coeff1Row5Norm,kineticDriftCof4Coeff1Row6Norm,kineticDriftCof4Coeff1Row7Norm,kineticDriftCof4Coeff2Row0Norm,kineticDriftCof4Coeff2Row1Norm,kineticDriftCof4Coeff2Row2Norm,kineticDriftCof4Coeff2Row3Norm,kineticDriftCof4Coeff2Row4Norm,kineticDriftCof4Coeff2Row5Norm,kineticDriftCof4Coeff2Row6Norm,kineticDriftCof4Coeff2Row7Norm,kineticDriftCof4Coeff3Row0Norm,kineticDriftCof4Coeff3Row1Norm,kineticDriftCof4Coeff3Row2Norm,kineticDriftCof4Coeff3Row3Norm,kineticDriftCof4Coeff3Row4Norm,kineticDriftCof4Coeff3Row5Norm,kineticDriftCof4Coeff3Row6Norm,kineticDriftCof4Coeff3Row7Norm,kineticDriftCof4Coeff4Row0Norm,kineticDriftCof4Coeff4Row1Norm,kineticDriftCof4Coeff4Row2Norm,kineticDriftCof4Coeff4Row3Norm,kineticDriftCof4Coeff4Row4Norm,kineticDriftCof4Coeff4Row5Norm,kineticDriftCof4Coeff4Row6Norm,kineticDriftCof4Coeff4Row7Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff1Row3Norm,kineticDriftBlock4Coeff2Row0Norm,kineticDriftBlock4Coeff2Row1Norm,kineticDriftBlock4Coeff2Row2Norm,kineticDriftBlock4Coeff2Row3Norm,kineticDriftBlock4Coeff3Row0Norm,kineticDriftBlock4Coeff3Row1Norm,kineticDriftBlock4Coeff3Row2Norm,kineticDriftBlock4Coeff3Row3Norm,kineticDriftBlock4Coeff4Row0Norm,kineticDriftBlock4Coeff4Row1Norm,kineticDriftBlock4Coeff4Row2Norm,kineticDriftBlock4Coeff4Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff4Row9Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 4 9=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 4 9=kineticDriftCell h (kineticCof6*kineticBlock6) 4 9 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftCof6Row3,kineticDriftCof6Row4,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2,kineticDriftBlock6Row3,kineticDriftBlock6Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff0Row4Norm,kineticDriftCof6Coeff0Row5Norm,kineticDriftCof6Coeff0Row6Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff1Row3Norm,kineticDriftCof6Coeff1Row4Norm,kineticDriftCof6Coeff1Row5Norm,kineticDriftCof6Coeff1Row6Norm,kineticDriftCof6Coeff2Row0Norm,kineticDriftCof6Coeff2Row1Norm,kineticDriftCof6Coeff2Row2Norm,kineticDriftCof6Coeff2Row3Norm,kineticDriftCof6Coeff2Row4Norm,kineticDriftCof6Coeff2Row5Norm,kineticDriftCof6Coeff2Row6Norm,kineticDriftCof6Coeff3Row0Norm,kineticDriftCof6Coeff3Row1Norm,kineticDriftCof6Coeff3Row2Norm,kineticDriftCof6Coeff3Row3Norm,kineticDriftCof6Coeff3Row4Norm,kineticDriftCof6Coeff3Row5Norm,kineticDriftCof6Coeff3Row6Norm,kineticDriftCof6Coeff4Row0Norm,kineticDriftCof6Coeff4Row1Norm,kineticDriftCof6Coeff4Row2Norm,kineticDriftCof6Coeff4Row3Norm,kineticDriftCof6Coeff4Row4Norm,kineticDriftCof6Coeff4Row5Norm,kineticDriftCof6Coeff4Row6Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff0Row4Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff1Row3Norm,kineticDriftBlock6Coeff1Row4Norm,kineticDriftBlock6Coeff2Row0Norm,kineticDriftBlock6Coeff2Row1Norm,kineticDriftBlock6Coeff2Row2Norm,kineticDriftBlock6Coeff2Row3Norm,kineticDriftBlock6Coeff2Row4Norm,kineticDriftBlock6Coeff3Row0Norm,kineticDriftBlock6Coeff3Row1Norm,kineticDriftBlock6Coeff3Row2Norm,kineticDriftBlock6Coeff3Row3Norm,kineticDriftBlock6Coeff3Row4Norm,kineticDriftBlock6Coeff4Row0Norm,kineticDriftBlock6Coeff4Row1Norm,kineticDriftBlock6Coeff4Row2Norm,kineticDriftBlock6Coeff4Row3Norm,kineticDriftBlock6Coeff4Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff4Row9Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 4 9=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 4 9=kineticDriftCell h (kineticCof8*kineticBlock8) 4 9 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftCof8Row3,kineticDriftCof8Row4,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2,kineticDriftBlock8Row3,kineticDriftBlock8Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff0Row4Norm,kineticDriftCof8Coeff0Row5Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff1Row3Norm,kineticDriftCof8Coeff1Row4Norm,kineticDriftCof8Coeff1Row5Norm,kineticDriftCof8Coeff2Row0Norm,kineticDriftCof8Coeff2Row1Norm,kineticDriftCof8Coeff2Row2Norm,kineticDriftCof8Coeff2Row3Norm,kineticDriftCof8Coeff2Row4Norm,kineticDriftCof8Coeff2Row5Norm,kineticDriftCof8Coeff3Row0Norm,kineticDriftCof8Coeff3Row1Norm,kineticDriftCof8Coeff3Row2Norm,kineticDriftCof8Coeff3Row3Norm,kineticDriftCof8Coeff3Row4Norm,kineticDriftCof8Coeff3Row5Norm,kineticDriftCof8Coeff4Row0Norm,kineticDriftCof8Coeff4Row1Norm,kineticDriftCof8Coeff4Row2Norm,kineticDriftCof8Coeff4Row3Norm,kineticDriftCof8Coeff4Row4Norm,kineticDriftCof8Coeff4Row5Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff0Row4Norm,kineticDriftBlock8Coeff0Row5Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff1Row3Norm,kineticDriftBlock8Coeff1Row4Norm,kineticDriftBlock8Coeff1Row5Norm,kineticDriftBlock8Coeff2Row0Norm,kineticDriftBlock8Coeff2Row1Norm,kineticDriftBlock8Coeff2Row2Norm,kineticDriftBlock8Coeff2Row3Norm,kineticDriftBlock8Coeff2Row4Norm,kineticDriftBlock8Coeff2Row5Norm,kineticDriftBlock8Coeff3Row0Norm,kineticDriftBlock8Coeff3Row1Norm,kineticDriftBlock8Coeff3Row2Norm,kineticDriftBlock8Coeff3Row3Norm,kineticDriftBlock8Coeff3Row4Norm,kineticDriftBlock8Coeff3Row5Norm,kineticDriftBlock8Coeff4Row0Norm,kineticDriftBlock8Coeff4Row1Norm,kineticDriftBlock8Coeff4Row2Norm,kineticDriftBlock8Coeff4Row3Norm,kineticDriftBlock8Coeff4Row4Norm,kineticDriftBlock8Coeff4Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff4Row9Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 4 9=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 4 9=kineticDriftCell h (kineticCof10*kineticBlock10) 4 9 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftCof10Row3,kineticDriftCof10Row4,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2,kineticDriftBlock10Row3,kineticDriftBlock10Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff0Row4Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff1Row3Norm,kineticDriftCof10Coeff1Row4Norm,kineticDriftCof10Coeff2Row0Norm,kineticDriftCof10Coeff2Row1Norm,kineticDriftCof10Coeff2Row2Norm,kineticDriftCof10Coeff2Row3Norm,kineticDriftCof10Coeff2Row4Norm,kineticDriftCof10Coeff3Row0Norm,kineticDriftCof10Coeff3Row1Norm,kineticDriftCof10Coeff3Row2Norm,kineticDriftCof10Coeff3Row3Norm,kineticDriftCof10Coeff3Row4Norm,kineticDriftCof10Coeff4Row0Norm,kineticDriftCof10Coeff4Row1Norm,kineticDriftCof10Coeff4Row2Norm,kineticDriftCof10Coeff4Row3Norm,kineticDriftCof10Coeff4Row4Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff0Row4Norm,kineticDriftBlock10Coeff0Row5Norm,kineticDriftBlock10Coeff0Row6Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff1Row3Norm,kineticDriftBlock10Coeff1Row4Norm,kineticDriftBlock10Coeff1Row5Norm,kineticDriftBlock10Coeff1Row6Norm,kineticDriftBlock10Coeff2Row0Norm,kineticDriftBlock10Coeff2Row1Norm,kineticDriftBlock10Coeff2Row2Norm,kineticDriftBlock10Coeff2Row3Norm,kineticDriftBlock10Coeff2Row4Norm,kineticDriftBlock10Coeff2Row5Norm,kineticDriftBlock10Coeff2Row6Norm,kineticDriftBlock10Coeff3Row0Norm,kineticDriftBlock10Coeff3Row1Norm,kineticDriftBlock10Coeff3Row2Norm,kineticDriftBlock10Coeff3Row3Norm,kineticDriftBlock10Coeff3Row4Norm,kineticDriftBlock10Coeff3Row5Norm,kineticDriftBlock10Coeff3Row6Norm,kineticDriftBlock10Coeff4Row0Norm,kineticDriftBlock10Coeff4Row1Norm,kineticDriftBlock10Coeff4Row2Norm,kineticDriftBlock10Coeff4Row3Norm,kineticDriftBlock10Coeff4Row4Norm,kineticDriftBlock10Coeff4Row5Norm,kineticDriftBlock10Coeff4Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff4Row10Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 4 10=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 4 10=kineticDriftCell h (kineticCof2*kineticBlock2) 4 10 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftCof2Row3,kineticDriftCof2Row4,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2,kineticDriftBlock2Row3]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm,kineticDriftCof2Coeff0Row4Norm,kineticDriftCof2Coeff0Row5Norm,kineticDriftCof2Coeff0Row6Norm,kineticDriftCof2Coeff0Row7Norm,kineticDriftCof2Coeff0Row8Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff1Row3Norm,kineticDriftCof2Coeff1Row4Norm,kineticDriftCof2Coeff1Row5Norm,kineticDriftCof2Coeff1Row6Norm,kineticDriftCof2Coeff1Row7Norm,kineticDriftCof2Coeff1Row8Norm,kineticDriftCof2Coeff2Row0Norm,kineticDriftCof2Coeff2Row1Norm,kineticDriftCof2Coeff2Row2Norm,kineticDriftCof2Coeff2Row3Norm,kineticDriftCof2Coeff2Row4Norm,kineticDriftCof2Coeff2Row5Norm,kineticDriftCof2Coeff2Row6Norm,kineticDriftCof2Coeff2Row7Norm,kineticDriftCof2Coeff2Row8Norm,kineticDriftCof2Coeff3Row0Norm,kineticDriftCof2Coeff3Row1Norm,kineticDriftCof2Coeff3Row2Norm,kineticDriftCof2Coeff3Row3Norm,kineticDriftCof2Coeff3Row4Norm,kineticDriftCof2Coeff3Row5Norm,kineticDriftCof2Coeff3Row6Norm,kineticDriftCof2Coeff3Row7Norm,kineticDriftCof2Coeff3Row8Norm,kineticDriftCof2Coeff4Row0Norm,kineticDriftCof2Coeff4Row1Norm,kineticDriftCof2Coeff4Row2Norm,kineticDriftCof2Coeff4Row3Norm,kineticDriftCof2Coeff4Row4Norm,kineticDriftCof2Coeff4Row5Norm,kineticDriftCof2Coeff4Row6Norm,kineticDriftCof2Coeff4Row7Norm,kineticDriftCof2Coeff4Row8Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm,kineticDriftBlock2Coeff2Row0Norm,kineticDriftBlock2Coeff2Row1Norm,kineticDriftBlock2Coeff2Row2Norm,kineticDriftBlock2Coeff3Row0Norm,kineticDriftBlock2Coeff3Row1Norm,kineticDriftBlock2Coeff3Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff4Row10Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 4 10=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 4 10=kineticDriftCell h (kineticCof4*kineticBlock4) 4 10 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftCof4Row3,kineticDriftCof4Row4,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2,kineticDriftBlock4Row3,kineticDriftBlock4Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff0Row4Norm,kineticDriftCof4Coeff0Row5Norm,kineticDriftCof4Coeff0Row6Norm,kineticDriftCof4Coeff0Row7Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff1Row3Norm,kineticDriftCof4Coeff1Row4Norm,kineticDriftCof4Coeff1Row5Norm,kineticDriftCof4Coeff1Row6Norm,kineticDriftCof4Coeff1Row7Norm,kineticDriftCof4Coeff2Row0Norm,kineticDriftCof4Coeff2Row1Norm,kineticDriftCof4Coeff2Row2Norm,kineticDriftCof4Coeff2Row3Norm,kineticDriftCof4Coeff2Row4Norm,kineticDriftCof4Coeff2Row5Norm,kineticDriftCof4Coeff2Row6Norm,kineticDriftCof4Coeff2Row7Norm,kineticDriftCof4Coeff3Row0Norm,kineticDriftCof4Coeff3Row1Norm,kineticDriftCof4Coeff3Row2Norm,kineticDriftCof4Coeff3Row3Norm,kineticDriftCof4Coeff3Row4Norm,kineticDriftCof4Coeff3Row5Norm,kineticDriftCof4Coeff3Row6Norm,kineticDriftCof4Coeff3Row7Norm,kineticDriftCof4Coeff4Row0Norm,kineticDriftCof4Coeff4Row1Norm,kineticDriftCof4Coeff4Row2Norm,kineticDriftCof4Coeff4Row3Norm,kineticDriftCof4Coeff4Row4Norm,kineticDriftCof4Coeff4Row5Norm,kineticDriftCof4Coeff4Row6Norm,kineticDriftCof4Coeff4Row7Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff1Row3Norm,kineticDriftBlock4Coeff2Row0Norm,kineticDriftBlock4Coeff2Row1Norm,kineticDriftBlock4Coeff2Row2Norm,kineticDriftBlock4Coeff2Row3Norm,kineticDriftBlock4Coeff3Row0Norm,kineticDriftBlock4Coeff3Row1Norm,kineticDriftBlock4Coeff3Row2Norm,kineticDriftBlock4Coeff3Row3Norm,kineticDriftBlock4Coeff4Row0Norm,kineticDriftBlock4Coeff4Row1Norm,kineticDriftBlock4Coeff4Row2Norm,kineticDriftBlock4Coeff4Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff4Row10Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 4 10=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 4 10=kineticDriftCell h (kineticCof6*kineticBlock6) 4 10 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftCof6Row3,kineticDriftCof6Row4,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2,kineticDriftBlock6Row3,kineticDriftBlock6Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff0Row4Norm,kineticDriftCof6Coeff0Row5Norm,kineticDriftCof6Coeff0Row6Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff1Row3Norm,kineticDriftCof6Coeff1Row4Norm,kineticDriftCof6Coeff1Row5Norm,kineticDriftCof6Coeff1Row6Norm,kineticDriftCof6Coeff2Row0Norm,kineticDriftCof6Coeff2Row1Norm,kineticDriftCof6Coeff2Row2Norm,kineticDriftCof6Coeff2Row3Norm,kineticDriftCof6Coeff2Row4Norm,kineticDriftCof6Coeff2Row5Norm,kineticDriftCof6Coeff2Row6Norm,kineticDriftCof6Coeff3Row0Norm,kineticDriftCof6Coeff3Row1Norm,kineticDriftCof6Coeff3Row2Norm,kineticDriftCof6Coeff3Row3Norm,kineticDriftCof6Coeff3Row4Norm,kineticDriftCof6Coeff3Row5Norm,kineticDriftCof6Coeff3Row6Norm,kineticDriftCof6Coeff4Row0Norm,kineticDriftCof6Coeff4Row1Norm,kineticDriftCof6Coeff4Row2Norm,kineticDriftCof6Coeff4Row3Norm,kineticDriftCof6Coeff4Row4Norm,kineticDriftCof6Coeff4Row5Norm,kineticDriftCof6Coeff4Row6Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff0Row4Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff1Row3Norm,kineticDriftBlock6Coeff1Row4Norm,kineticDriftBlock6Coeff2Row0Norm,kineticDriftBlock6Coeff2Row1Norm,kineticDriftBlock6Coeff2Row2Norm,kineticDriftBlock6Coeff2Row3Norm,kineticDriftBlock6Coeff2Row4Norm,kineticDriftBlock6Coeff3Row0Norm,kineticDriftBlock6Coeff3Row1Norm,kineticDriftBlock6Coeff3Row2Norm,kineticDriftBlock6Coeff3Row3Norm,kineticDriftBlock6Coeff3Row4Norm,kineticDriftBlock6Coeff4Row0Norm,kineticDriftBlock6Coeff4Row1Norm,kineticDriftBlock6Coeff4Row2Norm,kineticDriftBlock6Coeff4Row3Norm,kineticDriftBlock6Coeff4Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff4Row10Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 4 10=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 4 10=kineticDriftCell h (kineticCof8*kineticBlock8) 4 10 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftCof8Row3,kineticDriftCof8Row4,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2,kineticDriftBlock8Row3,kineticDriftBlock8Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff0Row4Norm,kineticDriftCof8Coeff0Row5Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff1Row3Norm,kineticDriftCof8Coeff1Row4Norm,kineticDriftCof8Coeff1Row5Norm,kineticDriftCof8Coeff2Row0Norm,kineticDriftCof8Coeff2Row1Norm,kineticDriftCof8Coeff2Row2Norm,kineticDriftCof8Coeff2Row3Norm,kineticDriftCof8Coeff2Row4Norm,kineticDriftCof8Coeff2Row5Norm,kineticDriftCof8Coeff3Row0Norm,kineticDriftCof8Coeff3Row1Norm,kineticDriftCof8Coeff3Row2Norm,kineticDriftCof8Coeff3Row3Norm,kineticDriftCof8Coeff3Row4Norm,kineticDriftCof8Coeff3Row5Norm,kineticDriftCof8Coeff4Row0Norm,kineticDriftCof8Coeff4Row1Norm,kineticDriftCof8Coeff4Row2Norm,kineticDriftCof8Coeff4Row3Norm,kineticDriftCof8Coeff4Row4Norm,kineticDriftCof8Coeff4Row5Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff0Row4Norm,kineticDriftBlock8Coeff0Row5Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff1Row3Norm,kineticDriftBlock8Coeff1Row4Norm,kineticDriftBlock8Coeff1Row5Norm,kineticDriftBlock8Coeff2Row0Norm,kineticDriftBlock8Coeff2Row1Norm,kineticDriftBlock8Coeff2Row2Norm,kineticDriftBlock8Coeff2Row3Norm,kineticDriftBlock8Coeff2Row4Norm,kineticDriftBlock8Coeff2Row5Norm,kineticDriftBlock8Coeff3Row0Norm,kineticDriftBlock8Coeff3Row1Norm,kineticDriftBlock8Coeff3Row2Norm,kineticDriftBlock8Coeff3Row3Norm,kineticDriftBlock8Coeff3Row4Norm,kineticDriftBlock8Coeff3Row5Norm,kineticDriftBlock8Coeff4Row0Norm,kineticDriftBlock8Coeff4Row1Norm,kineticDriftBlock8Coeff4Row2Norm,kineticDriftBlock8Coeff4Row3Norm,kineticDriftBlock8Coeff4Row4Norm,kineticDriftBlock8Coeff4Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff4Row10Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 4 10=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 4 10=kineticDriftCell h (kineticCof10*kineticBlock10) 4 10 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftCof10Row3,kineticDriftCof10Row4,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2,kineticDriftBlock10Row3,kineticDriftBlock10Row4]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff0Row4Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff1Row3Norm,kineticDriftCof10Coeff1Row4Norm,kineticDriftCof10Coeff2Row0Norm,kineticDriftCof10Coeff2Row1Norm,kineticDriftCof10Coeff2Row2Norm,kineticDriftCof10Coeff2Row3Norm,kineticDriftCof10Coeff2Row4Norm,kineticDriftCof10Coeff3Row0Norm,kineticDriftCof10Coeff3Row1Norm,kineticDriftCof10Coeff3Row2Norm,kineticDriftCof10Coeff3Row3Norm,kineticDriftCof10Coeff3Row4Norm,kineticDriftCof10Coeff4Row0Norm,kineticDriftCof10Coeff4Row1Norm,kineticDriftCof10Coeff4Row2Norm,kineticDriftCof10Coeff4Row3Norm,kineticDriftCof10Coeff4Row4Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff0Row4Norm,kineticDriftBlock10Coeff0Row5Norm,kineticDriftBlock10Coeff0Row6Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff1Row3Norm,kineticDriftBlock10Coeff1Row4Norm,kineticDriftBlock10Coeff1Row5Norm,kineticDriftBlock10Coeff1Row6Norm,kineticDriftBlock10Coeff2Row0Norm,kineticDriftBlock10Coeff2Row1Norm,kineticDriftBlock10Coeff2Row2Norm,kineticDriftBlock10Coeff2Row3Norm,kineticDriftBlock10Coeff2Row4Norm,kineticDriftBlock10Coeff2Row5Norm,kineticDriftBlock10Coeff2Row6Norm,kineticDriftBlock10Coeff3Row0Norm,kineticDriftBlock10Coeff3Row1Norm,kineticDriftBlock10Coeff3Row2Norm,kineticDriftBlock10Coeff3Row3Norm,kineticDriftBlock10Coeff3Row4Norm,kineticDriftBlock10Coeff3Row5Norm,kineticDriftBlock10Coeff3Row6Norm,kineticDriftBlock10Coeff4Row0Norm,kineticDriftBlock10Coeff4Row1Norm,kineticDriftBlock10Coeff4Row2Norm,kineticDriftBlock10Coeff4Row3Norm,kineticDriftBlock10Coeff4Row4Norm,kineticDriftBlock10Coeff4Row5Norm,kineticDriftBlock10Coeff4Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

end
end HTGeometry.ThetaRatioKineticContraction

