import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondSource
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def kineticSourcePart2Coeff7Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 7 1=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 7 1=kineticDriftCell h (kineticCof2*kineticBlock2) 7 1 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftCof2Row3,kineticDriftCof2Row4,kineticDriftCof2Row5,kineticDriftCof2Row6,kineticDriftCof2Row7,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2,kineticDriftBlock2Row3]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff2Row0Norm,kineticDriftCof2Coeff2Row1Norm,kineticDriftCof2Coeff3Row0Norm,kineticDriftCof2Coeff3Row1Norm,kineticDriftCof2Coeff4Row0Norm,kineticDriftCof2Coeff4Row1Norm,kineticDriftCof2Coeff5Row0Norm,kineticDriftCof2Coeff5Row1Norm,kineticDriftCof2Coeff6Row0Norm,kineticDriftCof2Coeff6Row1Norm,kineticDriftCof2Coeff7Row0Norm,kineticDriftCof2Coeff7Row1Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff2Row0Norm,kineticDriftBlock2Coeff2Row1Norm,kineticDriftBlock2Coeff3Row0Norm,kineticDriftBlock2Coeff3Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff7Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 7 1=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 7 1=kineticDriftCell h (kineticCof4*kineticBlock4) 7 1 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftCof4Row3,kineticDriftCof4Row4,kineticDriftCof4Row5,kineticDriftCof4Row6,kineticDriftCof4Row7,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2,kineticDriftBlock4Row3,kineticDriftBlock4Row4,kineticDriftBlock4Row5]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff2Row0Norm,kineticDriftCof4Coeff2Row1Norm,kineticDriftCof4Coeff3Row0Norm,kineticDriftCof4Coeff3Row1Norm,kineticDriftCof4Coeff4Row0Norm,kineticDriftCof4Coeff4Row1Norm,kineticDriftCof4Coeff5Row0Norm,kineticDriftCof4Coeff5Row1Norm,kineticDriftCof4Coeff6Row0Norm,kineticDriftCof4Coeff6Row1Norm,kineticDriftCof4Coeff7Row0Norm,kineticDriftCof4Coeff7Row1Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff2Row0Norm,kineticDriftBlock4Coeff2Row1Norm,kineticDriftBlock4Coeff3Row0Norm,kineticDriftBlock4Coeff3Row1Norm,kineticDriftBlock4Coeff4Row0Norm,kineticDriftBlock4Coeff4Row1Norm,kineticDriftBlock4Coeff5Row0Norm,kineticDriftBlock4Coeff5Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff7Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 7 1=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 7 1=kineticDriftCell h (kineticCof6*kineticBlock6) 7 1 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftCof6Row3,kineticDriftCof6Row4,kineticDriftCof6Row5,kineticDriftCof6Row6,kineticDriftCof6Row7,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2,kineticDriftBlock6Row3,kineticDriftBlock6Row4,kineticDriftBlock6Row5,kineticDriftBlock6Row6,kineticDriftBlock6Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff2Row0Norm,kineticDriftCof6Coeff2Row1Norm,kineticDriftCof6Coeff3Row0Norm,kineticDriftCof6Coeff3Row1Norm,kineticDriftCof6Coeff4Row0Norm,kineticDriftCof6Coeff4Row1Norm,kineticDriftCof6Coeff5Row0Norm,kineticDriftCof6Coeff5Row1Norm,kineticDriftCof6Coeff6Row0Norm,kineticDriftCof6Coeff6Row1Norm,kineticDriftCof6Coeff7Row0Norm,kineticDriftCof6Coeff7Row1Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff2Row0Norm,kineticDriftBlock6Coeff2Row1Norm,kineticDriftBlock6Coeff3Row0Norm,kineticDriftBlock6Coeff3Row1Norm,kineticDriftBlock6Coeff4Row0Norm,kineticDriftBlock6Coeff4Row1Norm,kineticDriftBlock6Coeff5Row0Norm,kineticDriftBlock6Coeff5Row1Norm,kineticDriftBlock6Coeff6Row0Norm,kineticDriftBlock6Coeff6Row1Norm,kineticDriftBlock6Coeff7Row0Norm,kineticDriftBlock6Coeff7Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff7Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 7 1=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 7 1=kineticDriftCell h (kineticCof8*kineticBlock8) 7 1 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftCof8Row3,kineticDriftCof8Row4,kineticDriftCof8Row5,kineticDriftCof8Row6,kineticDriftCof8Row7,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2,kineticDriftBlock8Row3,kineticDriftBlock8Row4,kineticDriftBlock8Row5,kineticDriftBlock8Row6,kineticDriftBlock8Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff2Row0Norm,kineticDriftCof8Coeff2Row1Norm,kineticDriftCof8Coeff3Row0Norm,kineticDriftCof8Coeff3Row1Norm,kineticDriftCof8Coeff4Row0Norm,kineticDriftCof8Coeff4Row1Norm,kineticDriftCof8Coeff5Row0Norm,kineticDriftCof8Coeff5Row1Norm,kineticDriftCof8Coeff6Row0Norm,kineticDriftCof8Coeff6Row1Norm,kineticDriftCof8Coeff7Row0Norm,kineticDriftCof8Coeff7Row1Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff2Row0Norm,kineticDriftBlock8Coeff2Row1Norm,kineticDriftBlock8Coeff3Row0Norm,kineticDriftBlock8Coeff3Row1Norm,kineticDriftBlock8Coeff4Row0Norm,kineticDriftBlock8Coeff4Row1Norm,kineticDriftBlock8Coeff5Row0Norm,kineticDriftBlock8Coeff5Row1Norm,kineticDriftBlock8Coeff6Row0Norm,kineticDriftBlock8Coeff6Row1Norm,kineticDriftBlock8Coeff7Row0Norm,kineticDriftBlock8Coeff7Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff7Row1Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 7 1=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 7 1=kineticDriftCell h (kineticCof10*kineticBlock10) 7 1 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftCof10Row3,kineticDriftCof10Row4,kineticDriftCof10Row5,kineticDriftCof10Row6,kineticDriftCof10Row7,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2,kineticDriftBlock10Row3,kineticDriftBlock10Row4,kineticDriftBlock10Row5,kineticDriftBlock10Row6,kineticDriftBlock10Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff2Row0Norm,kineticDriftCof10Coeff2Row1Norm,kineticDriftCof10Coeff3Row0Norm,kineticDriftCof10Coeff3Row1Norm,kineticDriftCof10Coeff4Row0Norm,kineticDriftCof10Coeff4Row1Norm,kineticDriftCof10Coeff5Row0Norm,kineticDriftCof10Coeff5Row1Norm,kineticDriftCof10Coeff6Row0Norm,kineticDriftCof10Coeff6Row1Norm,kineticDriftCof10Coeff7Row0Norm,kineticDriftCof10Coeff7Row1Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff2Row0Norm,kineticDriftBlock10Coeff2Row1Norm,kineticDriftBlock10Coeff3Row0Norm,kineticDriftBlock10Coeff3Row1Norm,kineticDriftBlock10Coeff4Row0Norm,kineticDriftBlock10Coeff4Row1Norm,kineticDriftBlock10Coeff5Row0Norm,kineticDriftBlock10Coeff5Row1Norm,kineticDriftBlock10Coeff6Row0Norm,kineticDriftBlock10Coeff6Row1Norm,kineticDriftBlock10Coeff7Row0Norm,kineticDriftBlock10Coeff7Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff7Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 7 2=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 7 2=kineticDriftCell h (kineticCof2*kineticBlock2) 7 2 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftCof2Row3,kineticDriftCof2Row4,kineticDriftCof2Row5,kineticDriftCof2Row6,kineticDriftCof2Row7,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2,kineticDriftBlock2Row3]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff2Row0Norm,kineticDriftCof2Coeff2Row1Norm,kineticDriftCof2Coeff2Row2Norm,kineticDriftCof2Coeff3Row0Norm,kineticDriftCof2Coeff3Row1Norm,kineticDriftCof2Coeff3Row2Norm,kineticDriftCof2Coeff4Row0Norm,kineticDriftCof2Coeff4Row1Norm,kineticDriftCof2Coeff4Row2Norm,kineticDriftCof2Coeff5Row0Norm,kineticDriftCof2Coeff5Row1Norm,kineticDriftCof2Coeff5Row2Norm,kineticDriftCof2Coeff6Row0Norm,kineticDriftCof2Coeff6Row1Norm,kineticDriftCof2Coeff6Row2Norm,kineticDriftCof2Coeff7Row0Norm,kineticDriftCof2Coeff7Row1Norm,kineticDriftCof2Coeff7Row2Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm,kineticDriftBlock2Coeff2Row0Norm,kineticDriftBlock2Coeff2Row1Norm,kineticDriftBlock2Coeff2Row2Norm,kineticDriftBlock2Coeff3Row0Norm,kineticDriftBlock2Coeff3Row1Norm,kineticDriftBlock2Coeff3Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff7Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 7 2=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 7 2=kineticDriftCell h (kineticCof4*kineticBlock4) 7 2 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftCof4Row3,kineticDriftCof4Row4,kineticDriftCof4Row5,kineticDriftCof4Row6,kineticDriftCof4Row7,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2,kineticDriftBlock4Row3,kineticDriftBlock4Row4,kineticDriftBlock4Row5]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff2Row0Norm,kineticDriftCof4Coeff2Row1Norm,kineticDriftCof4Coeff2Row2Norm,kineticDriftCof4Coeff3Row0Norm,kineticDriftCof4Coeff3Row1Norm,kineticDriftCof4Coeff3Row2Norm,kineticDriftCof4Coeff4Row0Norm,kineticDriftCof4Coeff4Row1Norm,kineticDriftCof4Coeff4Row2Norm,kineticDriftCof4Coeff5Row0Norm,kineticDriftCof4Coeff5Row1Norm,kineticDriftCof4Coeff5Row2Norm,kineticDriftCof4Coeff6Row0Norm,kineticDriftCof4Coeff6Row1Norm,kineticDriftCof4Coeff6Row2Norm,kineticDriftCof4Coeff7Row0Norm,kineticDriftCof4Coeff7Row1Norm,kineticDriftCof4Coeff7Row2Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff2Row0Norm,kineticDriftBlock4Coeff2Row1Norm,kineticDriftBlock4Coeff2Row2Norm,kineticDriftBlock4Coeff3Row0Norm,kineticDriftBlock4Coeff3Row1Norm,kineticDriftBlock4Coeff3Row2Norm,kineticDriftBlock4Coeff4Row0Norm,kineticDriftBlock4Coeff4Row1Norm,kineticDriftBlock4Coeff4Row2Norm,kineticDriftBlock4Coeff5Row0Norm,kineticDriftBlock4Coeff5Row1Norm,kineticDriftBlock4Coeff5Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff7Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 7 2=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 7 2=kineticDriftCell h (kineticCof6*kineticBlock6) 7 2 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftCof6Row3,kineticDriftCof6Row4,kineticDriftCof6Row5,kineticDriftCof6Row6,kineticDriftCof6Row7,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2,kineticDriftBlock6Row3,kineticDriftBlock6Row4,kineticDriftBlock6Row5,kineticDriftBlock6Row6,kineticDriftBlock6Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff2Row0Norm,kineticDriftCof6Coeff2Row1Norm,kineticDriftCof6Coeff2Row2Norm,kineticDriftCof6Coeff3Row0Norm,kineticDriftCof6Coeff3Row1Norm,kineticDriftCof6Coeff3Row2Norm,kineticDriftCof6Coeff4Row0Norm,kineticDriftCof6Coeff4Row1Norm,kineticDriftCof6Coeff4Row2Norm,kineticDriftCof6Coeff5Row0Norm,kineticDriftCof6Coeff5Row1Norm,kineticDriftCof6Coeff5Row2Norm,kineticDriftCof6Coeff6Row0Norm,kineticDriftCof6Coeff6Row1Norm,kineticDriftCof6Coeff6Row2Norm,kineticDriftCof6Coeff7Row0Norm,kineticDriftCof6Coeff7Row1Norm,kineticDriftCof6Coeff7Row2Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff2Row0Norm,kineticDriftBlock6Coeff2Row1Norm,kineticDriftBlock6Coeff2Row2Norm,kineticDriftBlock6Coeff3Row0Norm,kineticDriftBlock6Coeff3Row1Norm,kineticDriftBlock6Coeff3Row2Norm,kineticDriftBlock6Coeff4Row0Norm,kineticDriftBlock6Coeff4Row1Norm,kineticDriftBlock6Coeff4Row2Norm,kineticDriftBlock6Coeff5Row0Norm,kineticDriftBlock6Coeff5Row1Norm,kineticDriftBlock6Coeff5Row2Norm,kineticDriftBlock6Coeff6Row0Norm,kineticDriftBlock6Coeff6Row1Norm,kineticDriftBlock6Coeff6Row2Norm,kineticDriftBlock6Coeff7Row0Norm,kineticDriftBlock6Coeff7Row1Norm,kineticDriftBlock6Coeff7Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff7Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 7 2=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 7 2=kineticDriftCell h (kineticCof8*kineticBlock8) 7 2 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftCof8Row3,kineticDriftCof8Row4,kineticDriftCof8Row5,kineticDriftCof8Row6,kineticDriftCof8Row7,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2,kineticDriftBlock8Row3,kineticDriftBlock8Row4,kineticDriftBlock8Row5,kineticDriftBlock8Row6,kineticDriftBlock8Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff2Row0Norm,kineticDriftCof8Coeff2Row1Norm,kineticDriftCof8Coeff2Row2Norm,kineticDriftCof8Coeff3Row0Norm,kineticDriftCof8Coeff3Row1Norm,kineticDriftCof8Coeff3Row2Norm,kineticDriftCof8Coeff4Row0Norm,kineticDriftCof8Coeff4Row1Norm,kineticDriftCof8Coeff4Row2Norm,kineticDriftCof8Coeff5Row0Norm,kineticDriftCof8Coeff5Row1Norm,kineticDriftCof8Coeff5Row2Norm,kineticDriftCof8Coeff6Row0Norm,kineticDriftCof8Coeff6Row1Norm,kineticDriftCof8Coeff6Row2Norm,kineticDriftCof8Coeff7Row0Norm,kineticDriftCof8Coeff7Row1Norm,kineticDriftCof8Coeff7Row2Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff2Row0Norm,kineticDriftBlock8Coeff2Row1Norm,kineticDriftBlock8Coeff2Row2Norm,kineticDriftBlock8Coeff3Row0Norm,kineticDriftBlock8Coeff3Row1Norm,kineticDriftBlock8Coeff3Row2Norm,kineticDriftBlock8Coeff4Row0Norm,kineticDriftBlock8Coeff4Row1Norm,kineticDriftBlock8Coeff4Row2Norm,kineticDriftBlock8Coeff5Row0Norm,kineticDriftBlock8Coeff5Row1Norm,kineticDriftBlock8Coeff5Row2Norm,kineticDriftBlock8Coeff6Row0Norm,kineticDriftBlock8Coeff6Row1Norm,kineticDriftBlock8Coeff6Row2Norm,kineticDriftBlock8Coeff7Row0Norm,kineticDriftBlock8Coeff7Row1Norm,kineticDriftBlock8Coeff7Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff7Row2Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 7 2=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 7 2=kineticDriftCell h (kineticCof10*kineticBlock10) 7 2 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftCof10Row3,kineticDriftCof10Row4,kineticDriftCof10Row5,kineticDriftCof10Row6,kineticDriftCof10Row7,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2,kineticDriftBlock10Row3,kineticDriftBlock10Row4,kineticDriftBlock10Row5,kineticDriftBlock10Row6,kineticDriftBlock10Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff2Row0Norm,kineticDriftCof10Coeff2Row1Norm,kineticDriftCof10Coeff2Row2Norm,kineticDriftCof10Coeff3Row0Norm,kineticDriftCof10Coeff3Row1Norm,kineticDriftCof10Coeff3Row2Norm,kineticDriftCof10Coeff4Row0Norm,kineticDriftCof10Coeff4Row1Norm,kineticDriftCof10Coeff4Row2Norm,kineticDriftCof10Coeff5Row0Norm,kineticDriftCof10Coeff5Row1Norm,kineticDriftCof10Coeff5Row2Norm,kineticDriftCof10Coeff6Row0Norm,kineticDriftCof10Coeff6Row1Norm,kineticDriftCof10Coeff6Row2Norm,kineticDriftCof10Coeff7Row0Norm,kineticDriftCof10Coeff7Row1Norm,kineticDriftCof10Coeff7Row2Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff2Row0Norm,kineticDriftBlock10Coeff2Row1Norm,kineticDriftBlock10Coeff2Row2Norm,kineticDriftBlock10Coeff3Row0Norm,kineticDriftBlock10Coeff3Row1Norm,kineticDriftBlock10Coeff3Row2Norm,kineticDriftBlock10Coeff4Row0Norm,kineticDriftBlock10Coeff4Row1Norm,kineticDriftBlock10Coeff4Row2Norm,kineticDriftBlock10Coeff5Row0Norm,kineticDriftBlock10Coeff5Row1Norm,kineticDriftBlock10Coeff5Row2Norm,kineticDriftBlock10Coeff6Row0Norm,kineticDriftBlock10Coeff6Row1Norm,kineticDriftBlock10Coeff6Row2Norm,kineticDriftBlock10Coeff7Row0Norm,kineticDriftBlock10Coeff7Row1Norm,kineticDriftBlock10Coeff7Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff7Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 7 3=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 7 3=kineticDriftCell h (kineticCof2*kineticBlock2) 7 3 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftCof2Row3,kineticDriftCof2Row4,kineticDriftCof2Row5,kineticDriftCof2Row6,kineticDriftCof2Row7,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2,kineticDriftBlock2Row3]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff1Row3Norm,kineticDriftCof2Coeff2Row0Norm,kineticDriftCof2Coeff2Row1Norm,kineticDriftCof2Coeff2Row2Norm,kineticDriftCof2Coeff2Row3Norm,kineticDriftCof2Coeff3Row0Norm,kineticDriftCof2Coeff3Row1Norm,kineticDriftCof2Coeff3Row2Norm,kineticDriftCof2Coeff3Row3Norm,kineticDriftCof2Coeff4Row0Norm,kineticDriftCof2Coeff4Row1Norm,kineticDriftCof2Coeff4Row2Norm,kineticDriftCof2Coeff4Row3Norm,kineticDriftCof2Coeff5Row0Norm,kineticDriftCof2Coeff5Row1Norm,kineticDriftCof2Coeff5Row2Norm,kineticDriftCof2Coeff5Row3Norm,kineticDriftCof2Coeff6Row0Norm,kineticDriftCof2Coeff6Row1Norm,kineticDriftCof2Coeff6Row2Norm,kineticDriftCof2Coeff6Row3Norm,kineticDriftCof2Coeff7Row0Norm,kineticDriftCof2Coeff7Row1Norm,kineticDriftCof2Coeff7Row2Norm,kineticDriftCof2Coeff7Row3Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm,kineticDriftBlock2Coeff2Row0Norm,kineticDriftBlock2Coeff2Row1Norm,kineticDriftBlock2Coeff2Row2Norm,kineticDriftBlock2Coeff3Row0Norm,kineticDriftBlock2Coeff3Row1Norm,kineticDriftBlock2Coeff3Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff7Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 7 3=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 7 3=kineticDriftCell h (kineticCof4*kineticBlock4) 7 3 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftCof4Row3,kineticDriftCof4Row4,kineticDriftCof4Row5,kineticDriftCof4Row6,kineticDriftCof4Row7,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2,kineticDriftBlock4Row3,kineticDriftBlock4Row4,kineticDriftBlock4Row5]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff1Row3Norm,kineticDriftCof4Coeff2Row0Norm,kineticDriftCof4Coeff2Row1Norm,kineticDriftCof4Coeff2Row2Norm,kineticDriftCof4Coeff2Row3Norm,kineticDriftCof4Coeff3Row0Norm,kineticDriftCof4Coeff3Row1Norm,kineticDriftCof4Coeff3Row2Norm,kineticDriftCof4Coeff3Row3Norm,kineticDriftCof4Coeff4Row0Norm,kineticDriftCof4Coeff4Row1Norm,kineticDriftCof4Coeff4Row2Norm,kineticDriftCof4Coeff4Row3Norm,kineticDriftCof4Coeff5Row0Norm,kineticDriftCof4Coeff5Row1Norm,kineticDriftCof4Coeff5Row2Norm,kineticDriftCof4Coeff5Row3Norm,kineticDriftCof4Coeff6Row0Norm,kineticDriftCof4Coeff6Row1Norm,kineticDriftCof4Coeff6Row2Norm,kineticDriftCof4Coeff6Row3Norm,kineticDriftCof4Coeff7Row0Norm,kineticDriftCof4Coeff7Row1Norm,kineticDriftCof4Coeff7Row2Norm,kineticDriftCof4Coeff7Row3Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff1Row3Norm,kineticDriftBlock4Coeff2Row0Norm,kineticDriftBlock4Coeff2Row1Norm,kineticDriftBlock4Coeff2Row2Norm,kineticDriftBlock4Coeff2Row3Norm,kineticDriftBlock4Coeff3Row0Norm,kineticDriftBlock4Coeff3Row1Norm,kineticDriftBlock4Coeff3Row2Norm,kineticDriftBlock4Coeff3Row3Norm,kineticDriftBlock4Coeff4Row0Norm,kineticDriftBlock4Coeff4Row1Norm,kineticDriftBlock4Coeff4Row2Norm,kineticDriftBlock4Coeff4Row3Norm,kineticDriftBlock4Coeff5Row0Norm,kineticDriftBlock4Coeff5Row1Norm,kineticDriftBlock4Coeff5Row2Norm,kineticDriftBlock4Coeff5Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff7Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 7 3=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 7 3=kineticDriftCell h (kineticCof6*kineticBlock6) 7 3 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftCof6Row3,kineticDriftCof6Row4,kineticDriftCof6Row5,kineticDriftCof6Row6,kineticDriftCof6Row7,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2,kineticDriftBlock6Row3,kineticDriftBlock6Row4,kineticDriftBlock6Row5,kineticDriftBlock6Row6,kineticDriftBlock6Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff1Row3Norm,kineticDriftCof6Coeff2Row0Norm,kineticDriftCof6Coeff2Row1Norm,kineticDriftCof6Coeff2Row2Norm,kineticDriftCof6Coeff2Row3Norm,kineticDriftCof6Coeff3Row0Norm,kineticDriftCof6Coeff3Row1Norm,kineticDriftCof6Coeff3Row2Norm,kineticDriftCof6Coeff3Row3Norm,kineticDriftCof6Coeff4Row0Norm,kineticDriftCof6Coeff4Row1Norm,kineticDriftCof6Coeff4Row2Norm,kineticDriftCof6Coeff4Row3Norm,kineticDriftCof6Coeff5Row0Norm,kineticDriftCof6Coeff5Row1Norm,kineticDriftCof6Coeff5Row2Norm,kineticDriftCof6Coeff5Row3Norm,kineticDriftCof6Coeff6Row0Norm,kineticDriftCof6Coeff6Row1Norm,kineticDriftCof6Coeff6Row2Norm,kineticDriftCof6Coeff6Row3Norm,kineticDriftCof6Coeff7Row0Norm,kineticDriftCof6Coeff7Row1Norm,kineticDriftCof6Coeff7Row2Norm,kineticDriftCof6Coeff7Row3Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff1Row3Norm,kineticDriftBlock6Coeff2Row0Norm,kineticDriftBlock6Coeff2Row1Norm,kineticDriftBlock6Coeff2Row2Norm,kineticDriftBlock6Coeff2Row3Norm,kineticDriftBlock6Coeff3Row0Norm,kineticDriftBlock6Coeff3Row1Norm,kineticDriftBlock6Coeff3Row2Norm,kineticDriftBlock6Coeff3Row3Norm,kineticDriftBlock6Coeff4Row0Norm,kineticDriftBlock6Coeff4Row1Norm,kineticDriftBlock6Coeff4Row2Norm,kineticDriftBlock6Coeff4Row3Norm,kineticDriftBlock6Coeff5Row0Norm,kineticDriftBlock6Coeff5Row1Norm,kineticDriftBlock6Coeff5Row2Norm,kineticDriftBlock6Coeff5Row3Norm,kineticDriftBlock6Coeff6Row0Norm,kineticDriftBlock6Coeff6Row1Norm,kineticDriftBlock6Coeff6Row2Norm,kineticDriftBlock6Coeff6Row3Norm,kineticDriftBlock6Coeff7Row0Norm,kineticDriftBlock6Coeff7Row1Norm,kineticDriftBlock6Coeff7Row2Norm,kineticDriftBlock6Coeff7Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff7Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 7 3=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 7 3=kineticDriftCell h (kineticCof8*kineticBlock8) 7 3 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftCof8Row3,kineticDriftCof8Row4,kineticDriftCof8Row5,kineticDriftCof8Row6,kineticDriftCof8Row7,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2,kineticDriftBlock8Row3,kineticDriftBlock8Row4,kineticDriftBlock8Row5,kineticDriftBlock8Row6,kineticDriftBlock8Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff1Row3Norm,kineticDriftCof8Coeff2Row0Norm,kineticDriftCof8Coeff2Row1Norm,kineticDriftCof8Coeff2Row2Norm,kineticDriftCof8Coeff2Row3Norm,kineticDriftCof8Coeff3Row0Norm,kineticDriftCof8Coeff3Row1Norm,kineticDriftCof8Coeff3Row2Norm,kineticDriftCof8Coeff3Row3Norm,kineticDriftCof8Coeff4Row0Norm,kineticDriftCof8Coeff4Row1Norm,kineticDriftCof8Coeff4Row2Norm,kineticDriftCof8Coeff4Row3Norm,kineticDriftCof8Coeff5Row0Norm,kineticDriftCof8Coeff5Row1Norm,kineticDriftCof8Coeff5Row2Norm,kineticDriftCof8Coeff5Row3Norm,kineticDriftCof8Coeff6Row0Norm,kineticDriftCof8Coeff6Row1Norm,kineticDriftCof8Coeff6Row2Norm,kineticDriftCof8Coeff6Row3Norm,kineticDriftCof8Coeff7Row0Norm,kineticDriftCof8Coeff7Row1Norm,kineticDriftCof8Coeff7Row2Norm,kineticDriftCof8Coeff7Row3Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff1Row3Norm,kineticDriftBlock8Coeff2Row0Norm,kineticDriftBlock8Coeff2Row1Norm,kineticDriftBlock8Coeff2Row2Norm,kineticDriftBlock8Coeff2Row3Norm,kineticDriftBlock8Coeff3Row0Norm,kineticDriftBlock8Coeff3Row1Norm,kineticDriftBlock8Coeff3Row2Norm,kineticDriftBlock8Coeff3Row3Norm,kineticDriftBlock8Coeff4Row0Norm,kineticDriftBlock8Coeff4Row1Norm,kineticDriftBlock8Coeff4Row2Norm,kineticDriftBlock8Coeff4Row3Norm,kineticDriftBlock8Coeff5Row0Norm,kineticDriftBlock8Coeff5Row1Norm,kineticDriftBlock8Coeff5Row2Norm,kineticDriftBlock8Coeff5Row3Norm,kineticDriftBlock8Coeff6Row0Norm,kineticDriftBlock8Coeff6Row1Norm,kineticDriftBlock8Coeff6Row2Norm,kineticDriftBlock8Coeff6Row3Norm,kineticDriftBlock8Coeff7Row0Norm,kineticDriftBlock8Coeff7Row1Norm,kineticDriftBlock8Coeff7Row2Norm,kineticDriftBlock8Coeff7Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff7Row3Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 7 3=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 7 3=kineticDriftCell h (kineticCof10*kineticBlock10) 7 3 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftCof10Row3,kineticDriftCof10Row4,kineticDriftCof10Row5,kineticDriftCof10Row6,kineticDriftCof10Row7,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2,kineticDriftBlock10Row3,kineticDriftBlock10Row4,kineticDriftBlock10Row5,kineticDriftBlock10Row6,kineticDriftBlock10Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff1Row3Norm,kineticDriftCof10Coeff2Row0Norm,kineticDriftCof10Coeff2Row1Norm,kineticDriftCof10Coeff2Row2Norm,kineticDriftCof10Coeff2Row3Norm,kineticDriftCof10Coeff3Row0Norm,kineticDriftCof10Coeff3Row1Norm,kineticDriftCof10Coeff3Row2Norm,kineticDriftCof10Coeff3Row3Norm,kineticDriftCof10Coeff4Row0Norm,kineticDriftCof10Coeff4Row1Norm,kineticDriftCof10Coeff4Row2Norm,kineticDriftCof10Coeff4Row3Norm,kineticDriftCof10Coeff5Row0Norm,kineticDriftCof10Coeff5Row1Norm,kineticDriftCof10Coeff5Row2Norm,kineticDriftCof10Coeff5Row3Norm,kineticDriftCof10Coeff6Row0Norm,kineticDriftCof10Coeff6Row1Norm,kineticDriftCof10Coeff6Row2Norm,kineticDriftCof10Coeff6Row3Norm,kineticDriftCof10Coeff7Row0Norm,kineticDriftCof10Coeff7Row1Norm,kineticDriftCof10Coeff7Row2Norm,kineticDriftCof10Coeff7Row3Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff1Row3Norm,kineticDriftBlock10Coeff2Row0Norm,kineticDriftBlock10Coeff2Row1Norm,kineticDriftBlock10Coeff2Row2Norm,kineticDriftBlock10Coeff2Row3Norm,kineticDriftBlock10Coeff3Row0Norm,kineticDriftBlock10Coeff3Row1Norm,kineticDriftBlock10Coeff3Row2Norm,kineticDriftBlock10Coeff3Row3Norm,kineticDriftBlock10Coeff4Row0Norm,kineticDriftBlock10Coeff4Row1Norm,kineticDriftBlock10Coeff4Row2Norm,kineticDriftBlock10Coeff4Row3Norm,kineticDriftBlock10Coeff5Row0Norm,kineticDriftBlock10Coeff5Row1Norm,kineticDriftBlock10Coeff5Row2Norm,kineticDriftBlock10Coeff5Row3Norm,kineticDriftBlock10Coeff6Row0Norm,kineticDriftBlock10Coeff6Row1Norm,kineticDriftBlock10Coeff6Row2Norm,kineticDriftBlock10Coeff6Row3Norm,kineticDriftBlock10Coeff7Row0Norm,kineticDriftBlock10Coeff7Row1Norm,kineticDriftBlock10Coeff7Row2Norm,kineticDriftBlock10Coeff7Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff7Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 7 4=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 7 4=kineticDriftCell h (kineticCof2*kineticBlock2) 7 4 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftCof2Row3,kineticDriftCof2Row4,kineticDriftCof2Row5,kineticDriftCof2Row6,kineticDriftCof2Row7,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2,kineticDriftBlock2Row3]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm,kineticDriftCof2Coeff0Row4Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff1Row3Norm,kineticDriftCof2Coeff1Row4Norm,kineticDriftCof2Coeff2Row0Norm,kineticDriftCof2Coeff2Row1Norm,kineticDriftCof2Coeff2Row2Norm,kineticDriftCof2Coeff2Row3Norm,kineticDriftCof2Coeff2Row4Norm,kineticDriftCof2Coeff3Row0Norm,kineticDriftCof2Coeff3Row1Norm,kineticDriftCof2Coeff3Row2Norm,kineticDriftCof2Coeff3Row3Norm,kineticDriftCof2Coeff3Row4Norm,kineticDriftCof2Coeff4Row0Norm,kineticDriftCof2Coeff4Row1Norm,kineticDriftCof2Coeff4Row2Norm,kineticDriftCof2Coeff4Row3Norm,kineticDriftCof2Coeff4Row4Norm,kineticDriftCof2Coeff5Row0Norm,kineticDriftCof2Coeff5Row1Norm,kineticDriftCof2Coeff5Row2Norm,kineticDriftCof2Coeff5Row3Norm,kineticDriftCof2Coeff5Row4Norm,kineticDriftCof2Coeff6Row0Norm,kineticDriftCof2Coeff6Row1Norm,kineticDriftCof2Coeff6Row2Norm,kineticDriftCof2Coeff6Row3Norm,kineticDriftCof2Coeff6Row4Norm,kineticDriftCof2Coeff7Row0Norm,kineticDriftCof2Coeff7Row1Norm,kineticDriftCof2Coeff7Row2Norm,kineticDriftCof2Coeff7Row3Norm,kineticDriftCof2Coeff7Row4Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm,kineticDriftBlock2Coeff2Row0Norm,kineticDriftBlock2Coeff2Row1Norm,kineticDriftBlock2Coeff2Row2Norm,kineticDriftBlock2Coeff3Row0Norm,kineticDriftBlock2Coeff3Row1Norm,kineticDriftBlock2Coeff3Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff7Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 7 4=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 7 4=kineticDriftCell h (kineticCof4*kineticBlock4) 7 4 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftCof4Row3,kineticDriftCof4Row4,kineticDriftCof4Row5,kineticDriftCof4Row6,kineticDriftCof4Row7,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2,kineticDriftBlock4Row3,kineticDriftBlock4Row4,kineticDriftBlock4Row5]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff0Row4Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff1Row3Norm,kineticDriftCof4Coeff1Row4Norm,kineticDriftCof4Coeff2Row0Norm,kineticDriftCof4Coeff2Row1Norm,kineticDriftCof4Coeff2Row2Norm,kineticDriftCof4Coeff2Row3Norm,kineticDriftCof4Coeff2Row4Norm,kineticDriftCof4Coeff3Row0Norm,kineticDriftCof4Coeff3Row1Norm,kineticDriftCof4Coeff3Row2Norm,kineticDriftCof4Coeff3Row3Norm,kineticDriftCof4Coeff3Row4Norm,kineticDriftCof4Coeff4Row0Norm,kineticDriftCof4Coeff4Row1Norm,kineticDriftCof4Coeff4Row2Norm,kineticDriftCof4Coeff4Row3Norm,kineticDriftCof4Coeff4Row4Norm,kineticDriftCof4Coeff5Row0Norm,kineticDriftCof4Coeff5Row1Norm,kineticDriftCof4Coeff5Row2Norm,kineticDriftCof4Coeff5Row3Norm,kineticDriftCof4Coeff5Row4Norm,kineticDriftCof4Coeff6Row0Norm,kineticDriftCof4Coeff6Row1Norm,kineticDriftCof4Coeff6Row2Norm,kineticDriftCof4Coeff6Row3Norm,kineticDriftCof4Coeff6Row4Norm,kineticDriftCof4Coeff7Row0Norm,kineticDriftCof4Coeff7Row1Norm,kineticDriftCof4Coeff7Row2Norm,kineticDriftCof4Coeff7Row3Norm,kineticDriftCof4Coeff7Row4Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff1Row3Norm,kineticDriftBlock4Coeff2Row0Norm,kineticDriftBlock4Coeff2Row1Norm,kineticDriftBlock4Coeff2Row2Norm,kineticDriftBlock4Coeff2Row3Norm,kineticDriftBlock4Coeff3Row0Norm,kineticDriftBlock4Coeff3Row1Norm,kineticDriftBlock4Coeff3Row2Norm,kineticDriftBlock4Coeff3Row3Norm,kineticDriftBlock4Coeff4Row0Norm,kineticDriftBlock4Coeff4Row1Norm,kineticDriftBlock4Coeff4Row2Norm,kineticDriftBlock4Coeff4Row3Norm,kineticDriftBlock4Coeff5Row0Norm,kineticDriftBlock4Coeff5Row1Norm,kineticDriftBlock4Coeff5Row2Norm,kineticDriftBlock4Coeff5Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff7Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 7 4=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 7 4=kineticDriftCell h (kineticCof6*kineticBlock6) 7 4 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftCof6Row3,kineticDriftCof6Row4,kineticDriftCof6Row5,kineticDriftCof6Row6,kineticDriftCof6Row7,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2,kineticDriftBlock6Row3,kineticDriftBlock6Row4,kineticDriftBlock6Row5,kineticDriftBlock6Row6,kineticDriftBlock6Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff0Row4Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff1Row3Norm,kineticDriftCof6Coeff1Row4Norm,kineticDriftCof6Coeff2Row0Norm,kineticDriftCof6Coeff2Row1Norm,kineticDriftCof6Coeff2Row2Norm,kineticDriftCof6Coeff2Row3Norm,kineticDriftCof6Coeff2Row4Norm,kineticDriftCof6Coeff3Row0Norm,kineticDriftCof6Coeff3Row1Norm,kineticDriftCof6Coeff3Row2Norm,kineticDriftCof6Coeff3Row3Norm,kineticDriftCof6Coeff3Row4Norm,kineticDriftCof6Coeff4Row0Norm,kineticDriftCof6Coeff4Row1Norm,kineticDriftCof6Coeff4Row2Norm,kineticDriftCof6Coeff4Row3Norm,kineticDriftCof6Coeff4Row4Norm,kineticDriftCof6Coeff5Row0Norm,kineticDriftCof6Coeff5Row1Norm,kineticDriftCof6Coeff5Row2Norm,kineticDriftCof6Coeff5Row3Norm,kineticDriftCof6Coeff5Row4Norm,kineticDriftCof6Coeff6Row0Norm,kineticDriftCof6Coeff6Row1Norm,kineticDriftCof6Coeff6Row2Norm,kineticDriftCof6Coeff6Row3Norm,kineticDriftCof6Coeff6Row4Norm,kineticDriftCof6Coeff7Row0Norm,kineticDriftCof6Coeff7Row1Norm,kineticDriftCof6Coeff7Row2Norm,kineticDriftCof6Coeff7Row3Norm,kineticDriftCof6Coeff7Row4Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff0Row4Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff1Row3Norm,kineticDriftBlock6Coeff1Row4Norm,kineticDriftBlock6Coeff2Row0Norm,kineticDriftBlock6Coeff2Row1Norm,kineticDriftBlock6Coeff2Row2Norm,kineticDriftBlock6Coeff2Row3Norm,kineticDriftBlock6Coeff2Row4Norm,kineticDriftBlock6Coeff3Row0Norm,kineticDriftBlock6Coeff3Row1Norm,kineticDriftBlock6Coeff3Row2Norm,kineticDriftBlock6Coeff3Row3Norm,kineticDriftBlock6Coeff3Row4Norm,kineticDriftBlock6Coeff4Row0Norm,kineticDriftBlock6Coeff4Row1Norm,kineticDriftBlock6Coeff4Row2Norm,kineticDriftBlock6Coeff4Row3Norm,kineticDriftBlock6Coeff4Row4Norm,kineticDriftBlock6Coeff5Row0Norm,kineticDriftBlock6Coeff5Row1Norm,kineticDriftBlock6Coeff5Row2Norm,kineticDriftBlock6Coeff5Row3Norm,kineticDriftBlock6Coeff5Row4Norm,kineticDriftBlock6Coeff6Row0Norm,kineticDriftBlock6Coeff6Row1Norm,kineticDriftBlock6Coeff6Row2Norm,kineticDriftBlock6Coeff6Row3Norm,kineticDriftBlock6Coeff6Row4Norm,kineticDriftBlock6Coeff7Row0Norm,kineticDriftBlock6Coeff7Row1Norm,kineticDriftBlock6Coeff7Row2Norm,kineticDriftBlock6Coeff7Row3Norm,kineticDriftBlock6Coeff7Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff7Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 7 4=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 7 4=kineticDriftCell h (kineticCof8*kineticBlock8) 7 4 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftCof8Row3,kineticDriftCof8Row4,kineticDriftCof8Row5,kineticDriftCof8Row6,kineticDriftCof8Row7,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2,kineticDriftBlock8Row3,kineticDriftBlock8Row4,kineticDriftBlock8Row5,kineticDriftBlock8Row6,kineticDriftBlock8Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff0Row4Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff1Row3Norm,kineticDriftCof8Coeff1Row4Norm,kineticDriftCof8Coeff2Row0Norm,kineticDriftCof8Coeff2Row1Norm,kineticDriftCof8Coeff2Row2Norm,kineticDriftCof8Coeff2Row3Norm,kineticDriftCof8Coeff2Row4Norm,kineticDriftCof8Coeff3Row0Norm,kineticDriftCof8Coeff3Row1Norm,kineticDriftCof8Coeff3Row2Norm,kineticDriftCof8Coeff3Row3Norm,kineticDriftCof8Coeff3Row4Norm,kineticDriftCof8Coeff4Row0Norm,kineticDriftCof8Coeff4Row1Norm,kineticDriftCof8Coeff4Row2Norm,kineticDriftCof8Coeff4Row3Norm,kineticDriftCof8Coeff4Row4Norm,kineticDriftCof8Coeff5Row0Norm,kineticDriftCof8Coeff5Row1Norm,kineticDriftCof8Coeff5Row2Norm,kineticDriftCof8Coeff5Row3Norm,kineticDriftCof8Coeff5Row4Norm,kineticDriftCof8Coeff6Row0Norm,kineticDriftCof8Coeff6Row1Norm,kineticDriftCof8Coeff6Row2Norm,kineticDriftCof8Coeff6Row3Norm,kineticDriftCof8Coeff6Row4Norm,kineticDriftCof8Coeff7Row0Norm,kineticDriftCof8Coeff7Row1Norm,kineticDriftCof8Coeff7Row2Norm,kineticDriftCof8Coeff7Row3Norm,kineticDriftCof8Coeff7Row4Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff0Row4Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff1Row3Norm,kineticDriftBlock8Coeff1Row4Norm,kineticDriftBlock8Coeff2Row0Norm,kineticDriftBlock8Coeff2Row1Norm,kineticDriftBlock8Coeff2Row2Norm,kineticDriftBlock8Coeff2Row3Norm,kineticDriftBlock8Coeff2Row4Norm,kineticDriftBlock8Coeff3Row0Norm,kineticDriftBlock8Coeff3Row1Norm,kineticDriftBlock8Coeff3Row2Norm,kineticDriftBlock8Coeff3Row3Norm,kineticDriftBlock8Coeff3Row4Norm,kineticDriftBlock8Coeff4Row0Norm,kineticDriftBlock8Coeff4Row1Norm,kineticDriftBlock8Coeff4Row2Norm,kineticDriftBlock8Coeff4Row3Norm,kineticDriftBlock8Coeff4Row4Norm,kineticDriftBlock8Coeff5Row0Norm,kineticDriftBlock8Coeff5Row1Norm,kineticDriftBlock8Coeff5Row2Norm,kineticDriftBlock8Coeff5Row3Norm,kineticDriftBlock8Coeff5Row4Norm,kineticDriftBlock8Coeff6Row0Norm,kineticDriftBlock8Coeff6Row1Norm,kineticDriftBlock8Coeff6Row2Norm,kineticDriftBlock8Coeff6Row3Norm,kineticDriftBlock8Coeff6Row4Norm,kineticDriftBlock8Coeff7Row0Norm,kineticDriftBlock8Coeff7Row1Norm,kineticDriftBlock8Coeff7Row2Norm,kineticDriftBlock8Coeff7Row3Norm,kineticDriftBlock8Coeff7Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff7Row4Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 7 4=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 7 4=kineticDriftCell h (kineticCof10*kineticBlock10) 7 4 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftCof10Row3,kineticDriftCof10Row4,kineticDriftCof10Row5,kineticDriftCof10Row6,kineticDriftCof10Row7,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2,kineticDriftBlock10Row3,kineticDriftBlock10Row4,kineticDriftBlock10Row5,kineticDriftBlock10Row6,kineticDriftBlock10Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff0Row4Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff1Row3Norm,kineticDriftCof10Coeff1Row4Norm,kineticDriftCof10Coeff2Row0Norm,kineticDriftCof10Coeff2Row1Norm,kineticDriftCof10Coeff2Row2Norm,kineticDriftCof10Coeff2Row3Norm,kineticDriftCof10Coeff2Row4Norm,kineticDriftCof10Coeff3Row0Norm,kineticDriftCof10Coeff3Row1Norm,kineticDriftCof10Coeff3Row2Norm,kineticDriftCof10Coeff3Row3Norm,kineticDriftCof10Coeff3Row4Norm,kineticDriftCof10Coeff4Row0Norm,kineticDriftCof10Coeff4Row1Norm,kineticDriftCof10Coeff4Row2Norm,kineticDriftCof10Coeff4Row3Norm,kineticDriftCof10Coeff4Row4Norm,kineticDriftCof10Coeff5Row0Norm,kineticDriftCof10Coeff5Row1Norm,kineticDriftCof10Coeff5Row2Norm,kineticDriftCof10Coeff5Row3Norm,kineticDriftCof10Coeff5Row4Norm,kineticDriftCof10Coeff6Row0Norm,kineticDriftCof10Coeff6Row1Norm,kineticDriftCof10Coeff6Row2Norm,kineticDriftCof10Coeff6Row3Norm,kineticDriftCof10Coeff6Row4Norm,kineticDriftCof10Coeff7Row0Norm,kineticDriftCof10Coeff7Row1Norm,kineticDriftCof10Coeff7Row2Norm,kineticDriftCof10Coeff7Row3Norm,kineticDriftCof10Coeff7Row4Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff0Row4Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff1Row3Norm,kineticDriftBlock10Coeff1Row4Norm,kineticDriftBlock10Coeff2Row0Norm,kineticDriftBlock10Coeff2Row1Norm,kineticDriftBlock10Coeff2Row2Norm,kineticDriftBlock10Coeff2Row3Norm,kineticDriftBlock10Coeff2Row4Norm,kineticDriftBlock10Coeff3Row0Norm,kineticDriftBlock10Coeff3Row1Norm,kineticDriftBlock10Coeff3Row2Norm,kineticDriftBlock10Coeff3Row3Norm,kineticDriftBlock10Coeff3Row4Norm,kineticDriftBlock10Coeff4Row0Norm,kineticDriftBlock10Coeff4Row1Norm,kineticDriftBlock10Coeff4Row2Norm,kineticDriftBlock10Coeff4Row3Norm,kineticDriftBlock10Coeff4Row4Norm,kineticDriftBlock10Coeff5Row0Norm,kineticDriftBlock10Coeff5Row1Norm,kineticDriftBlock10Coeff5Row2Norm,kineticDriftBlock10Coeff5Row3Norm,kineticDriftBlock10Coeff5Row4Norm,kineticDriftBlock10Coeff6Row0Norm,kineticDriftBlock10Coeff6Row1Norm,kineticDriftBlock10Coeff6Row2Norm,kineticDriftBlock10Coeff6Row3Norm,kineticDriftBlock10Coeff6Row4Norm,kineticDriftBlock10Coeff7Row0Norm,kineticDriftBlock10Coeff7Row1Norm,kineticDriftBlock10Coeff7Row2Norm,kineticDriftBlock10Coeff7Row3Norm,kineticDriftBlock10Coeff7Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff7Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 7 5=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 7 5=kineticDriftCell h (kineticCof2*kineticBlock2) 7 5 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftCof2Row3,kineticDriftCof2Row4,kineticDriftCof2Row5,kineticDriftCof2Row6,kineticDriftCof2Row7,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2,kineticDriftBlock2Row3]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm,kineticDriftCof2Coeff0Row4Norm,kineticDriftCof2Coeff0Row5Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff1Row3Norm,kineticDriftCof2Coeff1Row4Norm,kineticDriftCof2Coeff1Row5Norm,kineticDriftCof2Coeff2Row0Norm,kineticDriftCof2Coeff2Row1Norm,kineticDriftCof2Coeff2Row2Norm,kineticDriftCof2Coeff2Row3Norm,kineticDriftCof2Coeff2Row4Norm,kineticDriftCof2Coeff2Row5Norm,kineticDriftCof2Coeff3Row0Norm,kineticDriftCof2Coeff3Row1Norm,kineticDriftCof2Coeff3Row2Norm,kineticDriftCof2Coeff3Row3Norm,kineticDriftCof2Coeff3Row4Norm,kineticDriftCof2Coeff3Row5Norm,kineticDriftCof2Coeff4Row0Norm,kineticDriftCof2Coeff4Row1Norm,kineticDriftCof2Coeff4Row2Norm,kineticDriftCof2Coeff4Row3Norm,kineticDriftCof2Coeff4Row4Norm,kineticDriftCof2Coeff4Row5Norm,kineticDriftCof2Coeff5Row0Norm,kineticDriftCof2Coeff5Row1Norm,kineticDriftCof2Coeff5Row2Norm,kineticDriftCof2Coeff5Row3Norm,kineticDriftCof2Coeff5Row4Norm,kineticDriftCof2Coeff5Row5Norm,kineticDriftCof2Coeff6Row0Norm,kineticDriftCof2Coeff6Row1Norm,kineticDriftCof2Coeff6Row2Norm,kineticDriftCof2Coeff6Row3Norm,kineticDriftCof2Coeff6Row4Norm,kineticDriftCof2Coeff6Row5Norm,kineticDriftCof2Coeff7Row0Norm,kineticDriftCof2Coeff7Row1Norm,kineticDriftCof2Coeff7Row2Norm,kineticDriftCof2Coeff7Row3Norm,kineticDriftCof2Coeff7Row4Norm,kineticDriftCof2Coeff7Row5Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm,kineticDriftBlock2Coeff2Row0Norm,kineticDriftBlock2Coeff2Row1Norm,kineticDriftBlock2Coeff2Row2Norm,kineticDriftBlock2Coeff3Row0Norm,kineticDriftBlock2Coeff3Row1Norm,kineticDriftBlock2Coeff3Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff7Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 7 5=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 7 5=kineticDriftCell h (kineticCof4*kineticBlock4) 7 5 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftCof4Row3,kineticDriftCof4Row4,kineticDriftCof4Row5,kineticDriftCof4Row6,kineticDriftCof4Row7,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2,kineticDriftBlock4Row3,kineticDriftBlock4Row4,kineticDriftBlock4Row5]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff0Row4Norm,kineticDriftCof4Coeff0Row5Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff1Row3Norm,kineticDriftCof4Coeff1Row4Norm,kineticDriftCof4Coeff1Row5Norm,kineticDriftCof4Coeff2Row0Norm,kineticDriftCof4Coeff2Row1Norm,kineticDriftCof4Coeff2Row2Norm,kineticDriftCof4Coeff2Row3Norm,kineticDriftCof4Coeff2Row4Norm,kineticDriftCof4Coeff2Row5Norm,kineticDriftCof4Coeff3Row0Norm,kineticDriftCof4Coeff3Row1Norm,kineticDriftCof4Coeff3Row2Norm,kineticDriftCof4Coeff3Row3Norm,kineticDriftCof4Coeff3Row4Norm,kineticDriftCof4Coeff3Row5Norm,kineticDriftCof4Coeff4Row0Norm,kineticDriftCof4Coeff4Row1Norm,kineticDriftCof4Coeff4Row2Norm,kineticDriftCof4Coeff4Row3Norm,kineticDriftCof4Coeff4Row4Norm,kineticDriftCof4Coeff4Row5Norm,kineticDriftCof4Coeff5Row0Norm,kineticDriftCof4Coeff5Row1Norm,kineticDriftCof4Coeff5Row2Norm,kineticDriftCof4Coeff5Row3Norm,kineticDriftCof4Coeff5Row4Norm,kineticDriftCof4Coeff5Row5Norm,kineticDriftCof4Coeff6Row0Norm,kineticDriftCof4Coeff6Row1Norm,kineticDriftCof4Coeff6Row2Norm,kineticDriftCof4Coeff6Row3Norm,kineticDriftCof4Coeff6Row4Norm,kineticDriftCof4Coeff6Row5Norm,kineticDriftCof4Coeff7Row0Norm,kineticDriftCof4Coeff7Row1Norm,kineticDriftCof4Coeff7Row2Norm,kineticDriftCof4Coeff7Row3Norm,kineticDriftCof4Coeff7Row4Norm,kineticDriftCof4Coeff7Row5Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff1Row3Norm,kineticDriftBlock4Coeff2Row0Norm,kineticDriftBlock4Coeff2Row1Norm,kineticDriftBlock4Coeff2Row2Norm,kineticDriftBlock4Coeff2Row3Norm,kineticDriftBlock4Coeff3Row0Norm,kineticDriftBlock4Coeff3Row1Norm,kineticDriftBlock4Coeff3Row2Norm,kineticDriftBlock4Coeff3Row3Norm,kineticDriftBlock4Coeff4Row0Norm,kineticDriftBlock4Coeff4Row1Norm,kineticDriftBlock4Coeff4Row2Norm,kineticDriftBlock4Coeff4Row3Norm,kineticDriftBlock4Coeff5Row0Norm,kineticDriftBlock4Coeff5Row1Norm,kineticDriftBlock4Coeff5Row2Norm,kineticDriftBlock4Coeff5Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff7Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 7 5=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 7 5=kineticDriftCell h (kineticCof6*kineticBlock6) 7 5 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftCof6Row3,kineticDriftCof6Row4,kineticDriftCof6Row5,kineticDriftCof6Row6,kineticDriftCof6Row7,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2,kineticDriftBlock6Row3,kineticDriftBlock6Row4,kineticDriftBlock6Row5,kineticDriftBlock6Row6,kineticDriftBlock6Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff0Row4Norm,kineticDriftCof6Coeff0Row5Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff1Row3Norm,kineticDriftCof6Coeff1Row4Norm,kineticDriftCof6Coeff1Row5Norm,kineticDriftCof6Coeff2Row0Norm,kineticDriftCof6Coeff2Row1Norm,kineticDriftCof6Coeff2Row2Norm,kineticDriftCof6Coeff2Row3Norm,kineticDriftCof6Coeff2Row4Norm,kineticDriftCof6Coeff2Row5Norm,kineticDriftCof6Coeff3Row0Norm,kineticDriftCof6Coeff3Row1Norm,kineticDriftCof6Coeff3Row2Norm,kineticDriftCof6Coeff3Row3Norm,kineticDriftCof6Coeff3Row4Norm,kineticDriftCof6Coeff3Row5Norm,kineticDriftCof6Coeff4Row0Norm,kineticDriftCof6Coeff4Row1Norm,kineticDriftCof6Coeff4Row2Norm,kineticDriftCof6Coeff4Row3Norm,kineticDriftCof6Coeff4Row4Norm,kineticDriftCof6Coeff4Row5Norm,kineticDriftCof6Coeff5Row0Norm,kineticDriftCof6Coeff5Row1Norm,kineticDriftCof6Coeff5Row2Norm,kineticDriftCof6Coeff5Row3Norm,kineticDriftCof6Coeff5Row4Norm,kineticDriftCof6Coeff5Row5Norm,kineticDriftCof6Coeff6Row0Norm,kineticDriftCof6Coeff6Row1Norm,kineticDriftCof6Coeff6Row2Norm,kineticDriftCof6Coeff6Row3Norm,kineticDriftCof6Coeff6Row4Norm,kineticDriftCof6Coeff6Row5Norm,kineticDriftCof6Coeff7Row0Norm,kineticDriftCof6Coeff7Row1Norm,kineticDriftCof6Coeff7Row2Norm,kineticDriftCof6Coeff7Row3Norm,kineticDriftCof6Coeff7Row4Norm,kineticDriftCof6Coeff7Row5Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff0Row4Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff1Row3Norm,kineticDriftBlock6Coeff1Row4Norm,kineticDriftBlock6Coeff2Row0Norm,kineticDriftBlock6Coeff2Row1Norm,kineticDriftBlock6Coeff2Row2Norm,kineticDriftBlock6Coeff2Row3Norm,kineticDriftBlock6Coeff2Row4Norm,kineticDriftBlock6Coeff3Row0Norm,kineticDriftBlock6Coeff3Row1Norm,kineticDriftBlock6Coeff3Row2Norm,kineticDriftBlock6Coeff3Row3Norm,kineticDriftBlock6Coeff3Row4Norm,kineticDriftBlock6Coeff4Row0Norm,kineticDriftBlock6Coeff4Row1Norm,kineticDriftBlock6Coeff4Row2Norm,kineticDriftBlock6Coeff4Row3Norm,kineticDriftBlock6Coeff4Row4Norm,kineticDriftBlock6Coeff5Row0Norm,kineticDriftBlock6Coeff5Row1Norm,kineticDriftBlock6Coeff5Row2Norm,kineticDriftBlock6Coeff5Row3Norm,kineticDriftBlock6Coeff5Row4Norm,kineticDriftBlock6Coeff6Row0Norm,kineticDriftBlock6Coeff6Row1Norm,kineticDriftBlock6Coeff6Row2Norm,kineticDriftBlock6Coeff6Row3Norm,kineticDriftBlock6Coeff6Row4Norm,kineticDriftBlock6Coeff7Row0Norm,kineticDriftBlock6Coeff7Row1Norm,kineticDriftBlock6Coeff7Row2Norm,kineticDriftBlock6Coeff7Row3Norm,kineticDriftBlock6Coeff7Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff7Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 7 5=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 7 5=kineticDriftCell h (kineticCof8*kineticBlock8) 7 5 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftCof8Row3,kineticDriftCof8Row4,kineticDriftCof8Row5,kineticDriftCof8Row6,kineticDriftCof8Row7,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2,kineticDriftBlock8Row3,kineticDriftBlock8Row4,kineticDriftBlock8Row5,kineticDriftBlock8Row6,kineticDriftBlock8Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff0Row4Norm,kineticDriftCof8Coeff0Row5Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff1Row3Norm,kineticDriftCof8Coeff1Row4Norm,kineticDriftCof8Coeff1Row5Norm,kineticDriftCof8Coeff2Row0Norm,kineticDriftCof8Coeff2Row1Norm,kineticDriftCof8Coeff2Row2Norm,kineticDriftCof8Coeff2Row3Norm,kineticDriftCof8Coeff2Row4Norm,kineticDriftCof8Coeff2Row5Norm,kineticDriftCof8Coeff3Row0Norm,kineticDriftCof8Coeff3Row1Norm,kineticDriftCof8Coeff3Row2Norm,kineticDriftCof8Coeff3Row3Norm,kineticDriftCof8Coeff3Row4Norm,kineticDriftCof8Coeff3Row5Norm,kineticDriftCof8Coeff4Row0Norm,kineticDriftCof8Coeff4Row1Norm,kineticDriftCof8Coeff4Row2Norm,kineticDriftCof8Coeff4Row3Norm,kineticDriftCof8Coeff4Row4Norm,kineticDriftCof8Coeff4Row5Norm,kineticDriftCof8Coeff5Row0Norm,kineticDriftCof8Coeff5Row1Norm,kineticDriftCof8Coeff5Row2Norm,kineticDriftCof8Coeff5Row3Norm,kineticDriftCof8Coeff5Row4Norm,kineticDriftCof8Coeff5Row5Norm,kineticDriftCof8Coeff6Row0Norm,kineticDriftCof8Coeff6Row1Norm,kineticDriftCof8Coeff6Row2Norm,kineticDriftCof8Coeff6Row3Norm,kineticDriftCof8Coeff6Row4Norm,kineticDriftCof8Coeff6Row5Norm,kineticDriftCof8Coeff7Row0Norm,kineticDriftCof8Coeff7Row1Norm,kineticDriftCof8Coeff7Row2Norm,kineticDriftCof8Coeff7Row3Norm,kineticDriftCof8Coeff7Row4Norm,kineticDriftCof8Coeff7Row5Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff0Row4Norm,kineticDriftBlock8Coeff0Row5Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff1Row3Norm,kineticDriftBlock8Coeff1Row4Norm,kineticDriftBlock8Coeff1Row5Norm,kineticDriftBlock8Coeff2Row0Norm,kineticDriftBlock8Coeff2Row1Norm,kineticDriftBlock8Coeff2Row2Norm,kineticDriftBlock8Coeff2Row3Norm,kineticDriftBlock8Coeff2Row4Norm,kineticDriftBlock8Coeff2Row5Norm,kineticDriftBlock8Coeff3Row0Norm,kineticDriftBlock8Coeff3Row1Norm,kineticDriftBlock8Coeff3Row2Norm,kineticDriftBlock8Coeff3Row3Norm,kineticDriftBlock8Coeff3Row4Norm,kineticDriftBlock8Coeff3Row5Norm,kineticDriftBlock8Coeff4Row0Norm,kineticDriftBlock8Coeff4Row1Norm,kineticDriftBlock8Coeff4Row2Norm,kineticDriftBlock8Coeff4Row3Norm,kineticDriftBlock8Coeff4Row4Norm,kineticDriftBlock8Coeff4Row5Norm,kineticDriftBlock8Coeff5Row0Norm,kineticDriftBlock8Coeff5Row1Norm,kineticDriftBlock8Coeff5Row2Norm,kineticDriftBlock8Coeff5Row3Norm,kineticDriftBlock8Coeff5Row4Norm,kineticDriftBlock8Coeff5Row5Norm,kineticDriftBlock8Coeff6Row0Norm,kineticDriftBlock8Coeff6Row1Norm,kineticDriftBlock8Coeff6Row2Norm,kineticDriftBlock8Coeff6Row3Norm,kineticDriftBlock8Coeff6Row4Norm,kineticDriftBlock8Coeff6Row5Norm,kineticDriftBlock8Coeff7Row0Norm,kineticDriftBlock8Coeff7Row1Norm,kineticDriftBlock8Coeff7Row2Norm,kineticDriftBlock8Coeff7Row3Norm,kineticDriftBlock8Coeff7Row4Norm,kineticDriftBlock8Coeff7Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff7Row5Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 7 5=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 7 5=kineticDriftCell h (kineticCof10*kineticBlock10) 7 5 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftCof10Row3,kineticDriftCof10Row4,kineticDriftCof10Row5,kineticDriftCof10Row6,kineticDriftCof10Row7,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2,kineticDriftBlock10Row3,kineticDriftBlock10Row4,kineticDriftBlock10Row5,kineticDriftBlock10Row6,kineticDriftBlock10Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff0Row4Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff1Row3Norm,kineticDriftCof10Coeff1Row4Norm,kineticDriftCof10Coeff2Row0Norm,kineticDriftCof10Coeff2Row1Norm,kineticDriftCof10Coeff2Row2Norm,kineticDriftCof10Coeff2Row3Norm,kineticDriftCof10Coeff2Row4Norm,kineticDriftCof10Coeff3Row0Norm,kineticDriftCof10Coeff3Row1Norm,kineticDriftCof10Coeff3Row2Norm,kineticDriftCof10Coeff3Row3Norm,kineticDriftCof10Coeff3Row4Norm,kineticDriftCof10Coeff4Row0Norm,kineticDriftCof10Coeff4Row1Norm,kineticDriftCof10Coeff4Row2Norm,kineticDriftCof10Coeff4Row3Norm,kineticDriftCof10Coeff4Row4Norm,kineticDriftCof10Coeff5Row0Norm,kineticDriftCof10Coeff5Row1Norm,kineticDriftCof10Coeff5Row2Norm,kineticDriftCof10Coeff5Row3Norm,kineticDriftCof10Coeff5Row4Norm,kineticDriftCof10Coeff6Row0Norm,kineticDriftCof10Coeff6Row1Norm,kineticDriftCof10Coeff6Row2Norm,kineticDriftCof10Coeff6Row3Norm,kineticDriftCof10Coeff6Row4Norm,kineticDriftCof10Coeff7Row0Norm,kineticDriftCof10Coeff7Row1Norm,kineticDriftCof10Coeff7Row2Norm,kineticDriftCof10Coeff7Row3Norm,kineticDriftCof10Coeff7Row4Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff0Row4Norm,kineticDriftBlock10Coeff0Row5Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff1Row3Norm,kineticDriftBlock10Coeff1Row4Norm,kineticDriftBlock10Coeff1Row5Norm,kineticDriftBlock10Coeff2Row0Norm,kineticDriftBlock10Coeff2Row1Norm,kineticDriftBlock10Coeff2Row2Norm,kineticDriftBlock10Coeff2Row3Norm,kineticDriftBlock10Coeff2Row4Norm,kineticDriftBlock10Coeff2Row5Norm,kineticDriftBlock10Coeff3Row0Norm,kineticDriftBlock10Coeff3Row1Norm,kineticDriftBlock10Coeff3Row2Norm,kineticDriftBlock10Coeff3Row3Norm,kineticDriftBlock10Coeff3Row4Norm,kineticDriftBlock10Coeff3Row5Norm,kineticDriftBlock10Coeff4Row0Norm,kineticDriftBlock10Coeff4Row1Norm,kineticDriftBlock10Coeff4Row2Norm,kineticDriftBlock10Coeff4Row3Norm,kineticDriftBlock10Coeff4Row4Norm,kineticDriftBlock10Coeff4Row5Norm,kineticDriftBlock10Coeff5Row0Norm,kineticDriftBlock10Coeff5Row1Norm,kineticDriftBlock10Coeff5Row2Norm,kineticDriftBlock10Coeff5Row3Norm,kineticDriftBlock10Coeff5Row4Norm,kineticDriftBlock10Coeff5Row5Norm,kineticDriftBlock10Coeff6Row0Norm,kineticDriftBlock10Coeff6Row1Norm,kineticDriftBlock10Coeff6Row2Norm,kineticDriftBlock10Coeff6Row3Norm,kineticDriftBlock10Coeff6Row4Norm,kineticDriftBlock10Coeff6Row5Norm,kineticDriftBlock10Coeff7Row0Norm,kineticDriftBlock10Coeff7Row1Norm,kineticDriftBlock10Coeff7Row2Norm,kineticDriftBlock10Coeff7Row3Norm,kineticDriftBlock10Coeff7Row4Norm,kineticDriftBlock10Coeff7Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff7Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 7 6=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 7 6=kineticDriftCell h (kineticCof2*kineticBlock2) 7 6 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftCof2Row3,kineticDriftCof2Row4,kineticDriftCof2Row5,kineticDriftCof2Row6,kineticDriftCof2Row7,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2,kineticDriftBlock2Row3]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm,kineticDriftCof2Coeff0Row4Norm,kineticDriftCof2Coeff0Row5Norm,kineticDriftCof2Coeff0Row6Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff1Row3Norm,kineticDriftCof2Coeff1Row4Norm,kineticDriftCof2Coeff1Row5Norm,kineticDriftCof2Coeff1Row6Norm,kineticDriftCof2Coeff2Row0Norm,kineticDriftCof2Coeff2Row1Norm,kineticDriftCof2Coeff2Row2Norm,kineticDriftCof2Coeff2Row3Norm,kineticDriftCof2Coeff2Row4Norm,kineticDriftCof2Coeff2Row5Norm,kineticDriftCof2Coeff2Row6Norm,kineticDriftCof2Coeff3Row0Norm,kineticDriftCof2Coeff3Row1Norm,kineticDriftCof2Coeff3Row2Norm,kineticDriftCof2Coeff3Row3Norm,kineticDriftCof2Coeff3Row4Norm,kineticDriftCof2Coeff3Row5Norm,kineticDriftCof2Coeff3Row6Norm,kineticDriftCof2Coeff4Row0Norm,kineticDriftCof2Coeff4Row1Norm,kineticDriftCof2Coeff4Row2Norm,kineticDriftCof2Coeff4Row3Norm,kineticDriftCof2Coeff4Row4Norm,kineticDriftCof2Coeff4Row5Norm,kineticDriftCof2Coeff4Row6Norm,kineticDriftCof2Coeff5Row0Norm,kineticDriftCof2Coeff5Row1Norm,kineticDriftCof2Coeff5Row2Norm,kineticDriftCof2Coeff5Row3Norm,kineticDriftCof2Coeff5Row4Norm,kineticDriftCof2Coeff5Row5Norm,kineticDriftCof2Coeff5Row6Norm,kineticDriftCof2Coeff6Row0Norm,kineticDriftCof2Coeff6Row1Norm,kineticDriftCof2Coeff6Row2Norm,kineticDriftCof2Coeff6Row3Norm,kineticDriftCof2Coeff6Row4Norm,kineticDriftCof2Coeff6Row5Norm,kineticDriftCof2Coeff6Row6Norm,kineticDriftCof2Coeff7Row0Norm,kineticDriftCof2Coeff7Row1Norm,kineticDriftCof2Coeff7Row2Norm,kineticDriftCof2Coeff7Row3Norm,kineticDriftCof2Coeff7Row4Norm,kineticDriftCof2Coeff7Row5Norm,kineticDriftCof2Coeff7Row6Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm,kineticDriftBlock2Coeff2Row0Norm,kineticDriftBlock2Coeff2Row1Norm,kineticDriftBlock2Coeff2Row2Norm,kineticDriftBlock2Coeff3Row0Norm,kineticDriftBlock2Coeff3Row1Norm,kineticDriftBlock2Coeff3Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff7Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 7 6=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 7 6=kineticDriftCell h (kineticCof4*kineticBlock4) 7 6 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftCof4Row3,kineticDriftCof4Row4,kineticDriftCof4Row5,kineticDriftCof4Row6,kineticDriftCof4Row7,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2,kineticDriftBlock4Row3,kineticDriftBlock4Row4,kineticDriftBlock4Row5]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff0Row4Norm,kineticDriftCof4Coeff0Row5Norm,kineticDriftCof4Coeff0Row6Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff1Row3Norm,kineticDriftCof4Coeff1Row4Norm,kineticDriftCof4Coeff1Row5Norm,kineticDriftCof4Coeff1Row6Norm,kineticDriftCof4Coeff2Row0Norm,kineticDriftCof4Coeff2Row1Norm,kineticDriftCof4Coeff2Row2Norm,kineticDriftCof4Coeff2Row3Norm,kineticDriftCof4Coeff2Row4Norm,kineticDriftCof4Coeff2Row5Norm,kineticDriftCof4Coeff2Row6Norm,kineticDriftCof4Coeff3Row0Norm,kineticDriftCof4Coeff3Row1Norm,kineticDriftCof4Coeff3Row2Norm,kineticDriftCof4Coeff3Row3Norm,kineticDriftCof4Coeff3Row4Norm,kineticDriftCof4Coeff3Row5Norm,kineticDriftCof4Coeff3Row6Norm,kineticDriftCof4Coeff4Row0Norm,kineticDriftCof4Coeff4Row1Norm,kineticDriftCof4Coeff4Row2Norm,kineticDriftCof4Coeff4Row3Norm,kineticDriftCof4Coeff4Row4Norm,kineticDriftCof4Coeff4Row5Norm,kineticDriftCof4Coeff4Row6Norm,kineticDriftCof4Coeff5Row0Norm,kineticDriftCof4Coeff5Row1Norm,kineticDriftCof4Coeff5Row2Norm,kineticDriftCof4Coeff5Row3Norm,kineticDriftCof4Coeff5Row4Norm,kineticDriftCof4Coeff5Row5Norm,kineticDriftCof4Coeff5Row6Norm,kineticDriftCof4Coeff6Row0Norm,kineticDriftCof4Coeff6Row1Norm,kineticDriftCof4Coeff6Row2Norm,kineticDriftCof4Coeff6Row3Norm,kineticDriftCof4Coeff6Row4Norm,kineticDriftCof4Coeff6Row5Norm,kineticDriftCof4Coeff6Row6Norm,kineticDriftCof4Coeff7Row0Norm,kineticDriftCof4Coeff7Row1Norm,kineticDriftCof4Coeff7Row2Norm,kineticDriftCof4Coeff7Row3Norm,kineticDriftCof4Coeff7Row4Norm,kineticDriftCof4Coeff7Row5Norm,kineticDriftCof4Coeff7Row6Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff1Row3Norm,kineticDriftBlock4Coeff2Row0Norm,kineticDriftBlock4Coeff2Row1Norm,kineticDriftBlock4Coeff2Row2Norm,kineticDriftBlock4Coeff2Row3Norm,kineticDriftBlock4Coeff3Row0Norm,kineticDriftBlock4Coeff3Row1Norm,kineticDriftBlock4Coeff3Row2Norm,kineticDriftBlock4Coeff3Row3Norm,kineticDriftBlock4Coeff4Row0Norm,kineticDriftBlock4Coeff4Row1Norm,kineticDriftBlock4Coeff4Row2Norm,kineticDriftBlock4Coeff4Row3Norm,kineticDriftBlock4Coeff5Row0Norm,kineticDriftBlock4Coeff5Row1Norm,kineticDriftBlock4Coeff5Row2Norm,kineticDriftBlock4Coeff5Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff7Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 7 6=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 7 6=kineticDriftCell h (kineticCof6*kineticBlock6) 7 6 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftCof6Row3,kineticDriftCof6Row4,kineticDriftCof6Row5,kineticDriftCof6Row6,kineticDriftCof6Row7,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2,kineticDriftBlock6Row3,kineticDriftBlock6Row4,kineticDriftBlock6Row5,kineticDriftBlock6Row6,kineticDriftBlock6Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff0Row4Norm,kineticDriftCof6Coeff0Row5Norm,kineticDriftCof6Coeff0Row6Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff1Row3Norm,kineticDriftCof6Coeff1Row4Norm,kineticDriftCof6Coeff1Row5Norm,kineticDriftCof6Coeff1Row6Norm,kineticDriftCof6Coeff2Row0Norm,kineticDriftCof6Coeff2Row1Norm,kineticDriftCof6Coeff2Row2Norm,kineticDriftCof6Coeff2Row3Norm,kineticDriftCof6Coeff2Row4Norm,kineticDriftCof6Coeff2Row5Norm,kineticDriftCof6Coeff2Row6Norm,kineticDriftCof6Coeff3Row0Norm,kineticDriftCof6Coeff3Row1Norm,kineticDriftCof6Coeff3Row2Norm,kineticDriftCof6Coeff3Row3Norm,kineticDriftCof6Coeff3Row4Norm,kineticDriftCof6Coeff3Row5Norm,kineticDriftCof6Coeff3Row6Norm,kineticDriftCof6Coeff4Row0Norm,kineticDriftCof6Coeff4Row1Norm,kineticDriftCof6Coeff4Row2Norm,kineticDriftCof6Coeff4Row3Norm,kineticDriftCof6Coeff4Row4Norm,kineticDriftCof6Coeff4Row5Norm,kineticDriftCof6Coeff4Row6Norm,kineticDriftCof6Coeff5Row0Norm,kineticDriftCof6Coeff5Row1Norm,kineticDriftCof6Coeff5Row2Norm,kineticDriftCof6Coeff5Row3Norm,kineticDriftCof6Coeff5Row4Norm,kineticDriftCof6Coeff5Row5Norm,kineticDriftCof6Coeff5Row6Norm,kineticDriftCof6Coeff6Row0Norm,kineticDriftCof6Coeff6Row1Norm,kineticDriftCof6Coeff6Row2Norm,kineticDriftCof6Coeff6Row3Norm,kineticDriftCof6Coeff6Row4Norm,kineticDriftCof6Coeff6Row5Norm,kineticDriftCof6Coeff6Row6Norm,kineticDriftCof6Coeff7Row0Norm,kineticDriftCof6Coeff7Row1Norm,kineticDriftCof6Coeff7Row2Norm,kineticDriftCof6Coeff7Row3Norm,kineticDriftCof6Coeff7Row4Norm,kineticDriftCof6Coeff7Row5Norm,kineticDriftCof6Coeff7Row6Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff0Row4Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff1Row3Norm,kineticDriftBlock6Coeff1Row4Norm,kineticDriftBlock6Coeff2Row0Norm,kineticDriftBlock6Coeff2Row1Norm,kineticDriftBlock6Coeff2Row2Norm,kineticDriftBlock6Coeff2Row3Norm,kineticDriftBlock6Coeff2Row4Norm,kineticDriftBlock6Coeff3Row0Norm,kineticDriftBlock6Coeff3Row1Norm,kineticDriftBlock6Coeff3Row2Norm,kineticDriftBlock6Coeff3Row3Norm,kineticDriftBlock6Coeff3Row4Norm,kineticDriftBlock6Coeff4Row0Norm,kineticDriftBlock6Coeff4Row1Norm,kineticDriftBlock6Coeff4Row2Norm,kineticDriftBlock6Coeff4Row3Norm,kineticDriftBlock6Coeff4Row4Norm,kineticDriftBlock6Coeff5Row0Norm,kineticDriftBlock6Coeff5Row1Norm,kineticDriftBlock6Coeff5Row2Norm,kineticDriftBlock6Coeff5Row3Norm,kineticDriftBlock6Coeff5Row4Norm,kineticDriftBlock6Coeff6Row0Norm,kineticDriftBlock6Coeff6Row1Norm,kineticDriftBlock6Coeff6Row2Norm,kineticDriftBlock6Coeff6Row3Norm,kineticDriftBlock6Coeff6Row4Norm,kineticDriftBlock6Coeff7Row0Norm,kineticDriftBlock6Coeff7Row1Norm,kineticDriftBlock6Coeff7Row2Norm,kineticDriftBlock6Coeff7Row3Norm,kineticDriftBlock6Coeff7Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff7Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 7 6=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 7 6=kineticDriftCell h (kineticCof8*kineticBlock8) 7 6 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftCof8Row3,kineticDriftCof8Row4,kineticDriftCof8Row5,kineticDriftCof8Row6,kineticDriftCof8Row7,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2,kineticDriftBlock8Row3,kineticDriftBlock8Row4,kineticDriftBlock8Row5,kineticDriftBlock8Row6,kineticDriftBlock8Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff0Row4Norm,kineticDriftCof8Coeff0Row5Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff1Row3Norm,kineticDriftCof8Coeff1Row4Norm,kineticDriftCof8Coeff1Row5Norm,kineticDriftCof8Coeff2Row0Norm,kineticDriftCof8Coeff2Row1Norm,kineticDriftCof8Coeff2Row2Norm,kineticDriftCof8Coeff2Row3Norm,kineticDriftCof8Coeff2Row4Norm,kineticDriftCof8Coeff2Row5Norm,kineticDriftCof8Coeff3Row0Norm,kineticDriftCof8Coeff3Row1Norm,kineticDriftCof8Coeff3Row2Norm,kineticDriftCof8Coeff3Row3Norm,kineticDriftCof8Coeff3Row4Norm,kineticDriftCof8Coeff3Row5Norm,kineticDriftCof8Coeff4Row0Norm,kineticDriftCof8Coeff4Row1Norm,kineticDriftCof8Coeff4Row2Norm,kineticDriftCof8Coeff4Row3Norm,kineticDriftCof8Coeff4Row4Norm,kineticDriftCof8Coeff4Row5Norm,kineticDriftCof8Coeff5Row0Norm,kineticDriftCof8Coeff5Row1Norm,kineticDriftCof8Coeff5Row2Norm,kineticDriftCof8Coeff5Row3Norm,kineticDriftCof8Coeff5Row4Norm,kineticDriftCof8Coeff5Row5Norm,kineticDriftCof8Coeff6Row0Norm,kineticDriftCof8Coeff6Row1Norm,kineticDriftCof8Coeff6Row2Norm,kineticDriftCof8Coeff6Row3Norm,kineticDriftCof8Coeff6Row4Norm,kineticDriftCof8Coeff6Row5Norm,kineticDriftCof8Coeff7Row0Norm,kineticDriftCof8Coeff7Row1Norm,kineticDriftCof8Coeff7Row2Norm,kineticDriftCof8Coeff7Row3Norm,kineticDriftCof8Coeff7Row4Norm,kineticDriftCof8Coeff7Row5Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff0Row4Norm,kineticDriftBlock8Coeff0Row5Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff1Row3Norm,kineticDriftBlock8Coeff1Row4Norm,kineticDriftBlock8Coeff1Row5Norm,kineticDriftBlock8Coeff2Row0Norm,kineticDriftBlock8Coeff2Row1Norm,kineticDriftBlock8Coeff2Row2Norm,kineticDriftBlock8Coeff2Row3Norm,kineticDriftBlock8Coeff2Row4Norm,kineticDriftBlock8Coeff2Row5Norm,kineticDriftBlock8Coeff3Row0Norm,kineticDriftBlock8Coeff3Row1Norm,kineticDriftBlock8Coeff3Row2Norm,kineticDriftBlock8Coeff3Row3Norm,kineticDriftBlock8Coeff3Row4Norm,kineticDriftBlock8Coeff3Row5Norm,kineticDriftBlock8Coeff4Row0Norm,kineticDriftBlock8Coeff4Row1Norm,kineticDriftBlock8Coeff4Row2Norm,kineticDriftBlock8Coeff4Row3Norm,kineticDriftBlock8Coeff4Row4Norm,kineticDriftBlock8Coeff4Row5Norm,kineticDriftBlock8Coeff5Row0Norm,kineticDriftBlock8Coeff5Row1Norm,kineticDriftBlock8Coeff5Row2Norm,kineticDriftBlock8Coeff5Row3Norm,kineticDriftBlock8Coeff5Row4Norm,kineticDriftBlock8Coeff5Row5Norm,kineticDriftBlock8Coeff6Row0Norm,kineticDriftBlock8Coeff6Row1Norm,kineticDriftBlock8Coeff6Row2Norm,kineticDriftBlock8Coeff6Row3Norm,kineticDriftBlock8Coeff6Row4Norm,kineticDriftBlock8Coeff6Row5Norm,kineticDriftBlock8Coeff7Row0Norm,kineticDriftBlock8Coeff7Row1Norm,kineticDriftBlock8Coeff7Row2Norm,kineticDriftBlock8Coeff7Row3Norm,kineticDriftBlock8Coeff7Row4Norm,kineticDriftBlock8Coeff7Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff7Row6Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 7 6=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 7 6=kineticDriftCell h (kineticCof10*kineticBlock10) 7 6 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftCof10Row3,kineticDriftCof10Row4,kineticDriftCof10Row5,kineticDriftCof10Row6,kineticDriftCof10Row7,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2,kineticDriftBlock10Row3,kineticDriftBlock10Row4,kineticDriftBlock10Row5,kineticDriftBlock10Row6,kineticDriftBlock10Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff0Row4Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff1Row3Norm,kineticDriftCof10Coeff1Row4Norm,kineticDriftCof10Coeff2Row0Norm,kineticDriftCof10Coeff2Row1Norm,kineticDriftCof10Coeff2Row2Norm,kineticDriftCof10Coeff2Row3Norm,kineticDriftCof10Coeff2Row4Norm,kineticDriftCof10Coeff3Row0Norm,kineticDriftCof10Coeff3Row1Norm,kineticDriftCof10Coeff3Row2Norm,kineticDriftCof10Coeff3Row3Norm,kineticDriftCof10Coeff3Row4Norm,kineticDriftCof10Coeff4Row0Norm,kineticDriftCof10Coeff4Row1Norm,kineticDriftCof10Coeff4Row2Norm,kineticDriftCof10Coeff4Row3Norm,kineticDriftCof10Coeff4Row4Norm,kineticDriftCof10Coeff5Row0Norm,kineticDriftCof10Coeff5Row1Norm,kineticDriftCof10Coeff5Row2Norm,kineticDriftCof10Coeff5Row3Norm,kineticDriftCof10Coeff5Row4Norm,kineticDriftCof10Coeff6Row0Norm,kineticDriftCof10Coeff6Row1Norm,kineticDriftCof10Coeff6Row2Norm,kineticDriftCof10Coeff6Row3Norm,kineticDriftCof10Coeff6Row4Norm,kineticDriftCof10Coeff7Row0Norm,kineticDriftCof10Coeff7Row1Norm,kineticDriftCof10Coeff7Row2Norm,kineticDriftCof10Coeff7Row3Norm,kineticDriftCof10Coeff7Row4Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff0Row4Norm,kineticDriftBlock10Coeff0Row5Norm,kineticDriftBlock10Coeff0Row6Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff1Row3Norm,kineticDriftBlock10Coeff1Row4Norm,kineticDriftBlock10Coeff1Row5Norm,kineticDriftBlock10Coeff1Row6Norm,kineticDriftBlock10Coeff2Row0Norm,kineticDriftBlock10Coeff2Row1Norm,kineticDriftBlock10Coeff2Row2Norm,kineticDriftBlock10Coeff2Row3Norm,kineticDriftBlock10Coeff2Row4Norm,kineticDriftBlock10Coeff2Row5Norm,kineticDriftBlock10Coeff2Row6Norm,kineticDriftBlock10Coeff3Row0Norm,kineticDriftBlock10Coeff3Row1Norm,kineticDriftBlock10Coeff3Row2Norm,kineticDriftBlock10Coeff3Row3Norm,kineticDriftBlock10Coeff3Row4Norm,kineticDriftBlock10Coeff3Row5Norm,kineticDriftBlock10Coeff3Row6Norm,kineticDriftBlock10Coeff4Row0Norm,kineticDriftBlock10Coeff4Row1Norm,kineticDriftBlock10Coeff4Row2Norm,kineticDriftBlock10Coeff4Row3Norm,kineticDriftBlock10Coeff4Row4Norm,kineticDriftBlock10Coeff4Row5Norm,kineticDriftBlock10Coeff4Row6Norm,kineticDriftBlock10Coeff5Row0Norm,kineticDriftBlock10Coeff5Row1Norm,kineticDriftBlock10Coeff5Row2Norm,kineticDriftBlock10Coeff5Row3Norm,kineticDriftBlock10Coeff5Row4Norm,kineticDriftBlock10Coeff5Row5Norm,kineticDriftBlock10Coeff5Row6Norm,kineticDriftBlock10Coeff6Row0Norm,kineticDriftBlock10Coeff6Row1Norm,kineticDriftBlock10Coeff6Row2Norm,kineticDriftBlock10Coeff6Row3Norm,kineticDriftBlock10Coeff6Row4Norm,kineticDriftBlock10Coeff6Row5Norm,kineticDriftBlock10Coeff6Row6Norm,kineticDriftBlock10Coeff7Row0Norm,kineticDriftBlock10Coeff7Row1Norm,kineticDriftBlock10Coeff7Row2Norm,kineticDriftBlock10Coeff7Row3Norm,kineticDriftBlock10Coeff7Row4Norm,kineticDriftBlock10Coeff7Row5Norm,kineticDriftBlock10Coeff7Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff7Row7Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 7 7=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 7 7=kineticDriftCell h (kineticCof2*kineticBlock2) 7 7 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftCof2Row3,kineticDriftCof2Row4,kineticDriftCof2Row5,kineticDriftCof2Row6,kineticDriftCof2Row7,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2,kineticDriftBlock2Row3]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm,kineticDriftCof2Coeff0Row4Norm,kineticDriftCof2Coeff0Row5Norm,kineticDriftCof2Coeff0Row6Norm,kineticDriftCof2Coeff0Row7Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff1Row3Norm,kineticDriftCof2Coeff1Row4Norm,kineticDriftCof2Coeff1Row5Norm,kineticDriftCof2Coeff1Row6Norm,kineticDriftCof2Coeff1Row7Norm,kineticDriftCof2Coeff2Row0Norm,kineticDriftCof2Coeff2Row1Norm,kineticDriftCof2Coeff2Row2Norm,kineticDriftCof2Coeff2Row3Norm,kineticDriftCof2Coeff2Row4Norm,kineticDriftCof2Coeff2Row5Norm,kineticDriftCof2Coeff2Row6Norm,kineticDriftCof2Coeff2Row7Norm,kineticDriftCof2Coeff3Row0Norm,kineticDriftCof2Coeff3Row1Norm,kineticDriftCof2Coeff3Row2Norm,kineticDriftCof2Coeff3Row3Norm,kineticDriftCof2Coeff3Row4Norm,kineticDriftCof2Coeff3Row5Norm,kineticDriftCof2Coeff3Row6Norm,kineticDriftCof2Coeff3Row7Norm,kineticDriftCof2Coeff4Row0Norm,kineticDriftCof2Coeff4Row1Norm,kineticDriftCof2Coeff4Row2Norm,kineticDriftCof2Coeff4Row3Norm,kineticDriftCof2Coeff4Row4Norm,kineticDriftCof2Coeff4Row5Norm,kineticDriftCof2Coeff4Row6Norm,kineticDriftCof2Coeff4Row7Norm,kineticDriftCof2Coeff5Row0Norm,kineticDriftCof2Coeff5Row1Norm,kineticDriftCof2Coeff5Row2Norm,kineticDriftCof2Coeff5Row3Norm,kineticDriftCof2Coeff5Row4Norm,kineticDriftCof2Coeff5Row5Norm,kineticDriftCof2Coeff5Row6Norm,kineticDriftCof2Coeff5Row7Norm,kineticDriftCof2Coeff6Row0Norm,kineticDriftCof2Coeff6Row1Norm,kineticDriftCof2Coeff6Row2Norm,kineticDriftCof2Coeff6Row3Norm,kineticDriftCof2Coeff6Row4Norm,kineticDriftCof2Coeff6Row5Norm,kineticDriftCof2Coeff6Row6Norm,kineticDriftCof2Coeff6Row7Norm,kineticDriftCof2Coeff7Row0Norm,kineticDriftCof2Coeff7Row1Norm,kineticDriftCof2Coeff7Row2Norm,kineticDriftCof2Coeff7Row3Norm,kineticDriftCof2Coeff7Row4Norm,kineticDriftCof2Coeff7Row5Norm,kineticDriftCof2Coeff7Row6Norm,kineticDriftCof2Coeff7Row7Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm,kineticDriftBlock2Coeff2Row0Norm,kineticDriftBlock2Coeff2Row1Norm,kineticDriftBlock2Coeff2Row2Norm,kineticDriftBlock2Coeff3Row0Norm,kineticDriftBlock2Coeff3Row1Norm,kineticDriftBlock2Coeff3Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff7Row7Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 7 7=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 7 7=kineticDriftCell h (kineticCof4*kineticBlock4) 7 7 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftCof4Row3,kineticDriftCof4Row4,kineticDriftCof4Row5,kineticDriftCof4Row6,kineticDriftCof4Row7,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2,kineticDriftBlock4Row3,kineticDriftBlock4Row4,kineticDriftBlock4Row5]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff0Row4Norm,kineticDriftCof4Coeff0Row5Norm,kineticDriftCof4Coeff0Row6Norm,kineticDriftCof4Coeff0Row7Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff1Row3Norm,kineticDriftCof4Coeff1Row4Norm,kineticDriftCof4Coeff1Row5Norm,kineticDriftCof4Coeff1Row6Norm,kineticDriftCof4Coeff1Row7Norm,kineticDriftCof4Coeff2Row0Norm,kineticDriftCof4Coeff2Row1Norm,kineticDriftCof4Coeff2Row2Norm,kineticDriftCof4Coeff2Row3Norm,kineticDriftCof4Coeff2Row4Norm,kineticDriftCof4Coeff2Row5Norm,kineticDriftCof4Coeff2Row6Norm,kineticDriftCof4Coeff2Row7Norm,kineticDriftCof4Coeff3Row0Norm,kineticDriftCof4Coeff3Row1Norm,kineticDriftCof4Coeff3Row2Norm,kineticDriftCof4Coeff3Row3Norm,kineticDriftCof4Coeff3Row4Norm,kineticDriftCof4Coeff3Row5Norm,kineticDriftCof4Coeff3Row6Norm,kineticDriftCof4Coeff3Row7Norm,kineticDriftCof4Coeff4Row0Norm,kineticDriftCof4Coeff4Row1Norm,kineticDriftCof4Coeff4Row2Norm,kineticDriftCof4Coeff4Row3Norm,kineticDriftCof4Coeff4Row4Norm,kineticDriftCof4Coeff4Row5Norm,kineticDriftCof4Coeff4Row6Norm,kineticDriftCof4Coeff4Row7Norm,kineticDriftCof4Coeff5Row0Norm,kineticDriftCof4Coeff5Row1Norm,kineticDriftCof4Coeff5Row2Norm,kineticDriftCof4Coeff5Row3Norm,kineticDriftCof4Coeff5Row4Norm,kineticDriftCof4Coeff5Row5Norm,kineticDriftCof4Coeff5Row6Norm,kineticDriftCof4Coeff5Row7Norm,kineticDriftCof4Coeff6Row0Norm,kineticDriftCof4Coeff6Row1Norm,kineticDriftCof4Coeff6Row2Norm,kineticDriftCof4Coeff6Row3Norm,kineticDriftCof4Coeff6Row4Norm,kineticDriftCof4Coeff6Row5Norm,kineticDriftCof4Coeff6Row6Norm,kineticDriftCof4Coeff6Row7Norm,kineticDriftCof4Coeff7Row0Norm,kineticDriftCof4Coeff7Row1Norm,kineticDriftCof4Coeff7Row2Norm,kineticDriftCof4Coeff7Row3Norm,kineticDriftCof4Coeff7Row4Norm,kineticDriftCof4Coeff7Row5Norm,kineticDriftCof4Coeff7Row6Norm,kineticDriftCof4Coeff7Row7Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff1Row3Norm,kineticDriftBlock4Coeff2Row0Norm,kineticDriftBlock4Coeff2Row1Norm,kineticDriftBlock4Coeff2Row2Norm,kineticDriftBlock4Coeff2Row3Norm,kineticDriftBlock4Coeff3Row0Norm,kineticDriftBlock4Coeff3Row1Norm,kineticDriftBlock4Coeff3Row2Norm,kineticDriftBlock4Coeff3Row3Norm,kineticDriftBlock4Coeff4Row0Norm,kineticDriftBlock4Coeff4Row1Norm,kineticDriftBlock4Coeff4Row2Norm,kineticDriftBlock4Coeff4Row3Norm,kineticDriftBlock4Coeff5Row0Norm,kineticDriftBlock4Coeff5Row1Norm,kineticDriftBlock4Coeff5Row2Norm,kineticDriftBlock4Coeff5Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff7Row7Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 7 7=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 7 7=kineticDriftCell h (kineticCof6*kineticBlock6) 7 7 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftCof6Row3,kineticDriftCof6Row4,kineticDriftCof6Row5,kineticDriftCof6Row6,kineticDriftCof6Row7,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2,kineticDriftBlock6Row3,kineticDriftBlock6Row4,kineticDriftBlock6Row5,kineticDriftBlock6Row6,kineticDriftBlock6Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff0Row4Norm,kineticDriftCof6Coeff0Row5Norm,kineticDriftCof6Coeff0Row6Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff1Row3Norm,kineticDriftCof6Coeff1Row4Norm,kineticDriftCof6Coeff1Row5Norm,kineticDriftCof6Coeff1Row6Norm,kineticDriftCof6Coeff2Row0Norm,kineticDriftCof6Coeff2Row1Norm,kineticDriftCof6Coeff2Row2Norm,kineticDriftCof6Coeff2Row3Norm,kineticDriftCof6Coeff2Row4Norm,kineticDriftCof6Coeff2Row5Norm,kineticDriftCof6Coeff2Row6Norm,kineticDriftCof6Coeff3Row0Norm,kineticDriftCof6Coeff3Row1Norm,kineticDriftCof6Coeff3Row2Norm,kineticDriftCof6Coeff3Row3Norm,kineticDriftCof6Coeff3Row4Norm,kineticDriftCof6Coeff3Row5Norm,kineticDriftCof6Coeff3Row6Norm,kineticDriftCof6Coeff4Row0Norm,kineticDriftCof6Coeff4Row1Norm,kineticDriftCof6Coeff4Row2Norm,kineticDriftCof6Coeff4Row3Norm,kineticDriftCof6Coeff4Row4Norm,kineticDriftCof6Coeff4Row5Norm,kineticDriftCof6Coeff4Row6Norm,kineticDriftCof6Coeff5Row0Norm,kineticDriftCof6Coeff5Row1Norm,kineticDriftCof6Coeff5Row2Norm,kineticDriftCof6Coeff5Row3Norm,kineticDriftCof6Coeff5Row4Norm,kineticDriftCof6Coeff5Row5Norm,kineticDriftCof6Coeff5Row6Norm,kineticDriftCof6Coeff6Row0Norm,kineticDriftCof6Coeff6Row1Norm,kineticDriftCof6Coeff6Row2Norm,kineticDriftCof6Coeff6Row3Norm,kineticDriftCof6Coeff6Row4Norm,kineticDriftCof6Coeff6Row5Norm,kineticDriftCof6Coeff6Row6Norm,kineticDriftCof6Coeff7Row0Norm,kineticDriftCof6Coeff7Row1Norm,kineticDriftCof6Coeff7Row2Norm,kineticDriftCof6Coeff7Row3Norm,kineticDriftCof6Coeff7Row4Norm,kineticDriftCof6Coeff7Row5Norm,kineticDriftCof6Coeff7Row6Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff0Row4Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff1Row3Norm,kineticDriftBlock6Coeff1Row4Norm,kineticDriftBlock6Coeff2Row0Norm,kineticDriftBlock6Coeff2Row1Norm,kineticDriftBlock6Coeff2Row2Norm,kineticDriftBlock6Coeff2Row3Norm,kineticDriftBlock6Coeff2Row4Norm,kineticDriftBlock6Coeff3Row0Norm,kineticDriftBlock6Coeff3Row1Norm,kineticDriftBlock6Coeff3Row2Norm,kineticDriftBlock6Coeff3Row3Norm,kineticDriftBlock6Coeff3Row4Norm,kineticDriftBlock6Coeff4Row0Norm,kineticDriftBlock6Coeff4Row1Norm,kineticDriftBlock6Coeff4Row2Norm,kineticDriftBlock6Coeff4Row3Norm,kineticDriftBlock6Coeff4Row4Norm,kineticDriftBlock6Coeff5Row0Norm,kineticDriftBlock6Coeff5Row1Norm,kineticDriftBlock6Coeff5Row2Norm,kineticDriftBlock6Coeff5Row3Norm,kineticDriftBlock6Coeff5Row4Norm,kineticDriftBlock6Coeff6Row0Norm,kineticDriftBlock6Coeff6Row1Norm,kineticDriftBlock6Coeff6Row2Norm,kineticDriftBlock6Coeff6Row3Norm,kineticDriftBlock6Coeff6Row4Norm,kineticDriftBlock6Coeff7Row0Norm,kineticDriftBlock6Coeff7Row1Norm,kineticDriftBlock6Coeff7Row2Norm,kineticDriftBlock6Coeff7Row3Norm,kineticDriftBlock6Coeff7Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff7Row7Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 7 7=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 7 7=kineticDriftCell h (kineticCof8*kineticBlock8) 7 7 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftCof8Row3,kineticDriftCof8Row4,kineticDriftCof8Row5,kineticDriftCof8Row6,kineticDriftCof8Row7,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2,kineticDriftBlock8Row3,kineticDriftBlock8Row4,kineticDriftBlock8Row5,kineticDriftBlock8Row6,kineticDriftBlock8Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff0Row4Norm,kineticDriftCof8Coeff0Row5Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff1Row3Norm,kineticDriftCof8Coeff1Row4Norm,kineticDriftCof8Coeff1Row5Norm,kineticDriftCof8Coeff2Row0Norm,kineticDriftCof8Coeff2Row1Norm,kineticDriftCof8Coeff2Row2Norm,kineticDriftCof8Coeff2Row3Norm,kineticDriftCof8Coeff2Row4Norm,kineticDriftCof8Coeff2Row5Norm,kineticDriftCof8Coeff3Row0Norm,kineticDriftCof8Coeff3Row1Norm,kineticDriftCof8Coeff3Row2Norm,kineticDriftCof8Coeff3Row3Norm,kineticDriftCof8Coeff3Row4Norm,kineticDriftCof8Coeff3Row5Norm,kineticDriftCof8Coeff4Row0Norm,kineticDriftCof8Coeff4Row1Norm,kineticDriftCof8Coeff4Row2Norm,kineticDriftCof8Coeff4Row3Norm,kineticDriftCof8Coeff4Row4Norm,kineticDriftCof8Coeff4Row5Norm,kineticDriftCof8Coeff5Row0Norm,kineticDriftCof8Coeff5Row1Norm,kineticDriftCof8Coeff5Row2Norm,kineticDriftCof8Coeff5Row3Norm,kineticDriftCof8Coeff5Row4Norm,kineticDriftCof8Coeff5Row5Norm,kineticDriftCof8Coeff6Row0Norm,kineticDriftCof8Coeff6Row1Norm,kineticDriftCof8Coeff6Row2Norm,kineticDriftCof8Coeff6Row3Norm,kineticDriftCof8Coeff6Row4Norm,kineticDriftCof8Coeff6Row5Norm,kineticDriftCof8Coeff7Row0Norm,kineticDriftCof8Coeff7Row1Norm,kineticDriftCof8Coeff7Row2Norm,kineticDriftCof8Coeff7Row3Norm,kineticDriftCof8Coeff7Row4Norm,kineticDriftCof8Coeff7Row5Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff0Row4Norm,kineticDriftBlock8Coeff0Row5Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff1Row3Norm,kineticDriftBlock8Coeff1Row4Norm,kineticDriftBlock8Coeff1Row5Norm,kineticDriftBlock8Coeff2Row0Norm,kineticDriftBlock8Coeff2Row1Norm,kineticDriftBlock8Coeff2Row2Norm,kineticDriftBlock8Coeff2Row3Norm,kineticDriftBlock8Coeff2Row4Norm,kineticDriftBlock8Coeff2Row5Norm,kineticDriftBlock8Coeff3Row0Norm,kineticDriftBlock8Coeff3Row1Norm,kineticDriftBlock8Coeff3Row2Norm,kineticDriftBlock8Coeff3Row3Norm,kineticDriftBlock8Coeff3Row4Norm,kineticDriftBlock8Coeff3Row5Norm,kineticDriftBlock8Coeff4Row0Norm,kineticDriftBlock8Coeff4Row1Norm,kineticDriftBlock8Coeff4Row2Norm,kineticDriftBlock8Coeff4Row3Norm,kineticDriftBlock8Coeff4Row4Norm,kineticDriftBlock8Coeff4Row5Norm,kineticDriftBlock8Coeff5Row0Norm,kineticDriftBlock8Coeff5Row1Norm,kineticDriftBlock8Coeff5Row2Norm,kineticDriftBlock8Coeff5Row3Norm,kineticDriftBlock8Coeff5Row4Norm,kineticDriftBlock8Coeff5Row5Norm,kineticDriftBlock8Coeff6Row0Norm,kineticDriftBlock8Coeff6Row1Norm,kineticDriftBlock8Coeff6Row2Norm,kineticDriftBlock8Coeff6Row3Norm,kineticDriftBlock8Coeff6Row4Norm,kineticDriftBlock8Coeff6Row5Norm,kineticDriftBlock8Coeff7Row0Norm,kineticDriftBlock8Coeff7Row1Norm,kineticDriftBlock8Coeff7Row2Norm,kineticDriftBlock8Coeff7Row3Norm,kineticDriftBlock8Coeff7Row4Norm,kineticDriftBlock8Coeff7Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff7Row7Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 7 7=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 7 7=kineticDriftCell h (kineticCof10*kineticBlock10) 7 7 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftCof10Row3,kineticDriftCof10Row4,kineticDriftCof10Row5,kineticDriftCof10Row6,kineticDriftCof10Row7,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2,kineticDriftBlock10Row3,kineticDriftBlock10Row4,kineticDriftBlock10Row5,kineticDriftBlock10Row6,kineticDriftBlock10Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff0Row4Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff1Row3Norm,kineticDriftCof10Coeff1Row4Norm,kineticDriftCof10Coeff2Row0Norm,kineticDriftCof10Coeff2Row1Norm,kineticDriftCof10Coeff2Row2Norm,kineticDriftCof10Coeff2Row3Norm,kineticDriftCof10Coeff2Row4Norm,kineticDriftCof10Coeff3Row0Norm,kineticDriftCof10Coeff3Row1Norm,kineticDriftCof10Coeff3Row2Norm,kineticDriftCof10Coeff3Row3Norm,kineticDriftCof10Coeff3Row4Norm,kineticDriftCof10Coeff4Row0Norm,kineticDriftCof10Coeff4Row1Norm,kineticDriftCof10Coeff4Row2Norm,kineticDriftCof10Coeff4Row3Norm,kineticDriftCof10Coeff4Row4Norm,kineticDriftCof10Coeff5Row0Norm,kineticDriftCof10Coeff5Row1Norm,kineticDriftCof10Coeff5Row2Norm,kineticDriftCof10Coeff5Row3Norm,kineticDriftCof10Coeff5Row4Norm,kineticDriftCof10Coeff6Row0Norm,kineticDriftCof10Coeff6Row1Norm,kineticDriftCof10Coeff6Row2Norm,kineticDriftCof10Coeff6Row3Norm,kineticDriftCof10Coeff6Row4Norm,kineticDriftCof10Coeff7Row0Norm,kineticDriftCof10Coeff7Row1Norm,kineticDriftCof10Coeff7Row2Norm,kineticDriftCof10Coeff7Row3Norm,kineticDriftCof10Coeff7Row4Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff0Row4Norm,kineticDriftBlock10Coeff0Row5Norm,kineticDriftBlock10Coeff0Row6Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff1Row3Norm,kineticDriftBlock10Coeff1Row4Norm,kineticDriftBlock10Coeff1Row5Norm,kineticDriftBlock10Coeff1Row6Norm,kineticDriftBlock10Coeff2Row0Norm,kineticDriftBlock10Coeff2Row1Norm,kineticDriftBlock10Coeff2Row2Norm,kineticDriftBlock10Coeff2Row3Norm,kineticDriftBlock10Coeff2Row4Norm,kineticDriftBlock10Coeff2Row5Norm,kineticDriftBlock10Coeff2Row6Norm,kineticDriftBlock10Coeff3Row0Norm,kineticDriftBlock10Coeff3Row1Norm,kineticDriftBlock10Coeff3Row2Norm,kineticDriftBlock10Coeff3Row3Norm,kineticDriftBlock10Coeff3Row4Norm,kineticDriftBlock10Coeff3Row5Norm,kineticDriftBlock10Coeff3Row6Norm,kineticDriftBlock10Coeff4Row0Norm,kineticDriftBlock10Coeff4Row1Norm,kineticDriftBlock10Coeff4Row2Norm,kineticDriftBlock10Coeff4Row3Norm,kineticDriftBlock10Coeff4Row4Norm,kineticDriftBlock10Coeff4Row5Norm,kineticDriftBlock10Coeff4Row6Norm,kineticDriftBlock10Coeff5Row0Norm,kineticDriftBlock10Coeff5Row1Norm,kineticDriftBlock10Coeff5Row2Norm,kineticDriftBlock10Coeff5Row3Norm,kineticDriftBlock10Coeff5Row4Norm,kineticDriftBlock10Coeff5Row5Norm,kineticDriftBlock10Coeff5Row6Norm,kineticDriftBlock10Coeff6Row0Norm,kineticDriftBlock10Coeff6Row1Norm,kineticDriftBlock10Coeff6Row2Norm,kineticDriftBlock10Coeff6Row3Norm,kineticDriftBlock10Coeff6Row4Norm,kineticDriftBlock10Coeff6Row5Norm,kineticDriftBlock10Coeff6Row6Norm,kineticDriftBlock10Coeff7Row0Norm,kineticDriftBlock10Coeff7Row1Norm,kineticDriftBlock10Coeff7Row2Norm,kineticDriftBlock10Coeff7Row3Norm,kineticDriftBlock10Coeff7Row4Norm,kineticDriftBlock10Coeff7Row5Norm,kineticDriftBlock10Coeff7Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff7Row8Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 7 8=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 7 8=kineticDriftCell h (kineticCof2*kineticBlock2) 7 8 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftCof2Row3,kineticDriftCof2Row4,kineticDriftCof2Row5,kineticDriftCof2Row6,kineticDriftCof2Row7,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2,kineticDriftBlock2Row3]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm,kineticDriftCof2Coeff0Row4Norm,kineticDriftCof2Coeff0Row5Norm,kineticDriftCof2Coeff0Row6Norm,kineticDriftCof2Coeff0Row7Norm,kineticDriftCof2Coeff0Row8Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff1Row3Norm,kineticDriftCof2Coeff1Row4Norm,kineticDriftCof2Coeff1Row5Norm,kineticDriftCof2Coeff1Row6Norm,kineticDriftCof2Coeff1Row7Norm,kineticDriftCof2Coeff1Row8Norm,kineticDriftCof2Coeff2Row0Norm,kineticDriftCof2Coeff2Row1Norm,kineticDriftCof2Coeff2Row2Norm,kineticDriftCof2Coeff2Row3Norm,kineticDriftCof2Coeff2Row4Norm,kineticDriftCof2Coeff2Row5Norm,kineticDriftCof2Coeff2Row6Norm,kineticDriftCof2Coeff2Row7Norm,kineticDriftCof2Coeff2Row8Norm,kineticDriftCof2Coeff3Row0Norm,kineticDriftCof2Coeff3Row1Norm,kineticDriftCof2Coeff3Row2Norm,kineticDriftCof2Coeff3Row3Norm,kineticDriftCof2Coeff3Row4Norm,kineticDriftCof2Coeff3Row5Norm,kineticDriftCof2Coeff3Row6Norm,kineticDriftCof2Coeff3Row7Norm,kineticDriftCof2Coeff3Row8Norm,kineticDriftCof2Coeff4Row0Norm,kineticDriftCof2Coeff4Row1Norm,kineticDriftCof2Coeff4Row2Norm,kineticDriftCof2Coeff4Row3Norm,kineticDriftCof2Coeff4Row4Norm,kineticDriftCof2Coeff4Row5Norm,kineticDriftCof2Coeff4Row6Norm,kineticDriftCof2Coeff4Row7Norm,kineticDriftCof2Coeff4Row8Norm,kineticDriftCof2Coeff5Row0Norm,kineticDriftCof2Coeff5Row1Norm,kineticDriftCof2Coeff5Row2Norm,kineticDriftCof2Coeff5Row3Norm,kineticDriftCof2Coeff5Row4Norm,kineticDriftCof2Coeff5Row5Norm,kineticDriftCof2Coeff5Row6Norm,kineticDriftCof2Coeff5Row7Norm,kineticDriftCof2Coeff5Row8Norm,kineticDriftCof2Coeff6Row0Norm,kineticDriftCof2Coeff6Row1Norm,kineticDriftCof2Coeff6Row2Norm,kineticDriftCof2Coeff6Row3Norm,kineticDriftCof2Coeff6Row4Norm,kineticDriftCof2Coeff6Row5Norm,kineticDriftCof2Coeff6Row6Norm,kineticDriftCof2Coeff6Row7Norm,kineticDriftCof2Coeff6Row8Norm,kineticDriftCof2Coeff7Row0Norm,kineticDriftCof2Coeff7Row1Norm,kineticDriftCof2Coeff7Row2Norm,kineticDriftCof2Coeff7Row3Norm,kineticDriftCof2Coeff7Row4Norm,kineticDriftCof2Coeff7Row5Norm,kineticDriftCof2Coeff7Row6Norm,kineticDriftCof2Coeff7Row7Norm,kineticDriftCof2Coeff7Row8Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm,kineticDriftBlock2Coeff2Row0Norm,kineticDriftBlock2Coeff2Row1Norm,kineticDriftBlock2Coeff2Row2Norm,kineticDriftBlock2Coeff3Row0Norm,kineticDriftBlock2Coeff3Row1Norm,kineticDriftBlock2Coeff3Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff7Row8Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 7 8=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 7 8=kineticDriftCell h (kineticCof4*kineticBlock4) 7 8 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftCof4Row3,kineticDriftCof4Row4,kineticDriftCof4Row5,kineticDriftCof4Row6,kineticDriftCof4Row7,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2,kineticDriftBlock4Row3,kineticDriftBlock4Row4,kineticDriftBlock4Row5]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff0Row4Norm,kineticDriftCof4Coeff0Row5Norm,kineticDriftCof4Coeff0Row6Norm,kineticDriftCof4Coeff0Row7Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff1Row3Norm,kineticDriftCof4Coeff1Row4Norm,kineticDriftCof4Coeff1Row5Norm,kineticDriftCof4Coeff1Row6Norm,kineticDriftCof4Coeff1Row7Norm,kineticDriftCof4Coeff2Row0Norm,kineticDriftCof4Coeff2Row1Norm,kineticDriftCof4Coeff2Row2Norm,kineticDriftCof4Coeff2Row3Norm,kineticDriftCof4Coeff2Row4Norm,kineticDriftCof4Coeff2Row5Norm,kineticDriftCof4Coeff2Row6Norm,kineticDriftCof4Coeff2Row7Norm,kineticDriftCof4Coeff3Row0Norm,kineticDriftCof4Coeff3Row1Norm,kineticDriftCof4Coeff3Row2Norm,kineticDriftCof4Coeff3Row3Norm,kineticDriftCof4Coeff3Row4Norm,kineticDriftCof4Coeff3Row5Norm,kineticDriftCof4Coeff3Row6Norm,kineticDriftCof4Coeff3Row7Norm,kineticDriftCof4Coeff4Row0Norm,kineticDriftCof4Coeff4Row1Norm,kineticDriftCof4Coeff4Row2Norm,kineticDriftCof4Coeff4Row3Norm,kineticDriftCof4Coeff4Row4Norm,kineticDriftCof4Coeff4Row5Norm,kineticDriftCof4Coeff4Row6Norm,kineticDriftCof4Coeff4Row7Norm,kineticDriftCof4Coeff5Row0Norm,kineticDriftCof4Coeff5Row1Norm,kineticDriftCof4Coeff5Row2Norm,kineticDriftCof4Coeff5Row3Norm,kineticDriftCof4Coeff5Row4Norm,kineticDriftCof4Coeff5Row5Norm,kineticDriftCof4Coeff5Row6Norm,kineticDriftCof4Coeff5Row7Norm,kineticDriftCof4Coeff6Row0Norm,kineticDriftCof4Coeff6Row1Norm,kineticDriftCof4Coeff6Row2Norm,kineticDriftCof4Coeff6Row3Norm,kineticDriftCof4Coeff6Row4Norm,kineticDriftCof4Coeff6Row5Norm,kineticDriftCof4Coeff6Row6Norm,kineticDriftCof4Coeff6Row7Norm,kineticDriftCof4Coeff7Row0Norm,kineticDriftCof4Coeff7Row1Norm,kineticDriftCof4Coeff7Row2Norm,kineticDriftCof4Coeff7Row3Norm,kineticDriftCof4Coeff7Row4Norm,kineticDriftCof4Coeff7Row5Norm,kineticDriftCof4Coeff7Row6Norm,kineticDriftCof4Coeff7Row7Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff1Row3Norm,kineticDriftBlock4Coeff2Row0Norm,kineticDriftBlock4Coeff2Row1Norm,kineticDriftBlock4Coeff2Row2Norm,kineticDriftBlock4Coeff2Row3Norm,kineticDriftBlock4Coeff3Row0Norm,kineticDriftBlock4Coeff3Row1Norm,kineticDriftBlock4Coeff3Row2Norm,kineticDriftBlock4Coeff3Row3Norm,kineticDriftBlock4Coeff4Row0Norm,kineticDriftBlock4Coeff4Row1Norm,kineticDriftBlock4Coeff4Row2Norm,kineticDriftBlock4Coeff4Row3Norm,kineticDriftBlock4Coeff5Row0Norm,kineticDriftBlock4Coeff5Row1Norm,kineticDriftBlock4Coeff5Row2Norm,kineticDriftBlock4Coeff5Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff7Row8Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 7 8=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 7 8=kineticDriftCell h (kineticCof6*kineticBlock6) 7 8 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftCof6Row3,kineticDriftCof6Row4,kineticDriftCof6Row5,kineticDriftCof6Row6,kineticDriftCof6Row7,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2,kineticDriftBlock6Row3,kineticDriftBlock6Row4,kineticDriftBlock6Row5,kineticDriftBlock6Row6,kineticDriftBlock6Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff0Row4Norm,kineticDriftCof6Coeff0Row5Norm,kineticDriftCof6Coeff0Row6Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff1Row3Norm,kineticDriftCof6Coeff1Row4Norm,kineticDriftCof6Coeff1Row5Norm,kineticDriftCof6Coeff1Row6Norm,kineticDriftCof6Coeff2Row0Norm,kineticDriftCof6Coeff2Row1Norm,kineticDriftCof6Coeff2Row2Norm,kineticDriftCof6Coeff2Row3Norm,kineticDriftCof6Coeff2Row4Norm,kineticDriftCof6Coeff2Row5Norm,kineticDriftCof6Coeff2Row6Norm,kineticDriftCof6Coeff3Row0Norm,kineticDriftCof6Coeff3Row1Norm,kineticDriftCof6Coeff3Row2Norm,kineticDriftCof6Coeff3Row3Norm,kineticDriftCof6Coeff3Row4Norm,kineticDriftCof6Coeff3Row5Norm,kineticDriftCof6Coeff3Row6Norm,kineticDriftCof6Coeff4Row0Norm,kineticDriftCof6Coeff4Row1Norm,kineticDriftCof6Coeff4Row2Norm,kineticDriftCof6Coeff4Row3Norm,kineticDriftCof6Coeff4Row4Norm,kineticDriftCof6Coeff4Row5Norm,kineticDriftCof6Coeff4Row6Norm,kineticDriftCof6Coeff5Row0Norm,kineticDriftCof6Coeff5Row1Norm,kineticDriftCof6Coeff5Row2Norm,kineticDriftCof6Coeff5Row3Norm,kineticDriftCof6Coeff5Row4Norm,kineticDriftCof6Coeff5Row5Norm,kineticDriftCof6Coeff5Row6Norm,kineticDriftCof6Coeff6Row0Norm,kineticDriftCof6Coeff6Row1Norm,kineticDriftCof6Coeff6Row2Norm,kineticDriftCof6Coeff6Row3Norm,kineticDriftCof6Coeff6Row4Norm,kineticDriftCof6Coeff6Row5Norm,kineticDriftCof6Coeff6Row6Norm,kineticDriftCof6Coeff7Row0Norm,kineticDriftCof6Coeff7Row1Norm,kineticDriftCof6Coeff7Row2Norm,kineticDriftCof6Coeff7Row3Norm,kineticDriftCof6Coeff7Row4Norm,kineticDriftCof6Coeff7Row5Norm,kineticDriftCof6Coeff7Row6Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff0Row4Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff1Row3Norm,kineticDriftBlock6Coeff1Row4Norm,kineticDriftBlock6Coeff2Row0Norm,kineticDriftBlock6Coeff2Row1Norm,kineticDriftBlock6Coeff2Row2Norm,kineticDriftBlock6Coeff2Row3Norm,kineticDriftBlock6Coeff2Row4Norm,kineticDriftBlock6Coeff3Row0Norm,kineticDriftBlock6Coeff3Row1Norm,kineticDriftBlock6Coeff3Row2Norm,kineticDriftBlock6Coeff3Row3Norm,kineticDriftBlock6Coeff3Row4Norm,kineticDriftBlock6Coeff4Row0Norm,kineticDriftBlock6Coeff4Row1Norm,kineticDriftBlock6Coeff4Row2Norm,kineticDriftBlock6Coeff4Row3Norm,kineticDriftBlock6Coeff4Row4Norm,kineticDriftBlock6Coeff5Row0Norm,kineticDriftBlock6Coeff5Row1Norm,kineticDriftBlock6Coeff5Row2Norm,kineticDriftBlock6Coeff5Row3Norm,kineticDriftBlock6Coeff5Row4Norm,kineticDriftBlock6Coeff6Row0Norm,kineticDriftBlock6Coeff6Row1Norm,kineticDriftBlock6Coeff6Row2Norm,kineticDriftBlock6Coeff6Row3Norm,kineticDriftBlock6Coeff6Row4Norm,kineticDriftBlock6Coeff7Row0Norm,kineticDriftBlock6Coeff7Row1Norm,kineticDriftBlock6Coeff7Row2Norm,kineticDriftBlock6Coeff7Row3Norm,kineticDriftBlock6Coeff7Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff7Row8Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 7 8=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 7 8=kineticDriftCell h (kineticCof8*kineticBlock8) 7 8 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftCof8Row3,kineticDriftCof8Row4,kineticDriftCof8Row5,kineticDriftCof8Row6,kineticDriftCof8Row7,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2,kineticDriftBlock8Row3,kineticDriftBlock8Row4,kineticDriftBlock8Row5,kineticDriftBlock8Row6,kineticDriftBlock8Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff0Row4Norm,kineticDriftCof8Coeff0Row5Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff1Row3Norm,kineticDriftCof8Coeff1Row4Norm,kineticDriftCof8Coeff1Row5Norm,kineticDriftCof8Coeff2Row0Norm,kineticDriftCof8Coeff2Row1Norm,kineticDriftCof8Coeff2Row2Norm,kineticDriftCof8Coeff2Row3Norm,kineticDriftCof8Coeff2Row4Norm,kineticDriftCof8Coeff2Row5Norm,kineticDriftCof8Coeff3Row0Norm,kineticDriftCof8Coeff3Row1Norm,kineticDriftCof8Coeff3Row2Norm,kineticDriftCof8Coeff3Row3Norm,kineticDriftCof8Coeff3Row4Norm,kineticDriftCof8Coeff3Row5Norm,kineticDriftCof8Coeff4Row0Norm,kineticDriftCof8Coeff4Row1Norm,kineticDriftCof8Coeff4Row2Norm,kineticDriftCof8Coeff4Row3Norm,kineticDriftCof8Coeff4Row4Norm,kineticDriftCof8Coeff4Row5Norm,kineticDriftCof8Coeff5Row0Norm,kineticDriftCof8Coeff5Row1Norm,kineticDriftCof8Coeff5Row2Norm,kineticDriftCof8Coeff5Row3Norm,kineticDriftCof8Coeff5Row4Norm,kineticDriftCof8Coeff5Row5Norm,kineticDriftCof8Coeff6Row0Norm,kineticDriftCof8Coeff6Row1Norm,kineticDriftCof8Coeff6Row2Norm,kineticDriftCof8Coeff6Row3Norm,kineticDriftCof8Coeff6Row4Norm,kineticDriftCof8Coeff6Row5Norm,kineticDriftCof8Coeff7Row0Norm,kineticDriftCof8Coeff7Row1Norm,kineticDriftCof8Coeff7Row2Norm,kineticDriftCof8Coeff7Row3Norm,kineticDriftCof8Coeff7Row4Norm,kineticDriftCof8Coeff7Row5Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff0Row4Norm,kineticDriftBlock8Coeff0Row5Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff1Row3Norm,kineticDriftBlock8Coeff1Row4Norm,kineticDriftBlock8Coeff1Row5Norm,kineticDriftBlock8Coeff2Row0Norm,kineticDriftBlock8Coeff2Row1Norm,kineticDriftBlock8Coeff2Row2Norm,kineticDriftBlock8Coeff2Row3Norm,kineticDriftBlock8Coeff2Row4Norm,kineticDriftBlock8Coeff2Row5Norm,kineticDriftBlock8Coeff3Row0Norm,kineticDriftBlock8Coeff3Row1Norm,kineticDriftBlock8Coeff3Row2Norm,kineticDriftBlock8Coeff3Row3Norm,kineticDriftBlock8Coeff3Row4Norm,kineticDriftBlock8Coeff3Row5Norm,kineticDriftBlock8Coeff4Row0Norm,kineticDriftBlock8Coeff4Row1Norm,kineticDriftBlock8Coeff4Row2Norm,kineticDriftBlock8Coeff4Row3Norm,kineticDriftBlock8Coeff4Row4Norm,kineticDriftBlock8Coeff4Row5Norm,kineticDriftBlock8Coeff5Row0Norm,kineticDriftBlock8Coeff5Row1Norm,kineticDriftBlock8Coeff5Row2Norm,kineticDriftBlock8Coeff5Row3Norm,kineticDriftBlock8Coeff5Row4Norm,kineticDriftBlock8Coeff5Row5Norm,kineticDriftBlock8Coeff6Row0Norm,kineticDriftBlock8Coeff6Row1Norm,kineticDriftBlock8Coeff6Row2Norm,kineticDriftBlock8Coeff6Row3Norm,kineticDriftBlock8Coeff6Row4Norm,kineticDriftBlock8Coeff6Row5Norm,kineticDriftBlock8Coeff7Row0Norm,kineticDriftBlock8Coeff7Row1Norm,kineticDriftBlock8Coeff7Row2Norm,kineticDriftBlock8Coeff7Row3Norm,kineticDriftBlock8Coeff7Row4Norm,kineticDriftBlock8Coeff7Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff7Row8Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 7 8=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 7 8=kineticDriftCell h (kineticCof10*kineticBlock10) 7 8 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftCof10Row3,kineticDriftCof10Row4,kineticDriftCof10Row5,kineticDriftCof10Row6,kineticDriftCof10Row7,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2,kineticDriftBlock10Row3,kineticDriftBlock10Row4,kineticDriftBlock10Row5,kineticDriftBlock10Row6,kineticDriftBlock10Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff0Row4Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff1Row3Norm,kineticDriftCof10Coeff1Row4Norm,kineticDriftCof10Coeff2Row0Norm,kineticDriftCof10Coeff2Row1Norm,kineticDriftCof10Coeff2Row2Norm,kineticDriftCof10Coeff2Row3Norm,kineticDriftCof10Coeff2Row4Norm,kineticDriftCof10Coeff3Row0Norm,kineticDriftCof10Coeff3Row1Norm,kineticDriftCof10Coeff3Row2Norm,kineticDriftCof10Coeff3Row3Norm,kineticDriftCof10Coeff3Row4Norm,kineticDriftCof10Coeff4Row0Norm,kineticDriftCof10Coeff4Row1Norm,kineticDriftCof10Coeff4Row2Norm,kineticDriftCof10Coeff4Row3Norm,kineticDriftCof10Coeff4Row4Norm,kineticDriftCof10Coeff5Row0Norm,kineticDriftCof10Coeff5Row1Norm,kineticDriftCof10Coeff5Row2Norm,kineticDriftCof10Coeff5Row3Norm,kineticDriftCof10Coeff5Row4Norm,kineticDriftCof10Coeff6Row0Norm,kineticDriftCof10Coeff6Row1Norm,kineticDriftCof10Coeff6Row2Norm,kineticDriftCof10Coeff6Row3Norm,kineticDriftCof10Coeff6Row4Norm,kineticDriftCof10Coeff7Row0Norm,kineticDriftCof10Coeff7Row1Norm,kineticDriftCof10Coeff7Row2Norm,kineticDriftCof10Coeff7Row3Norm,kineticDriftCof10Coeff7Row4Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff0Row4Norm,kineticDriftBlock10Coeff0Row5Norm,kineticDriftBlock10Coeff0Row6Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff1Row3Norm,kineticDriftBlock10Coeff1Row4Norm,kineticDriftBlock10Coeff1Row5Norm,kineticDriftBlock10Coeff1Row6Norm,kineticDriftBlock10Coeff2Row0Norm,kineticDriftBlock10Coeff2Row1Norm,kineticDriftBlock10Coeff2Row2Norm,kineticDriftBlock10Coeff2Row3Norm,kineticDriftBlock10Coeff2Row4Norm,kineticDriftBlock10Coeff2Row5Norm,kineticDriftBlock10Coeff2Row6Norm,kineticDriftBlock10Coeff3Row0Norm,kineticDriftBlock10Coeff3Row1Norm,kineticDriftBlock10Coeff3Row2Norm,kineticDriftBlock10Coeff3Row3Norm,kineticDriftBlock10Coeff3Row4Norm,kineticDriftBlock10Coeff3Row5Norm,kineticDriftBlock10Coeff3Row6Norm,kineticDriftBlock10Coeff4Row0Norm,kineticDriftBlock10Coeff4Row1Norm,kineticDriftBlock10Coeff4Row2Norm,kineticDriftBlock10Coeff4Row3Norm,kineticDriftBlock10Coeff4Row4Norm,kineticDriftBlock10Coeff4Row5Norm,kineticDriftBlock10Coeff4Row6Norm,kineticDriftBlock10Coeff5Row0Norm,kineticDriftBlock10Coeff5Row1Norm,kineticDriftBlock10Coeff5Row2Norm,kineticDriftBlock10Coeff5Row3Norm,kineticDriftBlock10Coeff5Row4Norm,kineticDriftBlock10Coeff5Row5Norm,kineticDriftBlock10Coeff5Row6Norm,kineticDriftBlock10Coeff6Row0Norm,kineticDriftBlock10Coeff6Row1Norm,kineticDriftBlock10Coeff6Row2Norm,kineticDriftBlock10Coeff6Row3Norm,kineticDriftBlock10Coeff6Row4Norm,kineticDriftBlock10Coeff6Row5Norm,kineticDriftBlock10Coeff6Row6Norm,kineticDriftBlock10Coeff7Row0Norm,kineticDriftBlock10Coeff7Row1Norm,kineticDriftBlock10Coeff7Row2Norm,kineticDriftBlock10Coeff7Row3Norm,kineticDriftBlock10Coeff7Row4Norm,kineticDriftBlock10Coeff7Row5Norm,kineticDriftBlock10Coeff7Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff7Row9Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 7 9=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 7 9=kineticDriftCell h (kineticCof2*kineticBlock2) 7 9 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftCof2Row3,kineticDriftCof2Row4,kineticDriftCof2Row5,kineticDriftCof2Row6,kineticDriftCof2Row7,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2,kineticDriftBlock2Row3]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm,kineticDriftCof2Coeff0Row4Norm,kineticDriftCof2Coeff0Row5Norm,kineticDriftCof2Coeff0Row6Norm,kineticDriftCof2Coeff0Row7Norm,kineticDriftCof2Coeff0Row8Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff1Row3Norm,kineticDriftCof2Coeff1Row4Norm,kineticDriftCof2Coeff1Row5Norm,kineticDriftCof2Coeff1Row6Norm,kineticDriftCof2Coeff1Row7Norm,kineticDriftCof2Coeff1Row8Norm,kineticDriftCof2Coeff2Row0Norm,kineticDriftCof2Coeff2Row1Norm,kineticDriftCof2Coeff2Row2Norm,kineticDriftCof2Coeff2Row3Norm,kineticDriftCof2Coeff2Row4Norm,kineticDriftCof2Coeff2Row5Norm,kineticDriftCof2Coeff2Row6Norm,kineticDriftCof2Coeff2Row7Norm,kineticDriftCof2Coeff2Row8Norm,kineticDriftCof2Coeff3Row0Norm,kineticDriftCof2Coeff3Row1Norm,kineticDriftCof2Coeff3Row2Norm,kineticDriftCof2Coeff3Row3Norm,kineticDriftCof2Coeff3Row4Norm,kineticDriftCof2Coeff3Row5Norm,kineticDriftCof2Coeff3Row6Norm,kineticDriftCof2Coeff3Row7Norm,kineticDriftCof2Coeff3Row8Norm,kineticDriftCof2Coeff4Row0Norm,kineticDriftCof2Coeff4Row1Norm,kineticDriftCof2Coeff4Row2Norm,kineticDriftCof2Coeff4Row3Norm,kineticDriftCof2Coeff4Row4Norm,kineticDriftCof2Coeff4Row5Norm,kineticDriftCof2Coeff4Row6Norm,kineticDriftCof2Coeff4Row7Norm,kineticDriftCof2Coeff4Row8Norm,kineticDriftCof2Coeff5Row0Norm,kineticDriftCof2Coeff5Row1Norm,kineticDriftCof2Coeff5Row2Norm,kineticDriftCof2Coeff5Row3Norm,kineticDriftCof2Coeff5Row4Norm,kineticDriftCof2Coeff5Row5Norm,kineticDriftCof2Coeff5Row6Norm,kineticDriftCof2Coeff5Row7Norm,kineticDriftCof2Coeff5Row8Norm,kineticDriftCof2Coeff6Row0Norm,kineticDriftCof2Coeff6Row1Norm,kineticDriftCof2Coeff6Row2Norm,kineticDriftCof2Coeff6Row3Norm,kineticDriftCof2Coeff6Row4Norm,kineticDriftCof2Coeff6Row5Norm,kineticDriftCof2Coeff6Row6Norm,kineticDriftCof2Coeff6Row7Norm,kineticDriftCof2Coeff6Row8Norm,kineticDriftCof2Coeff7Row0Norm,kineticDriftCof2Coeff7Row1Norm,kineticDriftCof2Coeff7Row2Norm,kineticDriftCof2Coeff7Row3Norm,kineticDriftCof2Coeff7Row4Norm,kineticDriftCof2Coeff7Row5Norm,kineticDriftCof2Coeff7Row6Norm,kineticDriftCof2Coeff7Row7Norm,kineticDriftCof2Coeff7Row8Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm,kineticDriftBlock2Coeff2Row0Norm,kineticDriftBlock2Coeff2Row1Norm,kineticDriftBlock2Coeff2Row2Norm,kineticDriftBlock2Coeff3Row0Norm,kineticDriftBlock2Coeff3Row1Norm,kineticDriftBlock2Coeff3Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff7Row9Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 7 9=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 7 9=kineticDriftCell h (kineticCof4*kineticBlock4) 7 9 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftCof4Row3,kineticDriftCof4Row4,kineticDriftCof4Row5,kineticDriftCof4Row6,kineticDriftCof4Row7,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2,kineticDriftBlock4Row3,kineticDriftBlock4Row4,kineticDriftBlock4Row5]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff0Row4Norm,kineticDriftCof4Coeff0Row5Norm,kineticDriftCof4Coeff0Row6Norm,kineticDriftCof4Coeff0Row7Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff1Row3Norm,kineticDriftCof4Coeff1Row4Norm,kineticDriftCof4Coeff1Row5Norm,kineticDriftCof4Coeff1Row6Norm,kineticDriftCof4Coeff1Row7Norm,kineticDriftCof4Coeff2Row0Norm,kineticDriftCof4Coeff2Row1Norm,kineticDriftCof4Coeff2Row2Norm,kineticDriftCof4Coeff2Row3Norm,kineticDriftCof4Coeff2Row4Norm,kineticDriftCof4Coeff2Row5Norm,kineticDriftCof4Coeff2Row6Norm,kineticDriftCof4Coeff2Row7Norm,kineticDriftCof4Coeff3Row0Norm,kineticDriftCof4Coeff3Row1Norm,kineticDriftCof4Coeff3Row2Norm,kineticDriftCof4Coeff3Row3Norm,kineticDriftCof4Coeff3Row4Norm,kineticDriftCof4Coeff3Row5Norm,kineticDriftCof4Coeff3Row6Norm,kineticDriftCof4Coeff3Row7Norm,kineticDriftCof4Coeff4Row0Norm,kineticDriftCof4Coeff4Row1Norm,kineticDriftCof4Coeff4Row2Norm,kineticDriftCof4Coeff4Row3Norm,kineticDriftCof4Coeff4Row4Norm,kineticDriftCof4Coeff4Row5Norm,kineticDriftCof4Coeff4Row6Norm,kineticDriftCof4Coeff4Row7Norm,kineticDriftCof4Coeff5Row0Norm,kineticDriftCof4Coeff5Row1Norm,kineticDriftCof4Coeff5Row2Norm,kineticDriftCof4Coeff5Row3Norm,kineticDriftCof4Coeff5Row4Norm,kineticDriftCof4Coeff5Row5Norm,kineticDriftCof4Coeff5Row6Norm,kineticDriftCof4Coeff5Row7Norm,kineticDriftCof4Coeff6Row0Norm,kineticDriftCof4Coeff6Row1Norm,kineticDriftCof4Coeff6Row2Norm,kineticDriftCof4Coeff6Row3Norm,kineticDriftCof4Coeff6Row4Norm,kineticDriftCof4Coeff6Row5Norm,kineticDriftCof4Coeff6Row6Norm,kineticDriftCof4Coeff6Row7Norm,kineticDriftCof4Coeff7Row0Norm,kineticDriftCof4Coeff7Row1Norm,kineticDriftCof4Coeff7Row2Norm,kineticDriftCof4Coeff7Row3Norm,kineticDriftCof4Coeff7Row4Norm,kineticDriftCof4Coeff7Row5Norm,kineticDriftCof4Coeff7Row6Norm,kineticDriftCof4Coeff7Row7Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff1Row3Norm,kineticDriftBlock4Coeff2Row0Norm,kineticDriftBlock4Coeff2Row1Norm,kineticDriftBlock4Coeff2Row2Norm,kineticDriftBlock4Coeff2Row3Norm,kineticDriftBlock4Coeff3Row0Norm,kineticDriftBlock4Coeff3Row1Norm,kineticDriftBlock4Coeff3Row2Norm,kineticDriftBlock4Coeff3Row3Norm,kineticDriftBlock4Coeff4Row0Norm,kineticDriftBlock4Coeff4Row1Norm,kineticDriftBlock4Coeff4Row2Norm,kineticDriftBlock4Coeff4Row3Norm,kineticDriftBlock4Coeff5Row0Norm,kineticDriftBlock4Coeff5Row1Norm,kineticDriftBlock4Coeff5Row2Norm,kineticDriftBlock4Coeff5Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff7Row9Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 7 9=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 7 9=kineticDriftCell h (kineticCof6*kineticBlock6) 7 9 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftCof6Row3,kineticDriftCof6Row4,kineticDriftCof6Row5,kineticDriftCof6Row6,kineticDriftCof6Row7,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2,kineticDriftBlock6Row3,kineticDriftBlock6Row4,kineticDriftBlock6Row5,kineticDriftBlock6Row6,kineticDriftBlock6Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff0Row4Norm,kineticDriftCof6Coeff0Row5Norm,kineticDriftCof6Coeff0Row6Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff1Row3Norm,kineticDriftCof6Coeff1Row4Norm,kineticDriftCof6Coeff1Row5Norm,kineticDriftCof6Coeff1Row6Norm,kineticDriftCof6Coeff2Row0Norm,kineticDriftCof6Coeff2Row1Norm,kineticDriftCof6Coeff2Row2Norm,kineticDriftCof6Coeff2Row3Norm,kineticDriftCof6Coeff2Row4Norm,kineticDriftCof6Coeff2Row5Norm,kineticDriftCof6Coeff2Row6Norm,kineticDriftCof6Coeff3Row0Norm,kineticDriftCof6Coeff3Row1Norm,kineticDriftCof6Coeff3Row2Norm,kineticDriftCof6Coeff3Row3Norm,kineticDriftCof6Coeff3Row4Norm,kineticDriftCof6Coeff3Row5Norm,kineticDriftCof6Coeff3Row6Norm,kineticDriftCof6Coeff4Row0Norm,kineticDriftCof6Coeff4Row1Norm,kineticDriftCof6Coeff4Row2Norm,kineticDriftCof6Coeff4Row3Norm,kineticDriftCof6Coeff4Row4Norm,kineticDriftCof6Coeff4Row5Norm,kineticDriftCof6Coeff4Row6Norm,kineticDriftCof6Coeff5Row0Norm,kineticDriftCof6Coeff5Row1Norm,kineticDriftCof6Coeff5Row2Norm,kineticDriftCof6Coeff5Row3Norm,kineticDriftCof6Coeff5Row4Norm,kineticDriftCof6Coeff5Row5Norm,kineticDriftCof6Coeff5Row6Norm,kineticDriftCof6Coeff6Row0Norm,kineticDriftCof6Coeff6Row1Norm,kineticDriftCof6Coeff6Row2Norm,kineticDriftCof6Coeff6Row3Norm,kineticDriftCof6Coeff6Row4Norm,kineticDriftCof6Coeff6Row5Norm,kineticDriftCof6Coeff6Row6Norm,kineticDriftCof6Coeff7Row0Norm,kineticDriftCof6Coeff7Row1Norm,kineticDriftCof6Coeff7Row2Norm,kineticDriftCof6Coeff7Row3Norm,kineticDriftCof6Coeff7Row4Norm,kineticDriftCof6Coeff7Row5Norm,kineticDriftCof6Coeff7Row6Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff0Row4Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff1Row3Norm,kineticDriftBlock6Coeff1Row4Norm,kineticDriftBlock6Coeff2Row0Norm,kineticDriftBlock6Coeff2Row1Norm,kineticDriftBlock6Coeff2Row2Norm,kineticDriftBlock6Coeff2Row3Norm,kineticDriftBlock6Coeff2Row4Norm,kineticDriftBlock6Coeff3Row0Norm,kineticDriftBlock6Coeff3Row1Norm,kineticDriftBlock6Coeff3Row2Norm,kineticDriftBlock6Coeff3Row3Norm,kineticDriftBlock6Coeff3Row4Norm,kineticDriftBlock6Coeff4Row0Norm,kineticDriftBlock6Coeff4Row1Norm,kineticDriftBlock6Coeff4Row2Norm,kineticDriftBlock6Coeff4Row3Norm,kineticDriftBlock6Coeff4Row4Norm,kineticDriftBlock6Coeff5Row0Norm,kineticDriftBlock6Coeff5Row1Norm,kineticDriftBlock6Coeff5Row2Norm,kineticDriftBlock6Coeff5Row3Norm,kineticDriftBlock6Coeff5Row4Norm,kineticDriftBlock6Coeff6Row0Norm,kineticDriftBlock6Coeff6Row1Norm,kineticDriftBlock6Coeff6Row2Norm,kineticDriftBlock6Coeff6Row3Norm,kineticDriftBlock6Coeff6Row4Norm,kineticDriftBlock6Coeff7Row0Norm,kineticDriftBlock6Coeff7Row1Norm,kineticDriftBlock6Coeff7Row2Norm,kineticDriftBlock6Coeff7Row3Norm,kineticDriftBlock6Coeff7Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff7Row9Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 7 9=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 7 9=kineticDriftCell h (kineticCof8*kineticBlock8) 7 9 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftCof8Row3,kineticDriftCof8Row4,kineticDriftCof8Row5,kineticDriftCof8Row6,kineticDriftCof8Row7,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2,kineticDriftBlock8Row3,kineticDriftBlock8Row4,kineticDriftBlock8Row5,kineticDriftBlock8Row6,kineticDriftBlock8Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff0Row4Norm,kineticDriftCof8Coeff0Row5Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff1Row3Norm,kineticDriftCof8Coeff1Row4Norm,kineticDriftCof8Coeff1Row5Norm,kineticDriftCof8Coeff2Row0Norm,kineticDriftCof8Coeff2Row1Norm,kineticDriftCof8Coeff2Row2Norm,kineticDriftCof8Coeff2Row3Norm,kineticDriftCof8Coeff2Row4Norm,kineticDriftCof8Coeff2Row5Norm,kineticDriftCof8Coeff3Row0Norm,kineticDriftCof8Coeff3Row1Norm,kineticDriftCof8Coeff3Row2Norm,kineticDriftCof8Coeff3Row3Norm,kineticDriftCof8Coeff3Row4Norm,kineticDriftCof8Coeff3Row5Norm,kineticDriftCof8Coeff4Row0Norm,kineticDriftCof8Coeff4Row1Norm,kineticDriftCof8Coeff4Row2Norm,kineticDriftCof8Coeff4Row3Norm,kineticDriftCof8Coeff4Row4Norm,kineticDriftCof8Coeff4Row5Norm,kineticDriftCof8Coeff5Row0Norm,kineticDriftCof8Coeff5Row1Norm,kineticDriftCof8Coeff5Row2Norm,kineticDriftCof8Coeff5Row3Norm,kineticDriftCof8Coeff5Row4Norm,kineticDriftCof8Coeff5Row5Norm,kineticDriftCof8Coeff6Row0Norm,kineticDriftCof8Coeff6Row1Norm,kineticDriftCof8Coeff6Row2Norm,kineticDriftCof8Coeff6Row3Norm,kineticDriftCof8Coeff6Row4Norm,kineticDriftCof8Coeff6Row5Norm,kineticDriftCof8Coeff7Row0Norm,kineticDriftCof8Coeff7Row1Norm,kineticDriftCof8Coeff7Row2Norm,kineticDriftCof8Coeff7Row3Norm,kineticDriftCof8Coeff7Row4Norm,kineticDriftCof8Coeff7Row5Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff0Row4Norm,kineticDriftBlock8Coeff0Row5Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff1Row3Norm,kineticDriftBlock8Coeff1Row4Norm,kineticDriftBlock8Coeff1Row5Norm,kineticDriftBlock8Coeff2Row0Norm,kineticDriftBlock8Coeff2Row1Norm,kineticDriftBlock8Coeff2Row2Norm,kineticDriftBlock8Coeff2Row3Norm,kineticDriftBlock8Coeff2Row4Norm,kineticDriftBlock8Coeff2Row5Norm,kineticDriftBlock8Coeff3Row0Norm,kineticDriftBlock8Coeff3Row1Norm,kineticDriftBlock8Coeff3Row2Norm,kineticDriftBlock8Coeff3Row3Norm,kineticDriftBlock8Coeff3Row4Norm,kineticDriftBlock8Coeff3Row5Norm,kineticDriftBlock8Coeff4Row0Norm,kineticDriftBlock8Coeff4Row1Norm,kineticDriftBlock8Coeff4Row2Norm,kineticDriftBlock8Coeff4Row3Norm,kineticDriftBlock8Coeff4Row4Norm,kineticDriftBlock8Coeff4Row5Norm,kineticDriftBlock8Coeff5Row0Norm,kineticDriftBlock8Coeff5Row1Norm,kineticDriftBlock8Coeff5Row2Norm,kineticDriftBlock8Coeff5Row3Norm,kineticDriftBlock8Coeff5Row4Norm,kineticDriftBlock8Coeff5Row5Norm,kineticDriftBlock8Coeff6Row0Norm,kineticDriftBlock8Coeff6Row1Norm,kineticDriftBlock8Coeff6Row2Norm,kineticDriftBlock8Coeff6Row3Norm,kineticDriftBlock8Coeff6Row4Norm,kineticDriftBlock8Coeff6Row5Norm,kineticDriftBlock8Coeff7Row0Norm,kineticDriftBlock8Coeff7Row1Norm,kineticDriftBlock8Coeff7Row2Norm,kineticDriftBlock8Coeff7Row3Norm,kineticDriftBlock8Coeff7Row4Norm,kineticDriftBlock8Coeff7Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff7Row9Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 7 9=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 7 9=kineticDriftCell h (kineticCof10*kineticBlock10) 7 9 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftCof10Row3,kineticDriftCof10Row4,kineticDriftCof10Row5,kineticDriftCof10Row6,kineticDriftCof10Row7,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2,kineticDriftBlock10Row3,kineticDriftBlock10Row4,kineticDriftBlock10Row5,kineticDriftBlock10Row6,kineticDriftBlock10Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff0Row4Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff1Row3Norm,kineticDriftCof10Coeff1Row4Norm,kineticDriftCof10Coeff2Row0Norm,kineticDriftCof10Coeff2Row1Norm,kineticDriftCof10Coeff2Row2Norm,kineticDriftCof10Coeff2Row3Norm,kineticDriftCof10Coeff2Row4Norm,kineticDriftCof10Coeff3Row0Norm,kineticDriftCof10Coeff3Row1Norm,kineticDriftCof10Coeff3Row2Norm,kineticDriftCof10Coeff3Row3Norm,kineticDriftCof10Coeff3Row4Norm,kineticDriftCof10Coeff4Row0Norm,kineticDriftCof10Coeff4Row1Norm,kineticDriftCof10Coeff4Row2Norm,kineticDriftCof10Coeff4Row3Norm,kineticDriftCof10Coeff4Row4Norm,kineticDriftCof10Coeff5Row0Norm,kineticDriftCof10Coeff5Row1Norm,kineticDriftCof10Coeff5Row2Norm,kineticDriftCof10Coeff5Row3Norm,kineticDriftCof10Coeff5Row4Norm,kineticDriftCof10Coeff6Row0Norm,kineticDriftCof10Coeff6Row1Norm,kineticDriftCof10Coeff6Row2Norm,kineticDriftCof10Coeff6Row3Norm,kineticDriftCof10Coeff6Row4Norm,kineticDriftCof10Coeff7Row0Norm,kineticDriftCof10Coeff7Row1Norm,kineticDriftCof10Coeff7Row2Norm,kineticDriftCof10Coeff7Row3Norm,kineticDriftCof10Coeff7Row4Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff0Row4Norm,kineticDriftBlock10Coeff0Row5Norm,kineticDriftBlock10Coeff0Row6Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff1Row3Norm,kineticDriftBlock10Coeff1Row4Norm,kineticDriftBlock10Coeff1Row5Norm,kineticDriftBlock10Coeff1Row6Norm,kineticDriftBlock10Coeff2Row0Norm,kineticDriftBlock10Coeff2Row1Norm,kineticDriftBlock10Coeff2Row2Norm,kineticDriftBlock10Coeff2Row3Norm,kineticDriftBlock10Coeff2Row4Norm,kineticDriftBlock10Coeff2Row5Norm,kineticDriftBlock10Coeff2Row6Norm,kineticDriftBlock10Coeff3Row0Norm,kineticDriftBlock10Coeff3Row1Norm,kineticDriftBlock10Coeff3Row2Norm,kineticDriftBlock10Coeff3Row3Norm,kineticDriftBlock10Coeff3Row4Norm,kineticDriftBlock10Coeff3Row5Norm,kineticDriftBlock10Coeff3Row6Norm,kineticDriftBlock10Coeff4Row0Norm,kineticDriftBlock10Coeff4Row1Norm,kineticDriftBlock10Coeff4Row2Norm,kineticDriftBlock10Coeff4Row3Norm,kineticDriftBlock10Coeff4Row4Norm,kineticDriftBlock10Coeff4Row5Norm,kineticDriftBlock10Coeff4Row6Norm,kineticDriftBlock10Coeff5Row0Norm,kineticDriftBlock10Coeff5Row1Norm,kineticDriftBlock10Coeff5Row2Norm,kineticDriftBlock10Coeff5Row3Norm,kineticDriftBlock10Coeff5Row4Norm,kineticDriftBlock10Coeff5Row5Norm,kineticDriftBlock10Coeff5Row6Norm,kineticDriftBlock10Coeff6Row0Norm,kineticDriftBlock10Coeff6Row1Norm,kineticDriftBlock10Coeff6Row2Norm,kineticDriftBlock10Coeff6Row3Norm,kineticDriftBlock10Coeff6Row4Norm,kineticDriftBlock10Coeff6Row5Norm,kineticDriftBlock10Coeff6Row6Norm,kineticDriftBlock10Coeff7Row0Norm,kineticDriftBlock10Coeff7Row1Norm,kineticDriftBlock10Coeff7Row2Norm,kineticDriftBlock10Coeff7Row3Norm,kineticDriftBlock10Coeff7Row4Norm,kineticDriftBlock10Coeff7Row5Norm,kineticDriftBlock10Coeff7Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff7Row10Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 7 10=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 7 10=kineticDriftCell h (kineticCof2*kineticBlock2) 7 10 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftCof2Row3,kineticDriftCof2Row4,kineticDriftCof2Row5,kineticDriftCof2Row6,kineticDriftCof2Row7,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2,kineticDriftBlock2Row3]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm,kineticDriftCof2Coeff0Row4Norm,kineticDriftCof2Coeff0Row5Norm,kineticDriftCof2Coeff0Row6Norm,kineticDriftCof2Coeff0Row7Norm,kineticDriftCof2Coeff0Row8Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff1Row3Norm,kineticDriftCof2Coeff1Row4Norm,kineticDriftCof2Coeff1Row5Norm,kineticDriftCof2Coeff1Row6Norm,kineticDriftCof2Coeff1Row7Norm,kineticDriftCof2Coeff1Row8Norm,kineticDriftCof2Coeff2Row0Norm,kineticDriftCof2Coeff2Row1Norm,kineticDriftCof2Coeff2Row2Norm,kineticDriftCof2Coeff2Row3Norm,kineticDriftCof2Coeff2Row4Norm,kineticDriftCof2Coeff2Row5Norm,kineticDriftCof2Coeff2Row6Norm,kineticDriftCof2Coeff2Row7Norm,kineticDriftCof2Coeff2Row8Norm,kineticDriftCof2Coeff3Row0Norm,kineticDriftCof2Coeff3Row1Norm,kineticDriftCof2Coeff3Row2Norm,kineticDriftCof2Coeff3Row3Norm,kineticDriftCof2Coeff3Row4Norm,kineticDriftCof2Coeff3Row5Norm,kineticDriftCof2Coeff3Row6Norm,kineticDriftCof2Coeff3Row7Norm,kineticDriftCof2Coeff3Row8Norm,kineticDriftCof2Coeff4Row0Norm,kineticDriftCof2Coeff4Row1Norm,kineticDriftCof2Coeff4Row2Norm,kineticDriftCof2Coeff4Row3Norm,kineticDriftCof2Coeff4Row4Norm,kineticDriftCof2Coeff4Row5Norm,kineticDriftCof2Coeff4Row6Norm,kineticDriftCof2Coeff4Row7Norm,kineticDriftCof2Coeff4Row8Norm,kineticDriftCof2Coeff5Row0Norm,kineticDriftCof2Coeff5Row1Norm,kineticDriftCof2Coeff5Row2Norm,kineticDriftCof2Coeff5Row3Norm,kineticDriftCof2Coeff5Row4Norm,kineticDriftCof2Coeff5Row5Norm,kineticDriftCof2Coeff5Row6Norm,kineticDriftCof2Coeff5Row7Norm,kineticDriftCof2Coeff5Row8Norm,kineticDriftCof2Coeff6Row0Norm,kineticDriftCof2Coeff6Row1Norm,kineticDriftCof2Coeff6Row2Norm,kineticDriftCof2Coeff6Row3Norm,kineticDriftCof2Coeff6Row4Norm,kineticDriftCof2Coeff6Row5Norm,kineticDriftCof2Coeff6Row6Norm,kineticDriftCof2Coeff6Row7Norm,kineticDriftCof2Coeff6Row8Norm,kineticDriftCof2Coeff7Row0Norm,kineticDriftCof2Coeff7Row1Norm,kineticDriftCof2Coeff7Row2Norm,kineticDriftCof2Coeff7Row3Norm,kineticDriftCof2Coeff7Row4Norm,kineticDriftCof2Coeff7Row5Norm,kineticDriftCof2Coeff7Row6Norm,kineticDriftCof2Coeff7Row7Norm,kineticDriftCof2Coeff7Row8Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm,kineticDriftBlock2Coeff2Row0Norm,kineticDriftBlock2Coeff2Row1Norm,kineticDriftBlock2Coeff2Row2Norm,kineticDriftBlock2Coeff3Row0Norm,kineticDriftBlock2Coeff3Row1Norm,kineticDriftBlock2Coeff3Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff7Row10Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 7 10=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 7 10=kineticDriftCell h (kineticCof4*kineticBlock4) 7 10 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftCof4Row3,kineticDriftCof4Row4,kineticDriftCof4Row5,kineticDriftCof4Row6,kineticDriftCof4Row7,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2,kineticDriftBlock4Row3,kineticDriftBlock4Row4,kineticDriftBlock4Row5]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff0Row4Norm,kineticDriftCof4Coeff0Row5Norm,kineticDriftCof4Coeff0Row6Norm,kineticDriftCof4Coeff0Row7Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff1Row3Norm,kineticDriftCof4Coeff1Row4Norm,kineticDriftCof4Coeff1Row5Norm,kineticDriftCof4Coeff1Row6Norm,kineticDriftCof4Coeff1Row7Norm,kineticDriftCof4Coeff2Row0Norm,kineticDriftCof4Coeff2Row1Norm,kineticDriftCof4Coeff2Row2Norm,kineticDriftCof4Coeff2Row3Norm,kineticDriftCof4Coeff2Row4Norm,kineticDriftCof4Coeff2Row5Norm,kineticDriftCof4Coeff2Row6Norm,kineticDriftCof4Coeff2Row7Norm,kineticDriftCof4Coeff3Row0Norm,kineticDriftCof4Coeff3Row1Norm,kineticDriftCof4Coeff3Row2Norm,kineticDriftCof4Coeff3Row3Norm,kineticDriftCof4Coeff3Row4Norm,kineticDriftCof4Coeff3Row5Norm,kineticDriftCof4Coeff3Row6Norm,kineticDriftCof4Coeff3Row7Norm,kineticDriftCof4Coeff4Row0Norm,kineticDriftCof4Coeff4Row1Norm,kineticDriftCof4Coeff4Row2Norm,kineticDriftCof4Coeff4Row3Norm,kineticDriftCof4Coeff4Row4Norm,kineticDriftCof4Coeff4Row5Norm,kineticDriftCof4Coeff4Row6Norm,kineticDriftCof4Coeff4Row7Norm,kineticDriftCof4Coeff5Row0Norm,kineticDriftCof4Coeff5Row1Norm,kineticDriftCof4Coeff5Row2Norm,kineticDriftCof4Coeff5Row3Norm,kineticDriftCof4Coeff5Row4Norm,kineticDriftCof4Coeff5Row5Norm,kineticDriftCof4Coeff5Row6Norm,kineticDriftCof4Coeff5Row7Norm,kineticDriftCof4Coeff6Row0Norm,kineticDriftCof4Coeff6Row1Norm,kineticDriftCof4Coeff6Row2Norm,kineticDriftCof4Coeff6Row3Norm,kineticDriftCof4Coeff6Row4Norm,kineticDriftCof4Coeff6Row5Norm,kineticDriftCof4Coeff6Row6Norm,kineticDriftCof4Coeff6Row7Norm,kineticDriftCof4Coeff7Row0Norm,kineticDriftCof4Coeff7Row1Norm,kineticDriftCof4Coeff7Row2Norm,kineticDriftCof4Coeff7Row3Norm,kineticDriftCof4Coeff7Row4Norm,kineticDriftCof4Coeff7Row5Norm,kineticDriftCof4Coeff7Row6Norm,kineticDriftCof4Coeff7Row7Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff1Row3Norm,kineticDriftBlock4Coeff2Row0Norm,kineticDriftBlock4Coeff2Row1Norm,kineticDriftBlock4Coeff2Row2Norm,kineticDriftBlock4Coeff2Row3Norm,kineticDriftBlock4Coeff3Row0Norm,kineticDriftBlock4Coeff3Row1Norm,kineticDriftBlock4Coeff3Row2Norm,kineticDriftBlock4Coeff3Row3Norm,kineticDriftBlock4Coeff4Row0Norm,kineticDriftBlock4Coeff4Row1Norm,kineticDriftBlock4Coeff4Row2Norm,kineticDriftBlock4Coeff4Row3Norm,kineticDriftBlock4Coeff5Row0Norm,kineticDriftBlock4Coeff5Row1Norm,kineticDriftBlock4Coeff5Row2Norm,kineticDriftBlock4Coeff5Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff7Row10Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 7 10=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 7 10=kineticDriftCell h (kineticCof6*kineticBlock6) 7 10 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftCof6Row3,kineticDriftCof6Row4,kineticDriftCof6Row5,kineticDriftCof6Row6,kineticDriftCof6Row7,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2,kineticDriftBlock6Row3,kineticDriftBlock6Row4,kineticDriftBlock6Row5,kineticDriftBlock6Row6,kineticDriftBlock6Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff0Row4Norm,kineticDriftCof6Coeff0Row5Norm,kineticDriftCof6Coeff0Row6Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff1Row3Norm,kineticDriftCof6Coeff1Row4Norm,kineticDriftCof6Coeff1Row5Norm,kineticDriftCof6Coeff1Row6Norm,kineticDriftCof6Coeff2Row0Norm,kineticDriftCof6Coeff2Row1Norm,kineticDriftCof6Coeff2Row2Norm,kineticDriftCof6Coeff2Row3Norm,kineticDriftCof6Coeff2Row4Norm,kineticDriftCof6Coeff2Row5Norm,kineticDriftCof6Coeff2Row6Norm,kineticDriftCof6Coeff3Row0Norm,kineticDriftCof6Coeff3Row1Norm,kineticDriftCof6Coeff3Row2Norm,kineticDriftCof6Coeff3Row3Norm,kineticDriftCof6Coeff3Row4Norm,kineticDriftCof6Coeff3Row5Norm,kineticDriftCof6Coeff3Row6Norm,kineticDriftCof6Coeff4Row0Norm,kineticDriftCof6Coeff4Row1Norm,kineticDriftCof6Coeff4Row2Norm,kineticDriftCof6Coeff4Row3Norm,kineticDriftCof6Coeff4Row4Norm,kineticDriftCof6Coeff4Row5Norm,kineticDriftCof6Coeff4Row6Norm,kineticDriftCof6Coeff5Row0Norm,kineticDriftCof6Coeff5Row1Norm,kineticDriftCof6Coeff5Row2Norm,kineticDriftCof6Coeff5Row3Norm,kineticDriftCof6Coeff5Row4Norm,kineticDriftCof6Coeff5Row5Norm,kineticDriftCof6Coeff5Row6Norm,kineticDriftCof6Coeff6Row0Norm,kineticDriftCof6Coeff6Row1Norm,kineticDriftCof6Coeff6Row2Norm,kineticDriftCof6Coeff6Row3Norm,kineticDriftCof6Coeff6Row4Norm,kineticDriftCof6Coeff6Row5Norm,kineticDriftCof6Coeff6Row6Norm,kineticDriftCof6Coeff7Row0Norm,kineticDriftCof6Coeff7Row1Norm,kineticDriftCof6Coeff7Row2Norm,kineticDriftCof6Coeff7Row3Norm,kineticDriftCof6Coeff7Row4Norm,kineticDriftCof6Coeff7Row5Norm,kineticDriftCof6Coeff7Row6Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff0Row4Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff1Row3Norm,kineticDriftBlock6Coeff1Row4Norm,kineticDriftBlock6Coeff2Row0Norm,kineticDriftBlock6Coeff2Row1Norm,kineticDriftBlock6Coeff2Row2Norm,kineticDriftBlock6Coeff2Row3Norm,kineticDriftBlock6Coeff2Row4Norm,kineticDriftBlock6Coeff3Row0Norm,kineticDriftBlock6Coeff3Row1Norm,kineticDriftBlock6Coeff3Row2Norm,kineticDriftBlock6Coeff3Row3Norm,kineticDriftBlock6Coeff3Row4Norm,kineticDriftBlock6Coeff4Row0Norm,kineticDriftBlock6Coeff4Row1Norm,kineticDriftBlock6Coeff4Row2Norm,kineticDriftBlock6Coeff4Row3Norm,kineticDriftBlock6Coeff4Row4Norm,kineticDriftBlock6Coeff5Row0Norm,kineticDriftBlock6Coeff5Row1Norm,kineticDriftBlock6Coeff5Row2Norm,kineticDriftBlock6Coeff5Row3Norm,kineticDriftBlock6Coeff5Row4Norm,kineticDriftBlock6Coeff6Row0Norm,kineticDriftBlock6Coeff6Row1Norm,kineticDriftBlock6Coeff6Row2Norm,kineticDriftBlock6Coeff6Row3Norm,kineticDriftBlock6Coeff6Row4Norm,kineticDriftBlock6Coeff7Row0Norm,kineticDriftBlock6Coeff7Row1Norm,kineticDriftBlock6Coeff7Row2Norm,kineticDriftBlock6Coeff7Row3Norm,kineticDriftBlock6Coeff7Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff7Row10Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 7 10=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 7 10=kineticDriftCell h (kineticCof8*kineticBlock8) 7 10 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftCof8Row3,kineticDriftCof8Row4,kineticDriftCof8Row5,kineticDriftCof8Row6,kineticDriftCof8Row7,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2,kineticDriftBlock8Row3,kineticDriftBlock8Row4,kineticDriftBlock8Row5,kineticDriftBlock8Row6,kineticDriftBlock8Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff0Row4Norm,kineticDriftCof8Coeff0Row5Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff1Row3Norm,kineticDriftCof8Coeff1Row4Norm,kineticDriftCof8Coeff1Row5Norm,kineticDriftCof8Coeff2Row0Norm,kineticDriftCof8Coeff2Row1Norm,kineticDriftCof8Coeff2Row2Norm,kineticDriftCof8Coeff2Row3Norm,kineticDriftCof8Coeff2Row4Norm,kineticDriftCof8Coeff2Row5Norm,kineticDriftCof8Coeff3Row0Norm,kineticDriftCof8Coeff3Row1Norm,kineticDriftCof8Coeff3Row2Norm,kineticDriftCof8Coeff3Row3Norm,kineticDriftCof8Coeff3Row4Norm,kineticDriftCof8Coeff3Row5Norm,kineticDriftCof8Coeff4Row0Norm,kineticDriftCof8Coeff4Row1Norm,kineticDriftCof8Coeff4Row2Norm,kineticDriftCof8Coeff4Row3Norm,kineticDriftCof8Coeff4Row4Norm,kineticDriftCof8Coeff4Row5Norm,kineticDriftCof8Coeff5Row0Norm,kineticDriftCof8Coeff5Row1Norm,kineticDriftCof8Coeff5Row2Norm,kineticDriftCof8Coeff5Row3Norm,kineticDriftCof8Coeff5Row4Norm,kineticDriftCof8Coeff5Row5Norm,kineticDriftCof8Coeff6Row0Norm,kineticDriftCof8Coeff6Row1Norm,kineticDriftCof8Coeff6Row2Norm,kineticDriftCof8Coeff6Row3Norm,kineticDriftCof8Coeff6Row4Norm,kineticDriftCof8Coeff6Row5Norm,kineticDriftCof8Coeff7Row0Norm,kineticDriftCof8Coeff7Row1Norm,kineticDriftCof8Coeff7Row2Norm,kineticDriftCof8Coeff7Row3Norm,kineticDriftCof8Coeff7Row4Norm,kineticDriftCof8Coeff7Row5Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff0Row4Norm,kineticDriftBlock8Coeff0Row5Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff1Row3Norm,kineticDriftBlock8Coeff1Row4Norm,kineticDriftBlock8Coeff1Row5Norm,kineticDriftBlock8Coeff2Row0Norm,kineticDriftBlock8Coeff2Row1Norm,kineticDriftBlock8Coeff2Row2Norm,kineticDriftBlock8Coeff2Row3Norm,kineticDriftBlock8Coeff2Row4Norm,kineticDriftBlock8Coeff2Row5Norm,kineticDriftBlock8Coeff3Row0Norm,kineticDriftBlock8Coeff3Row1Norm,kineticDriftBlock8Coeff3Row2Norm,kineticDriftBlock8Coeff3Row3Norm,kineticDriftBlock8Coeff3Row4Norm,kineticDriftBlock8Coeff3Row5Norm,kineticDriftBlock8Coeff4Row0Norm,kineticDriftBlock8Coeff4Row1Norm,kineticDriftBlock8Coeff4Row2Norm,kineticDriftBlock8Coeff4Row3Norm,kineticDriftBlock8Coeff4Row4Norm,kineticDriftBlock8Coeff4Row5Norm,kineticDriftBlock8Coeff5Row0Norm,kineticDriftBlock8Coeff5Row1Norm,kineticDriftBlock8Coeff5Row2Norm,kineticDriftBlock8Coeff5Row3Norm,kineticDriftBlock8Coeff5Row4Norm,kineticDriftBlock8Coeff5Row5Norm,kineticDriftBlock8Coeff6Row0Norm,kineticDriftBlock8Coeff6Row1Norm,kineticDriftBlock8Coeff6Row2Norm,kineticDriftBlock8Coeff6Row3Norm,kineticDriftBlock8Coeff6Row4Norm,kineticDriftBlock8Coeff6Row5Norm,kineticDriftBlock8Coeff7Row0Norm,kineticDriftBlock8Coeff7Row1Norm,kineticDriftBlock8Coeff7Row2Norm,kineticDriftBlock8Coeff7Row3Norm,kineticDriftBlock8Coeff7Row4Norm,kineticDriftBlock8Coeff7Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff7Row10Norm (h : ℂ) :
    {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 7 10=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 7 10=kineticDriftCell h (kineticCof10*kineticBlock10) 7 10 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftCof10Row3,kineticDriftCof10Row4,kineticDriftCof10Row5,kineticDriftCof10Row6,kineticDriftCof10Row7,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2,kineticDriftBlock10Row3,kineticDriftBlock10Row4,kineticDriftBlock10Row5,kineticDriftBlock10Row6,kineticDriftBlock10Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff0Row4Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff1Row3Norm,kineticDriftCof10Coeff1Row4Norm,kineticDriftCof10Coeff2Row0Norm,kineticDriftCof10Coeff2Row1Norm,kineticDriftCof10Coeff2Row2Norm,kineticDriftCof10Coeff2Row3Norm,kineticDriftCof10Coeff2Row4Norm,kineticDriftCof10Coeff3Row0Norm,kineticDriftCof10Coeff3Row1Norm,kineticDriftCof10Coeff3Row2Norm,kineticDriftCof10Coeff3Row3Norm,kineticDriftCof10Coeff3Row4Norm,kineticDriftCof10Coeff4Row0Norm,kineticDriftCof10Coeff4Row1Norm,kineticDriftCof10Coeff4Row2Norm,kineticDriftCof10Coeff4Row3Norm,kineticDriftCof10Coeff4Row4Norm,kineticDriftCof10Coeff5Row0Norm,kineticDriftCof10Coeff5Row1Norm,kineticDriftCof10Coeff5Row2Norm,kineticDriftCof10Coeff5Row3Norm,kineticDriftCof10Coeff5Row4Norm,kineticDriftCof10Coeff6Row0Norm,kineticDriftCof10Coeff6Row1Norm,kineticDriftCof10Coeff6Row2Norm,kineticDriftCof10Coeff6Row3Norm,kineticDriftCof10Coeff6Row4Norm,kineticDriftCof10Coeff7Row0Norm,kineticDriftCof10Coeff7Row1Norm,kineticDriftCof10Coeff7Row2Norm,kineticDriftCof10Coeff7Row3Norm,kineticDriftCof10Coeff7Row4Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff0Row4Norm,kineticDriftBlock10Coeff0Row5Norm,kineticDriftBlock10Coeff0Row6Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff1Row3Norm,kineticDriftBlock10Coeff1Row4Norm,kineticDriftBlock10Coeff1Row5Norm,kineticDriftBlock10Coeff1Row6Norm,kineticDriftBlock10Coeff2Row0Norm,kineticDriftBlock10Coeff2Row1Norm,kineticDriftBlock10Coeff2Row2Norm,kineticDriftBlock10Coeff2Row3Norm,kineticDriftBlock10Coeff2Row4Norm,kineticDriftBlock10Coeff2Row5Norm,kineticDriftBlock10Coeff2Row6Norm,kineticDriftBlock10Coeff3Row0Norm,kineticDriftBlock10Coeff3Row1Norm,kineticDriftBlock10Coeff3Row2Norm,kineticDriftBlock10Coeff3Row3Norm,kineticDriftBlock10Coeff3Row4Norm,kineticDriftBlock10Coeff3Row5Norm,kineticDriftBlock10Coeff3Row6Norm,kineticDriftBlock10Coeff4Row0Norm,kineticDriftBlock10Coeff4Row1Norm,kineticDriftBlock10Coeff4Row2Norm,kineticDriftBlock10Coeff4Row3Norm,kineticDriftBlock10Coeff4Row4Norm,kineticDriftBlock10Coeff4Row5Norm,kineticDriftBlock10Coeff4Row6Norm,kineticDriftBlock10Coeff5Row0Norm,kineticDriftBlock10Coeff5Row1Norm,kineticDriftBlock10Coeff5Row2Norm,kineticDriftBlock10Coeff5Row3Norm,kineticDriftBlock10Coeff5Row4Norm,kineticDriftBlock10Coeff5Row5Norm,kineticDriftBlock10Coeff5Row6Norm,kineticDriftBlock10Coeff6Row0Norm,kineticDriftBlock10Coeff6Row1Norm,kineticDriftBlock10Coeff6Row2Norm,kineticDriftBlock10Coeff6Row3Norm,kineticDriftBlock10Coeff6Row4Norm,kineticDriftBlock10Coeff6Row5Norm,kineticDriftBlock10Coeff6Row6Norm,kineticDriftBlock10Coeff7Row0Norm,kineticDriftBlock10Coeff7Row1Norm,kineticDriftBlock10Coeff7Row2Norm,kineticDriftBlock10Coeff7Row3Norm,kineticDriftBlock10Coeff7Row4Norm,kineticDriftBlock10Coeff7Row5Norm,kineticDriftBlock10Coeff7Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

end
end HTGeometry.ThetaRatioKineticContraction

