import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticFirstSourceReal
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

def kineticSourcePart2Coeff1Row1Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 1 1=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 1 1=kineticDriftCell h (kineticCof2*kineticBlock2) 1 1 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftBlock2Row0,kineticDriftBlock2Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff1Row1Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 1 1=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 1 1=kineticDriftCell h (kineticCof4*kineticBlock4) 1 1 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftBlock4Row0,kineticDriftBlock4Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff1Row1Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 1 1=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 1 1=kineticDriftCell h (kineticCof6*kineticBlock6) 1 1 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftBlock6Row0,kineticDriftBlock6Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff1Row1Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 1 1=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 1 1=kineticDriftCell h (kineticCof8*kineticBlock8) 1 1 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftBlock8Row0,kineticDriftBlock8Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff1Row1Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 1 1=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 1 1=kineticDriftCell h (kineticCof10*kineticBlock10) 1 1 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftBlock10Row0,kineticDriftBlock10Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff1Row2Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 1 2=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 1 2=kineticDriftCell h (kineticCof2*kineticBlock2) 1 2 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftBlock2Row0,kineticDriftBlock2Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff1Row2Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 1 2=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 1 2=kineticDriftCell h (kineticCof4*kineticBlock4) 1 2 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftBlock4Row0,kineticDriftBlock4Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff1Row2Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 1 2=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 1 2=kineticDriftCell h (kineticCof6*kineticBlock6) 1 2 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftBlock6Row0,kineticDriftBlock6Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff1Row2Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 1 2=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 1 2=kineticDriftCell h (kineticCof8*kineticBlock8) 1 2 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftBlock8Row0,kineticDriftBlock8Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff1Row2Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 1 2=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 1 2=kineticDriftCell h (kineticCof10*kineticBlock10) 1 2 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftBlock10Row0,kineticDriftBlock10Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff1Row3Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 1 3=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 1 3=kineticDriftCell h (kineticCof2*kineticBlock2) 1 3 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftBlock2Row0,kineticDriftBlock2Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff1Row3Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff1Row3Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 1 3=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 1 3=kineticDriftCell h (kineticCof4*kineticBlock4) 1 3 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftBlock4Row0,kineticDriftBlock4Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff1Row3Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff1Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff1Row3Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 1 3=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 1 3=kineticDriftCell h (kineticCof6*kineticBlock6) 1 3 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftBlock6Row0,kineticDriftBlock6Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff1Row3Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff1Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff1Row3Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 1 3=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 1 3=kineticDriftCell h (kineticCof8*kineticBlock8) 1 3 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftBlock8Row0,kineticDriftBlock8Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff1Row3Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff1Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff1Row3Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 1 3=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 1 3=kineticDriftCell h (kineticCof10*kineticBlock10) 1 3 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftBlock10Row0,kineticDriftBlock10Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff1Row3Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff1Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff1Row4Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 1 4=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 1 4=kineticDriftCell h (kineticCof2*kineticBlock2) 1 4 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftBlock2Row0,kineticDriftBlock2Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm,kineticDriftCof2Coeff0Row4Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff1Row3Norm,kineticDriftCof2Coeff1Row4Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff1Row4Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 1 4=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 1 4=kineticDriftCell h (kineticCof4*kineticBlock4) 1 4 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftBlock4Row0,kineticDriftBlock4Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff0Row4Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff1Row3Norm,kineticDriftCof4Coeff1Row4Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff1Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff1Row4Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 1 4=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 1 4=kineticDriftCell h (kineticCof6*kineticBlock6) 1 4 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftBlock6Row0,kineticDriftBlock6Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff0Row4Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff1Row3Norm,kineticDriftCof6Coeff1Row4Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff0Row4Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff1Row3Norm,kineticDriftBlock6Coeff1Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff1Row4Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 1 4=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 1 4=kineticDriftCell h (kineticCof8*kineticBlock8) 1 4 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftBlock8Row0,kineticDriftBlock8Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff0Row4Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff1Row3Norm,kineticDriftCof8Coeff1Row4Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff0Row4Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff1Row3Norm,kineticDriftBlock8Coeff1Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff1Row4Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 1 4=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 1 4=kineticDriftCell h (kineticCof10*kineticBlock10) 1 4 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftBlock10Row0,kineticDriftBlock10Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff0Row4Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff1Row3Norm,kineticDriftCof10Coeff1Row4Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff0Row4Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff1Row3Norm,kineticDriftBlock10Coeff1Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff1Row5Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 1 5=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 1 5=kineticDriftCell h (kineticCof2*kineticBlock2) 1 5 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftBlock2Row0,kineticDriftBlock2Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm,kineticDriftCof2Coeff0Row4Norm,kineticDriftCof2Coeff0Row5Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff1Row3Norm,kineticDriftCof2Coeff1Row4Norm,kineticDriftCof2Coeff1Row5Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff1Row5Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 1 5=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 1 5=kineticDriftCell h (kineticCof4*kineticBlock4) 1 5 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftBlock4Row0,kineticDriftBlock4Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff0Row4Norm,kineticDriftCof4Coeff0Row5Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff1Row3Norm,kineticDriftCof4Coeff1Row4Norm,kineticDriftCof4Coeff1Row5Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff1Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff1Row5Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 1 5=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 1 5=kineticDriftCell h (kineticCof6*kineticBlock6) 1 5 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftBlock6Row0,kineticDriftBlock6Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff0Row4Norm,kineticDriftCof6Coeff0Row5Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff1Row3Norm,kineticDriftCof6Coeff1Row4Norm,kineticDriftCof6Coeff1Row5Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff0Row4Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff1Row3Norm,kineticDriftBlock6Coeff1Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff1Row5Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 1 5=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 1 5=kineticDriftCell h (kineticCof8*kineticBlock8) 1 5 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftBlock8Row0,kineticDriftBlock8Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff0Row4Norm,kineticDriftCof8Coeff0Row5Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff1Row3Norm,kineticDriftCof8Coeff1Row4Norm,kineticDriftCof8Coeff1Row5Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff0Row4Norm,kineticDriftBlock8Coeff0Row5Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff1Row3Norm,kineticDriftBlock8Coeff1Row4Norm,kineticDriftBlock8Coeff1Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff1Row5Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 1 5=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 1 5=kineticDriftCell h (kineticCof10*kineticBlock10) 1 5 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftBlock10Row0,kineticDriftBlock10Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff0Row4Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff1Row3Norm,kineticDriftCof10Coeff1Row4Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff0Row4Norm,kineticDriftBlock10Coeff0Row5Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff1Row3Norm,kineticDriftBlock10Coeff1Row4Norm,kineticDriftBlock10Coeff1Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff1Row6Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 1 6=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 1 6=kineticDriftCell h (kineticCof2*kineticBlock2) 1 6 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftBlock2Row0,kineticDriftBlock2Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm,kineticDriftCof2Coeff0Row4Norm,kineticDriftCof2Coeff0Row5Norm,kineticDriftCof2Coeff0Row6Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff1Row3Norm,kineticDriftCof2Coeff1Row4Norm,kineticDriftCof2Coeff1Row5Norm,kineticDriftCof2Coeff1Row6Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff1Row6Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 1 6=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 1 6=kineticDriftCell h (kineticCof4*kineticBlock4) 1 6 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftBlock4Row0,kineticDriftBlock4Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff0Row4Norm,kineticDriftCof4Coeff0Row5Norm,kineticDriftCof4Coeff0Row6Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff1Row3Norm,kineticDriftCof4Coeff1Row4Norm,kineticDriftCof4Coeff1Row5Norm,kineticDriftCof4Coeff1Row6Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff1Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff1Row6Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 1 6=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 1 6=kineticDriftCell h (kineticCof6*kineticBlock6) 1 6 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftBlock6Row0,kineticDriftBlock6Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff0Row4Norm,kineticDriftCof6Coeff0Row5Norm,kineticDriftCof6Coeff0Row6Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff1Row3Norm,kineticDriftCof6Coeff1Row4Norm,kineticDriftCof6Coeff1Row5Norm,kineticDriftCof6Coeff1Row6Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff0Row4Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff1Row3Norm,kineticDriftBlock6Coeff1Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff1Row6Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 1 6=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 1 6=kineticDriftCell h (kineticCof8*kineticBlock8) 1 6 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftBlock8Row0,kineticDriftBlock8Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff0Row4Norm,kineticDriftCof8Coeff0Row5Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff1Row3Norm,kineticDriftCof8Coeff1Row4Norm,kineticDriftCof8Coeff1Row5Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff0Row4Norm,kineticDriftBlock8Coeff0Row5Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff1Row3Norm,kineticDriftBlock8Coeff1Row4Norm,kineticDriftBlock8Coeff1Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff1Row6Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 1 6=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 1 6=kineticDriftCell h (kineticCof10*kineticBlock10) 1 6 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftBlock10Row0,kineticDriftBlock10Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff0Row4Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff1Row3Norm,kineticDriftCof10Coeff1Row4Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff0Row4Norm,kineticDriftBlock10Coeff0Row5Norm,kineticDriftBlock10Coeff0Row6Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff1Row3Norm,kineticDriftBlock10Coeff1Row4Norm,kineticDriftBlock10Coeff1Row5Norm,kineticDriftBlock10Coeff1Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff1Row7Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 1 7=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 1 7=kineticDriftCell h (kineticCof2*kineticBlock2) 1 7 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftBlock2Row0,kineticDriftBlock2Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm,kineticDriftCof2Coeff0Row4Norm,kineticDriftCof2Coeff0Row5Norm,kineticDriftCof2Coeff0Row6Norm,kineticDriftCof2Coeff0Row7Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff1Row3Norm,kineticDriftCof2Coeff1Row4Norm,kineticDriftCof2Coeff1Row5Norm,kineticDriftCof2Coeff1Row6Norm,kineticDriftCof2Coeff1Row7Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff1Row7Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 1 7=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 1 7=kineticDriftCell h (kineticCof4*kineticBlock4) 1 7 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftBlock4Row0,kineticDriftBlock4Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff0Row4Norm,kineticDriftCof4Coeff0Row5Norm,kineticDriftCof4Coeff0Row6Norm,kineticDriftCof4Coeff0Row7Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff1Row3Norm,kineticDriftCof4Coeff1Row4Norm,kineticDriftCof4Coeff1Row5Norm,kineticDriftCof4Coeff1Row6Norm,kineticDriftCof4Coeff1Row7Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff1Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff1Row7Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 1 7=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 1 7=kineticDriftCell h (kineticCof6*kineticBlock6) 1 7 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftBlock6Row0,kineticDriftBlock6Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff0Row4Norm,kineticDriftCof6Coeff0Row5Norm,kineticDriftCof6Coeff0Row6Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff1Row3Norm,kineticDriftCof6Coeff1Row4Norm,kineticDriftCof6Coeff1Row5Norm,kineticDriftCof6Coeff1Row6Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff0Row4Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff1Row3Norm,kineticDriftBlock6Coeff1Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff1Row7Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 1 7=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 1 7=kineticDriftCell h (kineticCof8*kineticBlock8) 1 7 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftBlock8Row0,kineticDriftBlock8Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff0Row4Norm,kineticDriftCof8Coeff0Row5Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff1Row3Norm,kineticDriftCof8Coeff1Row4Norm,kineticDriftCof8Coeff1Row5Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff0Row4Norm,kineticDriftBlock8Coeff0Row5Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff1Row3Norm,kineticDriftBlock8Coeff1Row4Norm,kineticDriftBlock8Coeff1Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff1Row7Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 1 7=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 1 7=kineticDriftCell h (kineticCof10*kineticBlock10) 1 7 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftBlock10Row0,kineticDriftBlock10Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff0Row4Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff1Row3Norm,kineticDriftCof10Coeff1Row4Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff0Row4Norm,kineticDriftBlock10Coeff0Row5Norm,kineticDriftBlock10Coeff0Row6Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff1Row3Norm,kineticDriftBlock10Coeff1Row4Norm,kineticDriftBlock10Coeff1Row5Norm,kineticDriftBlock10Coeff1Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff1Row8Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 1 8=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 1 8=kineticDriftCell h (kineticCof2*kineticBlock2) 1 8 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftBlock2Row0,kineticDriftBlock2Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm,kineticDriftCof2Coeff0Row4Norm,kineticDriftCof2Coeff0Row5Norm,kineticDriftCof2Coeff0Row6Norm,kineticDriftCof2Coeff0Row7Norm,kineticDriftCof2Coeff0Row8Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff1Row3Norm,kineticDriftCof2Coeff1Row4Norm,kineticDriftCof2Coeff1Row5Norm,kineticDriftCof2Coeff1Row6Norm,kineticDriftCof2Coeff1Row7Norm,kineticDriftCof2Coeff1Row8Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff1Row8Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 1 8=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 1 8=kineticDriftCell h (kineticCof4*kineticBlock4) 1 8 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftBlock4Row0,kineticDriftBlock4Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff0Row4Norm,kineticDriftCof4Coeff0Row5Norm,kineticDriftCof4Coeff0Row6Norm,kineticDriftCof4Coeff0Row7Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff1Row3Norm,kineticDriftCof4Coeff1Row4Norm,kineticDriftCof4Coeff1Row5Norm,kineticDriftCof4Coeff1Row6Norm,kineticDriftCof4Coeff1Row7Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff1Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff1Row8Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 1 8=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 1 8=kineticDriftCell h (kineticCof6*kineticBlock6) 1 8 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftBlock6Row0,kineticDriftBlock6Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff0Row4Norm,kineticDriftCof6Coeff0Row5Norm,kineticDriftCof6Coeff0Row6Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff1Row3Norm,kineticDriftCof6Coeff1Row4Norm,kineticDriftCof6Coeff1Row5Norm,kineticDriftCof6Coeff1Row6Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff0Row4Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff1Row3Norm,kineticDriftBlock6Coeff1Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff1Row8Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 1 8=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 1 8=kineticDriftCell h (kineticCof8*kineticBlock8) 1 8 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftBlock8Row0,kineticDriftBlock8Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff0Row4Norm,kineticDriftCof8Coeff0Row5Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff1Row3Norm,kineticDriftCof8Coeff1Row4Norm,kineticDriftCof8Coeff1Row5Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff0Row4Norm,kineticDriftBlock8Coeff0Row5Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff1Row3Norm,kineticDriftBlock8Coeff1Row4Norm,kineticDriftBlock8Coeff1Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff1Row8Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 1 8=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 1 8=kineticDriftCell h (kineticCof10*kineticBlock10) 1 8 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftBlock10Row0,kineticDriftBlock10Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff0Row4Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff1Row3Norm,kineticDriftCof10Coeff1Row4Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff0Row4Norm,kineticDriftBlock10Coeff0Row5Norm,kineticDriftBlock10Coeff0Row6Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff1Row3Norm,kineticDriftBlock10Coeff1Row4Norm,kineticDriftBlock10Coeff1Row5Norm,kineticDriftBlock10Coeff1Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff1Row9Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 1 9=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 1 9=kineticDriftCell h (kineticCof2*kineticBlock2) 1 9 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftBlock2Row0,kineticDriftBlock2Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm,kineticDriftCof2Coeff0Row4Norm,kineticDriftCof2Coeff0Row5Norm,kineticDriftCof2Coeff0Row6Norm,kineticDriftCof2Coeff0Row7Norm,kineticDriftCof2Coeff0Row8Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff1Row3Norm,kineticDriftCof2Coeff1Row4Norm,kineticDriftCof2Coeff1Row5Norm,kineticDriftCof2Coeff1Row6Norm,kineticDriftCof2Coeff1Row7Norm,kineticDriftCof2Coeff1Row8Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff1Row9Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 1 9=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 1 9=kineticDriftCell h (kineticCof4*kineticBlock4) 1 9 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftBlock4Row0,kineticDriftBlock4Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff0Row4Norm,kineticDriftCof4Coeff0Row5Norm,kineticDriftCof4Coeff0Row6Norm,kineticDriftCof4Coeff0Row7Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff1Row3Norm,kineticDriftCof4Coeff1Row4Norm,kineticDriftCof4Coeff1Row5Norm,kineticDriftCof4Coeff1Row6Norm,kineticDriftCof4Coeff1Row7Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff1Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff1Row9Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 1 9=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 1 9=kineticDriftCell h (kineticCof6*kineticBlock6) 1 9 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftBlock6Row0,kineticDriftBlock6Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff0Row4Norm,kineticDriftCof6Coeff0Row5Norm,kineticDriftCof6Coeff0Row6Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff1Row3Norm,kineticDriftCof6Coeff1Row4Norm,kineticDriftCof6Coeff1Row5Norm,kineticDriftCof6Coeff1Row6Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff0Row4Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff1Row3Norm,kineticDriftBlock6Coeff1Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff1Row9Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 1 9=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 1 9=kineticDriftCell h (kineticCof8*kineticBlock8) 1 9 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftBlock8Row0,kineticDriftBlock8Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff0Row4Norm,kineticDriftCof8Coeff0Row5Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff1Row3Norm,kineticDriftCof8Coeff1Row4Norm,kineticDriftCof8Coeff1Row5Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff0Row4Norm,kineticDriftBlock8Coeff0Row5Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff1Row3Norm,kineticDriftBlock8Coeff1Row4Norm,kineticDriftBlock8Coeff1Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff1Row9Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 1 9=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 1 9=kineticDriftCell h (kineticCof10*kineticBlock10) 1 9 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftBlock10Row0,kineticDriftBlock10Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff0Row4Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff1Row3Norm,kineticDriftCof10Coeff1Row4Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff0Row4Norm,kineticDriftBlock10Coeff0Row5Norm,kineticDriftBlock10Coeff0Row6Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff1Row3Norm,kineticDriftBlock10Coeff1Row4Norm,kineticDriftBlock10Coeff1Row5Norm,kineticDriftBlock10Coeff1Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff1Row10Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 1 10=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 1 10=kineticDriftCell h (kineticCof2*kineticBlock2) 1 10 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftBlock2Row0,kineticDriftBlock2Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm,kineticDriftCof2Coeff0Row4Norm,kineticDriftCof2Coeff0Row5Norm,kineticDriftCof2Coeff0Row6Norm,kineticDriftCof2Coeff0Row7Norm,kineticDriftCof2Coeff0Row8Norm,kineticDriftCof2Coeff1Row0Norm,kineticDriftCof2Coeff1Row1Norm,kineticDriftCof2Coeff1Row2Norm,kineticDriftCof2Coeff1Row3Norm,kineticDriftCof2Coeff1Row4Norm,kineticDriftCof2Coeff1Row5Norm,kineticDriftCof2Coeff1Row6Norm,kineticDriftCof2Coeff1Row7Norm,kineticDriftCof2Coeff1Row8Norm,kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftBlock2Coeff1Row0Norm,kineticDriftBlock2Coeff1Row1Norm,kineticDriftBlock2Coeff1Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff1Row10Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 1 10=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 1 10=kineticDriftCell h (kineticCof4*kineticBlock4) 1 10 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftBlock4Row0,kineticDriftBlock4Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff0Row4Norm,kineticDriftCof4Coeff0Row5Norm,kineticDriftCof4Coeff0Row6Norm,kineticDriftCof4Coeff0Row7Norm,kineticDriftCof4Coeff1Row0Norm,kineticDriftCof4Coeff1Row1Norm,kineticDriftCof4Coeff1Row2Norm,kineticDriftCof4Coeff1Row3Norm,kineticDriftCof4Coeff1Row4Norm,kineticDriftCof4Coeff1Row5Norm,kineticDriftCof4Coeff1Row6Norm,kineticDriftCof4Coeff1Row7Norm,kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftBlock4Coeff1Row0Norm,kineticDriftBlock4Coeff1Row1Norm,kineticDriftBlock4Coeff1Row2Norm,kineticDriftBlock4Coeff1Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff1Row10Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 1 10=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 1 10=kineticDriftCell h (kineticCof6*kineticBlock6) 1 10 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftBlock6Row0,kineticDriftBlock6Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff0Row4Norm,kineticDriftCof6Coeff0Row5Norm,kineticDriftCof6Coeff0Row6Norm,kineticDriftCof6Coeff1Row0Norm,kineticDriftCof6Coeff1Row1Norm,kineticDriftCof6Coeff1Row2Norm,kineticDriftCof6Coeff1Row3Norm,kineticDriftCof6Coeff1Row4Norm,kineticDriftCof6Coeff1Row5Norm,kineticDriftCof6Coeff1Row6Norm,kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff0Row4Norm,kineticDriftBlock6Coeff1Row0Norm,kineticDriftBlock6Coeff1Row1Norm,kineticDriftBlock6Coeff1Row2Norm,kineticDriftBlock6Coeff1Row3Norm,kineticDriftBlock6Coeff1Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff1Row10Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 1 10=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 1 10=kineticDriftCell h (kineticCof8*kineticBlock8) 1 10 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftBlock8Row0,kineticDriftBlock8Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff0Row4Norm,kineticDriftCof8Coeff0Row5Norm,kineticDriftCof8Coeff1Row0Norm,kineticDriftCof8Coeff1Row1Norm,kineticDriftCof8Coeff1Row2Norm,kineticDriftCof8Coeff1Row3Norm,kineticDriftCof8Coeff1Row4Norm,kineticDriftCof8Coeff1Row5Norm,kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff0Row4Norm,kineticDriftBlock8Coeff0Row5Norm,kineticDriftBlock8Coeff1Row0Norm,kineticDriftBlock8Coeff1Row1Norm,kineticDriftBlock8Coeff1Row2Norm,kineticDriftBlock8Coeff1Row3Norm,kineticDriftBlock8Coeff1Row4Norm,kineticDriftBlock8Coeff1Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff1Row10Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 1 10=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 1 10=kineticDriftCell h (kineticCof10*kineticBlock10) 1 10 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftBlock10Row0,kineticDriftBlock10Row1]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff0Row4Norm,kineticDriftCof10Coeff1Row0Norm,kineticDriftCof10Coeff1Row1Norm,kineticDriftCof10Coeff1Row2Norm,kineticDriftCof10Coeff1Row3Norm,kineticDriftCof10Coeff1Row4Norm,kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff0Row4Norm,kineticDriftBlock10Coeff0Row5Norm,kineticDriftBlock10Coeff0Row6Norm,kineticDriftBlock10Coeff1Row0Norm,kineticDriftBlock10Coeff1Row1Norm,kineticDriftBlock10Coeff1Row2Norm,kineticDriftBlock10Coeff1Row3Norm,kineticDriftBlock10Coeff1Row4Norm,kineticDriftBlock10Coeff1Row5Norm,kineticDriftBlock10Coeff1Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

end
end HTGeometry.ThetaRatioKineticContraction
