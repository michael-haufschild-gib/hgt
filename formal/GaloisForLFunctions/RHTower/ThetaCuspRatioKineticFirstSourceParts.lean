import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticDriftCofactors2
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticDriftBlocks2
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticDriftCofactors4
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticDriftBlocks4
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticDriftCofactors6
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticDriftBlocks6
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticDriftCofactors8
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticDriftBlocks8
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticDriftCofactors10
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticDriftBlocks10
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticReducedTensor
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

def kineticSourcePart2Coeff0Row1Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 0 1=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 0 1=kineticDriftCell h (kineticCof2*kineticBlock2) 0 1 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftCof2Row3,kineticDriftCof2Row4,kineticDriftCof2Row5,kineticDriftCof2Row6,kineticDriftCof2Row7,kineticDriftCof2Row8,kineticDriftCof2Row9,kineticDriftCof2Row10,kineticDriftCof2Row11,kineticDriftCof2Row12,kineticDriftCof2Row13,kineticDriftCof2Row14,kineticDriftCof2Row15,kineticDriftCof2Row16,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2,kineticDriftBlock2Row3]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff0Row1Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 0 1=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 0 1=kineticDriftCell h (kineticCof4*kineticBlock4) 0 1 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftCof4Row3,kineticDriftCof4Row4,kineticDriftCof4Row5,kineticDriftCof4Row6,kineticDriftCof4Row7,kineticDriftCof4Row8,kineticDriftCof4Row9,kineticDriftCof4Row10,kineticDriftCof4Row11,kineticDriftCof4Row12,kineticDriftCof4Row13,kineticDriftCof4Row14,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2,kineticDriftBlock4Row3,kineticDriftBlock4Row4,kineticDriftBlock4Row5]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff0Row1Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 0 1=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 0 1=kineticDriftCell h (kineticCof6*kineticBlock6) 0 1 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftCof6Row3,kineticDriftCof6Row4,kineticDriftCof6Row5,kineticDriftCof6Row6,kineticDriftCof6Row7,kineticDriftCof6Row8,kineticDriftCof6Row9,kineticDriftCof6Row10,kineticDriftCof6Row11,kineticDriftCof6Row12,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2,kineticDriftBlock6Row3,kineticDriftBlock6Row4,kineticDriftBlock6Row5,kineticDriftBlock6Row6,kineticDriftBlock6Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff0Row1Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 0 1=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 0 1=kineticDriftCell h (kineticCof8*kineticBlock8) 0 1 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftCof8Row3,kineticDriftCof8Row4,kineticDriftCof8Row5,kineticDriftCof8Row6,kineticDriftCof8Row7,kineticDriftCof8Row8,kineticDriftCof8Row9,kineticDriftCof8Row10,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2,kineticDriftBlock8Row3,kineticDriftBlock8Row4,kineticDriftBlock8Row5,kineticDriftBlock8Row6,kineticDriftBlock8Row7,kineticDriftBlock8Row8,kineticDriftBlock8Row9]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff0Row1Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 0 1=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 0 1=kineticDriftCell h (kineticCof10*kineticBlock10) 0 1 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftCof10Row3,kineticDriftCof10Row4,kineticDriftCof10Row5,kineticDriftCof10Row6,kineticDriftCof10Row7,kineticDriftCof10Row8,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2,kineticDriftBlock10Row3,kineticDriftBlock10Row4,kineticDriftBlock10Row5,kineticDriftBlock10Row6,kineticDriftBlock10Row7,kineticDriftBlock10Row8,kineticDriftBlock10Row9,kineticDriftBlock10Row10,kineticDriftBlock10Row11]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff0Row2Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 0 2=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 0 2=kineticDriftCell h (kineticCof2*kineticBlock2) 0 2 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftCof2Row3,kineticDriftCof2Row4,kineticDriftCof2Row5,kineticDriftCof2Row6,kineticDriftCof2Row7,kineticDriftCof2Row8,kineticDriftCof2Row9,kineticDriftCof2Row10,kineticDriftCof2Row11,kineticDriftCof2Row12,kineticDriftCof2Row13,kineticDriftCof2Row14,kineticDriftCof2Row15,kineticDriftCof2Row16,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2,kineticDriftBlock2Row3]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftCof2Coeff0Row0Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff0Row2Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 0 2=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 0 2=kineticDriftCell h (kineticCof4*kineticBlock4) 0 2 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftCof4Row3,kineticDriftCof4Row4,kineticDriftCof4Row5,kineticDriftCof4Row6,kineticDriftCof4Row7,kineticDriftCof4Row8,kineticDriftCof4Row9,kineticDriftCof4Row10,kineticDriftCof4Row11,kineticDriftCof4Row12,kineticDriftCof4Row13,kineticDriftCof4Row14,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2,kineticDriftBlock4Row3,kineticDriftBlock4Row4,kineticDriftBlock4Row5]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff0Row2Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 0 2=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 0 2=kineticDriftCell h (kineticCof6*kineticBlock6) 0 2 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftCof6Row3,kineticDriftCof6Row4,kineticDriftCof6Row5,kineticDriftCof6Row6,kineticDriftCof6Row7,kineticDriftCof6Row8,kineticDriftCof6Row9,kineticDriftCof6Row10,kineticDriftCof6Row11,kineticDriftCof6Row12,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2,kineticDriftBlock6Row3,kineticDriftBlock6Row4,kineticDriftBlock6Row5,kineticDriftBlock6Row6,kineticDriftBlock6Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff0Row2Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 0 2=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 0 2=kineticDriftCell h (kineticCof8*kineticBlock8) 0 2 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftCof8Row3,kineticDriftCof8Row4,kineticDriftCof8Row5,kineticDriftCof8Row6,kineticDriftCof8Row7,kineticDriftCof8Row8,kineticDriftCof8Row9,kineticDriftCof8Row10,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2,kineticDriftBlock8Row3,kineticDriftBlock8Row4,kineticDriftBlock8Row5,kineticDriftBlock8Row6,kineticDriftBlock8Row7,kineticDriftBlock8Row8,kineticDriftBlock8Row9]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff0Row2Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 0 2=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 0 2=kineticDriftCell h (kineticCof10*kineticBlock10) 0 2 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftCof10Row3,kineticDriftCof10Row4,kineticDriftCof10Row5,kineticDriftCof10Row6,kineticDriftCof10Row7,kineticDriftCof10Row8,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2,kineticDriftBlock10Row3,kineticDriftBlock10Row4,kineticDriftBlock10Row5,kineticDriftBlock10Row6,kineticDriftBlock10Row7,kineticDriftBlock10Row8,kineticDriftBlock10Row9,kineticDriftBlock10Row10,kineticDriftBlock10Row11]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff0Row3Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 0 3=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 0 3=kineticDriftCell h (kineticCof2*kineticBlock2) 0 3 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftCof2Row3,kineticDriftCof2Row4,kineticDriftCof2Row5,kineticDriftCof2Row6,kineticDriftCof2Row7,kineticDriftCof2Row8,kineticDriftCof2Row9,kineticDriftCof2Row10,kineticDriftCof2Row11,kineticDriftCof2Row12,kineticDriftCof2Row13,kineticDriftCof2Row14,kineticDriftCof2Row15,kineticDriftCof2Row16,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2,kineticDriftBlock2Row3]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftCof2Coeff0Row1Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff0Row3Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 0 3=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 0 3=kineticDriftCell h (kineticCof4*kineticBlock4) 0 3 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftCof4Row3,kineticDriftCof4Row4,kineticDriftCof4Row5,kineticDriftCof4Row6,kineticDriftCof4Row7,kineticDriftCof4Row8,kineticDriftCof4Row9,kineticDriftCof4Row10,kineticDriftCof4Row11,kineticDriftCof4Row12,kineticDriftCof4Row13,kineticDriftCof4Row14,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2,kineticDriftBlock4Row3,kineticDriftBlock4Row4,kineticDriftBlock4Row5]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftCof4Coeff0Row0Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff0Row3Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 0 3=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 0 3=kineticDriftCell h (kineticCof6*kineticBlock6) 0 3 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftCof6Row3,kineticDriftCof6Row4,kineticDriftCof6Row5,kineticDriftCof6Row6,kineticDriftCof6Row7,kineticDriftCof6Row8,kineticDriftCof6Row9,kineticDriftCof6Row10,kineticDriftCof6Row11,kineticDriftCof6Row12,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2,kineticDriftBlock6Row3,kineticDriftBlock6Row4,kineticDriftBlock6Row5,kineticDriftBlock6Row6,kineticDriftBlock6Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff0Row3Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 0 3=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 0 3=kineticDriftCell h (kineticCof8*kineticBlock8) 0 3 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftCof8Row3,kineticDriftCof8Row4,kineticDriftCof8Row5,kineticDriftCof8Row6,kineticDriftCof8Row7,kineticDriftCof8Row8,kineticDriftCof8Row9,kineticDriftCof8Row10,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2,kineticDriftBlock8Row3,kineticDriftBlock8Row4,kineticDriftBlock8Row5,kineticDriftBlock8Row6,kineticDriftBlock8Row7,kineticDriftBlock8Row8,kineticDriftBlock8Row9]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff0Row3Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 0 3=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 0 3=kineticDriftCell h (kineticCof10*kineticBlock10) 0 3 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftCof10Row3,kineticDriftCof10Row4,kineticDriftCof10Row5,kineticDriftCof10Row6,kineticDriftCof10Row7,kineticDriftCof10Row8,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2,kineticDriftBlock10Row3,kineticDriftBlock10Row4,kineticDriftBlock10Row5,kineticDriftBlock10Row6,kineticDriftBlock10Row7,kineticDriftBlock10Row8,kineticDriftBlock10Row9,kineticDriftBlock10Row10,kineticDriftBlock10Row11]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff0Row4Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 0 4=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 0 4=kineticDriftCell h (kineticCof2*kineticBlock2) 0 4 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftCof2Row3,kineticDriftCof2Row4,kineticDriftCof2Row5,kineticDriftCof2Row6,kineticDriftCof2Row7,kineticDriftCof2Row8,kineticDriftCof2Row9,kineticDriftCof2Row10,kineticDriftCof2Row11,kineticDriftCof2Row12,kineticDriftCof2Row13,kineticDriftCof2Row14,kineticDriftCof2Row15,kineticDriftCof2Row16,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2,kineticDriftBlock2Row3]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftCof2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm,kineticDriftCof2Coeff0Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff0Row4Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 0 4=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 0 4=kineticDriftCell h (kineticCof4*kineticBlock4) 0 4 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftCof4Row3,kineticDriftCof4Row4,kineticDriftCof4Row5,kineticDriftCof4Row6,kineticDriftCof4Row7,kineticDriftCof4Row8,kineticDriftCof4Row9,kineticDriftCof4Row10,kineticDriftCof4Row11,kineticDriftCof4Row12,kineticDriftCof4Row13,kineticDriftCof4Row14,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2,kineticDriftBlock4Row3,kineticDriftBlock4Row4,kineticDriftBlock4Row5]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftCof4Coeff0Row1Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff0Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff0Row4Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 0 4=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 0 4=kineticDriftCell h (kineticCof6*kineticBlock6) 0 4 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftCof6Row3,kineticDriftCof6Row4,kineticDriftCof6Row5,kineticDriftCof6Row6,kineticDriftCof6Row7,kineticDriftCof6Row8,kineticDriftCof6Row9,kineticDriftCof6Row10,kineticDriftCof6Row11,kineticDriftCof6Row12,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2,kineticDriftBlock6Row3,kineticDriftBlock6Row4,kineticDriftBlock6Row5,kineticDriftBlock6Row6,kineticDriftBlock6Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff0Row4Norm,kineticDriftCof6Coeff0Row0Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff0Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff0Row4Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 0 4=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 0 4=kineticDriftCell h (kineticCof8*kineticBlock8) 0 4 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftCof8Row3,kineticDriftCof8Row4,kineticDriftCof8Row5,kineticDriftCof8Row6,kineticDriftCof8Row7,kineticDriftCof8Row8,kineticDriftCof8Row9,kineticDriftCof8Row10,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2,kineticDriftBlock8Row3,kineticDriftBlock8Row4,kineticDriftBlock8Row5,kineticDriftBlock8Row6,kineticDriftBlock8Row7,kineticDriftBlock8Row8,kineticDriftBlock8Row9]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff0Row4Norm,kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff0Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff0Row4Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 0 4=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 0 4=kineticDriftCell h (kineticCof10*kineticBlock10) 0 4 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftCof10Row3,kineticDriftCof10Row4,kineticDriftCof10Row5,kineticDriftCof10Row6,kineticDriftCof10Row7,kineticDriftCof10Row8,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2,kineticDriftBlock10Row3,kineticDriftBlock10Row4,kineticDriftBlock10Row5,kineticDriftBlock10Row6,kineticDriftBlock10Row7,kineticDriftBlock10Row8,kineticDriftBlock10Row9,kineticDriftBlock10Row10,kineticDriftBlock10Row11]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock10Coeff0Row0Norm,kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff0Row4Norm,kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff0Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff0Row5Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 0 5=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 0 5=kineticDriftCell h (kineticCof2*kineticBlock2) 0 5 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftCof2Row3,kineticDriftCof2Row4,kineticDriftCof2Row5,kineticDriftCof2Row6,kineticDriftCof2Row7,kineticDriftCof2Row8,kineticDriftCof2Row9,kineticDriftCof2Row10,kineticDriftCof2Row11,kineticDriftCof2Row12,kineticDriftCof2Row13,kineticDriftCof2Row14,kineticDriftCof2Row15,kineticDriftCof2Row16,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2,kineticDriftBlock2Row3]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftCof2Coeff0Row3Norm,kineticDriftCof2Coeff0Row4Norm,kineticDriftCof2Coeff0Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff0Row5Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 0 5=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 0 5=kineticDriftCell h (kineticCof4*kineticBlock4) 0 5 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftCof4Row3,kineticDriftCof4Row4,kineticDriftCof4Row5,kineticDriftCof4Row6,kineticDriftCof4Row7,kineticDriftCof4Row8,kineticDriftCof4Row9,kineticDriftCof4Row10,kineticDriftCof4Row11,kineticDriftCof4Row12,kineticDriftCof4Row13,kineticDriftCof4Row14,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2,kineticDriftBlock4Row3,kineticDriftBlock4Row4,kineticDriftBlock4Row5]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftCof4Coeff0Row2Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff0Row4Norm,kineticDriftCof4Coeff0Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff0Row5Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 0 5=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 0 5=kineticDriftCell h (kineticCof6*kineticBlock6) 0 5 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftCof6Row3,kineticDriftCof6Row4,kineticDriftCof6Row5,kineticDriftCof6Row6,kineticDriftCof6Row7,kineticDriftCof6Row8,kineticDriftCof6Row9,kineticDriftCof6Row10,kineticDriftCof6Row11,kineticDriftCof6Row12,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2,kineticDriftBlock6Row3,kineticDriftBlock6Row4,kineticDriftBlock6Row5,kineticDriftBlock6Row6,kineticDriftBlock6Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff0Row4Norm,kineticDriftCof6Coeff0Row1Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff0Row4Norm,kineticDriftCof6Coeff0Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff0Row5Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 0 5=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 0 5=kineticDriftCell h (kineticCof8*kineticBlock8) 0 5 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftCof8Row3,kineticDriftCof8Row4,kineticDriftCof8Row5,kineticDriftCof8Row6,kineticDriftCof8Row7,kineticDriftCof8Row8,kineticDriftCof8Row9,kineticDriftCof8Row10,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2,kineticDriftBlock8Row3,kineticDriftBlock8Row4,kineticDriftBlock8Row5,kineticDriftBlock8Row6,kineticDriftBlock8Row7,kineticDriftBlock8Row8,kineticDriftBlock8Row9]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock8Coeff0Row0Norm,kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff0Row4Norm,kineticDriftBlock8Coeff0Row5Norm,kineticDriftCof8Coeff0Row0Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff0Row4Norm,kineticDriftCof8Coeff0Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff0Row5Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 0 5=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 0 5=kineticDriftCell h (kineticCof10*kineticBlock10) 0 5 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftCof10Row3,kineticDriftCof10Row4,kineticDriftCof10Row5,kineticDriftCof10Row6,kineticDriftCof10Row7,kineticDriftCof10Row8,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2,kineticDriftBlock10Row3,kineticDriftBlock10Row4,kineticDriftBlock10Row5,kineticDriftBlock10Row6,kineticDriftBlock10Row7,kineticDriftBlock10Row8,kineticDriftBlock10Row9,kineticDriftBlock10Row10,kineticDriftBlock10Row11]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock10Coeff0Row1Norm,kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff0Row4Norm,kineticDriftBlock10Coeff0Row5Norm,kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff0Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff0Row6Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 0 6=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 0 6=kineticDriftCell h (kineticCof2*kineticBlock2) 0 6 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftCof2Row3,kineticDriftCof2Row4,kineticDriftCof2Row5,kineticDriftCof2Row6,kineticDriftCof2Row7,kineticDriftCof2Row8,kineticDriftCof2Row9,kineticDriftCof2Row10,kineticDriftCof2Row11,kineticDriftCof2Row12,kineticDriftCof2Row13,kineticDriftCof2Row14,kineticDriftCof2Row15,kineticDriftCof2Row16,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2,kineticDriftBlock2Row3]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftCof2Coeff0Row4Norm,kineticDriftCof2Coeff0Row5Norm,kineticDriftCof2Coeff0Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff0Row6Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 0 6=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 0 6=kineticDriftCell h (kineticCof4*kineticBlock4) 0 6 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftCof4Row3,kineticDriftCof4Row4,kineticDriftCof4Row5,kineticDriftCof4Row6,kineticDriftCof4Row7,kineticDriftCof4Row8,kineticDriftCof4Row9,kineticDriftCof4Row10,kineticDriftCof4Row11,kineticDriftCof4Row12,kineticDriftCof4Row13,kineticDriftCof4Row14,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2,kineticDriftBlock4Row3,kineticDriftBlock4Row4,kineticDriftBlock4Row5]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftCof4Coeff0Row3Norm,kineticDriftCof4Coeff0Row4Norm,kineticDriftCof4Coeff0Row5Norm,kineticDriftCof4Coeff0Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff0Row6Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 0 6=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 0 6=kineticDriftCell h (kineticCof6*kineticBlock6) 0 6 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftCof6Row3,kineticDriftCof6Row4,kineticDriftCof6Row5,kineticDriftCof6Row6,kineticDriftCof6Row7,kineticDriftCof6Row8,kineticDriftCof6Row9,kineticDriftCof6Row10,kineticDriftCof6Row11,kineticDriftCof6Row12,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2,kineticDriftBlock6Row3,kineticDriftBlock6Row4,kineticDriftBlock6Row5,kineticDriftBlock6Row6,kineticDriftBlock6Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock6Coeff0Row0Norm,kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff0Row4Norm,kineticDriftCof6Coeff0Row2Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff0Row4Norm,kineticDriftCof6Coeff0Row5Norm,kineticDriftCof6Coeff0Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff0Row6Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 0 6=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 0 6=kineticDriftCell h (kineticCof8*kineticBlock8) 0 6 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftCof8Row3,kineticDriftCof8Row4,kineticDriftCof8Row5,kineticDriftCof8Row6,kineticDriftCof8Row7,kineticDriftCof8Row8,kineticDriftCof8Row9,kineticDriftCof8Row10,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2,kineticDriftBlock8Row3,kineticDriftBlock8Row4,kineticDriftBlock8Row5,kineticDriftBlock8Row6,kineticDriftBlock8Row7,kineticDriftBlock8Row8,kineticDriftBlock8Row9]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock8Coeff0Row1Norm,kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff0Row4Norm,kineticDriftBlock8Coeff0Row5Norm,kineticDriftCof8Coeff0Row1Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff0Row4Norm,kineticDriftCof8Coeff0Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff0Row6Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 0 6=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 0 6=kineticDriftCell h (kineticCof10*kineticBlock10) 0 6 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftCof10Row3,kineticDriftCof10Row4,kineticDriftCof10Row5,kineticDriftCof10Row6,kineticDriftCof10Row7,kineticDriftCof10Row8,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2,kineticDriftBlock10Row3,kineticDriftBlock10Row4,kineticDriftBlock10Row5,kineticDriftBlock10Row6,kineticDriftBlock10Row7,kineticDriftBlock10Row8,kineticDriftBlock10Row9,kineticDriftBlock10Row10,kineticDriftBlock10Row11]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock10Coeff0Row2Norm,kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff0Row4Norm,kineticDriftBlock10Coeff0Row5Norm,kineticDriftBlock10Coeff0Row6Norm,kineticDriftCof10Coeff0Row0Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff0Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff0Row7Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 0 7=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 0 7=kineticDriftCell h (kineticCof2*kineticBlock2) 0 7 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftCof2Row3,kineticDriftCof2Row4,kineticDriftCof2Row5,kineticDriftCof2Row6,kineticDriftCof2Row7,kineticDriftCof2Row8,kineticDriftCof2Row9,kineticDriftCof2Row10,kineticDriftCof2Row11,kineticDriftCof2Row12,kineticDriftCof2Row13,kineticDriftCof2Row14,kineticDriftCof2Row15,kineticDriftCof2Row16,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2,kineticDriftBlock2Row3]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftCof2Coeff0Row5Norm,kineticDriftCof2Coeff0Row6Norm,kineticDriftCof2Coeff0Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff0Row7Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 0 7=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 0 7=kineticDriftCell h (kineticCof4*kineticBlock4) 0 7 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftCof4Row3,kineticDriftCof4Row4,kineticDriftCof4Row5,kineticDriftCof4Row6,kineticDriftCof4Row7,kineticDriftCof4Row8,kineticDriftCof4Row9,kineticDriftCof4Row10,kineticDriftCof4Row11,kineticDriftCof4Row12,kineticDriftCof4Row13,kineticDriftCof4Row14,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2,kineticDriftBlock4Row3,kineticDriftBlock4Row4,kineticDriftBlock4Row5]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock4Coeff0Row0Norm,kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftCof4Coeff0Row4Norm,kineticDriftCof4Coeff0Row5Norm,kineticDriftCof4Coeff0Row6Norm,kineticDriftCof4Coeff0Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff0Row7Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 0 7=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 0 7=kineticDriftCell h (kineticCof6*kineticBlock6) 0 7 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftCof6Row3,kineticDriftCof6Row4,kineticDriftCof6Row5,kineticDriftCof6Row6,kineticDriftCof6Row7,kineticDriftCof6Row8,kineticDriftCof6Row9,kineticDriftCof6Row10,kineticDriftCof6Row11,kineticDriftCof6Row12,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2,kineticDriftBlock6Row3,kineticDriftBlock6Row4,kineticDriftBlock6Row5,kineticDriftBlock6Row6,kineticDriftBlock6Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock6Coeff0Row1Norm,kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff0Row4Norm,kineticDriftCof6Coeff0Row3Norm,kineticDriftCof6Coeff0Row4Norm,kineticDriftCof6Coeff0Row5Norm,kineticDriftCof6Coeff0Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff0Row7Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 0 7=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 0 7=kineticDriftCell h (kineticCof8*kineticBlock8) 0 7 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftCof8Row3,kineticDriftCof8Row4,kineticDriftCof8Row5,kineticDriftCof8Row6,kineticDriftCof8Row7,kineticDriftCof8Row8,kineticDriftCof8Row9,kineticDriftCof8Row10,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2,kineticDriftBlock8Row3,kineticDriftBlock8Row4,kineticDriftBlock8Row5,kineticDriftBlock8Row6,kineticDriftBlock8Row7,kineticDriftBlock8Row8,kineticDriftBlock8Row9]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock8Coeff0Row2Norm,kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff0Row4Norm,kineticDriftBlock8Coeff0Row5Norm,kineticDriftCof8Coeff0Row2Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff0Row4Norm,kineticDriftCof8Coeff0Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff0Row7Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 0 7=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 0 7=kineticDriftCell h (kineticCof10*kineticBlock10) 0 7 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftCof10Row3,kineticDriftCof10Row4,kineticDriftCof10Row5,kineticDriftCof10Row6,kineticDriftCof10Row7,kineticDriftCof10Row8,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2,kineticDriftBlock10Row3,kineticDriftBlock10Row4,kineticDriftBlock10Row5,kineticDriftBlock10Row6,kineticDriftBlock10Row7,kineticDriftBlock10Row8,kineticDriftBlock10Row9,kineticDriftBlock10Row10,kineticDriftBlock10Row11]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock10Coeff0Row3Norm,kineticDriftBlock10Coeff0Row4Norm,kineticDriftBlock10Coeff0Row5Norm,kineticDriftBlock10Coeff0Row6Norm,kineticDriftCof10Coeff0Row1Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff0Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff0Row8Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 0 8=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 0 8=kineticDriftCell h (kineticCof2*kineticBlock2) 0 8 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftCof2Row3,kineticDriftCof2Row4,kineticDriftCof2Row5,kineticDriftCof2Row6,kineticDriftCof2Row7,kineticDriftCof2Row8,kineticDriftCof2Row9,kineticDriftCof2Row10,kineticDriftCof2Row11,kineticDriftCof2Row12,kineticDriftCof2Row13,kineticDriftCof2Row14,kineticDriftCof2Row15,kineticDriftCof2Row16,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2,kineticDriftBlock2Row3]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock2Coeff0Row0Norm,kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftCof2Coeff0Row6Norm,kineticDriftCof2Coeff0Row7Norm,kineticDriftCof2Coeff0Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff0Row8Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 0 8=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 0 8=kineticDriftCell h (kineticCof4*kineticBlock4) 0 8 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftCof4Row3,kineticDriftCof4Row4,kineticDriftCof4Row5,kineticDriftCof4Row6,kineticDriftCof4Row7,kineticDriftCof4Row8,kineticDriftCof4Row9,kineticDriftCof4Row10,kineticDriftCof4Row11,kineticDriftCof4Row12,kineticDriftCof4Row13,kineticDriftCof4Row14,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2,kineticDriftBlock4Row3,kineticDriftBlock4Row4,kineticDriftBlock4Row5]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock4Coeff0Row1Norm,kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftCof4Coeff0Row5Norm,kineticDriftCof4Coeff0Row6Norm,kineticDriftCof4Coeff0Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff0Row8Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 0 8=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 0 8=kineticDriftCell h (kineticCof6*kineticBlock6) 0 8 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftCof6Row3,kineticDriftCof6Row4,kineticDriftCof6Row5,kineticDriftCof6Row6,kineticDriftCof6Row7,kineticDriftCof6Row8,kineticDriftCof6Row9,kineticDriftCof6Row10,kineticDriftCof6Row11,kineticDriftCof6Row12,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2,kineticDriftBlock6Row3,kineticDriftBlock6Row4,kineticDriftBlock6Row5,kineticDriftBlock6Row6,kineticDriftBlock6Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock6Coeff0Row2Norm,kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff0Row4Norm,kineticDriftCof6Coeff0Row4Norm,kineticDriftCof6Coeff0Row5Norm,kineticDriftCof6Coeff0Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff0Row8Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 0 8=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 0 8=kineticDriftCell h (kineticCof8*kineticBlock8) 0 8 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftCof8Row3,kineticDriftCof8Row4,kineticDriftCof8Row5,kineticDriftCof8Row6,kineticDriftCof8Row7,kineticDriftCof8Row8,kineticDriftCof8Row9,kineticDriftCof8Row10,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2,kineticDriftBlock8Row3,kineticDriftBlock8Row4,kineticDriftBlock8Row5,kineticDriftBlock8Row6,kineticDriftBlock8Row7,kineticDriftBlock8Row8,kineticDriftBlock8Row9]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock8Coeff0Row3Norm,kineticDriftBlock8Coeff0Row4Norm,kineticDriftBlock8Coeff0Row5Norm,kineticDriftCof8Coeff0Row3Norm,kineticDriftCof8Coeff0Row4Norm,kineticDriftCof8Coeff0Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff0Row8Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 0 8=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 0 8=kineticDriftCell h (kineticCof10*kineticBlock10) 0 8 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftCof10Row3,kineticDriftCof10Row4,kineticDriftCof10Row5,kineticDriftCof10Row6,kineticDriftCof10Row7,kineticDriftCof10Row8,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2,kineticDriftBlock10Row3,kineticDriftBlock10Row4,kineticDriftBlock10Row5,kineticDriftBlock10Row6,kineticDriftBlock10Row7,kineticDriftBlock10Row8,kineticDriftBlock10Row9,kineticDriftBlock10Row10,kineticDriftBlock10Row11]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock10Coeff0Row4Norm,kineticDriftBlock10Coeff0Row5Norm,kineticDriftBlock10Coeff0Row6Norm,kineticDriftCof10Coeff0Row2Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff0Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff0Row9Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 0 9=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 0 9=kineticDriftCell h (kineticCof2*kineticBlock2) 0 9 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftCof2Row3,kineticDriftCof2Row4,kineticDriftCof2Row5,kineticDriftCof2Row6,kineticDriftCof2Row7,kineticDriftCof2Row8,kineticDriftCof2Row9,kineticDriftCof2Row10,kineticDriftCof2Row11,kineticDriftCof2Row12,kineticDriftCof2Row13,kineticDriftCof2Row14,kineticDriftCof2Row15,kineticDriftCof2Row16,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2,kineticDriftBlock2Row3]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock2Coeff0Row1Norm,kineticDriftBlock2Coeff0Row2Norm,kineticDriftCof2Coeff0Row7Norm,kineticDriftCof2Coeff0Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff0Row9Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 0 9=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 0 9=kineticDriftCell h (kineticCof4*kineticBlock4) 0 9 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftCof4Row3,kineticDriftCof4Row4,kineticDriftCof4Row5,kineticDriftCof4Row6,kineticDriftCof4Row7,kineticDriftCof4Row8,kineticDriftCof4Row9,kineticDriftCof4Row10,kineticDriftCof4Row11,kineticDriftCof4Row12,kineticDriftCof4Row13,kineticDriftCof4Row14,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2,kineticDriftBlock4Row3,kineticDriftBlock4Row4,kineticDriftBlock4Row5]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock4Coeff0Row2Norm,kineticDriftBlock4Coeff0Row3Norm,kineticDriftCof4Coeff0Row6Norm,kineticDriftCof4Coeff0Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff0Row9Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 0 9=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 0 9=kineticDriftCell h (kineticCof6*kineticBlock6) 0 9 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftCof6Row3,kineticDriftCof6Row4,kineticDriftCof6Row5,kineticDriftCof6Row6,kineticDriftCof6Row7,kineticDriftCof6Row8,kineticDriftCof6Row9,kineticDriftCof6Row10,kineticDriftCof6Row11,kineticDriftCof6Row12,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2,kineticDriftBlock6Row3,kineticDriftBlock6Row4,kineticDriftBlock6Row5,kineticDriftBlock6Row6,kineticDriftBlock6Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock6Coeff0Row3Norm,kineticDriftBlock6Coeff0Row4Norm,kineticDriftCof6Coeff0Row5Norm,kineticDriftCof6Coeff0Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff0Row9Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 0 9=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 0 9=kineticDriftCell h (kineticCof8*kineticBlock8) 0 9 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftCof8Row3,kineticDriftCof8Row4,kineticDriftCof8Row5,kineticDriftCof8Row6,kineticDriftCof8Row7,kineticDriftCof8Row8,kineticDriftCof8Row9,kineticDriftCof8Row10,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2,kineticDriftBlock8Row3,kineticDriftBlock8Row4,kineticDriftBlock8Row5,kineticDriftBlock8Row6,kineticDriftBlock8Row7,kineticDriftBlock8Row8,kineticDriftBlock8Row9]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock8Coeff0Row4Norm,kineticDriftBlock8Coeff0Row5Norm,kineticDriftCof8Coeff0Row4Norm,kineticDriftCof8Coeff0Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff0Row9Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 0 9=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 0 9=kineticDriftCell h (kineticCof10*kineticBlock10) 0 9 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftCof10Row3,kineticDriftCof10Row4,kineticDriftCof10Row5,kineticDriftCof10Row6,kineticDriftCof10Row7,kineticDriftCof10Row8,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2,kineticDriftBlock10Row3,kineticDriftBlock10Row4,kineticDriftBlock10Row5,kineticDriftBlock10Row6,kineticDriftBlock10Row7,kineticDriftBlock10Row8,kineticDriftBlock10Row9,kineticDriftBlock10Row10,kineticDriftBlock10Row11]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock10Coeff0Row5Norm,kineticDriftBlock10Coeff0Row6Norm,kineticDriftCof10Coeff0Row3Norm,kineticDriftCof10Coeff0Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart2Coeff0Row10Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof2*kineticBlock2) 0 10=c} := by
  have he : kineticDriftCell h (kineticCof2*kineticBlock2) 0 10=kineticDriftCell h (kineticCof2*kineticBlock2) 0 10 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof2_rows,kineticDriftBlock2_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof2Row0,kineticDriftCof2Row1,kineticDriftCof2Row2,kineticDriftCof2Row3,kineticDriftCof2Row4,kineticDriftCof2Row5,kineticDriftCof2Row6,kineticDriftCof2Row7,kineticDriftCof2Row8,kineticDriftCof2Row9,kineticDriftCof2Row10,kineticDriftCof2Row11,kineticDriftCof2Row12,kineticDriftCof2Row13,kineticDriftCof2Row14,kineticDriftCof2Row15,kineticDriftCof2Row16,kineticDriftBlock2Row0,kineticDriftBlock2Row1,kineticDriftBlock2Row2,kineticDriftBlock2Row3]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock2Coeff0Row2Norm,kineticDriftCof2Coeff0Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart4Coeff0Row10Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof4*kineticBlock4) 0 10=c} := by
  have he : kineticDriftCell h (kineticCof4*kineticBlock4) 0 10=kineticDriftCell h (kineticCof4*kineticBlock4) 0 10 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof4_rows,kineticDriftBlock4_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof4Row0,kineticDriftCof4Row1,kineticDriftCof4Row2,kineticDriftCof4Row3,kineticDriftCof4Row4,kineticDriftCof4Row5,kineticDriftCof4Row6,kineticDriftCof4Row7,kineticDriftCof4Row8,kineticDriftCof4Row9,kineticDriftCof4Row10,kineticDriftCof4Row11,kineticDriftCof4Row12,kineticDriftCof4Row13,kineticDriftCof4Row14,kineticDriftBlock4Row0,kineticDriftBlock4Row1,kineticDriftBlock4Row2,kineticDriftBlock4Row3,kineticDriftBlock4Row4,kineticDriftBlock4Row5]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock4Coeff0Row3Norm,kineticDriftCof4Coeff0Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart6Coeff0Row10Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof6*kineticBlock6) 0 10=c} := by
  have he : kineticDriftCell h (kineticCof6*kineticBlock6) 0 10=kineticDriftCell h (kineticCof6*kineticBlock6) 0 10 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof6_rows,kineticDriftBlock6_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof6Row0,kineticDriftCof6Row1,kineticDriftCof6Row2,kineticDriftCof6Row3,kineticDriftCof6Row4,kineticDriftCof6Row5,kineticDriftCof6Row6,kineticDriftCof6Row7,kineticDriftCof6Row8,kineticDriftCof6Row9,kineticDriftCof6Row10,kineticDriftCof6Row11,kineticDriftCof6Row12,kineticDriftBlock6Row0,kineticDriftBlock6Row1,kineticDriftBlock6Row2,kineticDriftBlock6Row3,kineticDriftBlock6Row4,kineticDriftBlock6Row5,kineticDriftBlock6Row6,kineticDriftBlock6Row7]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock6Coeff0Row4Norm,kineticDriftCof6Coeff0Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart8Coeff0Row10Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof8*kineticBlock8) 0 10=c} := by
  have he : kineticDriftCell h (kineticCof8*kineticBlock8) 0 10=kineticDriftCell h (kineticCof8*kineticBlock8) 0 10 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof8_rows,kineticDriftBlock8_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof8Row0,kineticDriftCof8Row1,kineticDriftCof8Row2,kineticDriftCof8Row3,kineticDriftCof8Row4,kineticDriftCof8Row5,kineticDriftCof8Row6,kineticDriftCof8Row7,kineticDriftCof8Row8,kineticDriftCof8Row9,kineticDriftCof8Row10,kineticDriftBlock8Row0,kineticDriftBlock8Row1,kineticDriftBlock8Row2,kineticDriftBlock8Row3,kineticDriftBlock8Row4,kineticDriftBlock8Row5,kineticDriftBlock8Row6,kineticDriftBlock8Row7,kineticDriftBlock8Row8,kineticDriftBlock8Row9]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock8Coeff0Row5Norm,kineticDriftCof8Coeff0Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourcePart10Coeff0Row10Norm (h : ℂ) : {c : ℂ // kineticDriftCell h (kineticCof10*kineticBlock10) 0 10=c} := by
  have he : kineticDriftCell h (kineticCof10*kineticBlock10) 0 10=kineticDriftCell h (kineticCof10*kineticBlock10) 0 10 := rfl
  conv at he =>
    rhs
    rw [kineticDriftCell_mul]
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    simp only [kineticDriftCof10_rows,kineticDriftBlock10_rows]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftCof10Row0,kineticDriftCof10Row1,kineticDriftCof10Row2,kineticDriftCof10Row3,kineticDriftCof10Row4,kineticDriftCof10Row5,kineticDriftCof10Row6,kineticDriftCof10Row7,kineticDriftCof10Row8,kineticDriftBlock10Row0,kineticDriftBlock10Row1,kineticDriftBlock10Row2,kineticDriftBlock10Row3,kineticDriftBlock10Row4,kineticDriftBlock10Row5,kineticDriftBlock10Row6,kineticDriftBlock10Row7,kineticDriftBlock10Row8,kineticDriftBlock10Row9,kineticDriftBlock10Row10,kineticDriftBlock10Row11]
    norm_num only
    simp only [ite_true,ite_false,zero_add,add_zero,zero_mul,mul_zero]
    dsimp only [kineticDriftBlock10Coeff0Row6Norm,kineticDriftCof10Coeff0Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

end
end HTGeometry.ThetaRatioKineticContraction
