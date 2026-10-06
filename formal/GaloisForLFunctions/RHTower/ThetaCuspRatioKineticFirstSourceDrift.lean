import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstSourceParts
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

def completeKineticSourceCoeff0Row1Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 0 1=c} := by
  have he : kineticDriftCell h completeKineticSlope 0 1=kineticDriftCell h completeKineticSlope 0 1 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff0Row1Norm h).property,(kineticSourcePart4Coeff0Row1Norm h).property,(kineticSourcePart6Coeff0Row1Norm h).property,(kineticSourcePart8Coeff0Row1Norm h).property,(kineticSourcePart10Coeff0Row1Norm h).property]
    dsimp only [kineticSourcePart2Coeff0Row1Norm,kineticSourcePart4Coeff0Row1Norm,kineticSourcePart6Coeff0Row1Norm,kineticSourcePart8Coeff0Row1Norm,kineticSourcePart10Coeff0Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff0Row2Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 0 2=c} := by
  have he : kineticDriftCell h completeKineticSlope 0 2=kineticDriftCell h completeKineticSlope 0 2 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff0Row2Norm h).property,(kineticSourcePart4Coeff0Row2Norm h).property,(kineticSourcePart6Coeff0Row2Norm h).property,(kineticSourcePart8Coeff0Row2Norm h).property,(kineticSourcePart10Coeff0Row2Norm h).property]
    dsimp only [kineticSourcePart2Coeff0Row2Norm,kineticSourcePart4Coeff0Row2Norm,kineticSourcePart6Coeff0Row2Norm,kineticSourcePart8Coeff0Row2Norm,kineticSourcePart10Coeff0Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff0Row3Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 0 3=c} := by
  have he : kineticDriftCell h completeKineticSlope 0 3=kineticDriftCell h completeKineticSlope 0 3 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff0Row3Norm h).property,(kineticSourcePart4Coeff0Row3Norm h).property,(kineticSourcePart6Coeff0Row3Norm h).property,(kineticSourcePart8Coeff0Row3Norm h).property,(kineticSourcePart10Coeff0Row3Norm h).property]
    dsimp only [kineticSourcePart2Coeff0Row3Norm,kineticSourcePart4Coeff0Row3Norm,kineticSourcePart6Coeff0Row3Norm,kineticSourcePart8Coeff0Row3Norm,kineticSourcePart10Coeff0Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff0Row4Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 0 4=c} := by
  have he : kineticDriftCell h completeKineticSlope 0 4=kineticDriftCell h completeKineticSlope 0 4 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff0Row4Norm h).property,(kineticSourcePart4Coeff0Row4Norm h).property,(kineticSourcePart6Coeff0Row4Norm h).property,(kineticSourcePart8Coeff0Row4Norm h).property,(kineticSourcePart10Coeff0Row4Norm h).property]
    dsimp only [kineticSourcePart2Coeff0Row4Norm,kineticSourcePart4Coeff0Row4Norm,kineticSourcePart6Coeff0Row4Norm,kineticSourcePart8Coeff0Row4Norm,kineticSourcePart10Coeff0Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff0Row5Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 0 5=c} := by
  have he : kineticDriftCell h completeKineticSlope 0 5=kineticDriftCell h completeKineticSlope 0 5 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff0Row5Norm h).property,(kineticSourcePart4Coeff0Row5Norm h).property,(kineticSourcePart6Coeff0Row5Norm h).property,(kineticSourcePart8Coeff0Row5Norm h).property,(kineticSourcePart10Coeff0Row5Norm h).property]
    dsimp only [kineticSourcePart2Coeff0Row5Norm,kineticSourcePart4Coeff0Row5Norm,kineticSourcePart6Coeff0Row5Norm,kineticSourcePart8Coeff0Row5Norm,kineticSourcePart10Coeff0Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff0Row6Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 0 6=c} := by
  have he : kineticDriftCell h completeKineticSlope 0 6=kineticDriftCell h completeKineticSlope 0 6 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff0Row6Norm h).property,(kineticSourcePart4Coeff0Row6Norm h).property,(kineticSourcePart6Coeff0Row6Norm h).property,(kineticSourcePart8Coeff0Row6Norm h).property,(kineticSourcePart10Coeff0Row6Norm h).property]
    dsimp only [kineticSourcePart2Coeff0Row6Norm,kineticSourcePart4Coeff0Row6Norm,kineticSourcePart6Coeff0Row6Norm,kineticSourcePart8Coeff0Row6Norm,kineticSourcePart10Coeff0Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff0Row7Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 0 7=c} := by
  have he : kineticDriftCell h completeKineticSlope 0 7=kineticDriftCell h completeKineticSlope 0 7 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff0Row7Norm h).property,(kineticSourcePart4Coeff0Row7Norm h).property,(kineticSourcePart6Coeff0Row7Norm h).property,(kineticSourcePart8Coeff0Row7Norm h).property,(kineticSourcePart10Coeff0Row7Norm h).property]
    dsimp only [kineticSourcePart2Coeff0Row7Norm,kineticSourcePart4Coeff0Row7Norm,kineticSourcePart6Coeff0Row7Norm,kineticSourcePart8Coeff0Row7Norm,kineticSourcePart10Coeff0Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff0Row8Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 0 8=c} := by
  have he : kineticDriftCell h completeKineticSlope 0 8=kineticDriftCell h completeKineticSlope 0 8 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff0Row8Norm h).property,(kineticSourcePart4Coeff0Row8Norm h).property,(kineticSourcePart6Coeff0Row8Norm h).property,(kineticSourcePart8Coeff0Row8Norm h).property,(kineticSourcePart10Coeff0Row8Norm h).property]
    dsimp only [kineticSourcePart2Coeff0Row8Norm,kineticSourcePart4Coeff0Row8Norm,kineticSourcePart6Coeff0Row8Norm,kineticSourcePart8Coeff0Row8Norm,kineticSourcePart10Coeff0Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff0Row9Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 0 9=c} := by
  have he : kineticDriftCell h completeKineticSlope 0 9=kineticDriftCell h completeKineticSlope 0 9 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff0Row9Norm h).property,(kineticSourcePart4Coeff0Row9Norm h).property,(kineticSourcePart6Coeff0Row9Norm h).property,(kineticSourcePart8Coeff0Row9Norm h).property,(kineticSourcePart10Coeff0Row9Norm h).property]
    dsimp only [kineticSourcePart2Coeff0Row9Norm,kineticSourcePart4Coeff0Row9Norm,kineticSourcePart6Coeff0Row9Norm,kineticSourcePart8Coeff0Row9Norm,kineticSourcePart10Coeff0Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff0Row10Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 0 10=c} := by
  have he : kineticDriftCell h completeKineticSlope 0 10=kineticDriftCell h completeKineticSlope 0 10 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff0Row10Norm h).property,(kineticSourcePart4Coeff0Row10Norm h).property,(kineticSourcePart6Coeff0Row10Norm h).property,(kineticSourcePart8Coeff0Row10Norm h).property,(kineticSourcePart10Coeff0Row10Norm h).property]
    dsimp only [kineticSourcePart2Coeff0Row10Norm,kineticSourcePart4Coeff0Row10Norm,kineticSourcePart6Coeff0Row10Norm,kineticSourcePart8Coeff0Row10Norm,kineticSourcePart10Coeff0Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def reducedKineticFullCoefficient0Norm (h v : ℂ) :
    {c : ℂ // (reducedKineticDriftCoefficient h 0).eval v=c} := by
  have he := reducedKineticDriftCoefficient_expansion h v 0
  conv at he =>
    rhs
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
    rw [(completeKineticSourceCoeff0Row1Norm h).property,(completeKineticSourceCoeff0Row2Norm h).property,(completeKineticSourceCoeff0Row3Norm h).property,(completeKineticSourceCoeff0Row4Norm h).property,(completeKineticSourceCoeff0Row5Norm h).property,(completeKineticSourceCoeff0Row6Norm h).property,(completeKineticSourceCoeff0Row7Norm h).property,(completeKineticSourceCoeff0Row8Norm h).property,(completeKineticSourceCoeff0Row9Norm h).property,(completeKineticSourceCoeff0Row10Norm h).property]
    dsimp only [completeKineticSourceCoeff0Row1Norm,completeKineticSourceCoeff0Row2Norm,completeKineticSourceCoeff0Row3Norm,completeKineticSourceCoeff0Row4Norm,completeKineticSourceCoeff0Row5Norm,completeKineticSourceCoeff0Row6Norm,completeKineticSourceCoeff0Row7Norm,completeKineticSourceCoeff0Row8Norm,completeKineticSourceCoeff0Row9Norm,completeKineticSourceCoeff0Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

end
end HTGeometry.ThetaRatioKineticContraction
