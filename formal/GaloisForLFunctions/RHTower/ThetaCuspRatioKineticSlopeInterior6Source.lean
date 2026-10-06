import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSlopeControl
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def negKineticSlopeControl6Drift0Norm (h : ℝ) : {c : ℝ // negKineticSlopeControlDriftCell h (1/3) 6 0=c} := by
  have he : negKineticSlopeControlDriftCell h (1/3) 6 0=negKineticSlopeControlDriftCell h (1/3) 6 0 := rfl
  conv at he =>
    rhs
    unfold negKineticSlopeControlDriftCell
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff1Row1RealNorm h).property,(kineticSourceCoeff2Row1RealNorm h).property,(kineticSourceCoeff3Row1RealNorm h).property,(kineticSourceCoeff4Row1RealNorm h).property,(kineticSourceCoeff5Row1RealNorm h).property,(kineticSourceCoeff6Row1RealNorm h).property,(kineticSourceCoeff7Row1RealNorm h).property]
    dsimp only [kineticSourceCoeff1Row1RealNorm,kineticSourceCoeff2Row1RealNorm,kineticSourceCoeff3Row1RealNorm,kineticSourceCoeff4Row1RealNorm,kineticSourceCoeff5Row1RealNorm,kineticSourceCoeff6Row1RealNorm,kineticSourceCoeff7Row1RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def negKineticSlopeControl6Drift1Norm (h : ℝ) : {c : ℝ // negKineticSlopeControlDriftCell h (1/3) 6 1=c} := by
  have he : negKineticSlopeControlDriftCell h (1/3) 6 1=negKineticSlopeControlDriftCell h (1/3) 6 1 := rfl
  conv at he =>
    rhs
    unfold negKineticSlopeControlDriftCell
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff1Row2RealNorm h).property,(kineticSourceCoeff2Row2RealNorm h).property,(kineticSourceCoeff3Row2RealNorm h).property,(kineticSourceCoeff4Row2RealNorm h).property,(kineticSourceCoeff5Row2RealNorm h).property,(kineticSourceCoeff6Row2RealNorm h).property,(kineticSourceCoeff7Row2RealNorm h).property]
    dsimp only [kineticSourceCoeff1Row2RealNorm,kineticSourceCoeff2Row2RealNorm,kineticSourceCoeff3Row2RealNorm,kineticSourceCoeff4Row2RealNorm,kineticSourceCoeff5Row2RealNorm,kineticSourceCoeff6Row2RealNorm,kineticSourceCoeff7Row2RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def negKineticSlopeControl6Drift2Norm (h : ℝ) : {c : ℝ // negKineticSlopeControlDriftCell h (1/3) 6 2=c} := by
  have he : negKineticSlopeControlDriftCell h (1/3) 6 2=negKineticSlopeControlDriftCell h (1/3) 6 2 := rfl
  conv at he =>
    rhs
    unfold negKineticSlopeControlDriftCell
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff1Row3RealNorm h).property,(kineticSourceCoeff2Row3RealNorm h).property,(kineticSourceCoeff3Row3RealNorm h).property,(kineticSourceCoeff4Row3RealNorm h).property,(kineticSourceCoeff5Row3RealNorm h).property,(kineticSourceCoeff6Row3RealNorm h).property,(kineticSourceCoeff7Row3RealNorm h).property]
    dsimp only [kineticSourceCoeff1Row3RealNorm,kineticSourceCoeff2Row3RealNorm,kineticSourceCoeff3Row3RealNorm,kineticSourceCoeff4Row3RealNorm,kineticSourceCoeff5Row3RealNorm,kineticSourceCoeff6Row3RealNorm,kineticSourceCoeff7Row3RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def negKineticSlopeControl6Drift3Norm (h : ℝ) : {c : ℝ // negKineticSlopeControlDriftCell h (1/3) 6 3=c} := by
  have he : negKineticSlopeControlDriftCell h (1/3) 6 3=negKineticSlopeControlDriftCell h (1/3) 6 3 := rfl
  conv at he =>
    rhs
    unfold negKineticSlopeControlDriftCell
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff1Row4RealNorm h).property,(kineticSourceCoeff2Row4RealNorm h).property,(kineticSourceCoeff3Row4RealNorm h).property,(kineticSourceCoeff4Row4RealNorm h).property,(kineticSourceCoeff5Row4RealNorm h).property,(kineticSourceCoeff6Row4RealNorm h).property,(kineticSourceCoeff7Row4RealNorm h).property]
    dsimp only [kineticSourceCoeff1Row4RealNorm,kineticSourceCoeff2Row4RealNorm,kineticSourceCoeff3Row4RealNorm,kineticSourceCoeff4Row4RealNorm,kineticSourceCoeff5Row4RealNorm,kineticSourceCoeff6Row4RealNorm,kineticSourceCoeff7Row4RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def negKineticSlopeControl6Drift4Norm (h : ℝ) : {c : ℝ // negKineticSlopeControlDriftCell h (1/3) 6 4=c} := by
  have he : negKineticSlopeControlDriftCell h (1/3) 6 4=negKineticSlopeControlDriftCell h (1/3) 6 4 := rfl
  conv at he =>
    rhs
    unfold negKineticSlopeControlDriftCell
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff1Row5RealNorm h).property,(kineticSourceCoeff2Row5RealNorm h).property,(kineticSourceCoeff3Row5RealNorm h).property,(kineticSourceCoeff4Row5RealNorm h).property,(kineticSourceCoeff5Row5RealNorm h).property,(kineticSourceCoeff6Row5RealNorm h).property,(kineticSourceCoeff7Row5RealNorm h).property]
    dsimp only [kineticSourceCoeff1Row5RealNorm,kineticSourceCoeff2Row5RealNorm,kineticSourceCoeff3Row5RealNorm,kineticSourceCoeff4Row5RealNorm,kineticSourceCoeff5Row5RealNorm,kineticSourceCoeff6Row5RealNorm,kineticSourceCoeff7Row5RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def negKineticSlopeControl6Drift5Norm (h : ℝ) : {c : ℝ // negKineticSlopeControlDriftCell h (1/3) 6 5=c} := by
  have he : negKineticSlopeControlDriftCell h (1/3) 6 5=negKineticSlopeControlDriftCell h (1/3) 6 5 := rfl
  conv at he =>
    rhs
    unfold negKineticSlopeControlDriftCell
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff1Row6RealNorm h).property,(kineticSourceCoeff2Row6RealNorm h).property,(kineticSourceCoeff3Row6RealNorm h).property,(kineticSourceCoeff4Row6RealNorm h).property,(kineticSourceCoeff5Row6RealNorm h).property,(kineticSourceCoeff6Row6RealNorm h).property,(kineticSourceCoeff7Row6RealNorm h).property]
    dsimp only [kineticSourceCoeff1Row6RealNorm,kineticSourceCoeff2Row6RealNorm,kineticSourceCoeff3Row6RealNorm,kineticSourceCoeff4Row6RealNorm,kineticSourceCoeff5Row6RealNorm,kineticSourceCoeff6Row6RealNorm,kineticSourceCoeff7Row6RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def negKineticSlopeControl6Drift6Norm (h : ℝ) : {c : ℝ // negKineticSlopeControlDriftCell h (1/3) 6 6=c} := by
  have he : negKineticSlopeControlDriftCell h (1/3) 6 6=negKineticSlopeControlDriftCell h (1/3) 6 6 := rfl
  conv at he =>
    rhs
    unfold negKineticSlopeControlDriftCell
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff1Row7RealNorm h).property,(kineticSourceCoeff2Row7RealNorm h).property,(kineticSourceCoeff3Row7RealNorm h).property,(kineticSourceCoeff4Row7RealNorm h).property,(kineticSourceCoeff5Row7RealNorm h).property,(kineticSourceCoeff6Row7RealNorm h).property,(kineticSourceCoeff7Row7RealNorm h).property]
    dsimp only [kineticSourceCoeff1Row7RealNorm,kineticSourceCoeff2Row7RealNorm,kineticSourceCoeff3Row7RealNorm,kineticSourceCoeff4Row7RealNorm,kineticSourceCoeff5Row7RealNorm,kineticSourceCoeff6Row7RealNorm,kineticSourceCoeff7Row7RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def negKineticSlopeControl6Drift7Norm (h : ℝ) : {c : ℝ // negKineticSlopeControlDriftCell h (1/3) 6 7=c} := by
  have he : negKineticSlopeControlDriftCell h (1/3) 6 7=negKineticSlopeControlDriftCell h (1/3) 6 7 := rfl
  conv at he =>
    rhs
    unfold negKineticSlopeControlDriftCell
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff1Row8RealNorm h).property,(kineticSourceCoeff2Row8RealNorm h).property,(kineticSourceCoeff3Row8RealNorm h).property,(kineticSourceCoeff4Row8RealNorm h).property,(kineticSourceCoeff5Row8RealNorm h).property,(kineticSourceCoeff6Row8RealNorm h).property,(kineticSourceCoeff7Row8RealNorm h).property]
    dsimp only [kineticSourceCoeff1Row8RealNorm,kineticSourceCoeff2Row8RealNorm,kineticSourceCoeff3Row8RealNorm,kineticSourceCoeff4Row8RealNorm,kineticSourceCoeff5Row8RealNorm,kineticSourceCoeff6Row8RealNorm,kineticSourceCoeff7Row8RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def negKineticSlopeControl6Drift8Norm (h : ℝ) : {c : ℝ // negKineticSlopeControlDriftCell h (1/3) 6 8=c} := by
  have he : negKineticSlopeControlDriftCell h (1/3) 6 8=negKineticSlopeControlDriftCell h (1/3) 6 8 := rfl
  conv at he =>
    rhs
    unfold negKineticSlopeControlDriftCell
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff1Row9RealNorm h).property,(kineticSourceCoeff2Row9RealNorm h).property,(kineticSourceCoeff3Row9RealNorm h).property,(kineticSourceCoeff4Row9RealNorm h).property,(kineticSourceCoeff5Row9RealNorm h).property,(kineticSourceCoeff6Row9RealNorm h).property,(kineticSourceCoeff7Row9RealNorm h).property]
    dsimp only [kineticSourceCoeff1Row9RealNorm,kineticSourceCoeff2Row9RealNorm,kineticSourceCoeff3Row9RealNorm,kineticSourceCoeff4Row9RealNorm,kineticSourceCoeff5Row9RealNorm,kineticSourceCoeff6Row9RealNorm,kineticSourceCoeff7Row9RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def negKineticSlopeControl6Drift9Norm (h : ℝ) : {c : ℝ // negKineticSlopeControlDriftCell h (1/3) 6 9=c} := by
  have he : negKineticSlopeControlDriftCell h (1/3) 6 9=negKineticSlopeControlDriftCell h (1/3) 6 9 := rfl
  conv at he =>
    rhs
    unfold negKineticSlopeControlDriftCell
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff1Row10RealNorm h).property,(kineticSourceCoeff2Row10RealNorm h).property,(kineticSourceCoeff3Row10RealNorm h).property,(kineticSourceCoeff4Row10RealNorm h).property,(kineticSourceCoeff5Row10RealNorm h).property,(kineticSourceCoeff6Row10RealNorm h).property,(kineticSourceCoeff7Row10RealNorm h).property]
    dsimp only [kineticSourceCoeff1Row10RealNorm,kineticSourceCoeff2Row10RealNorm,kineticSourceCoeff3Row10RealNorm,kineticSourceCoeff4Row10RealNorm,kineticSourceCoeff5Row10RealNorm,kineticSourceCoeff6Row10RealNorm,kineticSourceCoeff7Row10RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def negKineticSlopeDefectControl6Norm (h r : ℝ) :
    {c : ℝ // negKineticSlopeControl h (9-r*h^2) (1/3) 6=c} := by
  have he := negKineticSlopeControl_drift_expansion h (9-r*h^2) (1/3) 6
  conv at he =>
    rhs
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
    rw [(negKineticSlopeControl6Drift0Norm h).property,(negKineticSlopeControl6Drift1Norm h).property,(negKineticSlopeControl6Drift2Norm h).property,(negKineticSlopeControl6Drift3Norm h).property,(negKineticSlopeControl6Drift4Norm h).property,(negKineticSlopeControl6Drift5Norm h).property,(negKineticSlopeControl6Drift6Norm h).property,(negKineticSlopeControl6Drift7Norm h).property,(negKineticSlopeControl6Drift8Norm h).property,(negKineticSlopeControl6Drift9Norm h).property]
    dsimp only [negKineticSlopeControl6Drift0Norm,negKineticSlopeControl6Drift1Norm,negKineticSlopeControl6Drift2Norm,negKineticSlopeControl6Drift3Norm,negKineticSlopeControl6Drift4Norm,negKineticSlopeControl6Drift5Norm,negKineticSlopeControl6Drift6Norm,negKineticSlopeControl6Drift7Norm,negKineticSlopeControl6Drift8Norm,negKineticSlopeControl6Drift9Norm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

end
end HTGeometry.ThetaRatioKineticContraction

