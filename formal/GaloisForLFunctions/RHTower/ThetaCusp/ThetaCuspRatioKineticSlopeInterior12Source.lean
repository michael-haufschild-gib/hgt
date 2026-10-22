import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeControl
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def negKineticSlopeControl12Drift0Norm (h : ℝ) : {c : ℝ // negKineticSlopeControlDriftCell h (1/3) 12 0=c} := by
  have he : negKineticSlopeControlDriftCell h (1/3) 12 0=negKineticSlopeControlDriftCell h (1/3) 12 0 := rfl
  conv at he =>
    rhs
    unfold negKineticSlopeControlDriftCell
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff1Row1RealNorm h).property,(kineticSourceCoeff2Row1RealNorm h).property,(kineticSourceCoeff3Row1RealNorm h).property,(kineticSourceCoeff4Row1RealNorm h).property,(kineticSourceCoeff5Row1RealNorm h).property,(kineticSourceCoeff6Row1RealNorm h).property,(kineticSourceCoeff7Row1RealNorm h).property,(kineticSourceCoeff8Row1RealNorm h).property,(kineticSourceCoeff9Row1RealNorm h).property,(kineticSourceCoeff10Row1RealNorm h).property,(kineticSourceCoeff11Row1RealNorm h).property,(kineticSourceCoeff12Row1RealNorm h).property,(kineticSourceCoeff13Row1RealNorm h).property]
    dsimp only [kineticSourceCoeff1Row1RealNorm,kineticSourceCoeff2Row1RealNorm,kineticSourceCoeff3Row1RealNorm,kineticSourceCoeff4Row1RealNorm,kineticSourceCoeff5Row1RealNorm,kineticSourceCoeff6Row1RealNorm,kineticSourceCoeff7Row1RealNorm,kineticSourceCoeff8Row1RealNorm,kineticSourceCoeff9Row1RealNorm,kineticSourceCoeff10Row1RealNorm,kineticSourceCoeff11Row1RealNorm,kineticSourceCoeff12Row1RealNorm,kineticSourceCoeff13Row1RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def negKineticSlopeControl12Drift1Norm (h : ℝ) : {c : ℝ // negKineticSlopeControlDriftCell h (1/3) 12 1=c} := by
  have he : negKineticSlopeControlDriftCell h (1/3) 12 1=negKineticSlopeControlDriftCell h (1/3) 12 1 := rfl
  conv at he =>
    rhs
    unfold negKineticSlopeControlDriftCell
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff1Row2RealNorm h).property,(kineticSourceCoeff2Row2RealNorm h).property,(kineticSourceCoeff3Row2RealNorm h).property,(kineticSourceCoeff4Row2RealNorm h).property,(kineticSourceCoeff5Row2RealNorm h).property,(kineticSourceCoeff6Row2RealNorm h).property,(kineticSourceCoeff7Row2RealNorm h).property,(kineticSourceCoeff8Row2RealNorm h).property,(kineticSourceCoeff9Row2RealNorm h).property,(kineticSourceCoeff10Row2RealNorm h).property,(kineticSourceCoeff11Row2RealNorm h).property,(kineticSourceCoeff12Row2RealNorm h).property,(kineticSourceCoeff13Row2RealNorm h).property]
    dsimp only [kineticSourceCoeff1Row2RealNorm,kineticSourceCoeff2Row2RealNorm,kineticSourceCoeff3Row2RealNorm,kineticSourceCoeff4Row2RealNorm,kineticSourceCoeff5Row2RealNorm,kineticSourceCoeff6Row2RealNorm,kineticSourceCoeff7Row2RealNorm,kineticSourceCoeff8Row2RealNorm,kineticSourceCoeff9Row2RealNorm,kineticSourceCoeff10Row2RealNorm,kineticSourceCoeff11Row2RealNorm,kineticSourceCoeff12Row2RealNorm,kineticSourceCoeff13Row2RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def negKineticSlopeControl12Drift2Norm (h : ℝ) : {c : ℝ // negKineticSlopeControlDriftCell h (1/3) 12 2=c} := by
  have he : negKineticSlopeControlDriftCell h (1/3) 12 2=negKineticSlopeControlDriftCell h (1/3) 12 2 := rfl
  conv at he =>
    rhs
    unfold negKineticSlopeControlDriftCell
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff1Row3RealNorm h).property,(kineticSourceCoeff2Row3RealNorm h).property,(kineticSourceCoeff3Row3RealNorm h).property,(kineticSourceCoeff4Row3RealNorm h).property,(kineticSourceCoeff5Row3RealNorm h).property,(kineticSourceCoeff6Row3RealNorm h).property,(kineticSourceCoeff7Row3RealNorm h).property,(kineticSourceCoeff8Row3RealNorm h).property,(kineticSourceCoeff9Row3RealNorm h).property,(kineticSourceCoeff10Row3RealNorm h).property,(kineticSourceCoeff11Row3RealNorm h).property,(kineticSourceCoeff12Row3RealNorm h).property,(kineticSourceCoeff13Row3RealNorm h).property]
    dsimp only [kineticSourceCoeff1Row3RealNorm,kineticSourceCoeff2Row3RealNorm,kineticSourceCoeff3Row3RealNorm,kineticSourceCoeff4Row3RealNorm,kineticSourceCoeff5Row3RealNorm,kineticSourceCoeff6Row3RealNorm,kineticSourceCoeff7Row3RealNorm,kineticSourceCoeff8Row3RealNorm,kineticSourceCoeff9Row3RealNorm,kineticSourceCoeff10Row3RealNorm,kineticSourceCoeff11Row3RealNorm,kineticSourceCoeff12Row3RealNorm,kineticSourceCoeff13Row3RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def negKineticSlopeControl12Drift3Norm (h : ℝ) : {c : ℝ // negKineticSlopeControlDriftCell h (1/3) 12 3=c} := by
  have he : negKineticSlopeControlDriftCell h (1/3) 12 3=negKineticSlopeControlDriftCell h (1/3) 12 3 := rfl
  conv at he =>
    rhs
    unfold negKineticSlopeControlDriftCell
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff1Row4RealNorm h).property,(kineticSourceCoeff2Row4RealNorm h).property,(kineticSourceCoeff3Row4RealNorm h).property,(kineticSourceCoeff4Row4RealNorm h).property,(kineticSourceCoeff5Row4RealNorm h).property,(kineticSourceCoeff6Row4RealNorm h).property,(kineticSourceCoeff7Row4RealNorm h).property,(kineticSourceCoeff8Row4RealNorm h).property,(kineticSourceCoeff9Row4RealNorm h).property,(kineticSourceCoeff10Row4RealNorm h).property,(kineticSourceCoeff11Row4RealNorm h).property,(kineticSourceCoeff12Row4RealNorm h).property,(kineticSourceCoeff13Row4RealNorm h).property]
    dsimp only [kineticSourceCoeff1Row4RealNorm,kineticSourceCoeff2Row4RealNorm,kineticSourceCoeff3Row4RealNorm,kineticSourceCoeff4Row4RealNorm,kineticSourceCoeff5Row4RealNorm,kineticSourceCoeff6Row4RealNorm,kineticSourceCoeff7Row4RealNorm,kineticSourceCoeff8Row4RealNorm,kineticSourceCoeff9Row4RealNorm,kineticSourceCoeff10Row4RealNorm,kineticSourceCoeff11Row4RealNorm,kineticSourceCoeff12Row4RealNorm,kineticSourceCoeff13Row4RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def negKineticSlopeControl12Drift4Norm (h : ℝ) : {c : ℝ // negKineticSlopeControlDriftCell h (1/3) 12 4=c} := by
  have he : negKineticSlopeControlDriftCell h (1/3) 12 4=negKineticSlopeControlDriftCell h (1/3) 12 4 := rfl
  conv at he =>
    rhs
    unfold negKineticSlopeControlDriftCell
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff1Row5RealNorm h).property,(kineticSourceCoeff2Row5RealNorm h).property,(kineticSourceCoeff3Row5RealNorm h).property,(kineticSourceCoeff4Row5RealNorm h).property,(kineticSourceCoeff5Row5RealNorm h).property,(kineticSourceCoeff6Row5RealNorm h).property,(kineticSourceCoeff7Row5RealNorm h).property,(kineticSourceCoeff8Row5RealNorm h).property,(kineticSourceCoeff9Row5RealNorm h).property,(kineticSourceCoeff10Row5RealNorm h).property,(kineticSourceCoeff11Row5RealNorm h).property,(kineticSourceCoeff12Row5RealNorm h).property,(kineticSourceCoeff13Row5RealNorm h).property]
    dsimp only [kineticSourceCoeff1Row5RealNorm,kineticSourceCoeff2Row5RealNorm,kineticSourceCoeff3Row5RealNorm,kineticSourceCoeff4Row5RealNorm,kineticSourceCoeff5Row5RealNorm,kineticSourceCoeff6Row5RealNorm,kineticSourceCoeff7Row5RealNorm,kineticSourceCoeff8Row5RealNorm,kineticSourceCoeff9Row5RealNorm,kineticSourceCoeff10Row5RealNorm,kineticSourceCoeff11Row5RealNorm,kineticSourceCoeff12Row5RealNorm,kineticSourceCoeff13Row5RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def negKineticSlopeControl12Drift5Norm (h : ℝ) : {c : ℝ // negKineticSlopeControlDriftCell h (1/3) 12 5=c} := by
  have he : negKineticSlopeControlDriftCell h (1/3) 12 5=negKineticSlopeControlDriftCell h (1/3) 12 5 := rfl
  conv at he =>
    rhs
    unfold negKineticSlopeControlDriftCell
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff1Row6RealNorm h).property,(kineticSourceCoeff2Row6RealNorm h).property,(kineticSourceCoeff3Row6RealNorm h).property,(kineticSourceCoeff4Row6RealNorm h).property,(kineticSourceCoeff5Row6RealNorm h).property,(kineticSourceCoeff6Row6RealNorm h).property,(kineticSourceCoeff7Row6RealNorm h).property,(kineticSourceCoeff8Row6RealNorm h).property,(kineticSourceCoeff9Row6RealNorm h).property,(kineticSourceCoeff10Row6RealNorm h).property,(kineticSourceCoeff11Row6RealNorm h).property,(kineticSourceCoeff12Row6RealNorm h).property,(kineticSourceCoeff13Row6RealNorm h).property]
    dsimp only [kineticSourceCoeff1Row6RealNorm,kineticSourceCoeff2Row6RealNorm,kineticSourceCoeff3Row6RealNorm,kineticSourceCoeff4Row6RealNorm,kineticSourceCoeff5Row6RealNorm,kineticSourceCoeff6Row6RealNorm,kineticSourceCoeff7Row6RealNorm,kineticSourceCoeff8Row6RealNorm,kineticSourceCoeff9Row6RealNorm,kineticSourceCoeff10Row6RealNorm,kineticSourceCoeff11Row6RealNorm,kineticSourceCoeff12Row6RealNorm,kineticSourceCoeff13Row6RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def negKineticSlopeControl12Drift6Norm (h : ℝ) : {c : ℝ // negKineticSlopeControlDriftCell h (1/3) 12 6=c} := by
  have he : negKineticSlopeControlDriftCell h (1/3) 12 6=negKineticSlopeControlDriftCell h (1/3) 12 6 := rfl
  conv at he =>
    rhs
    unfold negKineticSlopeControlDriftCell
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff1Row7RealNorm h).property,(kineticSourceCoeff2Row7RealNorm h).property,(kineticSourceCoeff3Row7RealNorm h).property,(kineticSourceCoeff4Row7RealNorm h).property,(kineticSourceCoeff5Row7RealNorm h).property,(kineticSourceCoeff6Row7RealNorm h).property,(kineticSourceCoeff7Row7RealNorm h).property,(kineticSourceCoeff8Row7RealNorm h).property,(kineticSourceCoeff9Row7RealNorm h).property,(kineticSourceCoeff10Row7RealNorm h).property,(kineticSourceCoeff11Row7RealNorm h).property,(kineticSourceCoeff12Row7RealNorm h).property,(kineticSourceCoeff13Row7RealNorm h).property]
    dsimp only [kineticSourceCoeff1Row7RealNorm,kineticSourceCoeff2Row7RealNorm,kineticSourceCoeff3Row7RealNorm,kineticSourceCoeff4Row7RealNorm,kineticSourceCoeff5Row7RealNorm,kineticSourceCoeff6Row7RealNorm,kineticSourceCoeff7Row7RealNorm,kineticSourceCoeff8Row7RealNorm,kineticSourceCoeff9Row7RealNorm,kineticSourceCoeff10Row7RealNorm,kineticSourceCoeff11Row7RealNorm,kineticSourceCoeff12Row7RealNorm,kineticSourceCoeff13Row7RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def negKineticSlopeControl12Drift7Norm (h : ℝ) : {c : ℝ // negKineticSlopeControlDriftCell h (1/3) 12 7=c} := by
  have he : negKineticSlopeControlDriftCell h (1/3) 12 7=negKineticSlopeControlDriftCell h (1/3) 12 7 := rfl
  conv at he =>
    rhs
    unfold negKineticSlopeControlDriftCell
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff1Row8RealNorm h).property,(kineticSourceCoeff2Row8RealNorm h).property,(kineticSourceCoeff3Row8RealNorm h).property,(kineticSourceCoeff4Row8RealNorm h).property,(kineticSourceCoeff5Row8RealNorm h).property,(kineticSourceCoeff6Row8RealNorm h).property,(kineticSourceCoeff7Row8RealNorm h).property,(kineticSourceCoeff8Row8RealNorm h).property,(kineticSourceCoeff9Row8RealNorm h).property,(kineticSourceCoeff10Row8RealNorm h).property,(kineticSourceCoeff11Row8RealNorm h).property,(kineticSourceCoeff12Row8RealNorm h).property,(kineticSourceCoeff13Row8RealNorm h).property]
    dsimp only [kineticSourceCoeff1Row8RealNorm,kineticSourceCoeff2Row8RealNorm,kineticSourceCoeff3Row8RealNorm,kineticSourceCoeff4Row8RealNorm,kineticSourceCoeff5Row8RealNorm,kineticSourceCoeff6Row8RealNorm,kineticSourceCoeff7Row8RealNorm,kineticSourceCoeff8Row8RealNorm,kineticSourceCoeff9Row8RealNorm,kineticSourceCoeff10Row8RealNorm,kineticSourceCoeff11Row8RealNorm,kineticSourceCoeff12Row8RealNorm,kineticSourceCoeff13Row8RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def negKineticSlopeControl12Drift8Norm (h : ℝ) : {c : ℝ // negKineticSlopeControlDriftCell h (1/3) 12 8=c} := by
  have he : negKineticSlopeControlDriftCell h (1/3) 12 8=negKineticSlopeControlDriftCell h (1/3) 12 8 := rfl
  conv at he =>
    rhs
    unfold negKineticSlopeControlDriftCell
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff1Row9RealNorm h).property,(kineticSourceCoeff2Row9RealNorm h).property,(kineticSourceCoeff3Row9RealNorm h).property,(kineticSourceCoeff4Row9RealNorm h).property,(kineticSourceCoeff5Row9RealNorm h).property,(kineticSourceCoeff6Row9RealNorm h).property,(kineticSourceCoeff7Row9RealNorm h).property,(kineticSourceCoeff8Row9RealNorm h).property,(kineticSourceCoeff9Row9RealNorm h).property,(kineticSourceCoeff10Row9RealNorm h).property,(kineticSourceCoeff11Row9RealNorm h).property,(kineticSourceCoeff12Row9RealNorm h).property,(kineticSourceCoeff13Row9RealNorm h).property]
    dsimp only [kineticSourceCoeff1Row9RealNorm,kineticSourceCoeff2Row9RealNorm,kineticSourceCoeff3Row9RealNorm,kineticSourceCoeff4Row9RealNorm,kineticSourceCoeff5Row9RealNorm,kineticSourceCoeff6Row9RealNorm,kineticSourceCoeff7Row9RealNorm,kineticSourceCoeff8Row9RealNorm,kineticSourceCoeff9Row9RealNorm,kineticSourceCoeff10Row9RealNorm,kineticSourceCoeff11Row9RealNorm,kineticSourceCoeff12Row9RealNorm,kineticSourceCoeff13Row9RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def negKineticSlopeControl12Drift9Norm (h : ℝ) : {c : ℝ // negKineticSlopeControlDriftCell h (1/3) 12 9=c} := by
  have he : negKineticSlopeControlDriftCell h (1/3) 12 9=negKineticSlopeControlDriftCell h (1/3) 12 9 := rfl
  conv at he =>
    rhs
    unfold negKineticSlopeControlDriftCell
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff1Row10RealNorm h).property,(kineticSourceCoeff2Row10RealNorm h).property,(kineticSourceCoeff3Row10RealNorm h).property,(kineticSourceCoeff4Row10RealNorm h).property,(kineticSourceCoeff5Row10RealNorm h).property,(kineticSourceCoeff6Row10RealNorm h).property,(kineticSourceCoeff7Row10RealNorm h).property,(kineticSourceCoeff8Row10RealNorm h).property,(kineticSourceCoeff9Row10RealNorm h).property,(kineticSourceCoeff10Row10RealNorm h).property,(kineticSourceCoeff11Row10RealNorm h).property,(kineticSourceCoeff12Row10RealNorm h).property,(kineticSourceCoeff13Row10RealNorm h).property]
    dsimp only [kineticSourceCoeff1Row10RealNorm,kineticSourceCoeff2Row10RealNorm,kineticSourceCoeff3Row10RealNorm,kineticSourceCoeff4Row10RealNorm,kineticSourceCoeff5Row10RealNorm,kineticSourceCoeff6Row10RealNorm,kineticSourceCoeff7Row10RealNorm,kineticSourceCoeff8Row10RealNorm,kineticSourceCoeff9Row10RealNorm,kineticSourceCoeff10Row10RealNorm,kineticSourceCoeff11Row10RealNorm,kineticSourceCoeff12Row10RealNorm,kineticSourceCoeff13Row10RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def negKineticSlopeDefectControl12Norm (h r : ℝ) :
    {c : ℝ // negKineticSlopeControl h (9-r*h^2) (1/3) 12=c} := by
  have he := negKineticSlopeControl_drift_expansion h (9-r*h^2) (1/3) 12
  conv at he =>
    rhs
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
    rw [(negKineticSlopeControl12Drift0Norm h).property,(negKineticSlopeControl12Drift1Norm h).property,(negKineticSlopeControl12Drift2Norm h).property,(negKineticSlopeControl12Drift3Norm h).property,(negKineticSlopeControl12Drift4Norm h).property,(negKineticSlopeControl12Drift5Norm h).property,(negKineticSlopeControl12Drift6Norm h).property,(negKineticSlopeControl12Drift7Norm h).property,(negKineticSlopeControl12Drift8Norm h).property,(negKineticSlopeControl12Drift9Norm h).property]
    dsimp only [negKineticSlopeControl12Drift0Norm,negKineticSlopeControl12Drift1Norm,negKineticSlopeControl12Drift2Norm,negKineticSlopeControl12Drift3Norm,negKineticSlopeControl12Drift4Norm,negKineticSlopeControl12Drift5Norm,negKineticSlopeControl12Drift6Norm,negKineticSlopeControl12Drift7Norm,negKineticSlopeControl12Drift8Norm,negKineticSlopeControl12Drift9Norm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

end
end HTGeometry.ThetaRatioKineticContraction

