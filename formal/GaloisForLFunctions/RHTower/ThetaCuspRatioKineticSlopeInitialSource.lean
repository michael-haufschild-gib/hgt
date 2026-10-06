import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSlopeControl
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

theorem negKineticSlopeControl_zero (h v Z : ℝ) :
    negKineticSlopeControl h v Z 0 = -reducedKineticCoefficient h v 1 := by
  norm_num [negKineticSlopeControl,kineticControl,Finset.sum_range_succ,
    degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,Nat.factorial]

theorem reducedKineticValue_zero_deriv (h v : ℝ) :
    deriv (reducedKineticValue h v) 0 = reducedKineticCoefficient h v 1 := by
  rw [(reducedKineticValue_hasDerivAt h v 0).deriv]
  norm_num [reducedKineticSlopeValue,Finset.sum_range_succ]

def negKineticSlopeInitialDrift0Norm (h : ℝ) : {c : ℝ // negKineticSlopeControlDriftCell h (1/3) 0 0=c} := by
  have he : negKineticSlopeControlDriftCell h (1/3) 0 0=negKineticSlopeControlDriftCell h (1/3) 0 0 := rfl
  conv at he =>
    rhs
    unfold negKineticSlopeControlDriftCell
    norm_num [Finset.sum_range_succ,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff1Row1RealNorm h).property]
    dsimp only [kineticSourceCoeff1Row1RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def negKineticSlopeInitialDrift1Norm (h : ℝ) : {c : ℝ // negKineticSlopeControlDriftCell h (1/3) 0 1=c} := by
  have he : negKineticSlopeControlDriftCell h (1/3) 0 1=negKineticSlopeControlDriftCell h (1/3) 0 1 := rfl
  conv at he =>
    rhs
    unfold negKineticSlopeControlDriftCell
    norm_num [Finset.sum_range_succ,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff1Row2RealNorm h).property]
    dsimp only [kineticSourceCoeff1Row2RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def negKineticSlopeInitialDrift2Norm (h : ℝ) : {c : ℝ // negKineticSlopeControlDriftCell h (1/3) 0 2=c} := by
  have he : negKineticSlopeControlDriftCell h (1/3) 0 2=negKineticSlopeControlDriftCell h (1/3) 0 2 := rfl
  conv at he =>
    rhs
    unfold negKineticSlopeControlDriftCell
    norm_num [Finset.sum_range_succ,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff1Row3RealNorm h).property]
    dsimp only [kineticSourceCoeff1Row3RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def negKineticSlopeInitialDrift3Norm (h : ℝ) : {c : ℝ // negKineticSlopeControlDriftCell h (1/3) 0 3=c} := by
  have he : negKineticSlopeControlDriftCell h (1/3) 0 3=negKineticSlopeControlDriftCell h (1/3) 0 3 := rfl
  conv at he =>
    rhs
    unfold negKineticSlopeControlDriftCell
    norm_num [Finset.sum_range_succ,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff1Row4RealNorm h).property]
    dsimp only [kineticSourceCoeff1Row4RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def negKineticSlopeInitialDrift4Norm (h : ℝ) : {c : ℝ // negKineticSlopeControlDriftCell h (1/3) 0 4=c} := by
  have he : negKineticSlopeControlDriftCell h (1/3) 0 4=negKineticSlopeControlDriftCell h (1/3) 0 4 := rfl
  conv at he =>
    rhs
    unfold negKineticSlopeControlDriftCell
    norm_num [Finset.sum_range_succ,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff1Row5RealNorm h).property]
    dsimp only [kineticSourceCoeff1Row5RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def negKineticSlopeInitialDrift5Norm (h : ℝ) : {c : ℝ // negKineticSlopeControlDriftCell h (1/3) 0 5=c} := by
  have he : negKineticSlopeControlDriftCell h (1/3) 0 5=negKineticSlopeControlDriftCell h (1/3) 0 5 := rfl
  conv at he =>
    rhs
    unfold negKineticSlopeControlDriftCell
    norm_num [Finset.sum_range_succ,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff1Row6RealNorm h).property]
    dsimp only [kineticSourceCoeff1Row6RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def negKineticSlopeInitialDrift6Norm (h : ℝ) : {c : ℝ // negKineticSlopeControlDriftCell h (1/3) 0 6=c} := by
  have he : negKineticSlopeControlDriftCell h (1/3) 0 6=negKineticSlopeControlDriftCell h (1/3) 0 6 := rfl
  conv at he =>
    rhs
    unfold negKineticSlopeControlDriftCell
    norm_num [Finset.sum_range_succ,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff1Row7RealNorm h).property]
    dsimp only [kineticSourceCoeff1Row7RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def negKineticSlopeInitialDrift7Norm (h : ℝ) : {c : ℝ // negKineticSlopeControlDriftCell h (1/3) 0 7=c} := by
  have he : negKineticSlopeControlDriftCell h (1/3) 0 7=negKineticSlopeControlDriftCell h (1/3) 0 7 := rfl
  conv at he =>
    rhs
    unfold negKineticSlopeControlDriftCell
    norm_num [Finset.sum_range_succ,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff1Row8RealNorm h).property]
    dsimp only [kineticSourceCoeff1Row8RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def negKineticSlopeInitialDrift8Norm (h : ℝ) : {c : ℝ // negKineticSlopeControlDriftCell h (1/3) 0 8=c} := by
  have he : negKineticSlopeControlDriftCell h (1/3) 0 8=negKineticSlopeControlDriftCell h (1/3) 0 8 := rfl
  conv at he =>
    rhs
    unfold negKineticSlopeControlDriftCell
    norm_num [Finset.sum_range_succ,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff1Row9RealNorm h).property]
    dsimp only [kineticSourceCoeff1Row9RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def negKineticSlopeInitialDrift9Norm (h : ℝ) : {c : ℝ // negKineticSlopeControlDriftCell h (1/3) 0 9=c} := by
  have he : negKineticSlopeControlDriftCell h (1/3) 0 9=negKineticSlopeControlDriftCell h (1/3) 0 9 := rfl
  conv at he =>
    rhs
    unfold negKineticSlopeControlDriftCell
    norm_num [Finset.sum_range_succ,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff1Row10RealNorm h).property]
    dsimp only [kineticSourceCoeff1Row10RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def negKineticSlopeInitialNorm (h r : ℝ) :
    {c : ℝ // negKineticSlopeControl h (9-r*h^2) (1/3) 0=c} := by
  have he := negKineticSlopeControl_drift_expansion h (9-r*h^2) (1/3) 0
  conv at he =>
    rhs
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
    rw [(negKineticSlopeInitialDrift0Norm h).property,(negKineticSlopeInitialDrift1Norm h).property,(negKineticSlopeInitialDrift2Norm h).property,(negKineticSlopeInitialDrift3Norm h).property,(negKineticSlopeInitialDrift4Norm h).property,(negKineticSlopeInitialDrift5Norm h).property,(negKineticSlopeInitialDrift6Norm h).property,(negKineticSlopeInitialDrift7Norm h).property,(negKineticSlopeInitialDrift8Norm h).property,(negKineticSlopeInitialDrift9Norm h).property]
    dsimp only [negKineticSlopeInitialDrift0Norm,negKineticSlopeInitialDrift1Norm,negKineticSlopeInitialDrift2Norm,negKineticSlopeInitialDrift3Norm,negKineticSlopeInitialDrift4Norm,negKineticSlopeInitialDrift5Norm,negKineticSlopeInitialDrift6Norm,negKineticSlopeInitialDrift7Norm,negKineticSlopeInitialDrift8Norm,negKineticSlopeInitialDrift9Norm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

end
end HTGeometry.ThetaRatioKineticContraction
