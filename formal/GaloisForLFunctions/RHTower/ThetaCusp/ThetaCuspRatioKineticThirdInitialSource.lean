import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticThirdDerivative
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def kineticThirdInitialDrift0Norm (h : ℝ) : {c : ℝ // kineticThirdControlDriftCell h (1/3) 0 0=c} := by
  have he : kineticThirdControlDriftCell h (1/3) 0 0=kineticThirdControlDriftCell h (1/3) 0 0 := rfl
  conv at he =>
    rhs
    unfold kineticThirdControlDriftCell
    norm_num [Finset.sum_range_succ,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff3Row2RealNorm h).property]
    dsimp only [kineticSourceCoeff3Row2RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticThirdInitialDrift1Norm (h : ℝ) : {c : ℝ // kineticThirdControlDriftCell h (1/3) 0 1=c} := by
  have he : kineticThirdControlDriftCell h (1/3) 0 1=kineticThirdControlDriftCell h (1/3) 0 1 := rfl
  conv at he =>
    rhs
    unfold kineticThirdControlDriftCell
    norm_num [Finset.sum_range_succ,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff3Row3RealNorm h).property]
    dsimp only [kineticSourceCoeff3Row3RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticThirdInitialDrift2Norm (h : ℝ) : {c : ℝ // kineticThirdControlDriftCell h (1/3) 0 2=c} := by
  have he : kineticThirdControlDriftCell h (1/3) 0 2=kineticThirdControlDriftCell h (1/3) 0 2 := rfl
  conv at he =>
    rhs
    unfold kineticThirdControlDriftCell
    norm_num [Finset.sum_range_succ,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff3Row4RealNorm h).property]
    dsimp only [kineticSourceCoeff3Row4RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticThirdInitialDrift3Norm (h : ℝ) : {c : ℝ // kineticThirdControlDriftCell h (1/3) 0 3=c} := by
  have he : kineticThirdControlDriftCell h (1/3) 0 3=kineticThirdControlDriftCell h (1/3) 0 3 := rfl
  conv at he =>
    rhs
    unfold kineticThirdControlDriftCell
    norm_num [Finset.sum_range_succ,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff3Row5RealNorm h).property]
    dsimp only [kineticSourceCoeff3Row5RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticThirdInitialDrift4Norm (h : ℝ) : {c : ℝ // kineticThirdControlDriftCell h (1/3) 0 4=c} := by
  have he : kineticThirdControlDriftCell h (1/3) 0 4=kineticThirdControlDriftCell h (1/3) 0 4 := rfl
  conv at he =>
    rhs
    unfold kineticThirdControlDriftCell
    norm_num [Finset.sum_range_succ,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff3Row6RealNorm h).property]
    dsimp only [kineticSourceCoeff3Row6RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticThirdInitialDrift5Norm (h : ℝ) : {c : ℝ // kineticThirdControlDriftCell h (1/3) 0 5=c} := by
  have he : kineticThirdControlDriftCell h (1/3) 0 5=kineticThirdControlDriftCell h (1/3) 0 5 := rfl
  conv at he =>
    rhs
    unfold kineticThirdControlDriftCell
    norm_num [Finset.sum_range_succ,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff3Row7RealNorm h).property]
    dsimp only [kineticSourceCoeff3Row7RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticThirdInitialDrift6Norm (h : ℝ) : {c : ℝ // kineticThirdControlDriftCell h (1/3) 0 6=c} := by
  have he : kineticThirdControlDriftCell h (1/3) 0 6=kineticThirdControlDriftCell h (1/3) 0 6 := rfl
  conv at he =>
    rhs
    unfold kineticThirdControlDriftCell
    norm_num [Finset.sum_range_succ,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff3Row8RealNorm h).property]
    dsimp only [kineticSourceCoeff3Row8RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticThirdInitialDrift7Norm (h : ℝ) : {c : ℝ // kineticThirdControlDriftCell h (1/3) 0 7=c} := by
  have he : kineticThirdControlDriftCell h (1/3) 0 7=kineticThirdControlDriftCell h (1/3) 0 7 := rfl
  conv at he =>
    rhs
    unfold kineticThirdControlDriftCell
    norm_num [Finset.sum_range_succ,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff3Row9RealNorm h).property]
    dsimp only [kineticSourceCoeff3Row9RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticThirdInitialDrift8Norm (h : ℝ) : {c : ℝ // kineticThirdControlDriftCell h (1/3) 0 8=c} := by
  have he : kineticThirdControlDriftCell h (1/3) 0 8=kineticThirdControlDriftCell h (1/3) 0 8 := rfl
  conv at he =>
    rhs
    unfold kineticThirdControlDriftCell
    norm_num [Finset.sum_range_succ,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff3Row10RealNorm h).property]
    dsimp only [kineticSourceCoeff3Row10RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticThirdInitialNorm (h r : ℝ) :
    {c : ℝ // kineticThirdControl h (9-r*h^2) (1/3) 0=c} := by
  have he := kineticThirdControl_drift_expansion h (9-r*h^2) (1/3) 0
  conv at he =>
    rhs
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
    rw [(kineticThirdInitialDrift0Norm h).property,(kineticThirdInitialDrift1Norm h).property,(kineticThirdInitialDrift2Norm h).property,(kineticThirdInitialDrift3Norm h).property,(kineticThirdInitialDrift4Norm h).property,(kineticThirdInitialDrift5Norm h).property,(kineticThirdInitialDrift6Norm h).property,(kineticThirdInitialDrift7Norm h).property,(kineticThirdInitialDrift8Norm h).property]
    dsimp only [kineticThirdInitialDrift0Norm,kineticThirdInitialDrift1Norm,kineticThirdInitialDrift2Norm,kineticThirdInitialDrift3Norm,kineticThirdInitialDrift4Norm,kineticThirdInitialDrift5Norm,kineticThirdInitialDrift6Norm,kineticThirdInitialDrift7Norm,kineticThirdInitialDrift8Norm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

end
end HTGeometry.ThetaRatioKineticContraction

