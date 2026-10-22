import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticControlDrift
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSourceRow2
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSourceRow3
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSourceRow4
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSourceRow5
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSourceRow6
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSourceRow7
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSourceRow8
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSourceRow9
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSourceRow10
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSourceRow11
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSourceRow12
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSourceRow13
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSourceRow14
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSourceRow15
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSourceRow16
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSourceRow17
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSourceRow18
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

def reducedKineticControl18Drift0Norm (h : ℝ) : {c : ℝ // reducedKineticControlDriftCell h (1/3) 18 0=c} := by
  have he : reducedKineticControlDriftCell h (1/3) 18 0=reducedKineticControlDriftCell h (1/3) 18 0 := rfl
  conv at he =>
    rhs
    unfold reducedKineticControlDriftCell
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff0Row1RealNorm h).property,(kineticSourceCoeff1Row1RealNorm h).property,(kineticSourceCoeff2Row1RealNorm h).property,(kineticSourceCoeff3Row1RealNorm h).property,(kineticSourceCoeff4Row1RealNorm h).property,(kineticSourceCoeff5Row1RealNorm h).property,(kineticSourceCoeff6Row1RealNorm h).property,(kineticSourceCoeff7Row1RealNorm h).property,(kineticSourceCoeff8Row1RealNorm h).property,(kineticSourceCoeff9Row1RealNorm h).property,(kineticSourceCoeff10Row1RealNorm h).property,(kineticSourceCoeff11Row1RealNorm h).property,(kineticSourceCoeff12Row1RealNorm h).property,(kineticSourceCoeff13Row1RealNorm h).property,(kineticSourceCoeff14Row1RealNorm h).property,(kineticSourceCoeff15Row1RealNorm h).property,(kineticSourceCoeff16Row1RealNorm h).property,(kineticSourceCoeff17Row1RealNorm h).property,(kineticSourceCoeff18Row1RealNorm h).property]
    dsimp only [kineticSourceCoeff0Row1RealNorm,kineticSourceCoeff1Row1RealNorm,kineticSourceCoeff2Row1RealNorm,kineticSourceCoeff3Row1RealNorm,kineticSourceCoeff4Row1RealNorm,kineticSourceCoeff5Row1RealNorm,kineticSourceCoeff6Row1RealNorm,kineticSourceCoeff7Row1RealNorm,kineticSourceCoeff8Row1RealNorm,kineticSourceCoeff9Row1RealNorm,kineticSourceCoeff10Row1RealNorm,kineticSourceCoeff11Row1RealNorm,kineticSourceCoeff12Row1RealNorm,kineticSourceCoeff13Row1RealNorm,kineticSourceCoeff14Row1RealNorm,kineticSourceCoeff15Row1RealNorm,kineticSourceCoeff16Row1RealNorm,kineticSourceCoeff17Row1RealNorm,kineticSourceCoeff18Row1RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def reducedKineticControl18Drift1Norm (h : ℝ) : {c : ℝ // reducedKineticControlDriftCell h (1/3) 18 1=c} := by
  have he : reducedKineticControlDriftCell h (1/3) 18 1=reducedKineticControlDriftCell h (1/3) 18 1 := rfl
  conv at he =>
    rhs
    unfold reducedKineticControlDriftCell
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff0Row2RealNorm h).property,(kineticSourceCoeff1Row2RealNorm h).property,(kineticSourceCoeff2Row2RealNorm h).property,(kineticSourceCoeff3Row2RealNorm h).property,(kineticSourceCoeff4Row2RealNorm h).property,(kineticSourceCoeff5Row2RealNorm h).property,(kineticSourceCoeff6Row2RealNorm h).property,(kineticSourceCoeff7Row2RealNorm h).property,(kineticSourceCoeff8Row2RealNorm h).property,(kineticSourceCoeff9Row2RealNorm h).property,(kineticSourceCoeff10Row2RealNorm h).property,(kineticSourceCoeff11Row2RealNorm h).property,(kineticSourceCoeff12Row2RealNorm h).property,(kineticSourceCoeff13Row2RealNorm h).property,(kineticSourceCoeff14Row2RealNorm h).property,(kineticSourceCoeff15Row2RealNorm h).property,(kineticSourceCoeff16Row2RealNorm h).property,(kineticSourceCoeff17Row2RealNorm h).property,(kineticSourceCoeff18Row2RealNorm h).property]
    dsimp only [kineticSourceCoeff0Row2RealNorm,kineticSourceCoeff1Row2RealNorm,kineticSourceCoeff2Row2RealNorm,kineticSourceCoeff3Row2RealNorm,kineticSourceCoeff4Row2RealNorm,kineticSourceCoeff5Row2RealNorm,kineticSourceCoeff6Row2RealNorm,kineticSourceCoeff7Row2RealNorm,kineticSourceCoeff8Row2RealNorm,kineticSourceCoeff9Row2RealNorm,kineticSourceCoeff10Row2RealNorm,kineticSourceCoeff11Row2RealNorm,kineticSourceCoeff12Row2RealNorm,kineticSourceCoeff13Row2RealNorm,kineticSourceCoeff14Row2RealNorm,kineticSourceCoeff15Row2RealNorm,kineticSourceCoeff16Row2RealNorm,kineticSourceCoeff17Row2RealNorm,kineticSourceCoeff18Row2RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def reducedKineticControl18Drift2Norm (h : ℝ) : {c : ℝ // reducedKineticControlDriftCell h (1/3) 18 2=c} := by
  have he : reducedKineticControlDriftCell h (1/3) 18 2=reducedKineticControlDriftCell h (1/3) 18 2 := rfl
  conv at he =>
    rhs
    unfold reducedKineticControlDriftCell
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff0Row3RealNorm h).property,(kineticSourceCoeff1Row3RealNorm h).property,(kineticSourceCoeff2Row3RealNorm h).property,(kineticSourceCoeff3Row3RealNorm h).property,(kineticSourceCoeff4Row3RealNorm h).property,(kineticSourceCoeff5Row3RealNorm h).property,(kineticSourceCoeff6Row3RealNorm h).property,(kineticSourceCoeff7Row3RealNorm h).property,(kineticSourceCoeff8Row3RealNorm h).property,(kineticSourceCoeff9Row3RealNorm h).property,(kineticSourceCoeff10Row3RealNorm h).property,(kineticSourceCoeff11Row3RealNorm h).property,(kineticSourceCoeff12Row3RealNorm h).property,(kineticSourceCoeff13Row3RealNorm h).property,(kineticSourceCoeff14Row3RealNorm h).property,(kineticSourceCoeff15Row3RealNorm h).property,(kineticSourceCoeff16Row3RealNorm h).property,(kineticSourceCoeff17Row3RealNorm h).property,(kineticSourceCoeff18Row3RealNorm h).property]
    dsimp only [kineticSourceCoeff0Row3RealNorm,kineticSourceCoeff1Row3RealNorm,kineticSourceCoeff2Row3RealNorm,kineticSourceCoeff3Row3RealNorm,kineticSourceCoeff4Row3RealNorm,kineticSourceCoeff5Row3RealNorm,kineticSourceCoeff6Row3RealNorm,kineticSourceCoeff7Row3RealNorm,kineticSourceCoeff8Row3RealNorm,kineticSourceCoeff9Row3RealNorm,kineticSourceCoeff10Row3RealNorm,kineticSourceCoeff11Row3RealNorm,kineticSourceCoeff12Row3RealNorm,kineticSourceCoeff13Row3RealNorm,kineticSourceCoeff14Row3RealNorm,kineticSourceCoeff15Row3RealNorm,kineticSourceCoeff16Row3RealNorm,kineticSourceCoeff17Row3RealNorm,kineticSourceCoeff18Row3RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def reducedKineticControl18Drift3Norm (h : ℝ) : {c : ℝ // reducedKineticControlDriftCell h (1/3) 18 3=c} := by
  have he : reducedKineticControlDriftCell h (1/3) 18 3=reducedKineticControlDriftCell h (1/3) 18 3 := rfl
  conv at he =>
    rhs
    unfold reducedKineticControlDriftCell
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff0Row4RealNorm h).property,(kineticSourceCoeff1Row4RealNorm h).property,(kineticSourceCoeff2Row4RealNorm h).property,(kineticSourceCoeff3Row4RealNorm h).property,(kineticSourceCoeff4Row4RealNorm h).property,(kineticSourceCoeff5Row4RealNorm h).property,(kineticSourceCoeff6Row4RealNorm h).property,(kineticSourceCoeff7Row4RealNorm h).property,(kineticSourceCoeff8Row4RealNorm h).property,(kineticSourceCoeff9Row4RealNorm h).property,(kineticSourceCoeff10Row4RealNorm h).property,(kineticSourceCoeff11Row4RealNorm h).property,(kineticSourceCoeff12Row4RealNorm h).property,(kineticSourceCoeff13Row4RealNorm h).property,(kineticSourceCoeff14Row4RealNorm h).property,(kineticSourceCoeff15Row4RealNorm h).property,(kineticSourceCoeff16Row4RealNorm h).property,(kineticSourceCoeff17Row4RealNorm h).property,(kineticSourceCoeff18Row4RealNorm h).property]
    dsimp only [kineticSourceCoeff0Row4RealNorm,kineticSourceCoeff1Row4RealNorm,kineticSourceCoeff2Row4RealNorm,kineticSourceCoeff3Row4RealNorm,kineticSourceCoeff4Row4RealNorm,kineticSourceCoeff5Row4RealNorm,kineticSourceCoeff6Row4RealNorm,kineticSourceCoeff7Row4RealNorm,kineticSourceCoeff8Row4RealNorm,kineticSourceCoeff9Row4RealNorm,kineticSourceCoeff10Row4RealNorm,kineticSourceCoeff11Row4RealNorm,kineticSourceCoeff12Row4RealNorm,kineticSourceCoeff13Row4RealNorm,kineticSourceCoeff14Row4RealNorm,kineticSourceCoeff15Row4RealNorm,kineticSourceCoeff16Row4RealNorm,kineticSourceCoeff17Row4RealNorm,kineticSourceCoeff18Row4RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def reducedKineticControl18Drift4Norm (h : ℝ) : {c : ℝ // reducedKineticControlDriftCell h (1/3) 18 4=c} := by
  have he : reducedKineticControlDriftCell h (1/3) 18 4=reducedKineticControlDriftCell h (1/3) 18 4 := rfl
  conv at he =>
    rhs
    unfold reducedKineticControlDriftCell
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff0Row5RealNorm h).property,(kineticSourceCoeff1Row5RealNorm h).property,(kineticSourceCoeff2Row5RealNorm h).property,(kineticSourceCoeff3Row5RealNorm h).property,(kineticSourceCoeff4Row5RealNorm h).property,(kineticSourceCoeff5Row5RealNorm h).property,(kineticSourceCoeff6Row5RealNorm h).property,(kineticSourceCoeff7Row5RealNorm h).property,(kineticSourceCoeff8Row5RealNorm h).property,(kineticSourceCoeff9Row5RealNorm h).property,(kineticSourceCoeff10Row5RealNorm h).property,(kineticSourceCoeff11Row5RealNorm h).property,(kineticSourceCoeff12Row5RealNorm h).property,(kineticSourceCoeff13Row5RealNorm h).property,(kineticSourceCoeff14Row5RealNorm h).property,(kineticSourceCoeff15Row5RealNorm h).property,(kineticSourceCoeff16Row5RealNorm h).property,(kineticSourceCoeff17Row5RealNorm h).property,(kineticSourceCoeff18Row5RealNorm h).property]
    dsimp only [kineticSourceCoeff0Row5RealNorm,kineticSourceCoeff1Row5RealNorm,kineticSourceCoeff2Row5RealNorm,kineticSourceCoeff3Row5RealNorm,kineticSourceCoeff4Row5RealNorm,kineticSourceCoeff5Row5RealNorm,kineticSourceCoeff6Row5RealNorm,kineticSourceCoeff7Row5RealNorm,kineticSourceCoeff8Row5RealNorm,kineticSourceCoeff9Row5RealNorm,kineticSourceCoeff10Row5RealNorm,kineticSourceCoeff11Row5RealNorm,kineticSourceCoeff12Row5RealNorm,kineticSourceCoeff13Row5RealNorm,kineticSourceCoeff14Row5RealNorm,kineticSourceCoeff15Row5RealNorm,kineticSourceCoeff16Row5RealNorm,kineticSourceCoeff17Row5RealNorm,kineticSourceCoeff18Row5RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def reducedKineticControl18Drift5Norm (h : ℝ) : {c : ℝ // reducedKineticControlDriftCell h (1/3) 18 5=c} := by
  have he : reducedKineticControlDriftCell h (1/3) 18 5=reducedKineticControlDriftCell h (1/3) 18 5 := rfl
  conv at he =>
    rhs
    unfold reducedKineticControlDriftCell
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff0Row6RealNorm h).property,(kineticSourceCoeff1Row6RealNorm h).property,(kineticSourceCoeff2Row6RealNorm h).property,(kineticSourceCoeff3Row6RealNorm h).property,(kineticSourceCoeff4Row6RealNorm h).property,(kineticSourceCoeff5Row6RealNorm h).property,(kineticSourceCoeff6Row6RealNorm h).property,(kineticSourceCoeff7Row6RealNorm h).property,(kineticSourceCoeff8Row6RealNorm h).property,(kineticSourceCoeff9Row6RealNorm h).property,(kineticSourceCoeff10Row6RealNorm h).property,(kineticSourceCoeff11Row6RealNorm h).property,(kineticSourceCoeff12Row6RealNorm h).property,(kineticSourceCoeff13Row6RealNorm h).property,(kineticSourceCoeff14Row6RealNorm h).property,(kineticSourceCoeff15Row6RealNorm h).property,(kineticSourceCoeff16Row6RealNorm h).property,(kineticSourceCoeff17Row6RealNorm h).property,(kineticSourceCoeff18Row6RealNorm h).property]
    dsimp only [kineticSourceCoeff0Row6RealNorm,kineticSourceCoeff1Row6RealNorm,kineticSourceCoeff2Row6RealNorm,kineticSourceCoeff3Row6RealNorm,kineticSourceCoeff4Row6RealNorm,kineticSourceCoeff5Row6RealNorm,kineticSourceCoeff6Row6RealNorm,kineticSourceCoeff7Row6RealNorm,kineticSourceCoeff8Row6RealNorm,kineticSourceCoeff9Row6RealNorm,kineticSourceCoeff10Row6RealNorm,kineticSourceCoeff11Row6RealNorm,kineticSourceCoeff12Row6RealNorm,kineticSourceCoeff13Row6RealNorm,kineticSourceCoeff14Row6RealNorm,kineticSourceCoeff15Row6RealNorm,kineticSourceCoeff16Row6RealNorm,kineticSourceCoeff17Row6RealNorm,kineticSourceCoeff18Row6RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def reducedKineticControl18Drift6Norm (h : ℝ) : {c : ℝ // reducedKineticControlDriftCell h (1/3) 18 6=c} := by
  have he : reducedKineticControlDriftCell h (1/3) 18 6=reducedKineticControlDriftCell h (1/3) 18 6 := rfl
  conv at he =>
    rhs
    unfold reducedKineticControlDriftCell
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff0Row7RealNorm h).property,(kineticSourceCoeff1Row7RealNorm h).property,(kineticSourceCoeff2Row7RealNorm h).property,(kineticSourceCoeff3Row7RealNorm h).property,(kineticSourceCoeff4Row7RealNorm h).property,(kineticSourceCoeff5Row7RealNorm h).property,(kineticSourceCoeff6Row7RealNorm h).property,(kineticSourceCoeff7Row7RealNorm h).property,(kineticSourceCoeff8Row7RealNorm h).property,(kineticSourceCoeff9Row7RealNorm h).property,(kineticSourceCoeff10Row7RealNorm h).property,(kineticSourceCoeff11Row7RealNorm h).property,(kineticSourceCoeff12Row7RealNorm h).property,(kineticSourceCoeff13Row7RealNorm h).property,(kineticSourceCoeff14Row7RealNorm h).property,(kineticSourceCoeff15Row7RealNorm h).property,(kineticSourceCoeff16Row7RealNorm h).property,(kineticSourceCoeff17Row7RealNorm h).property,(kineticSourceCoeff18Row7RealNorm h).property]
    dsimp only [kineticSourceCoeff0Row7RealNorm,kineticSourceCoeff1Row7RealNorm,kineticSourceCoeff2Row7RealNorm,kineticSourceCoeff3Row7RealNorm,kineticSourceCoeff4Row7RealNorm,kineticSourceCoeff5Row7RealNorm,kineticSourceCoeff6Row7RealNorm,kineticSourceCoeff7Row7RealNorm,kineticSourceCoeff8Row7RealNorm,kineticSourceCoeff9Row7RealNorm,kineticSourceCoeff10Row7RealNorm,kineticSourceCoeff11Row7RealNorm,kineticSourceCoeff12Row7RealNorm,kineticSourceCoeff13Row7RealNorm,kineticSourceCoeff14Row7RealNorm,kineticSourceCoeff15Row7RealNorm,kineticSourceCoeff16Row7RealNorm,kineticSourceCoeff17Row7RealNorm,kineticSourceCoeff18Row7RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def reducedKineticControl18Drift7Norm (h : ℝ) : {c : ℝ // reducedKineticControlDriftCell h (1/3) 18 7=c} := by
  have he : reducedKineticControlDriftCell h (1/3) 18 7=reducedKineticControlDriftCell h (1/3) 18 7 := rfl
  conv at he =>
    rhs
    unfold reducedKineticControlDriftCell
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff0Row8RealNorm h).property,(kineticSourceCoeff1Row8RealNorm h).property,(kineticSourceCoeff2Row8RealNorm h).property,(kineticSourceCoeff3Row8RealNorm h).property,(kineticSourceCoeff4Row8RealNorm h).property,(kineticSourceCoeff5Row8RealNorm h).property,(kineticSourceCoeff6Row8RealNorm h).property,(kineticSourceCoeff7Row8RealNorm h).property,(kineticSourceCoeff8Row8RealNorm h).property,(kineticSourceCoeff9Row8RealNorm h).property,(kineticSourceCoeff10Row8RealNorm h).property,(kineticSourceCoeff11Row8RealNorm h).property,(kineticSourceCoeff12Row8RealNorm h).property,(kineticSourceCoeff13Row8RealNorm h).property,(kineticSourceCoeff14Row8RealNorm h).property,(kineticSourceCoeff15Row8RealNorm h).property,(kineticSourceCoeff16Row8RealNorm h).property,(kineticSourceCoeff17Row8RealNorm h).property,(kineticSourceCoeff18Row8RealNorm h).property]
    dsimp only [kineticSourceCoeff0Row8RealNorm,kineticSourceCoeff1Row8RealNorm,kineticSourceCoeff2Row8RealNorm,kineticSourceCoeff3Row8RealNorm,kineticSourceCoeff4Row8RealNorm,kineticSourceCoeff5Row8RealNorm,kineticSourceCoeff6Row8RealNorm,kineticSourceCoeff7Row8RealNorm,kineticSourceCoeff8Row8RealNorm,kineticSourceCoeff9Row8RealNorm,kineticSourceCoeff10Row8RealNorm,kineticSourceCoeff11Row8RealNorm,kineticSourceCoeff12Row8RealNorm,kineticSourceCoeff13Row8RealNorm,kineticSourceCoeff14Row8RealNorm,kineticSourceCoeff15Row8RealNorm,kineticSourceCoeff16Row8RealNorm,kineticSourceCoeff17Row8RealNorm,kineticSourceCoeff18Row8RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def reducedKineticControl18Drift8Norm (h : ℝ) : {c : ℝ // reducedKineticControlDriftCell h (1/3) 18 8=c} := by
  have he : reducedKineticControlDriftCell h (1/3) 18 8=reducedKineticControlDriftCell h (1/3) 18 8 := rfl
  conv at he =>
    rhs
    unfold reducedKineticControlDriftCell
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff0Row9RealNorm h).property,(kineticSourceCoeff1Row9RealNorm h).property,(kineticSourceCoeff2Row9RealNorm h).property,(kineticSourceCoeff3Row9RealNorm h).property,(kineticSourceCoeff4Row9RealNorm h).property,(kineticSourceCoeff5Row9RealNorm h).property,(kineticSourceCoeff6Row9RealNorm h).property,(kineticSourceCoeff7Row9RealNorm h).property,(kineticSourceCoeff8Row9RealNorm h).property,(kineticSourceCoeff9Row9RealNorm h).property,(kineticSourceCoeff10Row9RealNorm h).property,(kineticSourceCoeff11Row9RealNorm h).property,(kineticSourceCoeff12Row9RealNorm h).property,(kineticSourceCoeff13Row9RealNorm h).property,(kineticSourceCoeff14Row9RealNorm h).property,(kineticSourceCoeff15Row9RealNorm h).property,(kineticSourceCoeff16Row9RealNorm h).property,(kineticSourceCoeff17Row9RealNorm h).property,(kineticSourceCoeff18Row9RealNorm h).property]
    dsimp only [kineticSourceCoeff0Row9RealNorm,kineticSourceCoeff1Row9RealNorm,kineticSourceCoeff2Row9RealNorm,kineticSourceCoeff3Row9RealNorm,kineticSourceCoeff4Row9RealNorm,kineticSourceCoeff5Row9RealNorm,kineticSourceCoeff6Row9RealNorm,kineticSourceCoeff7Row9RealNorm,kineticSourceCoeff8Row9RealNorm,kineticSourceCoeff9Row9RealNorm,kineticSourceCoeff10Row9RealNorm,kineticSourceCoeff11Row9RealNorm,kineticSourceCoeff12Row9RealNorm,kineticSourceCoeff13Row9RealNorm,kineticSourceCoeff14Row9RealNorm,kineticSourceCoeff15Row9RealNorm,kineticSourceCoeff16Row9RealNorm,kineticSourceCoeff17Row9RealNorm,kineticSourceCoeff18Row9RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def reducedKineticControl18Drift9Norm (h : ℝ) : {c : ℝ // reducedKineticControlDriftCell h (1/3) 18 9=c} := by
  have he : reducedKineticControlDriftCell h (1/3) 18 9=reducedKineticControlDriftCell h (1/3) 18 9 := rfl
  conv at he =>
    rhs
    unfold reducedKineticControlDriftCell
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero]
    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial,Nat.factorial]
    rw [(kineticSourceCoeff0Row10RealNorm h).property,(kineticSourceCoeff1Row10RealNorm h).property,(kineticSourceCoeff2Row10RealNorm h).property,(kineticSourceCoeff3Row10RealNorm h).property,(kineticSourceCoeff4Row10RealNorm h).property,(kineticSourceCoeff5Row10RealNorm h).property,(kineticSourceCoeff6Row10RealNorm h).property,(kineticSourceCoeff7Row10RealNorm h).property,(kineticSourceCoeff8Row10RealNorm h).property,(kineticSourceCoeff9Row10RealNorm h).property,(kineticSourceCoeff10Row10RealNorm h).property,(kineticSourceCoeff11Row10RealNorm h).property,(kineticSourceCoeff12Row10RealNorm h).property,(kineticSourceCoeff13Row10RealNorm h).property,(kineticSourceCoeff14Row10RealNorm h).property,(kineticSourceCoeff15Row10RealNorm h).property,(kineticSourceCoeff16Row10RealNorm h).property,(kineticSourceCoeff17Row10RealNorm h).property,(kineticSourceCoeff18Row10RealNorm h).property]
    dsimp only [kineticSourceCoeff0Row10RealNorm,kineticSourceCoeff1Row10RealNorm,kineticSourceCoeff2Row10RealNorm,kineticSourceCoeff3Row10RealNorm,kineticSourceCoeff4Row10RealNorm,kineticSourceCoeff5Row10RealNorm,kineticSourceCoeff6Row10RealNorm,kineticSourceCoeff7Row10RealNorm,kineticSourceCoeff8Row10RealNorm,kineticSourceCoeff9Row10RealNorm,kineticSourceCoeff10Row10RealNorm,kineticSourceCoeff11Row10RealNorm,kineticSourceCoeff12Row10RealNorm,kineticSourceCoeff13Row10RealNorm,kineticSourceCoeff14Row10RealNorm,kineticSourceCoeff15Row10RealNorm,kineticSourceCoeff16Row10RealNorm,kineticSourceCoeff17Row10RealNorm,kineticSourceCoeff18Row10RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def reducedKineticDefectControl18Norm (h r : ℝ) :
    {c : ℝ // reducedKineticControl h (9-r*h^2) (1/3) 18=c} := by
  have he := reducedKineticControl_drift_expansion h (9-r*h^2) (1/3) 18
  conv at he =>
    rhs
    norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
    rw [(reducedKineticControl18Drift0Norm h).property,(reducedKineticControl18Drift1Norm h).property,(reducedKineticControl18Drift2Norm h).property,(reducedKineticControl18Drift3Norm h).property,(reducedKineticControl18Drift4Norm h).property,(reducedKineticControl18Drift5Norm h).property,(reducedKineticControl18Drift6Norm h).property,(reducedKineticControl18Drift7Norm h).property,(reducedKineticControl18Drift8Norm h).property,(reducedKineticControl18Drift9Norm h).property]
    dsimp only [reducedKineticControl18Drift0Norm,reducedKineticControl18Drift1Norm,reducedKineticControl18Drift2Norm,reducedKineticControl18Drift3Norm,reducedKineticControl18Drift4Norm,reducedKineticControl18Drift5Norm,reducedKineticControl18Drift6Norm,reducedKineticControl18Drift7Norm,reducedKineticControl18Drift8Norm,reducedKineticControl18Drift9Norm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

end
end HTGeometry.ThetaRatioKineticContraction

