import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerBernstein6_36Norm

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree0Scaled

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree1Scaled

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree2Scaled

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree3Scaled

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree4Scaled

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree5Scaled

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree6Scaled

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerTruncation

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryPowerBernstein77_6_0Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_0Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_0Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_0Chunk0=boundaryPowerBernstein77_6_0Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_0Chunk0]

    rw [boundaryFullPowerScaled77_0_0Norm.property,boundaryFullPowerScaled77_1_0Norm.property,boundaryFullPowerScaled77_2_0Norm.property,boundaryFullPowerScaled77_3_0Norm.property,boundaryFullPowerScaled77_4_0Norm.property,boundaryFullPowerScaled77_5_0Norm.property,boundaryFullPowerScaled77_6_0Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_0Norm,boundaryFullPowerScaled77_1_0Norm,boundaryFullPowerScaled77_2_0Norm,boundaryFullPowerScaled77_3_0Norm,boundaryFullPowerScaled77_4_0Norm,boundaryFullPowerScaled77_5_0Norm,boundaryFullPowerScaled77_6_0Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_0Norm : {c : ℝ // boundaryFullCoefficient77 6 0=c} := by

  have he : boundaryFullCoefficient77 6 0=(boundaryPowerBernstein77_6_0Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_0Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_0Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_0Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_1Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_1Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_1Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_1Chunk0=boundaryPowerBernstein77_6_1Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_1Chunk0]

    rw [boundaryFullPowerScaled77_0_1Norm.property,boundaryFullPowerScaled77_1_1Norm.property,boundaryFullPowerScaled77_2_1Norm.property,boundaryFullPowerScaled77_3_1Norm.property,boundaryFullPowerScaled77_4_1Norm.property,boundaryFullPowerScaled77_5_1Norm.property,boundaryFullPowerScaled77_6_1Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_1Norm,boundaryFullPowerScaled77_1_1Norm,boundaryFullPowerScaled77_2_1Norm,boundaryFullPowerScaled77_3_1Norm,boundaryFullPowerScaled77_4_1Norm,boundaryFullPowerScaled77_5_1Norm,boundaryFullPowerScaled77_6_1Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_1Norm : {c : ℝ // boundaryFullCoefficient77 6 1=c} := by

  have he : boundaryFullCoefficient77 6 1=(boundaryPowerBernstein77_6_1Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_1Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_1Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_1Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_2Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_2Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_2Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_2Chunk0=boundaryPowerBernstein77_6_2Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_2Chunk0]

    rw [boundaryFullPowerScaled77_0_2Norm.property,boundaryFullPowerScaled77_1_2Norm.property,boundaryFullPowerScaled77_2_2Norm.property,boundaryFullPowerScaled77_3_2Norm.property,boundaryFullPowerScaled77_4_2Norm.property,boundaryFullPowerScaled77_5_2Norm.property,boundaryFullPowerScaled77_6_2Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_2Norm,boundaryFullPowerScaled77_1_2Norm,boundaryFullPowerScaled77_2_2Norm,boundaryFullPowerScaled77_3_2Norm,boundaryFullPowerScaled77_4_2Norm,boundaryFullPowerScaled77_5_2Norm,boundaryFullPowerScaled77_6_2Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_2Norm : {c : ℝ // boundaryFullCoefficient77 6 2=c} := by

  have he : boundaryFullCoefficient77 6 2=(boundaryPowerBernstein77_6_2Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_2Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_2Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_2Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_3Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_3Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_3Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_3Chunk0=boundaryPowerBernstein77_6_3Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_3Chunk0]

    rw [boundaryFullPowerScaled77_0_3Norm.property,boundaryFullPowerScaled77_1_3Norm.property,boundaryFullPowerScaled77_2_3Norm.property,boundaryFullPowerScaled77_3_3Norm.property,boundaryFullPowerScaled77_4_3Norm.property,boundaryFullPowerScaled77_5_3Norm.property,boundaryFullPowerScaled77_6_3Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_3Norm,boundaryFullPowerScaled77_1_3Norm,boundaryFullPowerScaled77_2_3Norm,boundaryFullPowerScaled77_3_3Norm,boundaryFullPowerScaled77_4_3Norm,boundaryFullPowerScaled77_5_3Norm,boundaryFullPowerScaled77_6_3Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_3Norm : {c : ℝ // boundaryFullCoefficient77 6 3=c} := by

  have he : boundaryFullCoefficient77 6 3=(boundaryPowerBernstein77_6_3Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_3Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_3Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_3Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_4Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_4Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_4Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_4Chunk0=boundaryPowerBernstein77_6_4Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_4Chunk0]

    rw [boundaryFullPowerScaled77_0_4Norm.property,boundaryFullPowerScaled77_1_4Norm.property,boundaryFullPowerScaled77_2_4Norm.property,boundaryFullPowerScaled77_3_4Norm.property,boundaryFullPowerScaled77_4_4Norm.property,boundaryFullPowerScaled77_5_4Norm.property,boundaryFullPowerScaled77_6_4Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_4Norm,boundaryFullPowerScaled77_1_4Norm,boundaryFullPowerScaled77_2_4Norm,boundaryFullPowerScaled77_3_4Norm,boundaryFullPowerScaled77_4_4Norm,boundaryFullPowerScaled77_5_4Norm,boundaryFullPowerScaled77_6_4Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_4Norm : {c : ℝ // boundaryFullCoefficient77 6 4=c} := by

  have he : boundaryFullCoefficient77 6 4=(boundaryPowerBernstein77_6_4Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_4Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_4Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_4Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_5Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_5Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_5Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_5Chunk0=boundaryPowerBernstein77_6_5Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_5Chunk0]

    rw [boundaryFullPowerScaled77_0_5Norm.property,boundaryFullPowerScaled77_1_5Norm.property,boundaryFullPowerScaled77_2_5Norm.property,boundaryFullPowerScaled77_3_5Norm.property,boundaryFullPowerScaled77_4_5Norm.property,boundaryFullPowerScaled77_5_5Norm.property,boundaryFullPowerScaled77_6_5Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_5Norm,boundaryFullPowerScaled77_1_5Norm,boundaryFullPowerScaled77_2_5Norm,boundaryFullPowerScaled77_3_5Norm,boundaryFullPowerScaled77_4_5Norm,boundaryFullPowerScaled77_5_5Norm,boundaryFullPowerScaled77_6_5Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_5Norm : {c : ℝ // boundaryFullCoefficient77 6 5=c} := by

  have he : boundaryFullCoefficient77 6 5=(boundaryPowerBernstein77_6_5Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_5Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_5Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_5Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_6Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_6Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_6Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_6Chunk0=boundaryPowerBernstein77_6_6Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_6Chunk0]

    rw [boundaryFullPowerScaled77_0_6Norm.property,boundaryFullPowerScaled77_1_6Norm.property,boundaryFullPowerScaled77_2_6Norm.property,boundaryFullPowerScaled77_3_6Norm.property,boundaryFullPowerScaled77_4_6Norm.property,boundaryFullPowerScaled77_5_6Norm.property,boundaryFullPowerScaled77_6_6Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_6Norm,boundaryFullPowerScaled77_1_6Norm,boundaryFullPowerScaled77_2_6Norm,boundaryFullPowerScaled77_3_6Norm,boundaryFullPowerScaled77_4_6Norm,boundaryFullPowerScaled77_5_6Norm,boundaryFullPowerScaled77_6_6Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_6Norm : {c : ℝ // boundaryFullCoefficient77 6 6=c} := by

  have he : boundaryFullCoefficient77 6 6=(boundaryPowerBernstein77_6_6Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_6Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_6Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_6Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_7Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_7Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_7Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_7Chunk0=boundaryPowerBernstein77_6_7Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_7Chunk0]

    rw [boundaryFullPowerScaled77_0_7Norm.property,boundaryFullPowerScaled77_1_7Norm.property,boundaryFullPowerScaled77_2_7Norm.property,boundaryFullPowerScaled77_3_7Norm.property,boundaryFullPowerScaled77_4_7Norm.property,boundaryFullPowerScaled77_5_7Norm.property,boundaryFullPowerScaled77_6_7Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_7Norm,boundaryFullPowerScaled77_1_7Norm,boundaryFullPowerScaled77_2_7Norm,boundaryFullPowerScaled77_3_7Norm,boundaryFullPowerScaled77_4_7Norm,boundaryFullPowerScaled77_5_7Norm,boundaryFullPowerScaled77_6_7Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_7Norm : {c : ℝ // boundaryFullCoefficient77 6 7=c} := by

  have he : boundaryFullCoefficient77 6 7=(boundaryPowerBernstein77_6_7Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_7Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_7Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_7Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_8Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_8Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_8Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_8Chunk0=boundaryPowerBernstein77_6_8Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_8Chunk0]

    rw [boundaryFullPowerScaled77_0_8Norm.property,boundaryFullPowerScaled77_1_8Norm.property,boundaryFullPowerScaled77_2_8Norm.property,boundaryFullPowerScaled77_3_8Norm.property,boundaryFullPowerScaled77_4_8Norm.property,boundaryFullPowerScaled77_5_8Norm.property,boundaryFullPowerScaled77_6_8Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_8Norm,boundaryFullPowerScaled77_1_8Norm,boundaryFullPowerScaled77_2_8Norm,boundaryFullPowerScaled77_3_8Norm,boundaryFullPowerScaled77_4_8Norm,boundaryFullPowerScaled77_5_8Norm,boundaryFullPowerScaled77_6_8Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_8Norm : {c : ℝ // boundaryFullCoefficient77 6 8=c} := by

  have he : boundaryFullCoefficient77 6 8=(boundaryPowerBernstein77_6_8Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_8Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_8Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_8Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_9Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_9Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_9Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_9Chunk0=boundaryPowerBernstein77_6_9Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_9Chunk0]

    rw [boundaryFullPowerScaled77_0_9Norm.property,boundaryFullPowerScaled77_1_9Norm.property,boundaryFullPowerScaled77_2_9Norm.property,boundaryFullPowerScaled77_3_9Norm.property,boundaryFullPowerScaled77_4_9Norm.property,boundaryFullPowerScaled77_5_9Norm.property,boundaryFullPowerScaled77_6_9Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_9Norm,boundaryFullPowerScaled77_1_9Norm,boundaryFullPowerScaled77_2_9Norm,boundaryFullPowerScaled77_3_9Norm,boundaryFullPowerScaled77_4_9Norm,boundaryFullPowerScaled77_5_9Norm,boundaryFullPowerScaled77_6_9Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_9Norm : {c : ℝ // boundaryFullCoefficient77 6 9=c} := by

  have he : boundaryFullCoefficient77 6 9=(boundaryPowerBernstein77_6_9Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_9Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_9Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_9Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_10Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_10Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_10Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_10Chunk0=boundaryPowerBernstein77_6_10Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_10Chunk0]

    rw [boundaryFullPowerScaled77_0_10Norm.property,boundaryFullPowerScaled77_1_10Norm.property,boundaryFullPowerScaled77_2_10Norm.property,boundaryFullPowerScaled77_3_10Norm.property,boundaryFullPowerScaled77_4_10Norm.property,boundaryFullPowerScaled77_5_10Norm.property,boundaryFullPowerScaled77_6_10Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_10Norm,boundaryFullPowerScaled77_1_10Norm,boundaryFullPowerScaled77_2_10Norm,boundaryFullPowerScaled77_3_10Norm,boundaryFullPowerScaled77_4_10Norm,boundaryFullPowerScaled77_5_10Norm,boundaryFullPowerScaled77_6_10Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_10Norm : {c : ℝ // boundaryFullCoefficient77 6 10=c} := by

  have he : boundaryFullCoefficient77 6 10=(boundaryPowerBernstein77_6_10Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_10Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_10Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_10Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_11Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_11Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_11Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_11Chunk0=boundaryPowerBernstein77_6_11Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_11Chunk0]

    rw [boundaryFullPowerScaled77_0_11Norm.property,boundaryFullPowerScaled77_1_11Norm.property,boundaryFullPowerScaled77_2_11Norm.property,boundaryFullPowerScaled77_3_11Norm.property,boundaryFullPowerScaled77_4_11Norm.property,boundaryFullPowerScaled77_5_11Norm.property,boundaryFullPowerScaled77_6_11Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_11Norm,boundaryFullPowerScaled77_1_11Norm,boundaryFullPowerScaled77_2_11Norm,boundaryFullPowerScaled77_3_11Norm,boundaryFullPowerScaled77_4_11Norm,boundaryFullPowerScaled77_5_11Norm,boundaryFullPowerScaled77_6_11Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_11Norm : {c : ℝ // boundaryFullCoefficient77 6 11=c} := by

  have he : boundaryFullCoefficient77 6 11=(boundaryPowerBernstein77_6_11Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_11Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_11Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_11Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_12Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_12Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_12Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_12Chunk0=boundaryPowerBernstein77_6_12Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_12Chunk0]

    rw [boundaryFullPowerScaled77_0_12Norm.property,boundaryFullPowerScaled77_1_12Norm.property,boundaryFullPowerScaled77_2_12Norm.property,boundaryFullPowerScaled77_3_12Norm.property,boundaryFullPowerScaled77_4_12Norm.property,boundaryFullPowerScaled77_5_12Norm.property,boundaryFullPowerScaled77_6_12Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_12Norm,boundaryFullPowerScaled77_1_12Norm,boundaryFullPowerScaled77_2_12Norm,boundaryFullPowerScaled77_3_12Norm,boundaryFullPowerScaled77_4_12Norm,boundaryFullPowerScaled77_5_12Norm,boundaryFullPowerScaled77_6_12Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_12Norm : {c : ℝ // boundaryFullCoefficient77 6 12=c} := by

  have he : boundaryFullCoefficient77 6 12=(boundaryPowerBernstein77_6_12Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_12Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_12Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_12Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_13Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_13Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_13Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_13Chunk0=boundaryPowerBernstein77_6_13Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_13Chunk0]

    rw [boundaryFullPowerScaled77_0_13Norm.property,boundaryFullPowerScaled77_1_13Norm.property,boundaryFullPowerScaled77_2_13Norm.property,boundaryFullPowerScaled77_3_13Norm.property,boundaryFullPowerScaled77_4_13Norm.property,boundaryFullPowerScaled77_5_13Norm.property,boundaryFullPowerScaled77_6_13Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_13Norm,boundaryFullPowerScaled77_1_13Norm,boundaryFullPowerScaled77_2_13Norm,boundaryFullPowerScaled77_3_13Norm,boundaryFullPowerScaled77_4_13Norm,boundaryFullPowerScaled77_5_13Norm,boundaryFullPowerScaled77_6_13Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_13Norm : {c : ℝ // boundaryFullCoefficient77 6 13=c} := by

  have he : boundaryFullCoefficient77 6 13=(boundaryPowerBernstein77_6_13Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_13Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_13Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_13Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_14Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_14Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_14Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_14Chunk0=boundaryPowerBernstein77_6_14Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_14Chunk0]

    rw [boundaryFullPowerScaled77_0_14Norm.property,boundaryFullPowerScaled77_1_14Norm.property,boundaryFullPowerScaled77_2_14Norm.property,boundaryFullPowerScaled77_3_14Norm.property,boundaryFullPowerScaled77_4_14Norm.property,boundaryFullPowerScaled77_5_14Norm.property,boundaryFullPowerScaled77_6_14Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_14Norm,boundaryFullPowerScaled77_1_14Norm,boundaryFullPowerScaled77_2_14Norm,boundaryFullPowerScaled77_3_14Norm,boundaryFullPowerScaled77_4_14Norm,boundaryFullPowerScaled77_5_14Norm,boundaryFullPowerScaled77_6_14Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_14Norm : {c : ℝ // boundaryFullCoefficient77 6 14=c} := by

  have he : boundaryFullCoefficient77 6 14=(boundaryPowerBernstein77_6_14Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_14Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_14Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_14Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_15Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_15Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_15Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_15Chunk0=boundaryPowerBernstein77_6_15Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_15Chunk0]

    rw [boundaryFullPowerScaled77_0_15Norm.property,boundaryFullPowerScaled77_1_15Norm.property,boundaryFullPowerScaled77_2_15Norm.property,boundaryFullPowerScaled77_3_15Norm.property,boundaryFullPowerScaled77_4_15Norm.property,boundaryFullPowerScaled77_5_15Norm.property,boundaryFullPowerScaled77_6_15Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_15Norm,boundaryFullPowerScaled77_1_15Norm,boundaryFullPowerScaled77_2_15Norm,boundaryFullPowerScaled77_3_15Norm,boundaryFullPowerScaled77_4_15Norm,boundaryFullPowerScaled77_5_15Norm,boundaryFullPowerScaled77_6_15Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_15Norm : {c : ℝ // boundaryFullCoefficient77 6 15=c} := by

  have he : boundaryFullCoefficient77 6 15=(boundaryPowerBernstein77_6_15Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_15Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_15Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_15Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_16Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_16Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_16Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_16Chunk0=boundaryPowerBernstein77_6_16Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_16Chunk0]

    rw [boundaryFullPowerScaled77_0_16Norm.property,boundaryFullPowerScaled77_1_16Norm.property,boundaryFullPowerScaled77_2_16Norm.property,boundaryFullPowerScaled77_3_16Norm.property,boundaryFullPowerScaled77_4_16Norm.property,boundaryFullPowerScaled77_5_16Norm.property,boundaryFullPowerScaled77_6_16Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_16Norm,boundaryFullPowerScaled77_1_16Norm,boundaryFullPowerScaled77_2_16Norm,boundaryFullPowerScaled77_3_16Norm,boundaryFullPowerScaled77_4_16Norm,boundaryFullPowerScaled77_5_16Norm,boundaryFullPowerScaled77_6_16Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_16Norm : {c : ℝ // boundaryFullCoefficient77 6 16=c} := by

  have he : boundaryFullCoefficient77 6 16=(boundaryPowerBernstein77_6_16Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_16Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_16Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_16Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_17Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_17Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_17Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_17Chunk0=boundaryPowerBernstein77_6_17Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_17Chunk0]

    rw [boundaryFullPowerScaled77_0_17Norm.property,boundaryFullPowerScaled77_1_17Norm.property,boundaryFullPowerScaled77_2_17Norm.property,boundaryFullPowerScaled77_3_17Norm.property,boundaryFullPowerScaled77_4_17Norm.property,boundaryFullPowerScaled77_5_17Norm.property,boundaryFullPowerScaled77_6_17Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_17Norm,boundaryFullPowerScaled77_1_17Norm,boundaryFullPowerScaled77_2_17Norm,boundaryFullPowerScaled77_3_17Norm,boundaryFullPowerScaled77_4_17Norm,boundaryFullPowerScaled77_5_17Norm,boundaryFullPowerScaled77_6_17Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_17Norm : {c : ℝ // boundaryFullCoefficient77 6 17=c} := by

  have he : boundaryFullCoefficient77 6 17=(boundaryPowerBernstein77_6_17Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_17Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_17Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_17Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_18Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_18Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_18Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_18Chunk0=boundaryPowerBernstein77_6_18Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_18Chunk0]

    rw [boundaryFullPowerScaled77_0_18Norm.property,boundaryFullPowerScaled77_1_18Norm.property,boundaryFullPowerScaled77_2_18Norm.property,boundaryFullPowerScaled77_3_18Norm.property,boundaryFullPowerScaled77_4_18Norm.property,boundaryFullPowerScaled77_5_18Norm.property,boundaryFullPowerScaled77_6_18Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_18Norm,boundaryFullPowerScaled77_1_18Norm,boundaryFullPowerScaled77_2_18Norm,boundaryFullPowerScaled77_3_18Norm,boundaryFullPowerScaled77_4_18Norm,boundaryFullPowerScaled77_5_18Norm,boundaryFullPowerScaled77_6_18Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_18Norm : {c : ℝ // boundaryFullCoefficient77 6 18=c} := by

  have he : boundaryFullCoefficient77 6 18=(boundaryPowerBernstein77_6_18Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_18Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_18Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_18Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_19Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_19Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_19Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_19Chunk0=boundaryPowerBernstein77_6_19Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_19Chunk0]

    rw [boundaryFullPowerScaled77_0_19Norm.property,boundaryFullPowerScaled77_1_19Norm.property,boundaryFullPowerScaled77_2_19Norm.property,boundaryFullPowerScaled77_3_19Norm.property,boundaryFullPowerScaled77_4_19Norm.property,boundaryFullPowerScaled77_5_19Norm.property,boundaryFullPowerScaled77_6_19Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_19Norm,boundaryFullPowerScaled77_1_19Norm,boundaryFullPowerScaled77_2_19Norm,boundaryFullPowerScaled77_3_19Norm,boundaryFullPowerScaled77_4_19Norm,boundaryFullPowerScaled77_5_19Norm,boundaryFullPowerScaled77_6_19Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_19Norm : {c : ℝ // boundaryFullCoefficient77 6 19=c} := by

  have he : boundaryFullCoefficient77 6 19=(boundaryPowerBernstein77_6_19Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_19Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_19Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_19Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_20Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_20Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_20Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_20Chunk0=boundaryPowerBernstein77_6_20Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_20Chunk0]

    rw [boundaryFullPowerScaled77_0_20Norm.property,boundaryFullPowerScaled77_1_20Norm.property,boundaryFullPowerScaled77_2_20Norm.property,boundaryFullPowerScaled77_3_20Norm.property,boundaryFullPowerScaled77_4_20Norm.property,boundaryFullPowerScaled77_5_20Norm.property,boundaryFullPowerScaled77_6_20Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_20Norm,boundaryFullPowerScaled77_1_20Norm,boundaryFullPowerScaled77_2_20Norm,boundaryFullPowerScaled77_3_20Norm,boundaryFullPowerScaled77_4_20Norm,boundaryFullPowerScaled77_5_20Norm,boundaryFullPowerScaled77_6_20Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_20Norm : {c : ℝ // boundaryFullCoefficient77 6 20=c} := by

  have he : boundaryFullCoefficient77 6 20=(boundaryPowerBernstein77_6_20Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_20Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_20Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_20Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_21Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_21Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_21Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_21Chunk0=boundaryPowerBernstein77_6_21Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_21Chunk0]

    rw [boundaryFullPowerScaled77_0_21Norm.property,boundaryFullPowerScaled77_1_21Norm.property,boundaryFullPowerScaled77_2_21Norm.property,boundaryFullPowerScaled77_3_21Norm.property,boundaryFullPowerScaled77_4_21Norm.property,boundaryFullPowerScaled77_5_21Norm.property,boundaryFullPowerScaled77_6_21Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_21Norm,boundaryFullPowerScaled77_1_21Norm,boundaryFullPowerScaled77_2_21Norm,boundaryFullPowerScaled77_3_21Norm,boundaryFullPowerScaled77_4_21Norm,boundaryFullPowerScaled77_5_21Norm,boundaryFullPowerScaled77_6_21Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_21Norm : {c : ℝ // boundaryFullCoefficient77 6 21=c} := by

  have he : boundaryFullCoefficient77 6 21=(boundaryPowerBernstein77_6_21Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_21Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_21Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_21Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_22Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_22Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_22Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_22Chunk0=boundaryPowerBernstein77_6_22Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_22Chunk0]

    rw [boundaryFullPowerScaled77_0_22Norm.property,boundaryFullPowerScaled77_1_22Norm.property,boundaryFullPowerScaled77_2_22Norm.property,boundaryFullPowerScaled77_3_22Norm.property,boundaryFullPowerScaled77_4_22Norm.property,boundaryFullPowerScaled77_5_22Norm.property,boundaryFullPowerScaled77_6_22Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_22Norm,boundaryFullPowerScaled77_1_22Norm,boundaryFullPowerScaled77_2_22Norm,boundaryFullPowerScaled77_3_22Norm,boundaryFullPowerScaled77_4_22Norm,boundaryFullPowerScaled77_5_22Norm,boundaryFullPowerScaled77_6_22Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_22Norm : {c : ℝ // boundaryFullCoefficient77 6 22=c} := by

  have he : boundaryFullCoefficient77 6 22=(boundaryPowerBernstein77_6_22Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_22Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_22Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_22Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_23Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_23Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_23Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_23Chunk0=boundaryPowerBernstein77_6_23Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_23Chunk0]

    rw [boundaryFullPowerScaled77_0_23Norm.property,boundaryFullPowerScaled77_1_23Norm.property,boundaryFullPowerScaled77_2_23Norm.property,boundaryFullPowerScaled77_3_23Norm.property,boundaryFullPowerScaled77_4_23Norm.property,boundaryFullPowerScaled77_5_23Norm.property,boundaryFullPowerScaled77_6_23Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_23Norm,boundaryFullPowerScaled77_1_23Norm,boundaryFullPowerScaled77_2_23Norm,boundaryFullPowerScaled77_3_23Norm,boundaryFullPowerScaled77_4_23Norm,boundaryFullPowerScaled77_5_23Norm,boundaryFullPowerScaled77_6_23Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_23Norm : {c : ℝ // boundaryFullCoefficient77 6 23=c} := by

  have he : boundaryFullCoefficient77 6 23=(boundaryPowerBernstein77_6_23Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_23Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_23Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_23Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_24Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_24Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_24Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_24Chunk0=boundaryPowerBernstein77_6_24Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_24Chunk0]

    rw [boundaryFullPowerScaled77_0_24Norm.property,boundaryFullPowerScaled77_1_24Norm.property,boundaryFullPowerScaled77_2_24Norm.property,boundaryFullPowerScaled77_3_24Norm.property,boundaryFullPowerScaled77_4_24Norm.property,boundaryFullPowerScaled77_5_24Norm.property,boundaryFullPowerScaled77_6_24Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_24Norm,boundaryFullPowerScaled77_1_24Norm,boundaryFullPowerScaled77_2_24Norm,boundaryFullPowerScaled77_3_24Norm,boundaryFullPowerScaled77_4_24Norm,boundaryFullPowerScaled77_5_24Norm,boundaryFullPowerScaled77_6_24Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_24Norm : {c : ℝ // boundaryFullCoefficient77 6 24=c} := by

  have he : boundaryFullCoefficient77 6 24=(boundaryPowerBernstein77_6_24Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_24Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_24Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_24Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_25Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_25Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_25Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_25Chunk0=boundaryPowerBernstein77_6_25Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_25Chunk0]

    rw [boundaryFullPowerScaled77_0_25Norm.property,boundaryFullPowerScaled77_1_25Norm.property,boundaryFullPowerScaled77_2_25Norm.property,boundaryFullPowerScaled77_3_25Norm.property,boundaryFullPowerScaled77_4_25Norm.property,boundaryFullPowerScaled77_5_25Norm.property,boundaryFullPowerScaled77_6_25Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_25Norm,boundaryFullPowerScaled77_1_25Norm,boundaryFullPowerScaled77_2_25Norm,boundaryFullPowerScaled77_3_25Norm,boundaryFullPowerScaled77_4_25Norm,boundaryFullPowerScaled77_5_25Norm,boundaryFullPowerScaled77_6_25Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_25Norm : {c : ℝ // boundaryFullCoefficient77 6 25=c} := by

  have he : boundaryFullCoefficient77 6 25=(boundaryPowerBernstein77_6_25Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_25Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_25Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_25Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_26Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_26Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_26Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_26Chunk0=boundaryPowerBernstein77_6_26Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_26Chunk0]

    rw [boundaryFullPowerScaled77_0_26Norm.property,boundaryFullPowerScaled77_1_26Norm.property,boundaryFullPowerScaled77_2_26Norm.property,boundaryFullPowerScaled77_3_26Norm.property,boundaryFullPowerScaled77_4_26Norm.property,boundaryFullPowerScaled77_5_26Norm.property,boundaryFullPowerScaled77_6_26Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_26Norm,boundaryFullPowerScaled77_1_26Norm,boundaryFullPowerScaled77_2_26Norm,boundaryFullPowerScaled77_3_26Norm,boundaryFullPowerScaled77_4_26Norm,boundaryFullPowerScaled77_5_26Norm,boundaryFullPowerScaled77_6_26Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_26Norm : {c : ℝ // boundaryFullCoefficient77 6 26=c} := by

  have he : boundaryFullCoefficient77 6 26=(boundaryPowerBernstein77_6_26Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_26Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_26Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_26Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_27Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_27Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_27Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_27Chunk0=boundaryPowerBernstein77_6_27Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_27Chunk0]

    rw [boundaryFullPowerScaled77_0_27Norm.property,boundaryFullPowerScaled77_1_27Norm.property,boundaryFullPowerScaled77_2_27Norm.property,boundaryFullPowerScaled77_3_27Norm.property,boundaryFullPowerScaled77_4_27Norm.property,boundaryFullPowerScaled77_5_27Norm.property,boundaryFullPowerScaled77_6_27Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_27Norm,boundaryFullPowerScaled77_1_27Norm,boundaryFullPowerScaled77_2_27Norm,boundaryFullPowerScaled77_3_27Norm,boundaryFullPowerScaled77_4_27Norm,boundaryFullPowerScaled77_5_27Norm,boundaryFullPowerScaled77_6_27Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_27Norm : {c : ℝ // boundaryFullCoefficient77 6 27=c} := by

  have he : boundaryFullCoefficient77 6 27=(boundaryPowerBernstein77_6_27Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_27Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_27Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_27Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_28Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_28Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_28Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_28Chunk0=boundaryPowerBernstein77_6_28Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_28Chunk0]

    rw [boundaryFullPowerScaled77_0_28Norm.property,boundaryFullPowerScaled77_1_28Norm.property,boundaryFullPowerScaled77_2_28Norm.property,boundaryFullPowerScaled77_3_28Norm.property,boundaryFullPowerScaled77_4_28Norm.property,boundaryFullPowerScaled77_5_28Norm.property,boundaryFullPowerScaled77_6_28Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_28Norm,boundaryFullPowerScaled77_1_28Norm,boundaryFullPowerScaled77_2_28Norm,boundaryFullPowerScaled77_3_28Norm,boundaryFullPowerScaled77_4_28Norm,boundaryFullPowerScaled77_5_28Norm,boundaryFullPowerScaled77_6_28Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_28Norm : {c : ℝ // boundaryFullCoefficient77 6 28=c} := by

  have he : boundaryFullCoefficient77 6 28=(boundaryPowerBernstein77_6_28Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_28Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_28Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_28Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_29Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_29Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_29Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_29Chunk0=boundaryPowerBernstein77_6_29Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_29Chunk0]

    rw [boundaryFullPowerScaled77_0_29Norm.property,boundaryFullPowerScaled77_1_29Norm.property,boundaryFullPowerScaled77_2_29Norm.property,boundaryFullPowerScaled77_3_29Norm.property,boundaryFullPowerScaled77_4_29Norm.property,boundaryFullPowerScaled77_5_29Norm.property,boundaryFullPowerScaled77_6_29Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_29Norm,boundaryFullPowerScaled77_1_29Norm,boundaryFullPowerScaled77_2_29Norm,boundaryFullPowerScaled77_3_29Norm,boundaryFullPowerScaled77_4_29Norm,boundaryFullPowerScaled77_5_29Norm,boundaryFullPowerScaled77_6_29Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_29Norm : {c : ℝ // boundaryFullCoefficient77 6 29=c} := by

  have he : boundaryFullCoefficient77 6 29=(boundaryPowerBernstein77_6_29Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_29Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_29Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_29Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_30Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_30Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_30Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_30Chunk0=boundaryPowerBernstein77_6_30Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_30Chunk0]

    rw [boundaryFullPowerScaled77_0_30Norm.property,boundaryFullPowerScaled77_1_30Norm.property,boundaryFullPowerScaled77_2_30Norm.property,boundaryFullPowerScaled77_3_30Norm.property,boundaryFullPowerScaled77_4_30Norm.property,boundaryFullPowerScaled77_5_30Norm.property,boundaryFullPowerScaled77_6_30Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_30Norm,boundaryFullPowerScaled77_1_30Norm,boundaryFullPowerScaled77_2_30Norm,boundaryFullPowerScaled77_3_30Norm,boundaryFullPowerScaled77_4_30Norm,boundaryFullPowerScaled77_5_30Norm,boundaryFullPowerScaled77_6_30Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_30Norm : {c : ℝ // boundaryFullCoefficient77 6 30=c} := by

  have he : boundaryFullCoefficient77 6 30=(boundaryPowerBernstein77_6_30Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_30Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_30Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_30Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_31Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_31Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_31Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_31Chunk0=boundaryPowerBernstein77_6_31Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_31Chunk0]

    rw [boundaryFullPowerScaled77_0_31Norm.property,boundaryFullPowerScaled77_1_31Norm.property,boundaryFullPowerScaled77_2_31Norm.property,boundaryFullPowerScaled77_3_31Norm.property,boundaryFullPowerScaled77_4_31Norm.property,boundaryFullPowerScaled77_5_31Norm.property,boundaryFullPowerScaled77_6_31Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_31Norm,boundaryFullPowerScaled77_1_31Norm,boundaryFullPowerScaled77_2_31Norm,boundaryFullPowerScaled77_3_31Norm,boundaryFullPowerScaled77_4_31Norm,boundaryFullPowerScaled77_5_31Norm,boundaryFullPowerScaled77_6_31Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_31Norm : {c : ℝ // boundaryFullCoefficient77 6 31=c} := by

  have he : boundaryFullCoefficient77 6 31=(boundaryPowerBernstein77_6_31Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_31Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_31Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_31Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_32Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_32Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_32Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_32Chunk0=boundaryPowerBernstein77_6_32Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_32Chunk0]

    rw [boundaryFullPowerScaled77_0_32Norm.property,boundaryFullPowerScaled77_1_32Norm.property,boundaryFullPowerScaled77_2_32Norm.property,boundaryFullPowerScaled77_3_32Norm.property,boundaryFullPowerScaled77_4_32Norm.property,boundaryFullPowerScaled77_5_32Norm.property,boundaryFullPowerScaled77_6_32Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_32Norm,boundaryFullPowerScaled77_1_32Norm,boundaryFullPowerScaled77_2_32Norm,boundaryFullPowerScaled77_3_32Norm,boundaryFullPowerScaled77_4_32Norm,boundaryFullPowerScaled77_5_32Norm,boundaryFullPowerScaled77_6_32Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_32Norm : {c : ℝ // boundaryFullCoefficient77 6 32=c} := by

  have he : boundaryFullCoefficient77 6 32=(boundaryPowerBernstein77_6_32Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_32Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_32Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_32Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_33Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_33Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_33Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_33Chunk0=boundaryPowerBernstein77_6_33Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_33Chunk0]

    rw [boundaryFullPowerScaled77_0_33Norm.property,boundaryFullPowerScaled77_1_33Norm.property,boundaryFullPowerScaled77_2_33Norm.property,boundaryFullPowerScaled77_3_33Norm.property,boundaryFullPowerScaled77_4_33Norm.property,boundaryFullPowerScaled77_5_33Norm.property,boundaryFullPowerScaled77_6_33Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_33Norm,boundaryFullPowerScaled77_1_33Norm,boundaryFullPowerScaled77_2_33Norm,boundaryFullPowerScaled77_3_33Norm,boundaryFullPowerScaled77_4_33Norm,boundaryFullPowerScaled77_5_33Norm,boundaryFullPowerScaled77_6_33Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_33Norm : {c : ℝ // boundaryFullCoefficient77 6 33=c} := by

  have he : boundaryFullCoefficient77 6 33=(boundaryPowerBernstein77_6_33Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_33Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_33Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_33Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_34Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_34Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_34Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_34Chunk0=boundaryPowerBernstein77_6_34Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_34Chunk0]

    rw [boundaryFullPowerScaled77_0_34Norm.property,boundaryFullPowerScaled77_1_34Norm.property,boundaryFullPowerScaled77_2_34Norm.property,boundaryFullPowerScaled77_3_34Norm.property,boundaryFullPowerScaled77_4_34Norm.property,boundaryFullPowerScaled77_5_34Norm.property,boundaryFullPowerScaled77_6_34Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_34Norm,boundaryFullPowerScaled77_1_34Norm,boundaryFullPowerScaled77_2_34Norm,boundaryFullPowerScaled77_3_34Norm,boundaryFullPowerScaled77_4_34Norm,boundaryFullPowerScaled77_5_34Norm,boundaryFullPowerScaled77_6_34Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_34Norm : {c : ℝ // boundaryFullCoefficient77 6 34=c} := by

  have he : boundaryFullCoefficient77 6 34=(boundaryPowerBernstein77_6_34Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_34Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_34Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_34Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_6_35Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_35Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_35Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_35Chunk0=boundaryPowerBernstein77_6_35Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_35Chunk0]

    rw [boundaryFullPowerScaled77_0_35Norm.property,boundaryFullPowerScaled77_1_35Norm.property,boundaryFullPowerScaled77_2_35Norm.property,boundaryFullPowerScaled77_3_35Norm.property,boundaryFullPowerScaled77_4_35Norm.property,boundaryFullPowerScaled77_5_35Norm.property,boundaryFullPowerScaled77_6_35Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_35Norm,boundaryFullPowerScaled77_1_35Norm,boundaryFullPowerScaled77_2_35Norm,boundaryFullPowerScaled77_3_35Norm,boundaryFullPowerScaled77_4_35Norm,boundaryFullPowerScaled77_5_35Norm,boundaryFullPowerScaled77_6_35Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_35Norm : {c : ℝ // boundaryFullCoefficient77 6 35=c} := by

  have he : boundaryFullCoefficient77 6 35=(boundaryPowerBernstein77_6_35Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_35Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_35Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_35Chunk0Norm]

    norm_num

  exact ⟨_,he⟩




end

end HTGeometry.ThetaRatioInfinity
