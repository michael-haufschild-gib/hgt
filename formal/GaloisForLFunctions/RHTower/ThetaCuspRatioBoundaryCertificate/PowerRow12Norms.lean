import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree0Scaled

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree10Scaled

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree11Scaled

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree12Scaled

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree1Scaled

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree2Scaled

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree3Scaled

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree4Scaled

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree5Scaled

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree6Scaled

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree7Scaled

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree8Scaled

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree9Scaled

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerTruncation

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryPowerBernstein77_12_0Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_0Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_0Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_0Chunk0=boundaryPowerBernstein77_12_0Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_0Chunk0]

    rw [boundaryFullPowerScaled77_0_0Norm.property,boundaryFullPowerScaled77_1_0Norm.property,boundaryFullPowerScaled77_2_0Norm.property,boundaryFullPowerScaled77_3_0Norm.property,boundaryFullPowerScaled77_4_0Norm.property,boundaryFullPowerScaled77_5_0Norm.property,boundaryFullPowerScaled77_6_0Norm.property,boundaryFullPowerScaled77_7_0Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_0Norm,boundaryFullPowerScaled77_1_0Norm,boundaryFullPowerScaled77_2_0Norm,boundaryFullPowerScaled77_3_0Norm,boundaryFullPowerScaled77_4_0Norm,boundaryFullPowerScaled77_5_0Norm,boundaryFullPowerScaled77_6_0Norm,boundaryFullPowerScaled77_7_0Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_0Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_0Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_0Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_0Chunk8=boundaryPowerBernstein77_12_0Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_0Chunk8]

    rw [boundaryFullPowerScaled77_8_0Norm.property,boundaryFullPowerScaled77_9_0Norm.property,boundaryFullPowerScaled77_10_0Norm.property,boundaryFullPowerScaled77_11_0Norm.property,boundaryFullPowerScaled77_12_0Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_0Norm,boundaryFullPowerScaled77_9_0Norm,boundaryFullPowerScaled77_10_0Norm,boundaryFullPowerScaled77_11_0Norm,boundaryFullPowerScaled77_12_0Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_0Norm : {c : ℝ // boundaryFullCoefficient77 12 0=c} := by

  have he : boundaryFullCoefficient77 12 0=((boundaryPowerBernstein77_12_0Chunk0) + (boundaryPowerBernstein77_12_0Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_0Chunk0,boundaryPowerBernstein77_12_0Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_0Chunk0Norm.property,boundaryPowerBernstein77_12_0Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_0Chunk0Norm,boundaryPowerBernstein77_12_0Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_1Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_1Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_1Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_1Chunk0=boundaryPowerBernstein77_12_1Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_1Chunk0]

    rw [boundaryFullPowerScaled77_0_1Norm.property,boundaryFullPowerScaled77_1_1Norm.property,boundaryFullPowerScaled77_2_1Norm.property,boundaryFullPowerScaled77_3_1Norm.property,boundaryFullPowerScaled77_4_1Norm.property,boundaryFullPowerScaled77_5_1Norm.property,boundaryFullPowerScaled77_6_1Norm.property,boundaryFullPowerScaled77_7_1Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_1Norm,boundaryFullPowerScaled77_1_1Norm,boundaryFullPowerScaled77_2_1Norm,boundaryFullPowerScaled77_3_1Norm,boundaryFullPowerScaled77_4_1Norm,boundaryFullPowerScaled77_5_1Norm,boundaryFullPowerScaled77_6_1Norm,boundaryFullPowerScaled77_7_1Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_1Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_1Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_1Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_1Chunk8=boundaryPowerBernstein77_12_1Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_1Chunk8]

    rw [boundaryFullPowerScaled77_8_1Norm.property,boundaryFullPowerScaled77_9_1Norm.property,boundaryFullPowerScaled77_10_1Norm.property,boundaryFullPowerScaled77_11_1Norm.property,boundaryFullPowerScaled77_12_1Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_1Norm,boundaryFullPowerScaled77_9_1Norm,boundaryFullPowerScaled77_10_1Norm,boundaryFullPowerScaled77_11_1Norm,boundaryFullPowerScaled77_12_1Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_1Norm : {c : ℝ // boundaryFullCoefficient77 12 1=c} := by

  have he : boundaryFullCoefficient77 12 1=((boundaryPowerBernstein77_12_1Chunk0) + (boundaryPowerBernstein77_12_1Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_1Chunk0,boundaryPowerBernstein77_12_1Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_1Chunk0Norm.property,boundaryPowerBernstein77_12_1Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_1Chunk0Norm,boundaryPowerBernstein77_12_1Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_2Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_2Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_2Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_2Chunk0=boundaryPowerBernstein77_12_2Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_2Chunk0]

    rw [boundaryFullPowerScaled77_0_2Norm.property,boundaryFullPowerScaled77_1_2Norm.property,boundaryFullPowerScaled77_2_2Norm.property,boundaryFullPowerScaled77_3_2Norm.property,boundaryFullPowerScaled77_4_2Norm.property,boundaryFullPowerScaled77_5_2Norm.property,boundaryFullPowerScaled77_6_2Norm.property,boundaryFullPowerScaled77_7_2Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_2Norm,boundaryFullPowerScaled77_1_2Norm,boundaryFullPowerScaled77_2_2Norm,boundaryFullPowerScaled77_3_2Norm,boundaryFullPowerScaled77_4_2Norm,boundaryFullPowerScaled77_5_2Norm,boundaryFullPowerScaled77_6_2Norm,boundaryFullPowerScaled77_7_2Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_2Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_2Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_2Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_2Chunk8=boundaryPowerBernstein77_12_2Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_2Chunk8]

    rw [boundaryFullPowerScaled77_8_2Norm.property,boundaryFullPowerScaled77_9_2Norm.property,boundaryFullPowerScaled77_10_2Norm.property,boundaryFullPowerScaled77_11_2Norm.property,boundaryFullPowerScaled77_12_2Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_2Norm,boundaryFullPowerScaled77_9_2Norm,boundaryFullPowerScaled77_10_2Norm,boundaryFullPowerScaled77_11_2Norm,boundaryFullPowerScaled77_12_2Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_2Norm : {c : ℝ // boundaryFullCoefficient77 12 2=c} := by

  have he : boundaryFullCoefficient77 12 2=((boundaryPowerBernstein77_12_2Chunk0) + (boundaryPowerBernstein77_12_2Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_2Chunk0,boundaryPowerBernstein77_12_2Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_2Chunk0Norm.property,boundaryPowerBernstein77_12_2Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_2Chunk0Norm,boundaryPowerBernstein77_12_2Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_3Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_3Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_3Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_3Chunk0=boundaryPowerBernstein77_12_3Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_3Chunk0]

    rw [boundaryFullPowerScaled77_0_3Norm.property,boundaryFullPowerScaled77_1_3Norm.property,boundaryFullPowerScaled77_2_3Norm.property,boundaryFullPowerScaled77_3_3Norm.property,boundaryFullPowerScaled77_4_3Norm.property,boundaryFullPowerScaled77_5_3Norm.property,boundaryFullPowerScaled77_6_3Norm.property,boundaryFullPowerScaled77_7_3Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_3Norm,boundaryFullPowerScaled77_1_3Norm,boundaryFullPowerScaled77_2_3Norm,boundaryFullPowerScaled77_3_3Norm,boundaryFullPowerScaled77_4_3Norm,boundaryFullPowerScaled77_5_3Norm,boundaryFullPowerScaled77_6_3Norm,boundaryFullPowerScaled77_7_3Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_3Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_3Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_3Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_3Chunk8=boundaryPowerBernstein77_12_3Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_3Chunk8]

    rw [boundaryFullPowerScaled77_8_3Norm.property,boundaryFullPowerScaled77_9_3Norm.property,boundaryFullPowerScaled77_10_3Norm.property,boundaryFullPowerScaled77_11_3Norm.property,boundaryFullPowerScaled77_12_3Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_3Norm,boundaryFullPowerScaled77_9_3Norm,boundaryFullPowerScaled77_10_3Norm,boundaryFullPowerScaled77_11_3Norm,boundaryFullPowerScaled77_12_3Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_3Norm : {c : ℝ // boundaryFullCoefficient77 12 3=c} := by

  have he : boundaryFullCoefficient77 12 3=((boundaryPowerBernstein77_12_3Chunk0) + (boundaryPowerBernstein77_12_3Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_3Chunk0,boundaryPowerBernstein77_12_3Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_3Chunk0Norm.property,boundaryPowerBernstein77_12_3Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_3Chunk0Norm,boundaryPowerBernstein77_12_3Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_4Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_4Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_4Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_4Chunk0=boundaryPowerBernstein77_12_4Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_4Chunk0]

    rw [boundaryFullPowerScaled77_0_4Norm.property,boundaryFullPowerScaled77_1_4Norm.property,boundaryFullPowerScaled77_2_4Norm.property,boundaryFullPowerScaled77_3_4Norm.property,boundaryFullPowerScaled77_4_4Norm.property,boundaryFullPowerScaled77_5_4Norm.property,boundaryFullPowerScaled77_6_4Norm.property,boundaryFullPowerScaled77_7_4Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_4Norm,boundaryFullPowerScaled77_1_4Norm,boundaryFullPowerScaled77_2_4Norm,boundaryFullPowerScaled77_3_4Norm,boundaryFullPowerScaled77_4_4Norm,boundaryFullPowerScaled77_5_4Norm,boundaryFullPowerScaled77_6_4Norm,boundaryFullPowerScaled77_7_4Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_4Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_4Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_4Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_4Chunk8=boundaryPowerBernstein77_12_4Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_4Chunk8]

    rw [boundaryFullPowerScaled77_8_4Norm.property,boundaryFullPowerScaled77_9_4Norm.property,boundaryFullPowerScaled77_10_4Norm.property,boundaryFullPowerScaled77_11_4Norm.property,boundaryFullPowerScaled77_12_4Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_4Norm,boundaryFullPowerScaled77_9_4Norm,boundaryFullPowerScaled77_10_4Norm,boundaryFullPowerScaled77_11_4Norm,boundaryFullPowerScaled77_12_4Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_4Norm : {c : ℝ // boundaryFullCoefficient77 12 4=c} := by

  have he : boundaryFullCoefficient77 12 4=((boundaryPowerBernstein77_12_4Chunk0) + (boundaryPowerBernstein77_12_4Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_4Chunk0,boundaryPowerBernstein77_12_4Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_4Chunk0Norm.property,boundaryPowerBernstein77_12_4Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_4Chunk0Norm,boundaryPowerBernstein77_12_4Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_5Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_5Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_5Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_5Chunk0=boundaryPowerBernstein77_12_5Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_5Chunk0]

    rw [boundaryFullPowerScaled77_0_5Norm.property,boundaryFullPowerScaled77_1_5Norm.property,boundaryFullPowerScaled77_2_5Norm.property,boundaryFullPowerScaled77_3_5Norm.property,boundaryFullPowerScaled77_4_5Norm.property,boundaryFullPowerScaled77_5_5Norm.property,boundaryFullPowerScaled77_6_5Norm.property,boundaryFullPowerScaled77_7_5Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_5Norm,boundaryFullPowerScaled77_1_5Norm,boundaryFullPowerScaled77_2_5Norm,boundaryFullPowerScaled77_3_5Norm,boundaryFullPowerScaled77_4_5Norm,boundaryFullPowerScaled77_5_5Norm,boundaryFullPowerScaled77_6_5Norm,boundaryFullPowerScaled77_7_5Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_5Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_5Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_5Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_5Chunk8=boundaryPowerBernstein77_12_5Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_5Chunk8]

    rw [boundaryFullPowerScaled77_8_5Norm.property,boundaryFullPowerScaled77_9_5Norm.property,boundaryFullPowerScaled77_10_5Norm.property,boundaryFullPowerScaled77_11_5Norm.property,boundaryFullPowerScaled77_12_5Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_5Norm,boundaryFullPowerScaled77_9_5Norm,boundaryFullPowerScaled77_10_5Norm,boundaryFullPowerScaled77_11_5Norm,boundaryFullPowerScaled77_12_5Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_5Norm : {c : ℝ // boundaryFullCoefficient77 12 5=c} := by

  have he : boundaryFullCoefficient77 12 5=((boundaryPowerBernstein77_12_5Chunk0) + (boundaryPowerBernstein77_12_5Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_5Chunk0,boundaryPowerBernstein77_12_5Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_5Chunk0Norm.property,boundaryPowerBernstein77_12_5Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_5Chunk0Norm,boundaryPowerBernstein77_12_5Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_6Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_6Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_6Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_6Chunk0=boundaryPowerBernstein77_12_6Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_6Chunk0]

    rw [boundaryFullPowerScaled77_0_6Norm.property,boundaryFullPowerScaled77_1_6Norm.property,boundaryFullPowerScaled77_2_6Norm.property,boundaryFullPowerScaled77_3_6Norm.property,boundaryFullPowerScaled77_4_6Norm.property,boundaryFullPowerScaled77_5_6Norm.property,boundaryFullPowerScaled77_6_6Norm.property,boundaryFullPowerScaled77_7_6Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_6Norm,boundaryFullPowerScaled77_1_6Norm,boundaryFullPowerScaled77_2_6Norm,boundaryFullPowerScaled77_3_6Norm,boundaryFullPowerScaled77_4_6Norm,boundaryFullPowerScaled77_5_6Norm,boundaryFullPowerScaled77_6_6Norm,boundaryFullPowerScaled77_7_6Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_6Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_6Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_6Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_6Chunk8=boundaryPowerBernstein77_12_6Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_6Chunk8]

    rw [boundaryFullPowerScaled77_8_6Norm.property,boundaryFullPowerScaled77_9_6Norm.property,boundaryFullPowerScaled77_10_6Norm.property,boundaryFullPowerScaled77_11_6Norm.property,boundaryFullPowerScaled77_12_6Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_6Norm,boundaryFullPowerScaled77_9_6Norm,boundaryFullPowerScaled77_10_6Norm,boundaryFullPowerScaled77_11_6Norm,boundaryFullPowerScaled77_12_6Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_6Norm : {c : ℝ // boundaryFullCoefficient77 12 6=c} := by

  have he : boundaryFullCoefficient77 12 6=((boundaryPowerBernstein77_12_6Chunk0) + (boundaryPowerBernstein77_12_6Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_6Chunk0,boundaryPowerBernstein77_12_6Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_6Chunk0Norm.property,boundaryPowerBernstein77_12_6Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_6Chunk0Norm,boundaryPowerBernstein77_12_6Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_7Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_7Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_7Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_7Chunk0=boundaryPowerBernstein77_12_7Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_7Chunk0]

    rw [boundaryFullPowerScaled77_0_7Norm.property,boundaryFullPowerScaled77_1_7Norm.property,boundaryFullPowerScaled77_2_7Norm.property,boundaryFullPowerScaled77_3_7Norm.property,boundaryFullPowerScaled77_4_7Norm.property,boundaryFullPowerScaled77_5_7Norm.property,boundaryFullPowerScaled77_6_7Norm.property,boundaryFullPowerScaled77_7_7Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_7Norm,boundaryFullPowerScaled77_1_7Norm,boundaryFullPowerScaled77_2_7Norm,boundaryFullPowerScaled77_3_7Norm,boundaryFullPowerScaled77_4_7Norm,boundaryFullPowerScaled77_5_7Norm,boundaryFullPowerScaled77_6_7Norm,boundaryFullPowerScaled77_7_7Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_7Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_7Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_7Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_7Chunk8=boundaryPowerBernstein77_12_7Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_7Chunk8]

    rw [boundaryFullPowerScaled77_8_7Norm.property,boundaryFullPowerScaled77_9_7Norm.property,boundaryFullPowerScaled77_10_7Norm.property,boundaryFullPowerScaled77_11_7Norm.property,boundaryFullPowerScaled77_12_7Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_7Norm,boundaryFullPowerScaled77_9_7Norm,boundaryFullPowerScaled77_10_7Norm,boundaryFullPowerScaled77_11_7Norm,boundaryFullPowerScaled77_12_7Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_7Norm : {c : ℝ // boundaryFullCoefficient77 12 7=c} := by

  have he : boundaryFullCoefficient77 12 7=((boundaryPowerBernstein77_12_7Chunk0) + (boundaryPowerBernstein77_12_7Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_7Chunk0,boundaryPowerBernstein77_12_7Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_7Chunk0Norm.property,boundaryPowerBernstein77_12_7Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_7Chunk0Norm,boundaryPowerBernstein77_12_7Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_8Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_8Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_8Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_8Chunk0=boundaryPowerBernstein77_12_8Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_8Chunk0]

    rw [boundaryFullPowerScaled77_0_8Norm.property,boundaryFullPowerScaled77_1_8Norm.property,boundaryFullPowerScaled77_2_8Norm.property,boundaryFullPowerScaled77_3_8Norm.property,boundaryFullPowerScaled77_4_8Norm.property,boundaryFullPowerScaled77_5_8Norm.property,boundaryFullPowerScaled77_6_8Norm.property,boundaryFullPowerScaled77_7_8Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_8Norm,boundaryFullPowerScaled77_1_8Norm,boundaryFullPowerScaled77_2_8Norm,boundaryFullPowerScaled77_3_8Norm,boundaryFullPowerScaled77_4_8Norm,boundaryFullPowerScaled77_5_8Norm,boundaryFullPowerScaled77_6_8Norm,boundaryFullPowerScaled77_7_8Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_8Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_8Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_8Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_8Chunk8=boundaryPowerBernstein77_12_8Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_8Chunk8]

    rw [boundaryFullPowerScaled77_8_8Norm.property,boundaryFullPowerScaled77_9_8Norm.property,boundaryFullPowerScaled77_10_8Norm.property,boundaryFullPowerScaled77_11_8Norm.property,boundaryFullPowerScaled77_12_8Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_8Norm,boundaryFullPowerScaled77_9_8Norm,boundaryFullPowerScaled77_10_8Norm,boundaryFullPowerScaled77_11_8Norm,boundaryFullPowerScaled77_12_8Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_8Norm : {c : ℝ // boundaryFullCoefficient77 12 8=c} := by

  have he : boundaryFullCoefficient77 12 8=((boundaryPowerBernstein77_12_8Chunk0) + (boundaryPowerBernstein77_12_8Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_8Chunk0,boundaryPowerBernstein77_12_8Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_8Chunk0Norm.property,boundaryPowerBernstein77_12_8Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_8Chunk0Norm,boundaryPowerBernstein77_12_8Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_9Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_9Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_9Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_9Chunk0=boundaryPowerBernstein77_12_9Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_9Chunk0]

    rw [boundaryFullPowerScaled77_0_9Norm.property,boundaryFullPowerScaled77_1_9Norm.property,boundaryFullPowerScaled77_2_9Norm.property,boundaryFullPowerScaled77_3_9Norm.property,boundaryFullPowerScaled77_4_9Norm.property,boundaryFullPowerScaled77_5_9Norm.property,boundaryFullPowerScaled77_6_9Norm.property,boundaryFullPowerScaled77_7_9Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_9Norm,boundaryFullPowerScaled77_1_9Norm,boundaryFullPowerScaled77_2_9Norm,boundaryFullPowerScaled77_3_9Norm,boundaryFullPowerScaled77_4_9Norm,boundaryFullPowerScaled77_5_9Norm,boundaryFullPowerScaled77_6_9Norm,boundaryFullPowerScaled77_7_9Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_9Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_9Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_9Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_9Chunk8=boundaryPowerBernstein77_12_9Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_9Chunk8]

    rw [boundaryFullPowerScaled77_8_9Norm.property,boundaryFullPowerScaled77_9_9Norm.property,boundaryFullPowerScaled77_10_9Norm.property,boundaryFullPowerScaled77_11_9Norm.property,boundaryFullPowerScaled77_12_9Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_9Norm,boundaryFullPowerScaled77_9_9Norm,boundaryFullPowerScaled77_10_9Norm,boundaryFullPowerScaled77_11_9Norm,boundaryFullPowerScaled77_12_9Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_9Norm : {c : ℝ // boundaryFullCoefficient77 12 9=c} := by

  have he : boundaryFullCoefficient77 12 9=((boundaryPowerBernstein77_12_9Chunk0) + (boundaryPowerBernstein77_12_9Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_9Chunk0,boundaryPowerBernstein77_12_9Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_9Chunk0Norm.property,boundaryPowerBernstein77_12_9Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_9Chunk0Norm,boundaryPowerBernstein77_12_9Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_10Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_10Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_10Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_10Chunk0=boundaryPowerBernstein77_12_10Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_10Chunk0]

    rw [boundaryFullPowerScaled77_0_10Norm.property,boundaryFullPowerScaled77_1_10Norm.property,boundaryFullPowerScaled77_2_10Norm.property,boundaryFullPowerScaled77_3_10Norm.property,boundaryFullPowerScaled77_4_10Norm.property,boundaryFullPowerScaled77_5_10Norm.property,boundaryFullPowerScaled77_6_10Norm.property,boundaryFullPowerScaled77_7_10Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_10Norm,boundaryFullPowerScaled77_1_10Norm,boundaryFullPowerScaled77_2_10Norm,boundaryFullPowerScaled77_3_10Norm,boundaryFullPowerScaled77_4_10Norm,boundaryFullPowerScaled77_5_10Norm,boundaryFullPowerScaled77_6_10Norm,boundaryFullPowerScaled77_7_10Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_10Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_10Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_10Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_10Chunk8=boundaryPowerBernstein77_12_10Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_10Chunk8]

    rw [boundaryFullPowerScaled77_8_10Norm.property,boundaryFullPowerScaled77_9_10Norm.property,boundaryFullPowerScaled77_10_10Norm.property,boundaryFullPowerScaled77_11_10Norm.property,boundaryFullPowerScaled77_12_10Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_10Norm,boundaryFullPowerScaled77_9_10Norm,boundaryFullPowerScaled77_10_10Norm,boundaryFullPowerScaled77_11_10Norm,boundaryFullPowerScaled77_12_10Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_10Norm : {c : ℝ // boundaryFullCoefficient77 12 10=c} := by

  have he : boundaryFullCoefficient77 12 10=((boundaryPowerBernstein77_12_10Chunk0) + (boundaryPowerBernstein77_12_10Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_10Chunk0,boundaryPowerBernstein77_12_10Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_10Chunk0Norm.property,boundaryPowerBernstein77_12_10Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_10Chunk0Norm,boundaryPowerBernstein77_12_10Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_11Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_11Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_11Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_11Chunk0=boundaryPowerBernstein77_12_11Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_11Chunk0]

    rw [boundaryFullPowerScaled77_0_11Norm.property,boundaryFullPowerScaled77_1_11Norm.property,boundaryFullPowerScaled77_2_11Norm.property,boundaryFullPowerScaled77_3_11Norm.property,boundaryFullPowerScaled77_4_11Norm.property,boundaryFullPowerScaled77_5_11Norm.property,boundaryFullPowerScaled77_6_11Norm.property,boundaryFullPowerScaled77_7_11Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_11Norm,boundaryFullPowerScaled77_1_11Norm,boundaryFullPowerScaled77_2_11Norm,boundaryFullPowerScaled77_3_11Norm,boundaryFullPowerScaled77_4_11Norm,boundaryFullPowerScaled77_5_11Norm,boundaryFullPowerScaled77_6_11Norm,boundaryFullPowerScaled77_7_11Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_11Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_11Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_11Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_11Chunk8=boundaryPowerBernstein77_12_11Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_11Chunk8]

    rw [boundaryFullPowerScaled77_8_11Norm.property,boundaryFullPowerScaled77_9_11Norm.property,boundaryFullPowerScaled77_10_11Norm.property,boundaryFullPowerScaled77_11_11Norm.property,boundaryFullPowerScaled77_12_11Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_11Norm,boundaryFullPowerScaled77_9_11Norm,boundaryFullPowerScaled77_10_11Norm,boundaryFullPowerScaled77_11_11Norm,boundaryFullPowerScaled77_12_11Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_11Norm : {c : ℝ // boundaryFullCoefficient77 12 11=c} := by

  have he : boundaryFullCoefficient77 12 11=((boundaryPowerBernstein77_12_11Chunk0) + (boundaryPowerBernstein77_12_11Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_11Chunk0,boundaryPowerBernstein77_12_11Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_11Chunk0Norm.property,boundaryPowerBernstein77_12_11Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_11Chunk0Norm,boundaryPowerBernstein77_12_11Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_12Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_12Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_12Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_12Chunk0=boundaryPowerBernstein77_12_12Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_12Chunk0]

    rw [boundaryFullPowerScaled77_0_12Norm.property,boundaryFullPowerScaled77_1_12Norm.property,boundaryFullPowerScaled77_2_12Norm.property,boundaryFullPowerScaled77_3_12Norm.property,boundaryFullPowerScaled77_4_12Norm.property,boundaryFullPowerScaled77_5_12Norm.property,boundaryFullPowerScaled77_6_12Norm.property,boundaryFullPowerScaled77_7_12Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_12Norm,boundaryFullPowerScaled77_1_12Norm,boundaryFullPowerScaled77_2_12Norm,boundaryFullPowerScaled77_3_12Norm,boundaryFullPowerScaled77_4_12Norm,boundaryFullPowerScaled77_5_12Norm,boundaryFullPowerScaled77_6_12Norm,boundaryFullPowerScaled77_7_12Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_12Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_12Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_12Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_12Chunk8=boundaryPowerBernstein77_12_12Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_12Chunk8]

    rw [boundaryFullPowerScaled77_8_12Norm.property,boundaryFullPowerScaled77_9_12Norm.property,boundaryFullPowerScaled77_10_12Norm.property,boundaryFullPowerScaled77_11_12Norm.property,boundaryFullPowerScaled77_12_12Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_12Norm,boundaryFullPowerScaled77_9_12Norm,boundaryFullPowerScaled77_10_12Norm,boundaryFullPowerScaled77_11_12Norm,boundaryFullPowerScaled77_12_12Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_12Norm : {c : ℝ // boundaryFullCoefficient77 12 12=c} := by

  have he : boundaryFullCoefficient77 12 12=((boundaryPowerBernstein77_12_12Chunk0) + (boundaryPowerBernstein77_12_12Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_12Chunk0,boundaryPowerBernstein77_12_12Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_12Chunk0Norm.property,boundaryPowerBernstein77_12_12Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_12Chunk0Norm,boundaryPowerBernstein77_12_12Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_13Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_13Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_13Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_13Chunk0=boundaryPowerBernstein77_12_13Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_13Chunk0]

    rw [boundaryFullPowerScaled77_0_13Norm.property,boundaryFullPowerScaled77_1_13Norm.property,boundaryFullPowerScaled77_2_13Norm.property,boundaryFullPowerScaled77_3_13Norm.property,boundaryFullPowerScaled77_4_13Norm.property,boundaryFullPowerScaled77_5_13Norm.property,boundaryFullPowerScaled77_6_13Norm.property,boundaryFullPowerScaled77_7_13Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_13Norm,boundaryFullPowerScaled77_1_13Norm,boundaryFullPowerScaled77_2_13Norm,boundaryFullPowerScaled77_3_13Norm,boundaryFullPowerScaled77_4_13Norm,boundaryFullPowerScaled77_5_13Norm,boundaryFullPowerScaled77_6_13Norm,boundaryFullPowerScaled77_7_13Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_13Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_13Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_13Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_13Chunk8=boundaryPowerBernstein77_12_13Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_13Chunk8]

    rw [boundaryFullPowerScaled77_8_13Norm.property,boundaryFullPowerScaled77_9_13Norm.property,boundaryFullPowerScaled77_10_13Norm.property,boundaryFullPowerScaled77_11_13Norm.property,boundaryFullPowerScaled77_12_13Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_13Norm,boundaryFullPowerScaled77_9_13Norm,boundaryFullPowerScaled77_10_13Norm,boundaryFullPowerScaled77_11_13Norm,boundaryFullPowerScaled77_12_13Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_13Norm : {c : ℝ // boundaryFullCoefficient77 12 13=c} := by

  have he : boundaryFullCoefficient77 12 13=((boundaryPowerBernstein77_12_13Chunk0) + (boundaryPowerBernstein77_12_13Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_13Chunk0,boundaryPowerBernstein77_12_13Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_13Chunk0Norm.property,boundaryPowerBernstein77_12_13Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_13Chunk0Norm,boundaryPowerBernstein77_12_13Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_14Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_14Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_14Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_14Chunk0=boundaryPowerBernstein77_12_14Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_14Chunk0]

    rw [boundaryFullPowerScaled77_0_14Norm.property,boundaryFullPowerScaled77_1_14Norm.property,boundaryFullPowerScaled77_2_14Norm.property,boundaryFullPowerScaled77_3_14Norm.property,boundaryFullPowerScaled77_4_14Norm.property,boundaryFullPowerScaled77_5_14Norm.property,boundaryFullPowerScaled77_6_14Norm.property,boundaryFullPowerScaled77_7_14Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_14Norm,boundaryFullPowerScaled77_1_14Norm,boundaryFullPowerScaled77_2_14Norm,boundaryFullPowerScaled77_3_14Norm,boundaryFullPowerScaled77_4_14Norm,boundaryFullPowerScaled77_5_14Norm,boundaryFullPowerScaled77_6_14Norm,boundaryFullPowerScaled77_7_14Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_14Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_14Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_14Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_14Chunk8=boundaryPowerBernstein77_12_14Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_14Chunk8]

    rw [boundaryFullPowerScaled77_8_14Norm.property,boundaryFullPowerScaled77_9_14Norm.property,boundaryFullPowerScaled77_10_14Norm.property,boundaryFullPowerScaled77_11_14Norm.property,boundaryFullPowerScaled77_12_14Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_14Norm,boundaryFullPowerScaled77_9_14Norm,boundaryFullPowerScaled77_10_14Norm,boundaryFullPowerScaled77_11_14Norm,boundaryFullPowerScaled77_12_14Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_14Norm : {c : ℝ // boundaryFullCoefficient77 12 14=c} := by

  have he : boundaryFullCoefficient77 12 14=((boundaryPowerBernstein77_12_14Chunk0) + (boundaryPowerBernstein77_12_14Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_14Chunk0,boundaryPowerBernstein77_12_14Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_14Chunk0Norm.property,boundaryPowerBernstein77_12_14Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_14Chunk0Norm,boundaryPowerBernstein77_12_14Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_15Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_15Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_15Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_15Chunk0=boundaryPowerBernstein77_12_15Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_15Chunk0]

    rw [boundaryFullPowerScaled77_0_15Norm.property,boundaryFullPowerScaled77_1_15Norm.property,boundaryFullPowerScaled77_2_15Norm.property,boundaryFullPowerScaled77_3_15Norm.property,boundaryFullPowerScaled77_4_15Norm.property,boundaryFullPowerScaled77_5_15Norm.property,boundaryFullPowerScaled77_6_15Norm.property,boundaryFullPowerScaled77_7_15Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_15Norm,boundaryFullPowerScaled77_1_15Norm,boundaryFullPowerScaled77_2_15Norm,boundaryFullPowerScaled77_3_15Norm,boundaryFullPowerScaled77_4_15Norm,boundaryFullPowerScaled77_5_15Norm,boundaryFullPowerScaled77_6_15Norm,boundaryFullPowerScaled77_7_15Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_15Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_15Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_15Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_15Chunk8=boundaryPowerBernstein77_12_15Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_15Chunk8]

    rw [boundaryFullPowerScaled77_8_15Norm.property,boundaryFullPowerScaled77_9_15Norm.property,boundaryFullPowerScaled77_10_15Norm.property,boundaryFullPowerScaled77_11_15Norm.property,boundaryFullPowerScaled77_12_15Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_15Norm,boundaryFullPowerScaled77_9_15Norm,boundaryFullPowerScaled77_10_15Norm,boundaryFullPowerScaled77_11_15Norm,boundaryFullPowerScaled77_12_15Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_15Norm : {c : ℝ // boundaryFullCoefficient77 12 15=c} := by

  have he : boundaryFullCoefficient77 12 15=((boundaryPowerBernstein77_12_15Chunk0) + (boundaryPowerBernstein77_12_15Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_15Chunk0,boundaryPowerBernstein77_12_15Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_15Chunk0Norm.property,boundaryPowerBernstein77_12_15Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_15Chunk0Norm,boundaryPowerBernstein77_12_15Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_16Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_16Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_16Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_16Chunk0=boundaryPowerBernstein77_12_16Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_16Chunk0]

    rw [boundaryFullPowerScaled77_0_16Norm.property,boundaryFullPowerScaled77_1_16Norm.property,boundaryFullPowerScaled77_2_16Norm.property,boundaryFullPowerScaled77_3_16Norm.property,boundaryFullPowerScaled77_4_16Norm.property,boundaryFullPowerScaled77_5_16Norm.property,boundaryFullPowerScaled77_6_16Norm.property,boundaryFullPowerScaled77_7_16Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_16Norm,boundaryFullPowerScaled77_1_16Norm,boundaryFullPowerScaled77_2_16Norm,boundaryFullPowerScaled77_3_16Norm,boundaryFullPowerScaled77_4_16Norm,boundaryFullPowerScaled77_5_16Norm,boundaryFullPowerScaled77_6_16Norm,boundaryFullPowerScaled77_7_16Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_16Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_16Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_16Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_16Chunk8=boundaryPowerBernstein77_12_16Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_16Chunk8]

    rw [boundaryFullPowerScaled77_8_16Norm.property,boundaryFullPowerScaled77_9_16Norm.property,boundaryFullPowerScaled77_10_16Norm.property,boundaryFullPowerScaled77_11_16Norm.property,boundaryFullPowerScaled77_12_16Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_16Norm,boundaryFullPowerScaled77_9_16Norm,boundaryFullPowerScaled77_10_16Norm,boundaryFullPowerScaled77_11_16Norm,boundaryFullPowerScaled77_12_16Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_16Norm : {c : ℝ // boundaryFullCoefficient77 12 16=c} := by

  have he : boundaryFullCoefficient77 12 16=((boundaryPowerBernstein77_12_16Chunk0) + (boundaryPowerBernstein77_12_16Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_16Chunk0,boundaryPowerBernstein77_12_16Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_16Chunk0Norm.property,boundaryPowerBernstein77_12_16Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_16Chunk0Norm,boundaryPowerBernstein77_12_16Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_17Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_17Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_17Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_17Chunk0=boundaryPowerBernstein77_12_17Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_17Chunk0]

    rw [boundaryFullPowerScaled77_0_17Norm.property,boundaryFullPowerScaled77_1_17Norm.property,boundaryFullPowerScaled77_2_17Norm.property,boundaryFullPowerScaled77_3_17Norm.property,boundaryFullPowerScaled77_4_17Norm.property,boundaryFullPowerScaled77_5_17Norm.property,boundaryFullPowerScaled77_6_17Norm.property,boundaryFullPowerScaled77_7_17Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_17Norm,boundaryFullPowerScaled77_1_17Norm,boundaryFullPowerScaled77_2_17Norm,boundaryFullPowerScaled77_3_17Norm,boundaryFullPowerScaled77_4_17Norm,boundaryFullPowerScaled77_5_17Norm,boundaryFullPowerScaled77_6_17Norm,boundaryFullPowerScaled77_7_17Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_17Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_17Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_17Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_17Chunk8=boundaryPowerBernstein77_12_17Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_17Chunk8]

    rw [boundaryFullPowerScaled77_8_17Norm.property,boundaryFullPowerScaled77_9_17Norm.property,boundaryFullPowerScaled77_10_17Norm.property,boundaryFullPowerScaled77_11_17Norm.property,boundaryFullPowerScaled77_12_17Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_17Norm,boundaryFullPowerScaled77_9_17Norm,boundaryFullPowerScaled77_10_17Norm,boundaryFullPowerScaled77_11_17Norm,boundaryFullPowerScaled77_12_17Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_17Norm : {c : ℝ // boundaryFullCoefficient77 12 17=c} := by

  have he : boundaryFullCoefficient77 12 17=((boundaryPowerBernstein77_12_17Chunk0) + (boundaryPowerBernstein77_12_17Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_17Chunk0,boundaryPowerBernstein77_12_17Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_17Chunk0Norm.property,boundaryPowerBernstein77_12_17Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_17Chunk0Norm,boundaryPowerBernstein77_12_17Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_18Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_18Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_18Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_18Chunk0=boundaryPowerBernstein77_12_18Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_18Chunk0]

    rw [boundaryFullPowerScaled77_0_18Norm.property,boundaryFullPowerScaled77_1_18Norm.property,boundaryFullPowerScaled77_2_18Norm.property,boundaryFullPowerScaled77_3_18Norm.property,boundaryFullPowerScaled77_4_18Norm.property,boundaryFullPowerScaled77_5_18Norm.property,boundaryFullPowerScaled77_6_18Norm.property,boundaryFullPowerScaled77_7_18Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_18Norm,boundaryFullPowerScaled77_1_18Norm,boundaryFullPowerScaled77_2_18Norm,boundaryFullPowerScaled77_3_18Norm,boundaryFullPowerScaled77_4_18Norm,boundaryFullPowerScaled77_5_18Norm,boundaryFullPowerScaled77_6_18Norm,boundaryFullPowerScaled77_7_18Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_18Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_18Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_18Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_18Chunk8=boundaryPowerBernstein77_12_18Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_18Chunk8]

    rw [boundaryFullPowerScaled77_8_18Norm.property,boundaryFullPowerScaled77_9_18Norm.property,boundaryFullPowerScaled77_10_18Norm.property,boundaryFullPowerScaled77_11_18Norm.property,boundaryFullPowerScaled77_12_18Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_18Norm,boundaryFullPowerScaled77_9_18Norm,boundaryFullPowerScaled77_10_18Norm,boundaryFullPowerScaled77_11_18Norm,boundaryFullPowerScaled77_12_18Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_18Norm : {c : ℝ // boundaryFullCoefficient77 12 18=c} := by

  have he : boundaryFullCoefficient77 12 18=((boundaryPowerBernstein77_12_18Chunk0) + (boundaryPowerBernstein77_12_18Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_18Chunk0,boundaryPowerBernstein77_12_18Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_18Chunk0Norm.property,boundaryPowerBernstein77_12_18Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_18Chunk0Norm,boundaryPowerBernstein77_12_18Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_19Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_19Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_19Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_19Chunk0=boundaryPowerBernstein77_12_19Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_19Chunk0]

    rw [boundaryFullPowerScaled77_0_19Norm.property,boundaryFullPowerScaled77_1_19Norm.property,boundaryFullPowerScaled77_2_19Norm.property,boundaryFullPowerScaled77_3_19Norm.property,boundaryFullPowerScaled77_4_19Norm.property,boundaryFullPowerScaled77_5_19Norm.property,boundaryFullPowerScaled77_6_19Norm.property,boundaryFullPowerScaled77_7_19Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_19Norm,boundaryFullPowerScaled77_1_19Norm,boundaryFullPowerScaled77_2_19Norm,boundaryFullPowerScaled77_3_19Norm,boundaryFullPowerScaled77_4_19Norm,boundaryFullPowerScaled77_5_19Norm,boundaryFullPowerScaled77_6_19Norm,boundaryFullPowerScaled77_7_19Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_19Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_19Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_19Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_19Chunk8=boundaryPowerBernstein77_12_19Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_19Chunk8]

    rw [boundaryFullPowerScaled77_8_19Norm.property,boundaryFullPowerScaled77_9_19Norm.property,boundaryFullPowerScaled77_10_19Norm.property,boundaryFullPowerScaled77_11_19Norm.property,boundaryFullPowerScaled77_12_19Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_19Norm,boundaryFullPowerScaled77_9_19Norm,boundaryFullPowerScaled77_10_19Norm,boundaryFullPowerScaled77_11_19Norm,boundaryFullPowerScaled77_12_19Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_19Norm : {c : ℝ // boundaryFullCoefficient77 12 19=c} := by

  have he : boundaryFullCoefficient77 12 19=((boundaryPowerBernstein77_12_19Chunk0) + (boundaryPowerBernstein77_12_19Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_19Chunk0,boundaryPowerBernstein77_12_19Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_19Chunk0Norm.property,boundaryPowerBernstein77_12_19Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_19Chunk0Norm,boundaryPowerBernstein77_12_19Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_20Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_20Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_20Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_20Chunk0=boundaryPowerBernstein77_12_20Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_20Chunk0]

    rw [boundaryFullPowerScaled77_0_20Norm.property,boundaryFullPowerScaled77_1_20Norm.property,boundaryFullPowerScaled77_2_20Norm.property,boundaryFullPowerScaled77_3_20Norm.property,boundaryFullPowerScaled77_4_20Norm.property,boundaryFullPowerScaled77_5_20Norm.property,boundaryFullPowerScaled77_6_20Norm.property,boundaryFullPowerScaled77_7_20Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_20Norm,boundaryFullPowerScaled77_1_20Norm,boundaryFullPowerScaled77_2_20Norm,boundaryFullPowerScaled77_3_20Norm,boundaryFullPowerScaled77_4_20Norm,boundaryFullPowerScaled77_5_20Norm,boundaryFullPowerScaled77_6_20Norm,boundaryFullPowerScaled77_7_20Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_20Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_20Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_20Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_20Chunk8=boundaryPowerBernstein77_12_20Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_20Chunk8]

    rw [boundaryFullPowerScaled77_8_20Norm.property,boundaryFullPowerScaled77_9_20Norm.property,boundaryFullPowerScaled77_10_20Norm.property,boundaryFullPowerScaled77_11_20Norm.property,boundaryFullPowerScaled77_12_20Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_20Norm,boundaryFullPowerScaled77_9_20Norm,boundaryFullPowerScaled77_10_20Norm,boundaryFullPowerScaled77_11_20Norm,boundaryFullPowerScaled77_12_20Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_20Norm : {c : ℝ // boundaryFullCoefficient77 12 20=c} := by

  have he : boundaryFullCoefficient77 12 20=((boundaryPowerBernstein77_12_20Chunk0) + (boundaryPowerBernstein77_12_20Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_20Chunk0,boundaryPowerBernstein77_12_20Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_20Chunk0Norm.property,boundaryPowerBernstein77_12_20Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_20Chunk0Norm,boundaryPowerBernstein77_12_20Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_21Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_21Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_21Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_21Chunk0=boundaryPowerBernstein77_12_21Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_21Chunk0]

    rw [boundaryFullPowerScaled77_0_21Norm.property,boundaryFullPowerScaled77_1_21Norm.property,boundaryFullPowerScaled77_2_21Norm.property,boundaryFullPowerScaled77_3_21Norm.property,boundaryFullPowerScaled77_4_21Norm.property,boundaryFullPowerScaled77_5_21Norm.property,boundaryFullPowerScaled77_6_21Norm.property,boundaryFullPowerScaled77_7_21Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_21Norm,boundaryFullPowerScaled77_1_21Norm,boundaryFullPowerScaled77_2_21Norm,boundaryFullPowerScaled77_3_21Norm,boundaryFullPowerScaled77_4_21Norm,boundaryFullPowerScaled77_5_21Norm,boundaryFullPowerScaled77_6_21Norm,boundaryFullPowerScaled77_7_21Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_21Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_21Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_21Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_21Chunk8=boundaryPowerBernstein77_12_21Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_21Chunk8]

    rw [boundaryFullPowerScaled77_8_21Norm.property,boundaryFullPowerScaled77_9_21Norm.property,boundaryFullPowerScaled77_10_21Norm.property,boundaryFullPowerScaled77_11_21Norm.property,boundaryFullPowerScaled77_12_21Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_21Norm,boundaryFullPowerScaled77_9_21Norm,boundaryFullPowerScaled77_10_21Norm,boundaryFullPowerScaled77_11_21Norm,boundaryFullPowerScaled77_12_21Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_21Norm : {c : ℝ // boundaryFullCoefficient77 12 21=c} := by

  have he : boundaryFullCoefficient77 12 21=((boundaryPowerBernstein77_12_21Chunk0) + (boundaryPowerBernstein77_12_21Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_21Chunk0,boundaryPowerBernstein77_12_21Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_21Chunk0Norm.property,boundaryPowerBernstein77_12_21Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_21Chunk0Norm,boundaryPowerBernstein77_12_21Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_22Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_22Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_22Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_22Chunk0=boundaryPowerBernstein77_12_22Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_22Chunk0]

    rw [boundaryFullPowerScaled77_0_22Norm.property,boundaryFullPowerScaled77_1_22Norm.property,boundaryFullPowerScaled77_2_22Norm.property,boundaryFullPowerScaled77_3_22Norm.property,boundaryFullPowerScaled77_4_22Norm.property,boundaryFullPowerScaled77_5_22Norm.property,boundaryFullPowerScaled77_6_22Norm.property,boundaryFullPowerScaled77_7_22Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_22Norm,boundaryFullPowerScaled77_1_22Norm,boundaryFullPowerScaled77_2_22Norm,boundaryFullPowerScaled77_3_22Norm,boundaryFullPowerScaled77_4_22Norm,boundaryFullPowerScaled77_5_22Norm,boundaryFullPowerScaled77_6_22Norm,boundaryFullPowerScaled77_7_22Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_22Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_22Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_22Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_22Chunk8=boundaryPowerBernstein77_12_22Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_22Chunk8]

    rw [boundaryFullPowerScaled77_8_22Norm.property,boundaryFullPowerScaled77_9_22Norm.property,boundaryFullPowerScaled77_10_22Norm.property,boundaryFullPowerScaled77_11_22Norm.property,boundaryFullPowerScaled77_12_22Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_22Norm,boundaryFullPowerScaled77_9_22Norm,boundaryFullPowerScaled77_10_22Norm,boundaryFullPowerScaled77_11_22Norm,boundaryFullPowerScaled77_12_22Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_22Norm : {c : ℝ // boundaryFullCoefficient77 12 22=c} := by

  have he : boundaryFullCoefficient77 12 22=((boundaryPowerBernstein77_12_22Chunk0) + (boundaryPowerBernstein77_12_22Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_22Chunk0,boundaryPowerBernstein77_12_22Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_22Chunk0Norm.property,boundaryPowerBernstein77_12_22Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_22Chunk0Norm,boundaryPowerBernstein77_12_22Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_23Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_23Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_23Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_23Chunk0=boundaryPowerBernstein77_12_23Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_23Chunk0]

    rw [boundaryFullPowerScaled77_0_23Norm.property,boundaryFullPowerScaled77_1_23Norm.property,boundaryFullPowerScaled77_2_23Norm.property,boundaryFullPowerScaled77_3_23Norm.property,boundaryFullPowerScaled77_4_23Norm.property,boundaryFullPowerScaled77_5_23Norm.property,boundaryFullPowerScaled77_6_23Norm.property,boundaryFullPowerScaled77_7_23Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_23Norm,boundaryFullPowerScaled77_1_23Norm,boundaryFullPowerScaled77_2_23Norm,boundaryFullPowerScaled77_3_23Norm,boundaryFullPowerScaled77_4_23Norm,boundaryFullPowerScaled77_5_23Norm,boundaryFullPowerScaled77_6_23Norm,boundaryFullPowerScaled77_7_23Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_23Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_23Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_23Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_23Chunk8=boundaryPowerBernstein77_12_23Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_23Chunk8]

    rw [boundaryFullPowerScaled77_8_23Norm.property,boundaryFullPowerScaled77_9_23Norm.property,boundaryFullPowerScaled77_10_23Norm.property,boundaryFullPowerScaled77_11_23Norm.property,boundaryFullPowerScaled77_12_23Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_23Norm,boundaryFullPowerScaled77_9_23Norm,boundaryFullPowerScaled77_10_23Norm,boundaryFullPowerScaled77_11_23Norm,boundaryFullPowerScaled77_12_23Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_23Norm : {c : ℝ // boundaryFullCoefficient77 12 23=c} := by

  have he : boundaryFullCoefficient77 12 23=((boundaryPowerBernstein77_12_23Chunk0) + (boundaryPowerBernstein77_12_23Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_23Chunk0,boundaryPowerBernstein77_12_23Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_23Chunk0Norm.property,boundaryPowerBernstein77_12_23Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_23Chunk0Norm,boundaryPowerBernstein77_12_23Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_24Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_24Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_24Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_24Chunk0=boundaryPowerBernstein77_12_24Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_24Chunk0]

    rw [boundaryFullPowerScaled77_0_24Norm.property,boundaryFullPowerScaled77_1_24Norm.property,boundaryFullPowerScaled77_2_24Norm.property,boundaryFullPowerScaled77_3_24Norm.property,boundaryFullPowerScaled77_4_24Norm.property,boundaryFullPowerScaled77_5_24Norm.property,boundaryFullPowerScaled77_6_24Norm.property,boundaryFullPowerScaled77_7_24Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_24Norm,boundaryFullPowerScaled77_1_24Norm,boundaryFullPowerScaled77_2_24Norm,boundaryFullPowerScaled77_3_24Norm,boundaryFullPowerScaled77_4_24Norm,boundaryFullPowerScaled77_5_24Norm,boundaryFullPowerScaled77_6_24Norm,boundaryFullPowerScaled77_7_24Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_24Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_24Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_24Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_24Chunk8=boundaryPowerBernstein77_12_24Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_24Chunk8]

    rw [boundaryFullPowerScaled77_8_24Norm.property,boundaryFullPowerScaled77_9_24Norm.property,boundaryFullPowerScaled77_10_24Norm.property,boundaryFullPowerScaled77_11_24Norm.property,boundaryFullPowerScaled77_12_24Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_24Norm,boundaryFullPowerScaled77_9_24Norm,boundaryFullPowerScaled77_10_24Norm,boundaryFullPowerScaled77_11_24Norm,boundaryFullPowerScaled77_12_24Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_24Norm : {c : ℝ // boundaryFullCoefficient77 12 24=c} := by

  have he : boundaryFullCoefficient77 12 24=((boundaryPowerBernstein77_12_24Chunk0) + (boundaryPowerBernstein77_12_24Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_24Chunk0,boundaryPowerBernstein77_12_24Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_24Chunk0Norm.property,boundaryPowerBernstein77_12_24Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_24Chunk0Norm,boundaryPowerBernstein77_12_24Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_25Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_25Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_25Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_25Chunk0=boundaryPowerBernstein77_12_25Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_25Chunk0]

    rw [boundaryFullPowerScaled77_0_25Norm.property,boundaryFullPowerScaled77_1_25Norm.property,boundaryFullPowerScaled77_2_25Norm.property,boundaryFullPowerScaled77_3_25Norm.property,boundaryFullPowerScaled77_4_25Norm.property,boundaryFullPowerScaled77_5_25Norm.property,boundaryFullPowerScaled77_6_25Norm.property,boundaryFullPowerScaled77_7_25Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_25Norm,boundaryFullPowerScaled77_1_25Norm,boundaryFullPowerScaled77_2_25Norm,boundaryFullPowerScaled77_3_25Norm,boundaryFullPowerScaled77_4_25Norm,boundaryFullPowerScaled77_5_25Norm,boundaryFullPowerScaled77_6_25Norm,boundaryFullPowerScaled77_7_25Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_25Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_25Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_25Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_25Chunk8=boundaryPowerBernstein77_12_25Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_25Chunk8]

    rw [boundaryFullPowerScaled77_8_25Norm.property,boundaryFullPowerScaled77_9_25Norm.property,boundaryFullPowerScaled77_10_25Norm.property,boundaryFullPowerScaled77_11_25Norm.property,boundaryFullPowerScaled77_12_25Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_25Norm,boundaryFullPowerScaled77_9_25Norm,boundaryFullPowerScaled77_10_25Norm,boundaryFullPowerScaled77_11_25Norm,boundaryFullPowerScaled77_12_25Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_25Norm : {c : ℝ // boundaryFullCoefficient77 12 25=c} := by

  have he : boundaryFullCoefficient77 12 25=((boundaryPowerBernstein77_12_25Chunk0) + (boundaryPowerBernstein77_12_25Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_25Chunk0,boundaryPowerBernstein77_12_25Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_25Chunk0Norm.property,boundaryPowerBernstein77_12_25Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_25Chunk0Norm,boundaryPowerBernstein77_12_25Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_26Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_26Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_26Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_26Chunk0=boundaryPowerBernstein77_12_26Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_26Chunk0]

    rw [boundaryFullPowerScaled77_0_26Norm.property,boundaryFullPowerScaled77_1_26Norm.property,boundaryFullPowerScaled77_2_26Norm.property,boundaryFullPowerScaled77_3_26Norm.property,boundaryFullPowerScaled77_4_26Norm.property,boundaryFullPowerScaled77_5_26Norm.property,boundaryFullPowerScaled77_6_26Norm.property,boundaryFullPowerScaled77_7_26Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_26Norm,boundaryFullPowerScaled77_1_26Norm,boundaryFullPowerScaled77_2_26Norm,boundaryFullPowerScaled77_3_26Norm,boundaryFullPowerScaled77_4_26Norm,boundaryFullPowerScaled77_5_26Norm,boundaryFullPowerScaled77_6_26Norm,boundaryFullPowerScaled77_7_26Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_26Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_26Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_26Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_26Chunk8=boundaryPowerBernstein77_12_26Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_26Chunk8]

    rw [boundaryFullPowerScaled77_8_26Norm.property,boundaryFullPowerScaled77_9_26Norm.property,boundaryFullPowerScaled77_10_26Norm.property,boundaryFullPowerScaled77_11_26Norm.property,boundaryFullPowerScaled77_12_26Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_26Norm,boundaryFullPowerScaled77_9_26Norm,boundaryFullPowerScaled77_10_26Norm,boundaryFullPowerScaled77_11_26Norm,boundaryFullPowerScaled77_12_26Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_26Norm : {c : ℝ // boundaryFullCoefficient77 12 26=c} := by

  have he : boundaryFullCoefficient77 12 26=((boundaryPowerBernstein77_12_26Chunk0) + (boundaryPowerBernstein77_12_26Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_26Chunk0,boundaryPowerBernstein77_12_26Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_26Chunk0Norm.property,boundaryPowerBernstein77_12_26Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_26Chunk0Norm,boundaryPowerBernstein77_12_26Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_27Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_27Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_27Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_27Chunk0=boundaryPowerBernstein77_12_27Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_27Chunk0]

    rw [boundaryFullPowerScaled77_0_27Norm.property,boundaryFullPowerScaled77_1_27Norm.property,boundaryFullPowerScaled77_2_27Norm.property,boundaryFullPowerScaled77_3_27Norm.property,boundaryFullPowerScaled77_4_27Norm.property,boundaryFullPowerScaled77_5_27Norm.property,boundaryFullPowerScaled77_6_27Norm.property,boundaryFullPowerScaled77_7_27Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_27Norm,boundaryFullPowerScaled77_1_27Norm,boundaryFullPowerScaled77_2_27Norm,boundaryFullPowerScaled77_3_27Norm,boundaryFullPowerScaled77_4_27Norm,boundaryFullPowerScaled77_5_27Norm,boundaryFullPowerScaled77_6_27Norm,boundaryFullPowerScaled77_7_27Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_27Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_27Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_27Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_27Chunk8=boundaryPowerBernstein77_12_27Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_27Chunk8]

    rw [boundaryFullPowerScaled77_8_27Norm.property,boundaryFullPowerScaled77_9_27Norm.property,boundaryFullPowerScaled77_10_27Norm.property,boundaryFullPowerScaled77_11_27Norm.property,boundaryFullPowerScaled77_12_27Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_27Norm,boundaryFullPowerScaled77_9_27Norm,boundaryFullPowerScaled77_10_27Norm,boundaryFullPowerScaled77_11_27Norm,boundaryFullPowerScaled77_12_27Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_27Norm : {c : ℝ // boundaryFullCoefficient77 12 27=c} := by

  have he : boundaryFullCoefficient77 12 27=((boundaryPowerBernstein77_12_27Chunk0) + (boundaryPowerBernstein77_12_27Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_27Chunk0,boundaryPowerBernstein77_12_27Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_27Chunk0Norm.property,boundaryPowerBernstein77_12_27Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_27Chunk0Norm,boundaryPowerBernstein77_12_27Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_28Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_28Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_28Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_28Chunk0=boundaryPowerBernstein77_12_28Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_28Chunk0]

    rw [boundaryFullPowerScaled77_0_28Norm.property,boundaryFullPowerScaled77_1_28Norm.property,boundaryFullPowerScaled77_2_28Norm.property,boundaryFullPowerScaled77_3_28Norm.property,boundaryFullPowerScaled77_4_28Norm.property,boundaryFullPowerScaled77_5_28Norm.property,boundaryFullPowerScaled77_6_28Norm.property,boundaryFullPowerScaled77_7_28Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_28Norm,boundaryFullPowerScaled77_1_28Norm,boundaryFullPowerScaled77_2_28Norm,boundaryFullPowerScaled77_3_28Norm,boundaryFullPowerScaled77_4_28Norm,boundaryFullPowerScaled77_5_28Norm,boundaryFullPowerScaled77_6_28Norm,boundaryFullPowerScaled77_7_28Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_28Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_28Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_28Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_28Chunk8=boundaryPowerBernstein77_12_28Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_28Chunk8]

    rw [boundaryFullPowerScaled77_8_28Norm.property,boundaryFullPowerScaled77_9_28Norm.property,boundaryFullPowerScaled77_10_28Norm.property,boundaryFullPowerScaled77_11_28Norm.property,boundaryFullPowerScaled77_12_28Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_28Norm,boundaryFullPowerScaled77_9_28Norm,boundaryFullPowerScaled77_10_28Norm,boundaryFullPowerScaled77_11_28Norm,boundaryFullPowerScaled77_12_28Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_28Norm : {c : ℝ // boundaryFullCoefficient77 12 28=c} := by

  have he : boundaryFullCoefficient77 12 28=((boundaryPowerBernstein77_12_28Chunk0) + (boundaryPowerBernstein77_12_28Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_28Chunk0,boundaryPowerBernstein77_12_28Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_28Chunk0Norm.property,boundaryPowerBernstein77_12_28Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_28Chunk0Norm,boundaryPowerBernstein77_12_28Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_29Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_29Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_29Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_29Chunk0=boundaryPowerBernstein77_12_29Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_29Chunk0]

    rw [boundaryFullPowerScaled77_0_29Norm.property,boundaryFullPowerScaled77_1_29Norm.property,boundaryFullPowerScaled77_2_29Norm.property,boundaryFullPowerScaled77_3_29Norm.property,boundaryFullPowerScaled77_4_29Norm.property,boundaryFullPowerScaled77_5_29Norm.property,boundaryFullPowerScaled77_6_29Norm.property,boundaryFullPowerScaled77_7_29Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_29Norm,boundaryFullPowerScaled77_1_29Norm,boundaryFullPowerScaled77_2_29Norm,boundaryFullPowerScaled77_3_29Norm,boundaryFullPowerScaled77_4_29Norm,boundaryFullPowerScaled77_5_29Norm,boundaryFullPowerScaled77_6_29Norm,boundaryFullPowerScaled77_7_29Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_29Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_29Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_29Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_29Chunk8=boundaryPowerBernstein77_12_29Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_29Chunk8]

    rw [boundaryFullPowerScaled77_8_29Norm.property,boundaryFullPowerScaled77_9_29Norm.property,boundaryFullPowerScaled77_10_29Norm.property,boundaryFullPowerScaled77_11_29Norm.property,boundaryFullPowerScaled77_12_29Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_29Norm,boundaryFullPowerScaled77_9_29Norm,boundaryFullPowerScaled77_10_29Norm,boundaryFullPowerScaled77_11_29Norm,boundaryFullPowerScaled77_12_29Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_29Norm : {c : ℝ // boundaryFullCoefficient77 12 29=c} := by

  have he : boundaryFullCoefficient77 12 29=((boundaryPowerBernstein77_12_29Chunk0) + (boundaryPowerBernstein77_12_29Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_29Chunk0,boundaryPowerBernstein77_12_29Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_29Chunk0Norm.property,boundaryPowerBernstein77_12_29Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_29Chunk0Norm,boundaryPowerBernstein77_12_29Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_30Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_30Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_30Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_30Chunk0=boundaryPowerBernstein77_12_30Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_30Chunk0]

    rw [boundaryFullPowerScaled77_0_30Norm.property,boundaryFullPowerScaled77_1_30Norm.property,boundaryFullPowerScaled77_2_30Norm.property,boundaryFullPowerScaled77_3_30Norm.property,boundaryFullPowerScaled77_4_30Norm.property,boundaryFullPowerScaled77_5_30Norm.property,boundaryFullPowerScaled77_6_30Norm.property,boundaryFullPowerScaled77_7_30Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_30Norm,boundaryFullPowerScaled77_1_30Norm,boundaryFullPowerScaled77_2_30Norm,boundaryFullPowerScaled77_3_30Norm,boundaryFullPowerScaled77_4_30Norm,boundaryFullPowerScaled77_5_30Norm,boundaryFullPowerScaled77_6_30Norm,boundaryFullPowerScaled77_7_30Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_30Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_30Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_30Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_30Chunk8=boundaryPowerBernstein77_12_30Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_30Chunk8]

    rw [boundaryFullPowerScaled77_8_30Norm.property,boundaryFullPowerScaled77_9_30Norm.property,boundaryFullPowerScaled77_10_30Norm.property,boundaryFullPowerScaled77_11_30Norm.property,boundaryFullPowerScaled77_12_30Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_30Norm,boundaryFullPowerScaled77_9_30Norm,boundaryFullPowerScaled77_10_30Norm,boundaryFullPowerScaled77_11_30Norm,boundaryFullPowerScaled77_12_30Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_30Norm : {c : ℝ // boundaryFullCoefficient77 12 30=c} := by

  have he : boundaryFullCoefficient77 12 30=((boundaryPowerBernstein77_12_30Chunk0) + (boundaryPowerBernstein77_12_30Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_30Chunk0,boundaryPowerBernstein77_12_30Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_30Chunk0Norm.property,boundaryPowerBernstein77_12_30Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_30Chunk0Norm,boundaryPowerBernstein77_12_30Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_31Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_31Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_31Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_31Chunk0=boundaryPowerBernstein77_12_31Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_31Chunk0]

    rw [boundaryFullPowerScaled77_0_31Norm.property,boundaryFullPowerScaled77_1_31Norm.property,boundaryFullPowerScaled77_2_31Norm.property,boundaryFullPowerScaled77_3_31Norm.property,boundaryFullPowerScaled77_4_31Norm.property,boundaryFullPowerScaled77_5_31Norm.property,boundaryFullPowerScaled77_6_31Norm.property,boundaryFullPowerScaled77_7_31Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_31Norm,boundaryFullPowerScaled77_1_31Norm,boundaryFullPowerScaled77_2_31Norm,boundaryFullPowerScaled77_3_31Norm,boundaryFullPowerScaled77_4_31Norm,boundaryFullPowerScaled77_5_31Norm,boundaryFullPowerScaled77_6_31Norm,boundaryFullPowerScaled77_7_31Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_31Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_31Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_31Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_31Chunk8=boundaryPowerBernstein77_12_31Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_31Chunk8]

    rw [boundaryFullPowerScaled77_8_31Norm.property,boundaryFullPowerScaled77_9_31Norm.property,boundaryFullPowerScaled77_10_31Norm.property,boundaryFullPowerScaled77_11_31Norm.property,boundaryFullPowerScaled77_12_31Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_31Norm,boundaryFullPowerScaled77_9_31Norm,boundaryFullPowerScaled77_10_31Norm,boundaryFullPowerScaled77_11_31Norm,boundaryFullPowerScaled77_12_31Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_31Norm : {c : ℝ // boundaryFullCoefficient77 12 31=c} := by

  have he : boundaryFullCoefficient77 12 31=((boundaryPowerBernstein77_12_31Chunk0) + (boundaryPowerBernstein77_12_31Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_31Chunk0,boundaryPowerBernstein77_12_31Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_31Chunk0Norm.property,boundaryPowerBernstein77_12_31Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_31Chunk0Norm,boundaryPowerBernstein77_12_31Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_32Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_32Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_32Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_32Chunk0=boundaryPowerBernstein77_12_32Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_32Chunk0]

    rw [boundaryFullPowerScaled77_0_32Norm.property,boundaryFullPowerScaled77_1_32Norm.property,boundaryFullPowerScaled77_2_32Norm.property,boundaryFullPowerScaled77_3_32Norm.property,boundaryFullPowerScaled77_4_32Norm.property,boundaryFullPowerScaled77_5_32Norm.property,boundaryFullPowerScaled77_6_32Norm.property,boundaryFullPowerScaled77_7_32Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_32Norm,boundaryFullPowerScaled77_1_32Norm,boundaryFullPowerScaled77_2_32Norm,boundaryFullPowerScaled77_3_32Norm,boundaryFullPowerScaled77_4_32Norm,boundaryFullPowerScaled77_5_32Norm,boundaryFullPowerScaled77_6_32Norm,boundaryFullPowerScaled77_7_32Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_32Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_32Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_32Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_32Chunk8=boundaryPowerBernstein77_12_32Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_32Chunk8]

    rw [boundaryFullPowerScaled77_8_32Norm.property,boundaryFullPowerScaled77_9_32Norm.property,boundaryFullPowerScaled77_10_32Norm.property,boundaryFullPowerScaled77_11_32Norm.property,boundaryFullPowerScaled77_12_32Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_32Norm,boundaryFullPowerScaled77_9_32Norm,boundaryFullPowerScaled77_10_32Norm,boundaryFullPowerScaled77_11_32Norm,boundaryFullPowerScaled77_12_32Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_32Norm : {c : ℝ // boundaryFullCoefficient77 12 32=c} := by

  have he : boundaryFullCoefficient77 12 32=((boundaryPowerBernstein77_12_32Chunk0) + (boundaryPowerBernstein77_12_32Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_32Chunk0,boundaryPowerBernstein77_12_32Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_32Chunk0Norm.property,boundaryPowerBernstein77_12_32Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_32Chunk0Norm,boundaryPowerBernstein77_12_32Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_33Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_33Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_33Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_33Chunk0=boundaryPowerBernstein77_12_33Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_33Chunk0]

    rw [boundaryFullPowerScaled77_0_33Norm.property,boundaryFullPowerScaled77_1_33Norm.property,boundaryFullPowerScaled77_2_33Norm.property,boundaryFullPowerScaled77_3_33Norm.property,boundaryFullPowerScaled77_4_33Norm.property,boundaryFullPowerScaled77_5_33Norm.property,boundaryFullPowerScaled77_6_33Norm.property,boundaryFullPowerScaled77_7_33Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_33Norm,boundaryFullPowerScaled77_1_33Norm,boundaryFullPowerScaled77_2_33Norm,boundaryFullPowerScaled77_3_33Norm,boundaryFullPowerScaled77_4_33Norm,boundaryFullPowerScaled77_5_33Norm,boundaryFullPowerScaled77_6_33Norm,boundaryFullPowerScaled77_7_33Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_33Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_33Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_33Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_33Chunk8=boundaryPowerBernstein77_12_33Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_33Chunk8]

    rw [boundaryFullPowerScaled77_8_33Norm.property,boundaryFullPowerScaled77_9_33Norm.property,boundaryFullPowerScaled77_10_33Norm.property,boundaryFullPowerScaled77_11_33Norm.property,boundaryFullPowerScaled77_12_33Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_33Norm,boundaryFullPowerScaled77_9_33Norm,boundaryFullPowerScaled77_10_33Norm,boundaryFullPowerScaled77_11_33Norm,boundaryFullPowerScaled77_12_33Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_33Norm : {c : ℝ // boundaryFullCoefficient77 12 33=c} := by

  have he : boundaryFullCoefficient77 12 33=((boundaryPowerBernstein77_12_33Chunk0) + (boundaryPowerBernstein77_12_33Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_33Chunk0,boundaryPowerBernstein77_12_33Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_33Chunk0Norm.property,boundaryPowerBernstein77_12_33Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_33Chunk0Norm,boundaryPowerBernstein77_12_33Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_34Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_34Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_34Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_34Chunk0=boundaryPowerBernstein77_12_34Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_34Chunk0]

    rw [boundaryFullPowerScaled77_0_34Norm.property,boundaryFullPowerScaled77_1_34Norm.property,boundaryFullPowerScaled77_2_34Norm.property,boundaryFullPowerScaled77_3_34Norm.property,boundaryFullPowerScaled77_4_34Norm.property,boundaryFullPowerScaled77_5_34Norm.property,boundaryFullPowerScaled77_6_34Norm.property,boundaryFullPowerScaled77_7_34Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_34Norm,boundaryFullPowerScaled77_1_34Norm,boundaryFullPowerScaled77_2_34Norm,boundaryFullPowerScaled77_3_34Norm,boundaryFullPowerScaled77_4_34Norm,boundaryFullPowerScaled77_5_34Norm,boundaryFullPowerScaled77_6_34Norm,boundaryFullPowerScaled77_7_34Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_34Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_34Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_34Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_34Chunk8=boundaryPowerBernstein77_12_34Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_34Chunk8]

    rw [boundaryFullPowerScaled77_8_34Norm.property,boundaryFullPowerScaled77_9_34Norm.property,boundaryFullPowerScaled77_10_34Norm.property,boundaryFullPowerScaled77_11_34Norm.property,boundaryFullPowerScaled77_12_34Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_34Norm,boundaryFullPowerScaled77_9_34Norm,boundaryFullPowerScaled77_10_34Norm,boundaryFullPowerScaled77_11_34Norm,boundaryFullPowerScaled77_12_34Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_34Norm : {c : ℝ // boundaryFullCoefficient77 12 34=c} := by

  have he : boundaryFullCoefficient77 12 34=((boundaryPowerBernstein77_12_34Chunk0) + (boundaryPowerBernstein77_12_34Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_34Chunk0,boundaryPowerBernstein77_12_34Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_34Chunk0Norm.property,boundaryPowerBernstein77_12_34Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_34Chunk0Norm,boundaryPowerBernstein77_12_34Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_35Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_35Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_35Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_35Chunk0=boundaryPowerBernstein77_12_35Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_35Chunk0]

    rw [boundaryFullPowerScaled77_0_35Norm.property,boundaryFullPowerScaled77_1_35Norm.property,boundaryFullPowerScaled77_2_35Norm.property,boundaryFullPowerScaled77_3_35Norm.property,boundaryFullPowerScaled77_4_35Norm.property,boundaryFullPowerScaled77_5_35Norm.property,boundaryFullPowerScaled77_6_35Norm.property,boundaryFullPowerScaled77_7_35Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_35Norm,boundaryFullPowerScaled77_1_35Norm,boundaryFullPowerScaled77_2_35Norm,boundaryFullPowerScaled77_3_35Norm,boundaryFullPowerScaled77_4_35Norm,boundaryFullPowerScaled77_5_35Norm,boundaryFullPowerScaled77_6_35Norm,boundaryFullPowerScaled77_7_35Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_35Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_35Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_35Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_35Chunk8=boundaryPowerBernstein77_12_35Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_35Chunk8]

    rw [boundaryFullPowerScaled77_8_35Norm.property,boundaryFullPowerScaled77_9_35Norm.property,boundaryFullPowerScaled77_10_35Norm.property,boundaryFullPowerScaled77_11_35Norm.property,boundaryFullPowerScaled77_12_35Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_35Norm,boundaryFullPowerScaled77_9_35Norm,boundaryFullPowerScaled77_10_35Norm,boundaryFullPowerScaled77_11_35Norm,boundaryFullPowerScaled77_12_35Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_35Norm : {c : ℝ // boundaryFullCoefficient77 12 35=c} := by

  have he : boundaryFullCoefficient77 12 35=((boundaryPowerBernstein77_12_35Chunk0) + (boundaryPowerBernstein77_12_35Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_35Chunk0,boundaryPowerBernstein77_12_35Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_35Chunk0Norm.property,boundaryPowerBernstein77_12_35Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_35Chunk0Norm,boundaryPowerBernstein77_12_35Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_12_36Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 0 12) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 1 12)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 2 12) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 3 12))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 4 12) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 5 12)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 6 12) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 7 12))))

def boundaryPowerBernstein77_12_36Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_12_36Chunk0=c} := by

  have he : boundaryPowerBernstein77_12_36Chunk0=boundaryPowerBernstein77_12_36Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_36Chunk0]

    rw [boundaryFullPowerScaled77_0_36Norm.property,boundaryFullPowerScaled77_1_36Norm.property,boundaryFullPowerScaled77_2_36Norm.property,boundaryFullPowerScaled77_3_36Norm.property,boundaryFullPowerScaled77_4_36Norm.property,boundaryFullPowerScaled77_5_36Norm.property,boundaryFullPowerScaled77_6_36Norm.property,boundaryFullPowerScaled77_7_36Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_36Norm,boundaryFullPowerScaled77_1_36Norm,boundaryFullPowerScaled77_2_36Norm,boundaryFullPowerScaled77_3_36Norm,boundaryFullPowerScaled77_4_36Norm,boundaryFullPowerScaled77_5_36Norm,boundaryFullPowerScaled77_6_36Norm,boundaryFullPowerScaled77_7_36Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_36Chunk8 : ℝ :=
  (((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 8 12) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 9 12)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 10 12) + ((boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 11 12) + (boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 12 12))))

def boundaryPowerBernstein77_12_36Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_12_36Chunk8=c} := by

  have he : boundaryPowerBernstein77_12_36Chunk8=boundaryPowerBernstein77_12_36Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_12_36Chunk8]

    rw [boundaryFullPowerScaled77_8_36Norm.property,boundaryFullPowerScaled77_9_36Norm.property,boundaryFullPowerScaled77_10_36Norm.property,boundaryFullPowerScaled77_11_36Norm.property,boundaryFullPowerScaled77_12_36Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_36Norm,boundaryFullPowerScaled77_9_36Norm,boundaryFullPowerScaled77_10_36Norm,boundaryFullPowerScaled77_11_36Norm,boundaryFullPowerScaled77_12_36Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_12_36Norm : {c : ℝ // boundaryFullCoefficient77 12 36=c} := by

  have he : boundaryFullCoefficient77 12 36=((boundaryPowerBernstein77_12_36Chunk0) + (boundaryPowerBernstein77_12_36Chunk8)) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 12 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_12_36Chunk0,boundaryPowerBernstein77_12_36Chunk8]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_12_36Chunk0Norm.property,boundaryPowerBernstein77_12_36Chunk8Norm.property]

    dsimp only [boundaryPowerBernstein77_12_36Chunk0Norm,boundaryPowerBernstein77_12_36Chunk8Norm]

    norm_num

  exact ⟨_,he⟩




end

end HTGeometry.ThetaRatioInfinity
