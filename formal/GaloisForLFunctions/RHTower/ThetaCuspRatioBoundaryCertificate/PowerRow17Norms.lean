import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree0Scaled

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree10Scaled

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree11Scaled

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree12Scaled

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree13Scaled

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree14Scaled

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree15Scaled

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree16Scaled

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree17Scaled

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

def boundaryPowerBernstein77_17_0Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_0Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_0Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_0Chunk0=boundaryPowerBernstein77_17_0Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_0Chunk0]

    rw [boundaryFullPowerScaled77_0_0Norm.property,boundaryFullPowerScaled77_1_0Norm.property,boundaryFullPowerScaled77_2_0Norm.property,boundaryFullPowerScaled77_3_0Norm.property,boundaryFullPowerScaled77_4_0Norm.property,boundaryFullPowerScaled77_5_0Norm.property,boundaryFullPowerScaled77_6_0Norm.property,boundaryFullPowerScaled77_7_0Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_0Norm,boundaryFullPowerScaled77_1_0Norm,boundaryFullPowerScaled77_2_0Norm,boundaryFullPowerScaled77_3_0Norm,boundaryFullPowerScaled77_4_0Norm,boundaryFullPowerScaled77_5_0Norm,boundaryFullPowerScaled77_6_0Norm,boundaryFullPowerScaled77_7_0Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_0Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_0Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_0Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_0Chunk8=boundaryPowerBernstein77_17_0Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_0Chunk8]

    rw [boundaryFullPowerScaled77_8_0Norm.property,boundaryFullPowerScaled77_9_0Norm.property,boundaryFullPowerScaled77_10_0Norm.property,boundaryFullPowerScaled77_11_0Norm.property,boundaryFullPowerScaled77_12_0Norm.property,boundaryFullPowerScaled77_13_0Norm.property,boundaryFullPowerScaled77_14_0Norm.property,boundaryFullPowerScaled77_15_0Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_0Norm,boundaryFullPowerScaled77_9_0Norm,boundaryFullPowerScaled77_10_0Norm,boundaryFullPowerScaled77_11_0Norm,boundaryFullPowerScaled77_12_0Norm,boundaryFullPowerScaled77_13_0Norm,boundaryFullPowerScaled77_14_0Norm,boundaryFullPowerScaled77_15_0Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_0Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 0)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_0Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_0Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_0Chunk16=boundaryPowerBernstein77_17_0Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_0Chunk16]

    rw [boundaryFullPowerScaled77_16_0Norm.property,boundaryFullPowerScaled77_17_0Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_0Norm,boundaryFullPowerScaled77_17_0Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_0Norm : {c : ℝ // boundaryFullCoefficient77 17 0=c} := by

  have he : boundaryFullCoefficient77 17 0=((boundaryPowerBernstein77_17_0Chunk0) + ((boundaryPowerBernstein77_17_0Chunk8) + (boundaryPowerBernstein77_17_0Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_0Chunk0,boundaryPowerBernstein77_17_0Chunk8,boundaryPowerBernstein77_17_0Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_0Chunk0Norm.property,boundaryPowerBernstein77_17_0Chunk8Norm.property,boundaryPowerBernstein77_17_0Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_0Chunk0Norm,boundaryPowerBernstein77_17_0Chunk8Norm,boundaryPowerBernstein77_17_0Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_1Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_1Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_1Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_1Chunk0=boundaryPowerBernstein77_17_1Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_1Chunk0]

    rw [boundaryFullPowerScaled77_0_1Norm.property,boundaryFullPowerScaled77_1_1Norm.property,boundaryFullPowerScaled77_2_1Norm.property,boundaryFullPowerScaled77_3_1Norm.property,boundaryFullPowerScaled77_4_1Norm.property,boundaryFullPowerScaled77_5_1Norm.property,boundaryFullPowerScaled77_6_1Norm.property,boundaryFullPowerScaled77_7_1Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_1Norm,boundaryFullPowerScaled77_1_1Norm,boundaryFullPowerScaled77_2_1Norm,boundaryFullPowerScaled77_3_1Norm,boundaryFullPowerScaled77_4_1Norm,boundaryFullPowerScaled77_5_1Norm,boundaryFullPowerScaled77_6_1Norm,boundaryFullPowerScaled77_7_1Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_1Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_1Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_1Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_1Chunk8=boundaryPowerBernstein77_17_1Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_1Chunk8]

    rw [boundaryFullPowerScaled77_8_1Norm.property,boundaryFullPowerScaled77_9_1Norm.property,boundaryFullPowerScaled77_10_1Norm.property,boundaryFullPowerScaled77_11_1Norm.property,boundaryFullPowerScaled77_12_1Norm.property,boundaryFullPowerScaled77_13_1Norm.property,boundaryFullPowerScaled77_14_1Norm.property,boundaryFullPowerScaled77_15_1Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_1Norm,boundaryFullPowerScaled77_9_1Norm,boundaryFullPowerScaled77_10_1Norm,boundaryFullPowerScaled77_11_1Norm,boundaryFullPowerScaled77_12_1Norm,boundaryFullPowerScaled77_13_1Norm,boundaryFullPowerScaled77_14_1Norm,boundaryFullPowerScaled77_15_1Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_1Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 1)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_1Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_1Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_1Chunk16=boundaryPowerBernstein77_17_1Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_1Chunk16]

    rw [boundaryFullPowerScaled77_16_1Norm.property,boundaryFullPowerScaled77_17_1Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_1Norm,boundaryFullPowerScaled77_17_1Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_1Norm : {c : ℝ // boundaryFullCoefficient77 17 1=c} := by

  have he : boundaryFullCoefficient77 17 1=((boundaryPowerBernstein77_17_1Chunk0) + ((boundaryPowerBernstein77_17_1Chunk8) + (boundaryPowerBernstein77_17_1Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_1Chunk0,boundaryPowerBernstein77_17_1Chunk8,boundaryPowerBernstein77_17_1Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_1Chunk0Norm.property,boundaryPowerBernstein77_17_1Chunk8Norm.property,boundaryPowerBernstein77_17_1Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_1Chunk0Norm,boundaryPowerBernstein77_17_1Chunk8Norm,boundaryPowerBernstein77_17_1Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_2Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_2Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_2Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_2Chunk0=boundaryPowerBernstein77_17_2Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_2Chunk0]

    rw [boundaryFullPowerScaled77_0_2Norm.property,boundaryFullPowerScaled77_1_2Norm.property,boundaryFullPowerScaled77_2_2Norm.property,boundaryFullPowerScaled77_3_2Norm.property,boundaryFullPowerScaled77_4_2Norm.property,boundaryFullPowerScaled77_5_2Norm.property,boundaryFullPowerScaled77_6_2Norm.property,boundaryFullPowerScaled77_7_2Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_2Norm,boundaryFullPowerScaled77_1_2Norm,boundaryFullPowerScaled77_2_2Norm,boundaryFullPowerScaled77_3_2Norm,boundaryFullPowerScaled77_4_2Norm,boundaryFullPowerScaled77_5_2Norm,boundaryFullPowerScaled77_6_2Norm,boundaryFullPowerScaled77_7_2Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_2Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_2Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_2Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_2Chunk8=boundaryPowerBernstein77_17_2Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_2Chunk8]

    rw [boundaryFullPowerScaled77_8_2Norm.property,boundaryFullPowerScaled77_9_2Norm.property,boundaryFullPowerScaled77_10_2Norm.property,boundaryFullPowerScaled77_11_2Norm.property,boundaryFullPowerScaled77_12_2Norm.property,boundaryFullPowerScaled77_13_2Norm.property,boundaryFullPowerScaled77_14_2Norm.property,boundaryFullPowerScaled77_15_2Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_2Norm,boundaryFullPowerScaled77_9_2Norm,boundaryFullPowerScaled77_10_2Norm,boundaryFullPowerScaled77_11_2Norm,boundaryFullPowerScaled77_12_2Norm,boundaryFullPowerScaled77_13_2Norm,boundaryFullPowerScaled77_14_2Norm,boundaryFullPowerScaled77_15_2Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_2Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 2)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_2Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_2Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_2Chunk16=boundaryPowerBernstein77_17_2Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_2Chunk16]

    rw [boundaryFullPowerScaled77_16_2Norm.property,boundaryFullPowerScaled77_17_2Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_2Norm,boundaryFullPowerScaled77_17_2Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_2Norm : {c : ℝ // boundaryFullCoefficient77 17 2=c} := by

  have he : boundaryFullCoefficient77 17 2=((boundaryPowerBernstein77_17_2Chunk0) + ((boundaryPowerBernstein77_17_2Chunk8) + (boundaryPowerBernstein77_17_2Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_2Chunk0,boundaryPowerBernstein77_17_2Chunk8,boundaryPowerBernstein77_17_2Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_2Chunk0Norm.property,boundaryPowerBernstein77_17_2Chunk8Norm.property,boundaryPowerBernstein77_17_2Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_2Chunk0Norm,boundaryPowerBernstein77_17_2Chunk8Norm,boundaryPowerBernstein77_17_2Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_3Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_3Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_3Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_3Chunk0=boundaryPowerBernstein77_17_3Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_3Chunk0]

    rw [boundaryFullPowerScaled77_0_3Norm.property,boundaryFullPowerScaled77_1_3Norm.property,boundaryFullPowerScaled77_2_3Norm.property,boundaryFullPowerScaled77_3_3Norm.property,boundaryFullPowerScaled77_4_3Norm.property,boundaryFullPowerScaled77_5_3Norm.property,boundaryFullPowerScaled77_6_3Norm.property,boundaryFullPowerScaled77_7_3Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_3Norm,boundaryFullPowerScaled77_1_3Norm,boundaryFullPowerScaled77_2_3Norm,boundaryFullPowerScaled77_3_3Norm,boundaryFullPowerScaled77_4_3Norm,boundaryFullPowerScaled77_5_3Norm,boundaryFullPowerScaled77_6_3Norm,boundaryFullPowerScaled77_7_3Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_3Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_3Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_3Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_3Chunk8=boundaryPowerBernstein77_17_3Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_3Chunk8]

    rw [boundaryFullPowerScaled77_8_3Norm.property,boundaryFullPowerScaled77_9_3Norm.property,boundaryFullPowerScaled77_10_3Norm.property,boundaryFullPowerScaled77_11_3Norm.property,boundaryFullPowerScaled77_12_3Norm.property,boundaryFullPowerScaled77_13_3Norm.property,boundaryFullPowerScaled77_14_3Norm.property,boundaryFullPowerScaled77_15_3Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_3Norm,boundaryFullPowerScaled77_9_3Norm,boundaryFullPowerScaled77_10_3Norm,boundaryFullPowerScaled77_11_3Norm,boundaryFullPowerScaled77_12_3Norm,boundaryFullPowerScaled77_13_3Norm,boundaryFullPowerScaled77_14_3Norm,boundaryFullPowerScaled77_15_3Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_3Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 3)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_3Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_3Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_3Chunk16=boundaryPowerBernstein77_17_3Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_3Chunk16]

    rw [boundaryFullPowerScaled77_16_3Norm.property,boundaryFullPowerScaled77_17_3Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_3Norm,boundaryFullPowerScaled77_17_3Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_3Norm : {c : ℝ // boundaryFullCoefficient77 17 3=c} := by

  have he : boundaryFullCoefficient77 17 3=((boundaryPowerBernstein77_17_3Chunk0) + ((boundaryPowerBernstein77_17_3Chunk8) + (boundaryPowerBernstein77_17_3Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_3Chunk0,boundaryPowerBernstein77_17_3Chunk8,boundaryPowerBernstein77_17_3Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_3Chunk0Norm.property,boundaryPowerBernstein77_17_3Chunk8Norm.property,boundaryPowerBernstein77_17_3Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_3Chunk0Norm,boundaryPowerBernstein77_17_3Chunk8Norm,boundaryPowerBernstein77_17_3Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_4Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_4Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_4Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_4Chunk0=boundaryPowerBernstein77_17_4Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_4Chunk0]

    rw [boundaryFullPowerScaled77_0_4Norm.property,boundaryFullPowerScaled77_1_4Norm.property,boundaryFullPowerScaled77_2_4Norm.property,boundaryFullPowerScaled77_3_4Norm.property,boundaryFullPowerScaled77_4_4Norm.property,boundaryFullPowerScaled77_5_4Norm.property,boundaryFullPowerScaled77_6_4Norm.property,boundaryFullPowerScaled77_7_4Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_4Norm,boundaryFullPowerScaled77_1_4Norm,boundaryFullPowerScaled77_2_4Norm,boundaryFullPowerScaled77_3_4Norm,boundaryFullPowerScaled77_4_4Norm,boundaryFullPowerScaled77_5_4Norm,boundaryFullPowerScaled77_6_4Norm,boundaryFullPowerScaled77_7_4Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_4Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_4Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_4Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_4Chunk8=boundaryPowerBernstein77_17_4Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_4Chunk8]

    rw [boundaryFullPowerScaled77_8_4Norm.property,boundaryFullPowerScaled77_9_4Norm.property,boundaryFullPowerScaled77_10_4Norm.property,boundaryFullPowerScaled77_11_4Norm.property,boundaryFullPowerScaled77_12_4Norm.property,boundaryFullPowerScaled77_13_4Norm.property,boundaryFullPowerScaled77_14_4Norm.property,boundaryFullPowerScaled77_15_4Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_4Norm,boundaryFullPowerScaled77_9_4Norm,boundaryFullPowerScaled77_10_4Norm,boundaryFullPowerScaled77_11_4Norm,boundaryFullPowerScaled77_12_4Norm,boundaryFullPowerScaled77_13_4Norm,boundaryFullPowerScaled77_14_4Norm,boundaryFullPowerScaled77_15_4Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_4Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 4)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_4Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_4Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_4Chunk16=boundaryPowerBernstein77_17_4Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_4Chunk16]

    rw [boundaryFullPowerScaled77_16_4Norm.property,boundaryFullPowerScaled77_17_4Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_4Norm,boundaryFullPowerScaled77_17_4Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_4Norm : {c : ℝ // boundaryFullCoefficient77 17 4=c} := by

  have he : boundaryFullCoefficient77 17 4=((boundaryPowerBernstein77_17_4Chunk0) + ((boundaryPowerBernstein77_17_4Chunk8) + (boundaryPowerBernstein77_17_4Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_4Chunk0,boundaryPowerBernstein77_17_4Chunk8,boundaryPowerBernstein77_17_4Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_4Chunk0Norm.property,boundaryPowerBernstein77_17_4Chunk8Norm.property,boundaryPowerBernstein77_17_4Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_4Chunk0Norm,boundaryPowerBernstein77_17_4Chunk8Norm,boundaryPowerBernstein77_17_4Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_5Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_5Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_5Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_5Chunk0=boundaryPowerBernstein77_17_5Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_5Chunk0]

    rw [boundaryFullPowerScaled77_0_5Norm.property,boundaryFullPowerScaled77_1_5Norm.property,boundaryFullPowerScaled77_2_5Norm.property,boundaryFullPowerScaled77_3_5Norm.property,boundaryFullPowerScaled77_4_5Norm.property,boundaryFullPowerScaled77_5_5Norm.property,boundaryFullPowerScaled77_6_5Norm.property,boundaryFullPowerScaled77_7_5Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_5Norm,boundaryFullPowerScaled77_1_5Norm,boundaryFullPowerScaled77_2_5Norm,boundaryFullPowerScaled77_3_5Norm,boundaryFullPowerScaled77_4_5Norm,boundaryFullPowerScaled77_5_5Norm,boundaryFullPowerScaled77_6_5Norm,boundaryFullPowerScaled77_7_5Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_5Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_5Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_5Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_5Chunk8=boundaryPowerBernstein77_17_5Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_5Chunk8]

    rw [boundaryFullPowerScaled77_8_5Norm.property,boundaryFullPowerScaled77_9_5Norm.property,boundaryFullPowerScaled77_10_5Norm.property,boundaryFullPowerScaled77_11_5Norm.property,boundaryFullPowerScaled77_12_5Norm.property,boundaryFullPowerScaled77_13_5Norm.property,boundaryFullPowerScaled77_14_5Norm.property,boundaryFullPowerScaled77_15_5Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_5Norm,boundaryFullPowerScaled77_9_5Norm,boundaryFullPowerScaled77_10_5Norm,boundaryFullPowerScaled77_11_5Norm,boundaryFullPowerScaled77_12_5Norm,boundaryFullPowerScaled77_13_5Norm,boundaryFullPowerScaled77_14_5Norm,boundaryFullPowerScaled77_15_5Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_5Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 5)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_5Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_5Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_5Chunk16=boundaryPowerBernstein77_17_5Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_5Chunk16]

    rw [boundaryFullPowerScaled77_16_5Norm.property,boundaryFullPowerScaled77_17_5Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_5Norm,boundaryFullPowerScaled77_17_5Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_5Norm : {c : ℝ // boundaryFullCoefficient77 17 5=c} := by

  have he : boundaryFullCoefficient77 17 5=((boundaryPowerBernstein77_17_5Chunk0) + ((boundaryPowerBernstein77_17_5Chunk8) + (boundaryPowerBernstein77_17_5Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_5Chunk0,boundaryPowerBernstein77_17_5Chunk8,boundaryPowerBernstein77_17_5Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_5Chunk0Norm.property,boundaryPowerBernstein77_17_5Chunk8Norm.property,boundaryPowerBernstein77_17_5Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_5Chunk0Norm,boundaryPowerBernstein77_17_5Chunk8Norm,boundaryPowerBernstein77_17_5Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_6Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_6Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_6Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_6Chunk0=boundaryPowerBernstein77_17_6Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_6Chunk0]

    rw [boundaryFullPowerScaled77_0_6Norm.property,boundaryFullPowerScaled77_1_6Norm.property,boundaryFullPowerScaled77_2_6Norm.property,boundaryFullPowerScaled77_3_6Norm.property,boundaryFullPowerScaled77_4_6Norm.property,boundaryFullPowerScaled77_5_6Norm.property,boundaryFullPowerScaled77_6_6Norm.property,boundaryFullPowerScaled77_7_6Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_6Norm,boundaryFullPowerScaled77_1_6Norm,boundaryFullPowerScaled77_2_6Norm,boundaryFullPowerScaled77_3_6Norm,boundaryFullPowerScaled77_4_6Norm,boundaryFullPowerScaled77_5_6Norm,boundaryFullPowerScaled77_6_6Norm,boundaryFullPowerScaled77_7_6Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_6Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_6Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_6Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_6Chunk8=boundaryPowerBernstein77_17_6Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_6Chunk8]

    rw [boundaryFullPowerScaled77_8_6Norm.property,boundaryFullPowerScaled77_9_6Norm.property,boundaryFullPowerScaled77_10_6Norm.property,boundaryFullPowerScaled77_11_6Norm.property,boundaryFullPowerScaled77_12_6Norm.property,boundaryFullPowerScaled77_13_6Norm.property,boundaryFullPowerScaled77_14_6Norm.property,boundaryFullPowerScaled77_15_6Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_6Norm,boundaryFullPowerScaled77_9_6Norm,boundaryFullPowerScaled77_10_6Norm,boundaryFullPowerScaled77_11_6Norm,boundaryFullPowerScaled77_12_6Norm,boundaryFullPowerScaled77_13_6Norm,boundaryFullPowerScaled77_14_6Norm,boundaryFullPowerScaled77_15_6Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_6Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 6)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_6Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_6Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_6Chunk16=boundaryPowerBernstein77_17_6Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_6Chunk16]

    rw [boundaryFullPowerScaled77_16_6Norm.property,boundaryFullPowerScaled77_17_6Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_6Norm,boundaryFullPowerScaled77_17_6Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_6Norm : {c : ℝ // boundaryFullCoefficient77 17 6=c} := by

  have he : boundaryFullCoefficient77 17 6=((boundaryPowerBernstein77_17_6Chunk0) + ((boundaryPowerBernstein77_17_6Chunk8) + (boundaryPowerBernstein77_17_6Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_6Chunk0,boundaryPowerBernstein77_17_6Chunk8,boundaryPowerBernstein77_17_6Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_6Chunk0Norm.property,boundaryPowerBernstein77_17_6Chunk8Norm.property,boundaryPowerBernstein77_17_6Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_6Chunk0Norm,boundaryPowerBernstein77_17_6Chunk8Norm,boundaryPowerBernstein77_17_6Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_7Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_7Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_7Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_7Chunk0=boundaryPowerBernstein77_17_7Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_7Chunk0]

    rw [boundaryFullPowerScaled77_0_7Norm.property,boundaryFullPowerScaled77_1_7Norm.property,boundaryFullPowerScaled77_2_7Norm.property,boundaryFullPowerScaled77_3_7Norm.property,boundaryFullPowerScaled77_4_7Norm.property,boundaryFullPowerScaled77_5_7Norm.property,boundaryFullPowerScaled77_6_7Norm.property,boundaryFullPowerScaled77_7_7Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_7Norm,boundaryFullPowerScaled77_1_7Norm,boundaryFullPowerScaled77_2_7Norm,boundaryFullPowerScaled77_3_7Norm,boundaryFullPowerScaled77_4_7Norm,boundaryFullPowerScaled77_5_7Norm,boundaryFullPowerScaled77_6_7Norm,boundaryFullPowerScaled77_7_7Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_7Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_7Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_7Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_7Chunk8=boundaryPowerBernstein77_17_7Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_7Chunk8]

    rw [boundaryFullPowerScaled77_8_7Norm.property,boundaryFullPowerScaled77_9_7Norm.property,boundaryFullPowerScaled77_10_7Norm.property,boundaryFullPowerScaled77_11_7Norm.property,boundaryFullPowerScaled77_12_7Norm.property,boundaryFullPowerScaled77_13_7Norm.property,boundaryFullPowerScaled77_14_7Norm.property,boundaryFullPowerScaled77_15_7Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_7Norm,boundaryFullPowerScaled77_9_7Norm,boundaryFullPowerScaled77_10_7Norm,boundaryFullPowerScaled77_11_7Norm,boundaryFullPowerScaled77_12_7Norm,boundaryFullPowerScaled77_13_7Norm,boundaryFullPowerScaled77_14_7Norm,boundaryFullPowerScaled77_15_7Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_7Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 7)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_7Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_7Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_7Chunk16=boundaryPowerBernstein77_17_7Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_7Chunk16]

    rw [boundaryFullPowerScaled77_16_7Norm.property,boundaryFullPowerScaled77_17_7Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_7Norm,boundaryFullPowerScaled77_17_7Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_7Norm : {c : ℝ // boundaryFullCoefficient77 17 7=c} := by

  have he : boundaryFullCoefficient77 17 7=((boundaryPowerBernstein77_17_7Chunk0) + ((boundaryPowerBernstein77_17_7Chunk8) + (boundaryPowerBernstein77_17_7Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_7Chunk0,boundaryPowerBernstein77_17_7Chunk8,boundaryPowerBernstein77_17_7Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_7Chunk0Norm.property,boundaryPowerBernstein77_17_7Chunk8Norm.property,boundaryPowerBernstein77_17_7Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_7Chunk0Norm,boundaryPowerBernstein77_17_7Chunk8Norm,boundaryPowerBernstein77_17_7Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_8Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_8Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_8Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_8Chunk0=boundaryPowerBernstein77_17_8Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_8Chunk0]

    rw [boundaryFullPowerScaled77_0_8Norm.property,boundaryFullPowerScaled77_1_8Norm.property,boundaryFullPowerScaled77_2_8Norm.property,boundaryFullPowerScaled77_3_8Norm.property,boundaryFullPowerScaled77_4_8Norm.property,boundaryFullPowerScaled77_5_8Norm.property,boundaryFullPowerScaled77_6_8Norm.property,boundaryFullPowerScaled77_7_8Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_8Norm,boundaryFullPowerScaled77_1_8Norm,boundaryFullPowerScaled77_2_8Norm,boundaryFullPowerScaled77_3_8Norm,boundaryFullPowerScaled77_4_8Norm,boundaryFullPowerScaled77_5_8Norm,boundaryFullPowerScaled77_6_8Norm,boundaryFullPowerScaled77_7_8Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_8Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_8Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_8Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_8Chunk8=boundaryPowerBernstein77_17_8Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_8Chunk8]

    rw [boundaryFullPowerScaled77_8_8Norm.property,boundaryFullPowerScaled77_9_8Norm.property,boundaryFullPowerScaled77_10_8Norm.property,boundaryFullPowerScaled77_11_8Norm.property,boundaryFullPowerScaled77_12_8Norm.property,boundaryFullPowerScaled77_13_8Norm.property,boundaryFullPowerScaled77_14_8Norm.property,boundaryFullPowerScaled77_15_8Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_8Norm,boundaryFullPowerScaled77_9_8Norm,boundaryFullPowerScaled77_10_8Norm,boundaryFullPowerScaled77_11_8Norm,boundaryFullPowerScaled77_12_8Norm,boundaryFullPowerScaled77_13_8Norm,boundaryFullPowerScaled77_14_8Norm,boundaryFullPowerScaled77_15_8Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_8Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 8)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_8Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_8Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_8Chunk16=boundaryPowerBernstein77_17_8Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_8Chunk16]

    rw [boundaryFullPowerScaled77_16_8Norm.property,boundaryFullPowerScaled77_17_8Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_8Norm,boundaryFullPowerScaled77_17_8Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_8Norm : {c : ℝ // boundaryFullCoefficient77 17 8=c} := by

  have he : boundaryFullCoefficient77 17 8=((boundaryPowerBernstein77_17_8Chunk0) + ((boundaryPowerBernstein77_17_8Chunk8) + (boundaryPowerBernstein77_17_8Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_8Chunk0,boundaryPowerBernstein77_17_8Chunk8,boundaryPowerBernstein77_17_8Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_8Chunk0Norm.property,boundaryPowerBernstein77_17_8Chunk8Norm.property,boundaryPowerBernstein77_17_8Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_8Chunk0Norm,boundaryPowerBernstein77_17_8Chunk8Norm,boundaryPowerBernstein77_17_8Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_9Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_9Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_9Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_9Chunk0=boundaryPowerBernstein77_17_9Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_9Chunk0]

    rw [boundaryFullPowerScaled77_0_9Norm.property,boundaryFullPowerScaled77_1_9Norm.property,boundaryFullPowerScaled77_2_9Norm.property,boundaryFullPowerScaled77_3_9Norm.property,boundaryFullPowerScaled77_4_9Norm.property,boundaryFullPowerScaled77_5_9Norm.property,boundaryFullPowerScaled77_6_9Norm.property,boundaryFullPowerScaled77_7_9Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_9Norm,boundaryFullPowerScaled77_1_9Norm,boundaryFullPowerScaled77_2_9Norm,boundaryFullPowerScaled77_3_9Norm,boundaryFullPowerScaled77_4_9Norm,boundaryFullPowerScaled77_5_9Norm,boundaryFullPowerScaled77_6_9Norm,boundaryFullPowerScaled77_7_9Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_9Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_9Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_9Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_9Chunk8=boundaryPowerBernstein77_17_9Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_9Chunk8]

    rw [boundaryFullPowerScaled77_8_9Norm.property,boundaryFullPowerScaled77_9_9Norm.property,boundaryFullPowerScaled77_10_9Norm.property,boundaryFullPowerScaled77_11_9Norm.property,boundaryFullPowerScaled77_12_9Norm.property,boundaryFullPowerScaled77_13_9Norm.property,boundaryFullPowerScaled77_14_9Norm.property,boundaryFullPowerScaled77_15_9Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_9Norm,boundaryFullPowerScaled77_9_9Norm,boundaryFullPowerScaled77_10_9Norm,boundaryFullPowerScaled77_11_9Norm,boundaryFullPowerScaled77_12_9Norm,boundaryFullPowerScaled77_13_9Norm,boundaryFullPowerScaled77_14_9Norm,boundaryFullPowerScaled77_15_9Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_9Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 9)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_9Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_9Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_9Chunk16=boundaryPowerBernstein77_17_9Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_9Chunk16]

    rw [boundaryFullPowerScaled77_16_9Norm.property,boundaryFullPowerScaled77_17_9Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_9Norm,boundaryFullPowerScaled77_17_9Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_9Norm : {c : ℝ // boundaryFullCoefficient77 17 9=c} := by

  have he : boundaryFullCoefficient77 17 9=((boundaryPowerBernstein77_17_9Chunk0) + ((boundaryPowerBernstein77_17_9Chunk8) + (boundaryPowerBernstein77_17_9Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_9Chunk0,boundaryPowerBernstein77_17_9Chunk8,boundaryPowerBernstein77_17_9Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_9Chunk0Norm.property,boundaryPowerBernstein77_17_9Chunk8Norm.property,boundaryPowerBernstein77_17_9Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_9Chunk0Norm,boundaryPowerBernstein77_17_9Chunk8Norm,boundaryPowerBernstein77_17_9Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_10Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_10Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_10Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_10Chunk0=boundaryPowerBernstein77_17_10Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_10Chunk0]

    rw [boundaryFullPowerScaled77_0_10Norm.property,boundaryFullPowerScaled77_1_10Norm.property,boundaryFullPowerScaled77_2_10Norm.property,boundaryFullPowerScaled77_3_10Norm.property,boundaryFullPowerScaled77_4_10Norm.property,boundaryFullPowerScaled77_5_10Norm.property,boundaryFullPowerScaled77_6_10Norm.property,boundaryFullPowerScaled77_7_10Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_10Norm,boundaryFullPowerScaled77_1_10Norm,boundaryFullPowerScaled77_2_10Norm,boundaryFullPowerScaled77_3_10Norm,boundaryFullPowerScaled77_4_10Norm,boundaryFullPowerScaled77_5_10Norm,boundaryFullPowerScaled77_6_10Norm,boundaryFullPowerScaled77_7_10Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_10Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_10Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_10Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_10Chunk8=boundaryPowerBernstein77_17_10Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_10Chunk8]

    rw [boundaryFullPowerScaled77_8_10Norm.property,boundaryFullPowerScaled77_9_10Norm.property,boundaryFullPowerScaled77_10_10Norm.property,boundaryFullPowerScaled77_11_10Norm.property,boundaryFullPowerScaled77_12_10Norm.property,boundaryFullPowerScaled77_13_10Norm.property,boundaryFullPowerScaled77_14_10Norm.property,boundaryFullPowerScaled77_15_10Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_10Norm,boundaryFullPowerScaled77_9_10Norm,boundaryFullPowerScaled77_10_10Norm,boundaryFullPowerScaled77_11_10Norm,boundaryFullPowerScaled77_12_10Norm,boundaryFullPowerScaled77_13_10Norm,boundaryFullPowerScaled77_14_10Norm,boundaryFullPowerScaled77_15_10Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_10Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 10)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_10Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_10Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_10Chunk16=boundaryPowerBernstein77_17_10Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_10Chunk16]

    rw [boundaryFullPowerScaled77_16_10Norm.property,boundaryFullPowerScaled77_17_10Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_10Norm,boundaryFullPowerScaled77_17_10Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_10Norm : {c : ℝ // boundaryFullCoefficient77 17 10=c} := by

  have he : boundaryFullCoefficient77 17 10=((boundaryPowerBernstein77_17_10Chunk0) + ((boundaryPowerBernstein77_17_10Chunk8) + (boundaryPowerBernstein77_17_10Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_10Chunk0,boundaryPowerBernstein77_17_10Chunk8,boundaryPowerBernstein77_17_10Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_10Chunk0Norm.property,boundaryPowerBernstein77_17_10Chunk8Norm.property,boundaryPowerBernstein77_17_10Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_10Chunk0Norm,boundaryPowerBernstein77_17_10Chunk8Norm,boundaryPowerBernstein77_17_10Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_11Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_11Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_11Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_11Chunk0=boundaryPowerBernstein77_17_11Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_11Chunk0]

    rw [boundaryFullPowerScaled77_0_11Norm.property,boundaryFullPowerScaled77_1_11Norm.property,boundaryFullPowerScaled77_2_11Norm.property,boundaryFullPowerScaled77_3_11Norm.property,boundaryFullPowerScaled77_4_11Norm.property,boundaryFullPowerScaled77_5_11Norm.property,boundaryFullPowerScaled77_6_11Norm.property,boundaryFullPowerScaled77_7_11Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_11Norm,boundaryFullPowerScaled77_1_11Norm,boundaryFullPowerScaled77_2_11Norm,boundaryFullPowerScaled77_3_11Norm,boundaryFullPowerScaled77_4_11Norm,boundaryFullPowerScaled77_5_11Norm,boundaryFullPowerScaled77_6_11Norm,boundaryFullPowerScaled77_7_11Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_11Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_11Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_11Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_11Chunk8=boundaryPowerBernstein77_17_11Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_11Chunk8]

    rw [boundaryFullPowerScaled77_8_11Norm.property,boundaryFullPowerScaled77_9_11Norm.property,boundaryFullPowerScaled77_10_11Norm.property,boundaryFullPowerScaled77_11_11Norm.property,boundaryFullPowerScaled77_12_11Norm.property,boundaryFullPowerScaled77_13_11Norm.property,boundaryFullPowerScaled77_14_11Norm.property,boundaryFullPowerScaled77_15_11Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_11Norm,boundaryFullPowerScaled77_9_11Norm,boundaryFullPowerScaled77_10_11Norm,boundaryFullPowerScaled77_11_11Norm,boundaryFullPowerScaled77_12_11Norm,boundaryFullPowerScaled77_13_11Norm,boundaryFullPowerScaled77_14_11Norm,boundaryFullPowerScaled77_15_11Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_11Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 11)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_11Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_11Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_11Chunk16=boundaryPowerBernstein77_17_11Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_11Chunk16]

    rw [boundaryFullPowerScaled77_16_11Norm.property,boundaryFullPowerScaled77_17_11Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_11Norm,boundaryFullPowerScaled77_17_11Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_11Norm : {c : ℝ // boundaryFullCoefficient77 17 11=c} := by

  have he : boundaryFullCoefficient77 17 11=((boundaryPowerBernstein77_17_11Chunk0) + ((boundaryPowerBernstein77_17_11Chunk8) + (boundaryPowerBernstein77_17_11Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_11Chunk0,boundaryPowerBernstein77_17_11Chunk8,boundaryPowerBernstein77_17_11Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_11Chunk0Norm.property,boundaryPowerBernstein77_17_11Chunk8Norm.property,boundaryPowerBernstein77_17_11Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_11Chunk0Norm,boundaryPowerBernstein77_17_11Chunk8Norm,boundaryPowerBernstein77_17_11Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_12Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_12Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_12Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_12Chunk0=boundaryPowerBernstein77_17_12Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_12Chunk0]

    rw [boundaryFullPowerScaled77_0_12Norm.property,boundaryFullPowerScaled77_1_12Norm.property,boundaryFullPowerScaled77_2_12Norm.property,boundaryFullPowerScaled77_3_12Norm.property,boundaryFullPowerScaled77_4_12Norm.property,boundaryFullPowerScaled77_5_12Norm.property,boundaryFullPowerScaled77_6_12Norm.property,boundaryFullPowerScaled77_7_12Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_12Norm,boundaryFullPowerScaled77_1_12Norm,boundaryFullPowerScaled77_2_12Norm,boundaryFullPowerScaled77_3_12Norm,boundaryFullPowerScaled77_4_12Norm,boundaryFullPowerScaled77_5_12Norm,boundaryFullPowerScaled77_6_12Norm,boundaryFullPowerScaled77_7_12Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_12Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_12Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_12Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_12Chunk8=boundaryPowerBernstein77_17_12Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_12Chunk8]

    rw [boundaryFullPowerScaled77_8_12Norm.property,boundaryFullPowerScaled77_9_12Norm.property,boundaryFullPowerScaled77_10_12Norm.property,boundaryFullPowerScaled77_11_12Norm.property,boundaryFullPowerScaled77_12_12Norm.property,boundaryFullPowerScaled77_13_12Norm.property,boundaryFullPowerScaled77_14_12Norm.property,boundaryFullPowerScaled77_15_12Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_12Norm,boundaryFullPowerScaled77_9_12Norm,boundaryFullPowerScaled77_10_12Norm,boundaryFullPowerScaled77_11_12Norm,boundaryFullPowerScaled77_12_12Norm,boundaryFullPowerScaled77_13_12Norm,boundaryFullPowerScaled77_14_12Norm,boundaryFullPowerScaled77_15_12Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_12Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 12)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_12Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_12Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_12Chunk16=boundaryPowerBernstein77_17_12Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_12Chunk16]

    rw [boundaryFullPowerScaled77_16_12Norm.property,boundaryFullPowerScaled77_17_12Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_12Norm,boundaryFullPowerScaled77_17_12Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_12Norm : {c : ℝ // boundaryFullCoefficient77 17 12=c} := by

  have he : boundaryFullCoefficient77 17 12=((boundaryPowerBernstein77_17_12Chunk0) + ((boundaryPowerBernstein77_17_12Chunk8) + (boundaryPowerBernstein77_17_12Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_12Chunk0,boundaryPowerBernstein77_17_12Chunk8,boundaryPowerBernstein77_17_12Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_12Chunk0Norm.property,boundaryPowerBernstein77_17_12Chunk8Norm.property,boundaryPowerBernstein77_17_12Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_12Chunk0Norm,boundaryPowerBernstein77_17_12Chunk8Norm,boundaryPowerBernstein77_17_12Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_13Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_13Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_13Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_13Chunk0=boundaryPowerBernstein77_17_13Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_13Chunk0]

    rw [boundaryFullPowerScaled77_0_13Norm.property,boundaryFullPowerScaled77_1_13Norm.property,boundaryFullPowerScaled77_2_13Norm.property,boundaryFullPowerScaled77_3_13Norm.property,boundaryFullPowerScaled77_4_13Norm.property,boundaryFullPowerScaled77_5_13Norm.property,boundaryFullPowerScaled77_6_13Norm.property,boundaryFullPowerScaled77_7_13Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_13Norm,boundaryFullPowerScaled77_1_13Norm,boundaryFullPowerScaled77_2_13Norm,boundaryFullPowerScaled77_3_13Norm,boundaryFullPowerScaled77_4_13Norm,boundaryFullPowerScaled77_5_13Norm,boundaryFullPowerScaled77_6_13Norm,boundaryFullPowerScaled77_7_13Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_13Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_13Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_13Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_13Chunk8=boundaryPowerBernstein77_17_13Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_13Chunk8]

    rw [boundaryFullPowerScaled77_8_13Norm.property,boundaryFullPowerScaled77_9_13Norm.property,boundaryFullPowerScaled77_10_13Norm.property,boundaryFullPowerScaled77_11_13Norm.property,boundaryFullPowerScaled77_12_13Norm.property,boundaryFullPowerScaled77_13_13Norm.property,boundaryFullPowerScaled77_14_13Norm.property,boundaryFullPowerScaled77_15_13Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_13Norm,boundaryFullPowerScaled77_9_13Norm,boundaryFullPowerScaled77_10_13Norm,boundaryFullPowerScaled77_11_13Norm,boundaryFullPowerScaled77_12_13Norm,boundaryFullPowerScaled77_13_13Norm,boundaryFullPowerScaled77_14_13Norm,boundaryFullPowerScaled77_15_13Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_13Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 13)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_13Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_13Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_13Chunk16=boundaryPowerBernstein77_17_13Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_13Chunk16]

    rw [boundaryFullPowerScaled77_16_13Norm.property,boundaryFullPowerScaled77_17_13Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_13Norm,boundaryFullPowerScaled77_17_13Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_13Norm : {c : ℝ // boundaryFullCoefficient77 17 13=c} := by

  have he : boundaryFullCoefficient77 17 13=((boundaryPowerBernstein77_17_13Chunk0) + ((boundaryPowerBernstein77_17_13Chunk8) + (boundaryPowerBernstein77_17_13Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_13Chunk0,boundaryPowerBernstein77_17_13Chunk8,boundaryPowerBernstein77_17_13Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_13Chunk0Norm.property,boundaryPowerBernstein77_17_13Chunk8Norm.property,boundaryPowerBernstein77_17_13Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_13Chunk0Norm,boundaryPowerBernstein77_17_13Chunk8Norm,boundaryPowerBernstein77_17_13Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_14Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_14Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_14Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_14Chunk0=boundaryPowerBernstein77_17_14Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_14Chunk0]

    rw [boundaryFullPowerScaled77_0_14Norm.property,boundaryFullPowerScaled77_1_14Norm.property,boundaryFullPowerScaled77_2_14Norm.property,boundaryFullPowerScaled77_3_14Norm.property,boundaryFullPowerScaled77_4_14Norm.property,boundaryFullPowerScaled77_5_14Norm.property,boundaryFullPowerScaled77_6_14Norm.property,boundaryFullPowerScaled77_7_14Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_14Norm,boundaryFullPowerScaled77_1_14Norm,boundaryFullPowerScaled77_2_14Norm,boundaryFullPowerScaled77_3_14Norm,boundaryFullPowerScaled77_4_14Norm,boundaryFullPowerScaled77_5_14Norm,boundaryFullPowerScaled77_6_14Norm,boundaryFullPowerScaled77_7_14Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_14Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_14Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_14Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_14Chunk8=boundaryPowerBernstein77_17_14Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_14Chunk8]

    rw [boundaryFullPowerScaled77_8_14Norm.property,boundaryFullPowerScaled77_9_14Norm.property,boundaryFullPowerScaled77_10_14Norm.property,boundaryFullPowerScaled77_11_14Norm.property,boundaryFullPowerScaled77_12_14Norm.property,boundaryFullPowerScaled77_13_14Norm.property,boundaryFullPowerScaled77_14_14Norm.property,boundaryFullPowerScaled77_15_14Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_14Norm,boundaryFullPowerScaled77_9_14Norm,boundaryFullPowerScaled77_10_14Norm,boundaryFullPowerScaled77_11_14Norm,boundaryFullPowerScaled77_12_14Norm,boundaryFullPowerScaled77_13_14Norm,boundaryFullPowerScaled77_14_14Norm,boundaryFullPowerScaled77_15_14Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_14Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 14)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_14Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_14Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_14Chunk16=boundaryPowerBernstein77_17_14Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_14Chunk16]

    rw [boundaryFullPowerScaled77_16_14Norm.property,boundaryFullPowerScaled77_17_14Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_14Norm,boundaryFullPowerScaled77_17_14Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_14Norm : {c : ℝ // boundaryFullCoefficient77 17 14=c} := by

  have he : boundaryFullCoefficient77 17 14=((boundaryPowerBernstein77_17_14Chunk0) + ((boundaryPowerBernstein77_17_14Chunk8) + (boundaryPowerBernstein77_17_14Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_14Chunk0,boundaryPowerBernstein77_17_14Chunk8,boundaryPowerBernstein77_17_14Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_14Chunk0Norm.property,boundaryPowerBernstein77_17_14Chunk8Norm.property,boundaryPowerBernstein77_17_14Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_14Chunk0Norm,boundaryPowerBernstein77_17_14Chunk8Norm,boundaryPowerBernstein77_17_14Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_15Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_15Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_15Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_15Chunk0=boundaryPowerBernstein77_17_15Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_15Chunk0]

    rw [boundaryFullPowerScaled77_0_15Norm.property,boundaryFullPowerScaled77_1_15Norm.property,boundaryFullPowerScaled77_2_15Norm.property,boundaryFullPowerScaled77_3_15Norm.property,boundaryFullPowerScaled77_4_15Norm.property,boundaryFullPowerScaled77_5_15Norm.property,boundaryFullPowerScaled77_6_15Norm.property,boundaryFullPowerScaled77_7_15Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_15Norm,boundaryFullPowerScaled77_1_15Norm,boundaryFullPowerScaled77_2_15Norm,boundaryFullPowerScaled77_3_15Norm,boundaryFullPowerScaled77_4_15Norm,boundaryFullPowerScaled77_5_15Norm,boundaryFullPowerScaled77_6_15Norm,boundaryFullPowerScaled77_7_15Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_15Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_15Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_15Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_15Chunk8=boundaryPowerBernstein77_17_15Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_15Chunk8]

    rw [boundaryFullPowerScaled77_8_15Norm.property,boundaryFullPowerScaled77_9_15Norm.property,boundaryFullPowerScaled77_10_15Norm.property,boundaryFullPowerScaled77_11_15Norm.property,boundaryFullPowerScaled77_12_15Norm.property,boundaryFullPowerScaled77_13_15Norm.property,boundaryFullPowerScaled77_14_15Norm.property,boundaryFullPowerScaled77_15_15Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_15Norm,boundaryFullPowerScaled77_9_15Norm,boundaryFullPowerScaled77_10_15Norm,boundaryFullPowerScaled77_11_15Norm,boundaryFullPowerScaled77_12_15Norm,boundaryFullPowerScaled77_13_15Norm,boundaryFullPowerScaled77_14_15Norm,boundaryFullPowerScaled77_15_15Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_15Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 15)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_15Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_15Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_15Chunk16=boundaryPowerBernstein77_17_15Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_15Chunk16]

    rw [boundaryFullPowerScaled77_16_15Norm.property,boundaryFullPowerScaled77_17_15Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_15Norm,boundaryFullPowerScaled77_17_15Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_15Norm : {c : ℝ // boundaryFullCoefficient77 17 15=c} := by

  have he : boundaryFullCoefficient77 17 15=((boundaryPowerBernstein77_17_15Chunk0) + ((boundaryPowerBernstein77_17_15Chunk8) + (boundaryPowerBernstein77_17_15Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_15Chunk0,boundaryPowerBernstein77_17_15Chunk8,boundaryPowerBernstein77_17_15Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_15Chunk0Norm.property,boundaryPowerBernstein77_17_15Chunk8Norm.property,boundaryPowerBernstein77_17_15Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_15Chunk0Norm,boundaryPowerBernstein77_17_15Chunk8Norm,boundaryPowerBernstein77_17_15Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_16Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_16Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_16Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_16Chunk0=boundaryPowerBernstein77_17_16Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_16Chunk0]

    rw [boundaryFullPowerScaled77_0_16Norm.property,boundaryFullPowerScaled77_1_16Norm.property,boundaryFullPowerScaled77_2_16Norm.property,boundaryFullPowerScaled77_3_16Norm.property,boundaryFullPowerScaled77_4_16Norm.property,boundaryFullPowerScaled77_5_16Norm.property,boundaryFullPowerScaled77_6_16Norm.property,boundaryFullPowerScaled77_7_16Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_16Norm,boundaryFullPowerScaled77_1_16Norm,boundaryFullPowerScaled77_2_16Norm,boundaryFullPowerScaled77_3_16Norm,boundaryFullPowerScaled77_4_16Norm,boundaryFullPowerScaled77_5_16Norm,boundaryFullPowerScaled77_6_16Norm,boundaryFullPowerScaled77_7_16Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_16Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_16Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_16Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_16Chunk8=boundaryPowerBernstein77_17_16Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_16Chunk8]

    rw [boundaryFullPowerScaled77_8_16Norm.property,boundaryFullPowerScaled77_9_16Norm.property,boundaryFullPowerScaled77_10_16Norm.property,boundaryFullPowerScaled77_11_16Norm.property,boundaryFullPowerScaled77_12_16Norm.property,boundaryFullPowerScaled77_13_16Norm.property,boundaryFullPowerScaled77_14_16Norm.property,boundaryFullPowerScaled77_15_16Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_16Norm,boundaryFullPowerScaled77_9_16Norm,boundaryFullPowerScaled77_10_16Norm,boundaryFullPowerScaled77_11_16Norm,boundaryFullPowerScaled77_12_16Norm,boundaryFullPowerScaled77_13_16Norm,boundaryFullPowerScaled77_14_16Norm,boundaryFullPowerScaled77_15_16Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_16Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 16)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_16Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_16Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_16Chunk16=boundaryPowerBernstein77_17_16Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_16Chunk16]

    rw [boundaryFullPowerScaled77_16_16Norm.property,boundaryFullPowerScaled77_17_16Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_16Norm,boundaryFullPowerScaled77_17_16Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_16Norm : {c : ℝ // boundaryFullCoefficient77 17 16=c} := by

  have he : boundaryFullCoefficient77 17 16=((boundaryPowerBernstein77_17_16Chunk0) + ((boundaryPowerBernstein77_17_16Chunk8) + (boundaryPowerBernstein77_17_16Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_16Chunk0,boundaryPowerBernstein77_17_16Chunk8,boundaryPowerBernstein77_17_16Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_16Chunk0Norm.property,boundaryPowerBernstein77_17_16Chunk8Norm.property,boundaryPowerBernstein77_17_16Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_16Chunk0Norm,boundaryPowerBernstein77_17_16Chunk8Norm,boundaryPowerBernstein77_17_16Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_17Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_17Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_17Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_17Chunk0=boundaryPowerBernstein77_17_17Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_17Chunk0]

    rw [boundaryFullPowerScaled77_0_17Norm.property,boundaryFullPowerScaled77_1_17Norm.property,boundaryFullPowerScaled77_2_17Norm.property,boundaryFullPowerScaled77_3_17Norm.property,boundaryFullPowerScaled77_4_17Norm.property,boundaryFullPowerScaled77_5_17Norm.property,boundaryFullPowerScaled77_6_17Norm.property,boundaryFullPowerScaled77_7_17Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_17Norm,boundaryFullPowerScaled77_1_17Norm,boundaryFullPowerScaled77_2_17Norm,boundaryFullPowerScaled77_3_17Norm,boundaryFullPowerScaled77_4_17Norm,boundaryFullPowerScaled77_5_17Norm,boundaryFullPowerScaled77_6_17Norm,boundaryFullPowerScaled77_7_17Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_17Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_17Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_17Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_17Chunk8=boundaryPowerBernstein77_17_17Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_17Chunk8]

    rw [boundaryFullPowerScaled77_8_17Norm.property,boundaryFullPowerScaled77_9_17Norm.property,boundaryFullPowerScaled77_10_17Norm.property,boundaryFullPowerScaled77_11_17Norm.property,boundaryFullPowerScaled77_12_17Norm.property,boundaryFullPowerScaled77_13_17Norm.property,boundaryFullPowerScaled77_14_17Norm.property,boundaryFullPowerScaled77_15_17Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_17Norm,boundaryFullPowerScaled77_9_17Norm,boundaryFullPowerScaled77_10_17Norm,boundaryFullPowerScaled77_11_17Norm,boundaryFullPowerScaled77_12_17Norm,boundaryFullPowerScaled77_13_17Norm,boundaryFullPowerScaled77_14_17Norm,boundaryFullPowerScaled77_15_17Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_17Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 17)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_17Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_17Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_17Chunk16=boundaryPowerBernstein77_17_17Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_17Chunk16]

    rw [boundaryFullPowerScaled77_16_17Norm.property,boundaryFullPowerScaled77_17_17Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_17Norm,boundaryFullPowerScaled77_17_17Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_17Norm : {c : ℝ // boundaryFullCoefficient77 17 17=c} := by

  have he : boundaryFullCoefficient77 17 17=((boundaryPowerBernstein77_17_17Chunk0) + ((boundaryPowerBernstein77_17_17Chunk8) + (boundaryPowerBernstein77_17_17Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_17Chunk0,boundaryPowerBernstein77_17_17Chunk8,boundaryPowerBernstein77_17_17Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_17Chunk0Norm.property,boundaryPowerBernstein77_17_17Chunk8Norm.property,boundaryPowerBernstein77_17_17Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_17Chunk0Norm,boundaryPowerBernstein77_17_17Chunk8Norm,boundaryPowerBernstein77_17_17Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_18Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_18Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_18Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_18Chunk0=boundaryPowerBernstein77_17_18Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_18Chunk0]

    rw [boundaryFullPowerScaled77_0_18Norm.property,boundaryFullPowerScaled77_1_18Norm.property,boundaryFullPowerScaled77_2_18Norm.property,boundaryFullPowerScaled77_3_18Norm.property,boundaryFullPowerScaled77_4_18Norm.property,boundaryFullPowerScaled77_5_18Norm.property,boundaryFullPowerScaled77_6_18Norm.property,boundaryFullPowerScaled77_7_18Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_18Norm,boundaryFullPowerScaled77_1_18Norm,boundaryFullPowerScaled77_2_18Norm,boundaryFullPowerScaled77_3_18Norm,boundaryFullPowerScaled77_4_18Norm,boundaryFullPowerScaled77_5_18Norm,boundaryFullPowerScaled77_6_18Norm,boundaryFullPowerScaled77_7_18Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_18Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_18Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_18Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_18Chunk8=boundaryPowerBernstein77_17_18Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_18Chunk8]

    rw [boundaryFullPowerScaled77_8_18Norm.property,boundaryFullPowerScaled77_9_18Norm.property,boundaryFullPowerScaled77_10_18Norm.property,boundaryFullPowerScaled77_11_18Norm.property,boundaryFullPowerScaled77_12_18Norm.property,boundaryFullPowerScaled77_13_18Norm.property,boundaryFullPowerScaled77_14_18Norm.property,boundaryFullPowerScaled77_15_18Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_18Norm,boundaryFullPowerScaled77_9_18Norm,boundaryFullPowerScaled77_10_18Norm,boundaryFullPowerScaled77_11_18Norm,boundaryFullPowerScaled77_12_18Norm,boundaryFullPowerScaled77_13_18Norm,boundaryFullPowerScaled77_14_18Norm,boundaryFullPowerScaled77_15_18Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_18Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 18)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_18Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_18Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_18Chunk16=boundaryPowerBernstein77_17_18Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_18Chunk16]

    rw [boundaryFullPowerScaled77_16_18Norm.property,boundaryFullPowerScaled77_17_18Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_18Norm,boundaryFullPowerScaled77_17_18Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_18Norm : {c : ℝ // boundaryFullCoefficient77 17 18=c} := by

  have he : boundaryFullCoefficient77 17 18=((boundaryPowerBernstein77_17_18Chunk0) + ((boundaryPowerBernstein77_17_18Chunk8) + (boundaryPowerBernstein77_17_18Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_18Chunk0,boundaryPowerBernstein77_17_18Chunk8,boundaryPowerBernstein77_17_18Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_18Chunk0Norm.property,boundaryPowerBernstein77_17_18Chunk8Norm.property,boundaryPowerBernstein77_17_18Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_18Chunk0Norm,boundaryPowerBernstein77_17_18Chunk8Norm,boundaryPowerBernstein77_17_18Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_19Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_19Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_19Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_19Chunk0=boundaryPowerBernstein77_17_19Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_19Chunk0]

    rw [boundaryFullPowerScaled77_0_19Norm.property,boundaryFullPowerScaled77_1_19Norm.property,boundaryFullPowerScaled77_2_19Norm.property,boundaryFullPowerScaled77_3_19Norm.property,boundaryFullPowerScaled77_4_19Norm.property,boundaryFullPowerScaled77_5_19Norm.property,boundaryFullPowerScaled77_6_19Norm.property,boundaryFullPowerScaled77_7_19Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_19Norm,boundaryFullPowerScaled77_1_19Norm,boundaryFullPowerScaled77_2_19Norm,boundaryFullPowerScaled77_3_19Norm,boundaryFullPowerScaled77_4_19Norm,boundaryFullPowerScaled77_5_19Norm,boundaryFullPowerScaled77_6_19Norm,boundaryFullPowerScaled77_7_19Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_19Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_19Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_19Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_19Chunk8=boundaryPowerBernstein77_17_19Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_19Chunk8]

    rw [boundaryFullPowerScaled77_8_19Norm.property,boundaryFullPowerScaled77_9_19Norm.property,boundaryFullPowerScaled77_10_19Norm.property,boundaryFullPowerScaled77_11_19Norm.property,boundaryFullPowerScaled77_12_19Norm.property,boundaryFullPowerScaled77_13_19Norm.property,boundaryFullPowerScaled77_14_19Norm.property,boundaryFullPowerScaled77_15_19Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_19Norm,boundaryFullPowerScaled77_9_19Norm,boundaryFullPowerScaled77_10_19Norm,boundaryFullPowerScaled77_11_19Norm,boundaryFullPowerScaled77_12_19Norm,boundaryFullPowerScaled77_13_19Norm,boundaryFullPowerScaled77_14_19Norm,boundaryFullPowerScaled77_15_19Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_19Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 19)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_19Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_19Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_19Chunk16=boundaryPowerBernstein77_17_19Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_19Chunk16]

    rw [boundaryFullPowerScaled77_16_19Norm.property,boundaryFullPowerScaled77_17_19Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_19Norm,boundaryFullPowerScaled77_17_19Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_19Norm : {c : ℝ // boundaryFullCoefficient77 17 19=c} := by

  have he : boundaryFullCoefficient77 17 19=((boundaryPowerBernstein77_17_19Chunk0) + ((boundaryPowerBernstein77_17_19Chunk8) + (boundaryPowerBernstein77_17_19Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_19Chunk0,boundaryPowerBernstein77_17_19Chunk8,boundaryPowerBernstein77_17_19Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_19Chunk0Norm.property,boundaryPowerBernstein77_17_19Chunk8Norm.property,boundaryPowerBernstein77_17_19Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_19Chunk0Norm,boundaryPowerBernstein77_17_19Chunk8Norm,boundaryPowerBernstein77_17_19Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_20Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_20Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_20Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_20Chunk0=boundaryPowerBernstein77_17_20Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_20Chunk0]

    rw [boundaryFullPowerScaled77_0_20Norm.property,boundaryFullPowerScaled77_1_20Norm.property,boundaryFullPowerScaled77_2_20Norm.property,boundaryFullPowerScaled77_3_20Norm.property,boundaryFullPowerScaled77_4_20Norm.property,boundaryFullPowerScaled77_5_20Norm.property,boundaryFullPowerScaled77_6_20Norm.property,boundaryFullPowerScaled77_7_20Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_20Norm,boundaryFullPowerScaled77_1_20Norm,boundaryFullPowerScaled77_2_20Norm,boundaryFullPowerScaled77_3_20Norm,boundaryFullPowerScaled77_4_20Norm,boundaryFullPowerScaled77_5_20Norm,boundaryFullPowerScaled77_6_20Norm,boundaryFullPowerScaled77_7_20Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_20Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_20Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_20Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_20Chunk8=boundaryPowerBernstein77_17_20Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_20Chunk8]

    rw [boundaryFullPowerScaled77_8_20Norm.property,boundaryFullPowerScaled77_9_20Norm.property,boundaryFullPowerScaled77_10_20Norm.property,boundaryFullPowerScaled77_11_20Norm.property,boundaryFullPowerScaled77_12_20Norm.property,boundaryFullPowerScaled77_13_20Norm.property,boundaryFullPowerScaled77_14_20Norm.property,boundaryFullPowerScaled77_15_20Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_20Norm,boundaryFullPowerScaled77_9_20Norm,boundaryFullPowerScaled77_10_20Norm,boundaryFullPowerScaled77_11_20Norm,boundaryFullPowerScaled77_12_20Norm,boundaryFullPowerScaled77_13_20Norm,boundaryFullPowerScaled77_14_20Norm,boundaryFullPowerScaled77_15_20Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_20Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 20)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_20Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_20Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_20Chunk16=boundaryPowerBernstein77_17_20Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_20Chunk16]

    rw [boundaryFullPowerScaled77_16_20Norm.property,boundaryFullPowerScaled77_17_20Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_20Norm,boundaryFullPowerScaled77_17_20Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_20Norm : {c : ℝ // boundaryFullCoefficient77 17 20=c} := by

  have he : boundaryFullCoefficient77 17 20=((boundaryPowerBernstein77_17_20Chunk0) + ((boundaryPowerBernstein77_17_20Chunk8) + (boundaryPowerBernstein77_17_20Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_20Chunk0,boundaryPowerBernstein77_17_20Chunk8,boundaryPowerBernstein77_17_20Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_20Chunk0Norm.property,boundaryPowerBernstein77_17_20Chunk8Norm.property,boundaryPowerBernstein77_17_20Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_20Chunk0Norm,boundaryPowerBernstein77_17_20Chunk8Norm,boundaryPowerBernstein77_17_20Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_21Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_21Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_21Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_21Chunk0=boundaryPowerBernstein77_17_21Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_21Chunk0]

    rw [boundaryFullPowerScaled77_0_21Norm.property,boundaryFullPowerScaled77_1_21Norm.property,boundaryFullPowerScaled77_2_21Norm.property,boundaryFullPowerScaled77_3_21Norm.property,boundaryFullPowerScaled77_4_21Norm.property,boundaryFullPowerScaled77_5_21Norm.property,boundaryFullPowerScaled77_6_21Norm.property,boundaryFullPowerScaled77_7_21Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_21Norm,boundaryFullPowerScaled77_1_21Norm,boundaryFullPowerScaled77_2_21Norm,boundaryFullPowerScaled77_3_21Norm,boundaryFullPowerScaled77_4_21Norm,boundaryFullPowerScaled77_5_21Norm,boundaryFullPowerScaled77_6_21Norm,boundaryFullPowerScaled77_7_21Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_21Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_21Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_21Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_21Chunk8=boundaryPowerBernstein77_17_21Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_21Chunk8]

    rw [boundaryFullPowerScaled77_8_21Norm.property,boundaryFullPowerScaled77_9_21Norm.property,boundaryFullPowerScaled77_10_21Norm.property,boundaryFullPowerScaled77_11_21Norm.property,boundaryFullPowerScaled77_12_21Norm.property,boundaryFullPowerScaled77_13_21Norm.property,boundaryFullPowerScaled77_14_21Norm.property,boundaryFullPowerScaled77_15_21Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_21Norm,boundaryFullPowerScaled77_9_21Norm,boundaryFullPowerScaled77_10_21Norm,boundaryFullPowerScaled77_11_21Norm,boundaryFullPowerScaled77_12_21Norm,boundaryFullPowerScaled77_13_21Norm,boundaryFullPowerScaled77_14_21Norm,boundaryFullPowerScaled77_15_21Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_21Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 21)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_21Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_21Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_21Chunk16=boundaryPowerBernstein77_17_21Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_21Chunk16]

    rw [boundaryFullPowerScaled77_16_21Norm.property,boundaryFullPowerScaled77_17_21Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_21Norm,boundaryFullPowerScaled77_17_21Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_21Norm : {c : ℝ // boundaryFullCoefficient77 17 21=c} := by

  have he : boundaryFullCoefficient77 17 21=((boundaryPowerBernstein77_17_21Chunk0) + ((boundaryPowerBernstein77_17_21Chunk8) + (boundaryPowerBernstein77_17_21Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_21Chunk0,boundaryPowerBernstein77_17_21Chunk8,boundaryPowerBernstein77_17_21Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_21Chunk0Norm.property,boundaryPowerBernstein77_17_21Chunk8Norm.property,boundaryPowerBernstein77_17_21Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_21Chunk0Norm,boundaryPowerBernstein77_17_21Chunk8Norm,boundaryPowerBernstein77_17_21Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_22Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_22Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_22Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_22Chunk0=boundaryPowerBernstein77_17_22Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_22Chunk0]

    rw [boundaryFullPowerScaled77_0_22Norm.property,boundaryFullPowerScaled77_1_22Norm.property,boundaryFullPowerScaled77_2_22Norm.property,boundaryFullPowerScaled77_3_22Norm.property,boundaryFullPowerScaled77_4_22Norm.property,boundaryFullPowerScaled77_5_22Norm.property,boundaryFullPowerScaled77_6_22Norm.property,boundaryFullPowerScaled77_7_22Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_22Norm,boundaryFullPowerScaled77_1_22Norm,boundaryFullPowerScaled77_2_22Norm,boundaryFullPowerScaled77_3_22Norm,boundaryFullPowerScaled77_4_22Norm,boundaryFullPowerScaled77_5_22Norm,boundaryFullPowerScaled77_6_22Norm,boundaryFullPowerScaled77_7_22Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_22Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_22Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_22Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_22Chunk8=boundaryPowerBernstein77_17_22Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_22Chunk8]

    rw [boundaryFullPowerScaled77_8_22Norm.property,boundaryFullPowerScaled77_9_22Norm.property,boundaryFullPowerScaled77_10_22Norm.property,boundaryFullPowerScaled77_11_22Norm.property,boundaryFullPowerScaled77_12_22Norm.property,boundaryFullPowerScaled77_13_22Norm.property,boundaryFullPowerScaled77_14_22Norm.property,boundaryFullPowerScaled77_15_22Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_22Norm,boundaryFullPowerScaled77_9_22Norm,boundaryFullPowerScaled77_10_22Norm,boundaryFullPowerScaled77_11_22Norm,boundaryFullPowerScaled77_12_22Norm,boundaryFullPowerScaled77_13_22Norm,boundaryFullPowerScaled77_14_22Norm,boundaryFullPowerScaled77_15_22Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_22Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 22)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_22Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_22Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_22Chunk16=boundaryPowerBernstein77_17_22Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_22Chunk16]

    rw [boundaryFullPowerScaled77_16_22Norm.property,boundaryFullPowerScaled77_17_22Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_22Norm,boundaryFullPowerScaled77_17_22Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_22Norm : {c : ℝ // boundaryFullCoefficient77 17 22=c} := by

  have he : boundaryFullCoefficient77 17 22=((boundaryPowerBernstein77_17_22Chunk0) + ((boundaryPowerBernstein77_17_22Chunk8) + (boundaryPowerBernstein77_17_22Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_22Chunk0,boundaryPowerBernstein77_17_22Chunk8,boundaryPowerBernstein77_17_22Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_22Chunk0Norm.property,boundaryPowerBernstein77_17_22Chunk8Norm.property,boundaryPowerBernstein77_17_22Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_22Chunk0Norm,boundaryPowerBernstein77_17_22Chunk8Norm,boundaryPowerBernstein77_17_22Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_23Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_23Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_23Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_23Chunk0=boundaryPowerBernstein77_17_23Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_23Chunk0]

    rw [boundaryFullPowerScaled77_0_23Norm.property,boundaryFullPowerScaled77_1_23Norm.property,boundaryFullPowerScaled77_2_23Norm.property,boundaryFullPowerScaled77_3_23Norm.property,boundaryFullPowerScaled77_4_23Norm.property,boundaryFullPowerScaled77_5_23Norm.property,boundaryFullPowerScaled77_6_23Norm.property,boundaryFullPowerScaled77_7_23Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_23Norm,boundaryFullPowerScaled77_1_23Norm,boundaryFullPowerScaled77_2_23Norm,boundaryFullPowerScaled77_3_23Norm,boundaryFullPowerScaled77_4_23Norm,boundaryFullPowerScaled77_5_23Norm,boundaryFullPowerScaled77_6_23Norm,boundaryFullPowerScaled77_7_23Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_23Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_23Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_23Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_23Chunk8=boundaryPowerBernstein77_17_23Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_23Chunk8]

    rw [boundaryFullPowerScaled77_8_23Norm.property,boundaryFullPowerScaled77_9_23Norm.property,boundaryFullPowerScaled77_10_23Norm.property,boundaryFullPowerScaled77_11_23Norm.property,boundaryFullPowerScaled77_12_23Norm.property,boundaryFullPowerScaled77_13_23Norm.property,boundaryFullPowerScaled77_14_23Norm.property,boundaryFullPowerScaled77_15_23Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_23Norm,boundaryFullPowerScaled77_9_23Norm,boundaryFullPowerScaled77_10_23Norm,boundaryFullPowerScaled77_11_23Norm,boundaryFullPowerScaled77_12_23Norm,boundaryFullPowerScaled77_13_23Norm,boundaryFullPowerScaled77_14_23Norm,boundaryFullPowerScaled77_15_23Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_23Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 23)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_23Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_23Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_23Chunk16=boundaryPowerBernstein77_17_23Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_23Chunk16]

    rw [boundaryFullPowerScaled77_16_23Norm.property,boundaryFullPowerScaled77_17_23Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_23Norm,boundaryFullPowerScaled77_17_23Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_23Norm : {c : ℝ // boundaryFullCoefficient77 17 23=c} := by

  have he : boundaryFullCoefficient77 17 23=((boundaryPowerBernstein77_17_23Chunk0) + ((boundaryPowerBernstein77_17_23Chunk8) + (boundaryPowerBernstein77_17_23Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_23Chunk0,boundaryPowerBernstein77_17_23Chunk8,boundaryPowerBernstein77_17_23Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_23Chunk0Norm.property,boundaryPowerBernstein77_17_23Chunk8Norm.property,boundaryPowerBernstein77_17_23Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_23Chunk0Norm,boundaryPowerBernstein77_17_23Chunk8Norm,boundaryPowerBernstein77_17_23Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_24Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_24Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_24Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_24Chunk0=boundaryPowerBernstein77_17_24Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_24Chunk0]

    rw [boundaryFullPowerScaled77_0_24Norm.property,boundaryFullPowerScaled77_1_24Norm.property,boundaryFullPowerScaled77_2_24Norm.property,boundaryFullPowerScaled77_3_24Norm.property,boundaryFullPowerScaled77_4_24Norm.property,boundaryFullPowerScaled77_5_24Norm.property,boundaryFullPowerScaled77_6_24Norm.property,boundaryFullPowerScaled77_7_24Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_24Norm,boundaryFullPowerScaled77_1_24Norm,boundaryFullPowerScaled77_2_24Norm,boundaryFullPowerScaled77_3_24Norm,boundaryFullPowerScaled77_4_24Norm,boundaryFullPowerScaled77_5_24Norm,boundaryFullPowerScaled77_6_24Norm,boundaryFullPowerScaled77_7_24Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_24Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_24Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_24Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_24Chunk8=boundaryPowerBernstein77_17_24Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_24Chunk8]

    rw [boundaryFullPowerScaled77_8_24Norm.property,boundaryFullPowerScaled77_9_24Norm.property,boundaryFullPowerScaled77_10_24Norm.property,boundaryFullPowerScaled77_11_24Norm.property,boundaryFullPowerScaled77_12_24Norm.property,boundaryFullPowerScaled77_13_24Norm.property,boundaryFullPowerScaled77_14_24Norm.property,boundaryFullPowerScaled77_15_24Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_24Norm,boundaryFullPowerScaled77_9_24Norm,boundaryFullPowerScaled77_10_24Norm,boundaryFullPowerScaled77_11_24Norm,boundaryFullPowerScaled77_12_24Norm,boundaryFullPowerScaled77_13_24Norm,boundaryFullPowerScaled77_14_24Norm,boundaryFullPowerScaled77_15_24Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_24Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 24)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_24Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_24Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_24Chunk16=boundaryPowerBernstein77_17_24Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_24Chunk16]

    rw [boundaryFullPowerScaled77_16_24Norm.property,boundaryFullPowerScaled77_17_24Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_24Norm,boundaryFullPowerScaled77_17_24Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_24Norm : {c : ℝ // boundaryFullCoefficient77 17 24=c} := by

  have he : boundaryFullCoefficient77 17 24=((boundaryPowerBernstein77_17_24Chunk0) + ((boundaryPowerBernstein77_17_24Chunk8) + (boundaryPowerBernstein77_17_24Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_24Chunk0,boundaryPowerBernstein77_17_24Chunk8,boundaryPowerBernstein77_17_24Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_24Chunk0Norm.property,boundaryPowerBernstein77_17_24Chunk8Norm.property,boundaryPowerBernstein77_17_24Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_24Chunk0Norm,boundaryPowerBernstein77_17_24Chunk8Norm,boundaryPowerBernstein77_17_24Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_25Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_25Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_25Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_25Chunk0=boundaryPowerBernstein77_17_25Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_25Chunk0]

    rw [boundaryFullPowerScaled77_0_25Norm.property,boundaryFullPowerScaled77_1_25Norm.property,boundaryFullPowerScaled77_2_25Norm.property,boundaryFullPowerScaled77_3_25Norm.property,boundaryFullPowerScaled77_4_25Norm.property,boundaryFullPowerScaled77_5_25Norm.property,boundaryFullPowerScaled77_6_25Norm.property,boundaryFullPowerScaled77_7_25Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_25Norm,boundaryFullPowerScaled77_1_25Norm,boundaryFullPowerScaled77_2_25Norm,boundaryFullPowerScaled77_3_25Norm,boundaryFullPowerScaled77_4_25Norm,boundaryFullPowerScaled77_5_25Norm,boundaryFullPowerScaled77_6_25Norm,boundaryFullPowerScaled77_7_25Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_25Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_25Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_25Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_25Chunk8=boundaryPowerBernstein77_17_25Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_25Chunk8]

    rw [boundaryFullPowerScaled77_8_25Norm.property,boundaryFullPowerScaled77_9_25Norm.property,boundaryFullPowerScaled77_10_25Norm.property,boundaryFullPowerScaled77_11_25Norm.property,boundaryFullPowerScaled77_12_25Norm.property,boundaryFullPowerScaled77_13_25Norm.property,boundaryFullPowerScaled77_14_25Norm.property,boundaryFullPowerScaled77_15_25Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_25Norm,boundaryFullPowerScaled77_9_25Norm,boundaryFullPowerScaled77_10_25Norm,boundaryFullPowerScaled77_11_25Norm,boundaryFullPowerScaled77_12_25Norm,boundaryFullPowerScaled77_13_25Norm,boundaryFullPowerScaled77_14_25Norm,boundaryFullPowerScaled77_15_25Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_25Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 25)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_25Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_25Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_25Chunk16=boundaryPowerBernstein77_17_25Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_25Chunk16]

    rw [boundaryFullPowerScaled77_16_25Norm.property,boundaryFullPowerScaled77_17_25Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_25Norm,boundaryFullPowerScaled77_17_25Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_25Norm : {c : ℝ // boundaryFullCoefficient77 17 25=c} := by

  have he : boundaryFullCoefficient77 17 25=((boundaryPowerBernstein77_17_25Chunk0) + ((boundaryPowerBernstein77_17_25Chunk8) + (boundaryPowerBernstein77_17_25Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_25Chunk0,boundaryPowerBernstein77_17_25Chunk8,boundaryPowerBernstein77_17_25Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_25Chunk0Norm.property,boundaryPowerBernstein77_17_25Chunk8Norm.property,boundaryPowerBernstein77_17_25Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_25Chunk0Norm,boundaryPowerBernstein77_17_25Chunk8Norm,boundaryPowerBernstein77_17_25Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_26Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_26Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_26Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_26Chunk0=boundaryPowerBernstein77_17_26Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_26Chunk0]

    rw [boundaryFullPowerScaled77_0_26Norm.property,boundaryFullPowerScaled77_1_26Norm.property,boundaryFullPowerScaled77_2_26Norm.property,boundaryFullPowerScaled77_3_26Norm.property,boundaryFullPowerScaled77_4_26Norm.property,boundaryFullPowerScaled77_5_26Norm.property,boundaryFullPowerScaled77_6_26Norm.property,boundaryFullPowerScaled77_7_26Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_26Norm,boundaryFullPowerScaled77_1_26Norm,boundaryFullPowerScaled77_2_26Norm,boundaryFullPowerScaled77_3_26Norm,boundaryFullPowerScaled77_4_26Norm,boundaryFullPowerScaled77_5_26Norm,boundaryFullPowerScaled77_6_26Norm,boundaryFullPowerScaled77_7_26Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_26Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_26Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_26Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_26Chunk8=boundaryPowerBernstein77_17_26Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_26Chunk8]

    rw [boundaryFullPowerScaled77_8_26Norm.property,boundaryFullPowerScaled77_9_26Norm.property,boundaryFullPowerScaled77_10_26Norm.property,boundaryFullPowerScaled77_11_26Norm.property,boundaryFullPowerScaled77_12_26Norm.property,boundaryFullPowerScaled77_13_26Norm.property,boundaryFullPowerScaled77_14_26Norm.property,boundaryFullPowerScaled77_15_26Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_26Norm,boundaryFullPowerScaled77_9_26Norm,boundaryFullPowerScaled77_10_26Norm,boundaryFullPowerScaled77_11_26Norm,boundaryFullPowerScaled77_12_26Norm,boundaryFullPowerScaled77_13_26Norm,boundaryFullPowerScaled77_14_26Norm,boundaryFullPowerScaled77_15_26Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_26Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 26)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_26Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_26Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_26Chunk16=boundaryPowerBernstein77_17_26Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_26Chunk16]

    rw [boundaryFullPowerScaled77_16_26Norm.property,boundaryFullPowerScaled77_17_26Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_26Norm,boundaryFullPowerScaled77_17_26Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_26Norm : {c : ℝ // boundaryFullCoefficient77 17 26=c} := by

  have he : boundaryFullCoefficient77 17 26=((boundaryPowerBernstein77_17_26Chunk0) + ((boundaryPowerBernstein77_17_26Chunk8) + (boundaryPowerBernstein77_17_26Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_26Chunk0,boundaryPowerBernstein77_17_26Chunk8,boundaryPowerBernstein77_17_26Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_26Chunk0Norm.property,boundaryPowerBernstein77_17_26Chunk8Norm.property,boundaryPowerBernstein77_17_26Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_26Chunk0Norm,boundaryPowerBernstein77_17_26Chunk8Norm,boundaryPowerBernstein77_17_26Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_27Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_27Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_27Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_27Chunk0=boundaryPowerBernstein77_17_27Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_27Chunk0]

    rw [boundaryFullPowerScaled77_0_27Norm.property,boundaryFullPowerScaled77_1_27Norm.property,boundaryFullPowerScaled77_2_27Norm.property,boundaryFullPowerScaled77_3_27Norm.property,boundaryFullPowerScaled77_4_27Norm.property,boundaryFullPowerScaled77_5_27Norm.property,boundaryFullPowerScaled77_6_27Norm.property,boundaryFullPowerScaled77_7_27Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_27Norm,boundaryFullPowerScaled77_1_27Norm,boundaryFullPowerScaled77_2_27Norm,boundaryFullPowerScaled77_3_27Norm,boundaryFullPowerScaled77_4_27Norm,boundaryFullPowerScaled77_5_27Norm,boundaryFullPowerScaled77_6_27Norm,boundaryFullPowerScaled77_7_27Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_27Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_27Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_27Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_27Chunk8=boundaryPowerBernstein77_17_27Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_27Chunk8]

    rw [boundaryFullPowerScaled77_8_27Norm.property,boundaryFullPowerScaled77_9_27Norm.property,boundaryFullPowerScaled77_10_27Norm.property,boundaryFullPowerScaled77_11_27Norm.property,boundaryFullPowerScaled77_12_27Norm.property,boundaryFullPowerScaled77_13_27Norm.property,boundaryFullPowerScaled77_14_27Norm.property,boundaryFullPowerScaled77_15_27Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_27Norm,boundaryFullPowerScaled77_9_27Norm,boundaryFullPowerScaled77_10_27Norm,boundaryFullPowerScaled77_11_27Norm,boundaryFullPowerScaled77_12_27Norm,boundaryFullPowerScaled77_13_27Norm,boundaryFullPowerScaled77_14_27Norm,boundaryFullPowerScaled77_15_27Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_27Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 27)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_27Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_27Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_27Chunk16=boundaryPowerBernstein77_17_27Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_27Chunk16]

    rw [boundaryFullPowerScaled77_16_27Norm.property,boundaryFullPowerScaled77_17_27Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_27Norm,boundaryFullPowerScaled77_17_27Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_27Norm : {c : ℝ // boundaryFullCoefficient77 17 27=c} := by

  have he : boundaryFullCoefficient77 17 27=((boundaryPowerBernstein77_17_27Chunk0) + ((boundaryPowerBernstein77_17_27Chunk8) + (boundaryPowerBernstein77_17_27Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_27Chunk0,boundaryPowerBernstein77_17_27Chunk8,boundaryPowerBernstein77_17_27Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_27Chunk0Norm.property,boundaryPowerBernstein77_17_27Chunk8Norm.property,boundaryPowerBernstein77_17_27Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_27Chunk0Norm,boundaryPowerBernstein77_17_27Chunk8Norm,boundaryPowerBernstein77_17_27Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_28Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_28Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_28Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_28Chunk0=boundaryPowerBernstein77_17_28Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_28Chunk0]

    rw [boundaryFullPowerScaled77_0_28Norm.property,boundaryFullPowerScaled77_1_28Norm.property,boundaryFullPowerScaled77_2_28Norm.property,boundaryFullPowerScaled77_3_28Norm.property,boundaryFullPowerScaled77_4_28Norm.property,boundaryFullPowerScaled77_5_28Norm.property,boundaryFullPowerScaled77_6_28Norm.property,boundaryFullPowerScaled77_7_28Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_28Norm,boundaryFullPowerScaled77_1_28Norm,boundaryFullPowerScaled77_2_28Norm,boundaryFullPowerScaled77_3_28Norm,boundaryFullPowerScaled77_4_28Norm,boundaryFullPowerScaled77_5_28Norm,boundaryFullPowerScaled77_6_28Norm,boundaryFullPowerScaled77_7_28Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_28Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_28Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_28Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_28Chunk8=boundaryPowerBernstein77_17_28Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_28Chunk8]

    rw [boundaryFullPowerScaled77_8_28Norm.property,boundaryFullPowerScaled77_9_28Norm.property,boundaryFullPowerScaled77_10_28Norm.property,boundaryFullPowerScaled77_11_28Norm.property,boundaryFullPowerScaled77_12_28Norm.property,boundaryFullPowerScaled77_13_28Norm.property,boundaryFullPowerScaled77_14_28Norm.property,boundaryFullPowerScaled77_15_28Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_28Norm,boundaryFullPowerScaled77_9_28Norm,boundaryFullPowerScaled77_10_28Norm,boundaryFullPowerScaled77_11_28Norm,boundaryFullPowerScaled77_12_28Norm,boundaryFullPowerScaled77_13_28Norm,boundaryFullPowerScaled77_14_28Norm,boundaryFullPowerScaled77_15_28Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_28Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 28)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_28Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_28Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_28Chunk16=boundaryPowerBernstein77_17_28Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_28Chunk16]

    rw [boundaryFullPowerScaled77_16_28Norm.property,boundaryFullPowerScaled77_17_28Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_28Norm,boundaryFullPowerScaled77_17_28Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_28Norm : {c : ℝ // boundaryFullCoefficient77 17 28=c} := by

  have he : boundaryFullCoefficient77 17 28=((boundaryPowerBernstein77_17_28Chunk0) + ((boundaryPowerBernstein77_17_28Chunk8) + (boundaryPowerBernstein77_17_28Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_28Chunk0,boundaryPowerBernstein77_17_28Chunk8,boundaryPowerBernstein77_17_28Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_28Chunk0Norm.property,boundaryPowerBernstein77_17_28Chunk8Norm.property,boundaryPowerBernstein77_17_28Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_28Chunk0Norm,boundaryPowerBernstein77_17_28Chunk8Norm,boundaryPowerBernstein77_17_28Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_29Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_29Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_29Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_29Chunk0=boundaryPowerBernstein77_17_29Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_29Chunk0]

    rw [boundaryFullPowerScaled77_0_29Norm.property,boundaryFullPowerScaled77_1_29Norm.property,boundaryFullPowerScaled77_2_29Norm.property,boundaryFullPowerScaled77_3_29Norm.property,boundaryFullPowerScaled77_4_29Norm.property,boundaryFullPowerScaled77_5_29Norm.property,boundaryFullPowerScaled77_6_29Norm.property,boundaryFullPowerScaled77_7_29Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_29Norm,boundaryFullPowerScaled77_1_29Norm,boundaryFullPowerScaled77_2_29Norm,boundaryFullPowerScaled77_3_29Norm,boundaryFullPowerScaled77_4_29Norm,boundaryFullPowerScaled77_5_29Norm,boundaryFullPowerScaled77_6_29Norm,boundaryFullPowerScaled77_7_29Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_29Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_29Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_29Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_29Chunk8=boundaryPowerBernstein77_17_29Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_29Chunk8]

    rw [boundaryFullPowerScaled77_8_29Norm.property,boundaryFullPowerScaled77_9_29Norm.property,boundaryFullPowerScaled77_10_29Norm.property,boundaryFullPowerScaled77_11_29Norm.property,boundaryFullPowerScaled77_12_29Norm.property,boundaryFullPowerScaled77_13_29Norm.property,boundaryFullPowerScaled77_14_29Norm.property,boundaryFullPowerScaled77_15_29Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_29Norm,boundaryFullPowerScaled77_9_29Norm,boundaryFullPowerScaled77_10_29Norm,boundaryFullPowerScaled77_11_29Norm,boundaryFullPowerScaled77_12_29Norm,boundaryFullPowerScaled77_13_29Norm,boundaryFullPowerScaled77_14_29Norm,boundaryFullPowerScaled77_15_29Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_29Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 29)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_29Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_29Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_29Chunk16=boundaryPowerBernstein77_17_29Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_29Chunk16]

    rw [boundaryFullPowerScaled77_16_29Norm.property,boundaryFullPowerScaled77_17_29Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_29Norm,boundaryFullPowerScaled77_17_29Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_29Norm : {c : ℝ // boundaryFullCoefficient77 17 29=c} := by

  have he : boundaryFullCoefficient77 17 29=((boundaryPowerBernstein77_17_29Chunk0) + ((boundaryPowerBernstein77_17_29Chunk8) + (boundaryPowerBernstein77_17_29Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_29Chunk0,boundaryPowerBernstein77_17_29Chunk8,boundaryPowerBernstein77_17_29Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_29Chunk0Norm.property,boundaryPowerBernstein77_17_29Chunk8Norm.property,boundaryPowerBernstein77_17_29Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_29Chunk0Norm,boundaryPowerBernstein77_17_29Chunk8Norm,boundaryPowerBernstein77_17_29Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_30Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_30Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_30Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_30Chunk0=boundaryPowerBernstein77_17_30Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_30Chunk0]

    rw [boundaryFullPowerScaled77_0_30Norm.property,boundaryFullPowerScaled77_1_30Norm.property,boundaryFullPowerScaled77_2_30Norm.property,boundaryFullPowerScaled77_3_30Norm.property,boundaryFullPowerScaled77_4_30Norm.property,boundaryFullPowerScaled77_5_30Norm.property,boundaryFullPowerScaled77_6_30Norm.property,boundaryFullPowerScaled77_7_30Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_30Norm,boundaryFullPowerScaled77_1_30Norm,boundaryFullPowerScaled77_2_30Norm,boundaryFullPowerScaled77_3_30Norm,boundaryFullPowerScaled77_4_30Norm,boundaryFullPowerScaled77_5_30Norm,boundaryFullPowerScaled77_6_30Norm,boundaryFullPowerScaled77_7_30Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_30Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_30Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_30Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_30Chunk8=boundaryPowerBernstein77_17_30Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_30Chunk8]

    rw [boundaryFullPowerScaled77_8_30Norm.property,boundaryFullPowerScaled77_9_30Norm.property,boundaryFullPowerScaled77_10_30Norm.property,boundaryFullPowerScaled77_11_30Norm.property,boundaryFullPowerScaled77_12_30Norm.property,boundaryFullPowerScaled77_13_30Norm.property,boundaryFullPowerScaled77_14_30Norm.property,boundaryFullPowerScaled77_15_30Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_30Norm,boundaryFullPowerScaled77_9_30Norm,boundaryFullPowerScaled77_10_30Norm,boundaryFullPowerScaled77_11_30Norm,boundaryFullPowerScaled77_12_30Norm,boundaryFullPowerScaled77_13_30Norm,boundaryFullPowerScaled77_14_30Norm,boundaryFullPowerScaled77_15_30Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_30Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 30)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_30Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_30Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_30Chunk16=boundaryPowerBernstein77_17_30Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_30Chunk16]

    rw [boundaryFullPowerScaled77_16_30Norm.property,boundaryFullPowerScaled77_17_30Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_30Norm,boundaryFullPowerScaled77_17_30Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_30Norm : {c : ℝ // boundaryFullCoefficient77 17 30=c} := by

  have he : boundaryFullCoefficient77 17 30=((boundaryPowerBernstein77_17_30Chunk0) + ((boundaryPowerBernstein77_17_30Chunk8) + (boundaryPowerBernstein77_17_30Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_30Chunk0,boundaryPowerBernstein77_17_30Chunk8,boundaryPowerBernstein77_17_30Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_30Chunk0Norm.property,boundaryPowerBernstein77_17_30Chunk8Norm.property,boundaryPowerBernstein77_17_30Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_30Chunk0Norm,boundaryPowerBernstein77_17_30Chunk8Norm,boundaryPowerBernstein77_17_30Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_31Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_31Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_31Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_31Chunk0=boundaryPowerBernstein77_17_31Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_31Chunk0]

    rw [boundaryFullPowerScaled77_0_31Norm.property,boundaryFullPowerScaled77_1_31Norm.property,boundaryFullPowerScaled77_2_31Norm.property,boundaryFullPowerScaled77_3_31Norm.property,boundaryFullPowerScaled77_4_31Norm.property,boundaryFullPowerScaled77_5_31Norm.property,boundaryFullPowerScaled77_6_31Norm.property,boundaryFullPowerScaled77_7_31Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_31Norm,boundaryFullPowerScaled77_1_31Norm,boundaryFullPowerScaled77_2_31Norm,boundaryFullPowerScaled77_3_31Norm,boundaryFullPowerScaled77_4_31Norm,boundaryFullPowerScaled77_5_31Norm,boundaryFullPowerScaled77_6_31Norm,boundaryFullPowerScaled77_7_31Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_31Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_31Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_31Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_31Chunk8=boundaryPowerBernstein77_17_31Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_31Chunk8]

    rw [boundaryFullPowerScaled77_8_31Norm.property,boundaryFullPowerScaled77_9_31Norm.property,boundaryFullPowerScaled77_10_31Norm.property,boundaryFullPowerScaled77_11_31Norm.property,boundaryFullPowerScaled77_12_31Norm.property,boundaryFullPowerScaled77_13_31Norm.property,boundaryFullPowerScaled77_14_31Norm.property,boundaryFullPowerScaled77_15_31Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_31Norm,boundaryFullPowerScaled77_9_31Norm,boundaryFullPowerScaled77_10_31Norm,boundaryFullPowerScaled77_11_31Norm,boundaryFullPowerScaled77_12_31Norm,boundaryFullPowerScaled77_13_31Norm,boundaryFullPowerScaled77_14_31Norm,boundaryFullPowerScaled77_15_31Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_31Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 31)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_31Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_31Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_31Chunk16=boundaryPowerBernstein77_17_31Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_31Chunk16]

    rw [boundaryFullPowerScaled77_16_31Norm.property,boundaryFullPowerScaled77_17_31Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_31Norm,boundaryFullPowerScaled77_17_31Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_31Norm : {c : ℝ // boundaryFullCoefficient77 17 31=c} := by

  have he : boundaryFullCoefficient77 17 31=((boundaryPowerBernstein77_17_31Chunk0) + ((boundaryPowerBernstein77_17_31Chunk8) + (boundaryPowerBernstein77_17_31Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_31Chunk0,boundaryPowerBernstein77_17_31Chunk8,boundaryPowerBernstein77_17_31Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_31Chunk0Norm.property,boundaryPowerBernstein77_17_31Chunk8Norm.property,boundaryPowerBernstein77_17_31Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_31Chunk0Norm,boundaryPowerBernstein77_17_31Chunk8Norm,boundaryPowerBernstein77_17_31Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_32Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_32Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_32Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_32Chunk0=boundaryPowerBernstein77_17_32Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_32Chunk0]

    rw [boundaryFullPowerScaled77_0_32Norm.property,boundaryFullPowerScaled77_1_32Norm.property,boundaryFullPowerScaled77_2_32Norm.property,boundaryFullPowerScaled77_3_32Norm.property,boundaryFullPowerScaled77_4_32Norm.property,boundaryFullPowerScaled77_5_32Norm.property,boundaryFullPowerScaled77_6_32Norm.property,boundaryFullPowerScaled77_7_32Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_32Norm,boundaryFullPowerScaled77_1_32Norm,boundaryFullPowerScaled77_2_32Norm,boundaryFullPowerScaled77_3_32Norm,boundaryFullPowerScaled77_4_32Norm,boundaryFullPowerScaled77_5_32Norm,boundaryFullPowerScaled77_6_32Norm,boundaryFullPowerScaled77_7_32Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_32Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_32Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_32Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_32Chunk8=boundaryPowerBernstein77_17_32Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_32Chunk8]

    rw [boundaryFullPowerScaled77_8_32Norm.property,boundaryFullPowerScaled77_9_32Norm.property,boundaryFullPowerScaled77_10_32Norm.property,boundaryFullPowerScaled77_11_32Norm.property,boundaryFullPowerScaled77_12_32Norm.property,boundaryFullPowerScaled77_13_32Norm.property,boundaryFullPowerScaled77_14_32Norm.property,boundaryFullPowerScaled77_15_32Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_32Norm,boundaryFullPowerScaled77_9_32Norm,boundaryFullPowerScaled77_10_32Norm,boundaryFullPowerScaled77_11_32Norm,boundaryFullPowerScaled77_12_32Norm,boundaryFullPowerScaled77_13_32Norm,boundaryFullPowerScaled77_14_32Norm,boundaryFullPowerScaled77_15_32Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_32Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 32)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_32Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_32Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_32Chunk16=boundaryPowerBernstein77_17_32Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_32Chunk16]

    rw [boundaryFullPowerScaled77_16_32Norm.property,boundaryFullPowerScaled77_17_32Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_32Norm,boundaryFullPowerScaled77_17_32Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_32Norm : {c : ℝ // boundaryFullCoefficient77 17 32=c} := by

  have he : boundaryFullCoefficient77 17 32=((boundaryPowerBernstein77_17_32Chunk0) + ((boundaryPowerBernstein77_17_32Chunk8) + (boundaryPowerBernstein77_17_32Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_32Chunk0,boundaryPowerBernstein77_17_32Chunk8,boundaryPowerBernstein77_17_32Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_32Chunk0Norm.property,boundaryPowerBernstein77_17_32Chunk8Norm.property,boundaryPowerBernstein77_17_32Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_32Chunk0Norm,boundaryPowerBernstein77_17_32Chunk8Norm,boundaryPowerBernstein77_17_32Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_33Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_33Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_33Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_33Chunk0=boundaryPowerBernstein77_17_33Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_33Chunk0]

    rw [boundaryFullPowerScaled77_0_33Norm.property,boundaryFullPowerScaled77_1_33Norm.property,boundaryFullPowerScaled77_2_33Norm.property,boundaryFullPowerScaled77_3_33Norm.property,boundaryFullPowerScaled77_4_33Norm.property,boundaryFullPowerScaled77_5_33Norm.property,boundaryFullPowerScaled77_6_33Norm.property,boundaryFullPowerScaled77_7_33Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_33Norm,boundaryFullPowerScaled77_1_33Norm,boundaryFullPowerScaled77_2_33Norm,boundaryFullPowerScaled77_3_33Norm,boundaryFullPowerScaled77_4_33Norm,boundaryFullPowerScaled77_5_33Norm,boundaryFullPowerScaled77_6_33Norm,boundaryFullPowerScaled77_7_33Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_33Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_33Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_33Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_33Chunk8=boundaryPowerBernstein77_17_33Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_33Chunk8]

    rw [boundaryFullPowerScaled77_8_33Norm.property,boundaryFullPowerScaled77_9_33Norm.property,boundaryFullPowerScaled77_10_33Norm.property,boundaryFullPowerScaled77_11_33Norm.property,boundaryFullPowerScaled77_12_33Norm.property,boundaryFullPowerScaled77_13_33Norm.property,boundaryFullPowerScaled77_14_33Norm.property,boundaryFullPowerScaled77_15_33Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_33Norm,boundaryFullPowerScaled77_9_33Norm,boundaryFullPowerScaled77_10_33Norm,boundaryFullPowerScaled77_11_33Norm,boundaryFullPowerScaled77_12_33Norm,boundaryFullPowerScaled77_13_33Norm,boundaryFullPowerScaled77_14_33Norm,boundaryFullPowerScaled77_15_33Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_33Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 33)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_33Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_33Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_33Chunk16=boundaryPowerBernstein77_17_33Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_33Chunk16]

    rw [boundaryFullPowerScaled77_16_33Norm.property,boundaryFullPowerScaled77_17_33Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_33Norm,boundaryFullPowerScaled77_17_33Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_33Norm : {c : ℝ // boundaryFullCoefficient77 17 33=c} := by

  have he : boundaryFullCoefficient77 17 33=((boundaryPowerBernstein77_17_33Chunk0) + ((boundaryPowerBernstein77_17_33Chunk8) + (boundaryPowerBernstein77_17_33Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_33Chunk0,boundaryPowerBernstein77_17_33Chunk8,boundaryPowerBernstein77_17_33Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_33Chunk0Norm.property,boundaryPowerBernstein77_17_33Chunk8Norm.property,boundaryPowerBernstein77_17_33Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_33Chunk0Norm,boundaryPowerBernstein77_17_33Chunk8Norm,boundaryPowerBernstein77_17_33Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_34Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_34Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_34Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_34Chunk0=boundaryPowerBernstein77_17_34Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_34Chunk0]

    rw [boundaryFullPowerScaled77_0_34Norm.property,boundaryFullPowerScaled77_1_34Norm.property,boundaryFullPowerScaled77_2_34Norm.property,boundaryFullPowerScaled77_3_34Norm.property,boundaryFullPowerScaled77_4_34Norm.property,boundaryFullPowerScaled77_5_34Norm.property,boundaryFullPowerScaled77_6_34Norm.property,boundaryFullPowerScaled77_7_34Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_34Norm,boundaryFullPowerScaled77_1_34Norm,boundaryFullPowerScaled77_2_34Norm,boundaryFullPowerScaled77_3_34Norm,boundaryFullPowerScaled77_4_34Norm,boundaryFullPowerScaled77_5_34Norm,boundaryFullPowerScaled77_6_34Norm,boundaryFullPowerScaled77_7_34Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_34Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_34Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_34Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_34Chunk8=boundaryPowerBernstein77_17_34Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_34Chunk8]

    rw [boundaryFullPowerScaled77_8_34Norm.property,boundaryFullPowerScaled77_9_34Norm.property,boundaryFullPowerScaled77_10_34Norm.property,boundaryFullPowerScaled77_11_34Norm.property,boundaryFullPowerScaled77_12_34Norm.property,boundaryFullPowerScaled77_13_34Norm.property,boundaryFullPowerScaled77_14_34Norm.property,boundaryFullPowerScaled77_15_34Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_34Norm,boundaryFullPowerScaled77_9_34Norm,boundaryFullPowerScaled77_10_34Norm,boundaryFullPowerScaled77_11_34Norm,boundaryFullPowerScaled77_12_34Norm,boundaryFullPowerScaled77_13_34Norm,boundaryFullPowerScaled77_14_34Norm,boundaryFullPowerScaled77_15_34Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_34Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 34)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_34Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_34Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_34Chunk16=boundaryPowerBernstein77_17_34Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_34Chunk16]

    rw [boundaryFullPowerScaled77_16_34Norm.property,boundaryFullPowerScaled77_17_34Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_34Norm,boundaryFullPowerScaled77_17_34Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_34Norm : {c : ℝ // boundaryFullCoefficient77 17 34=c} := by

  have he : boundaryFullCoefficient77 17 34=((boundaryPowerBernstein77_17_34Chunk0) + ((boundaryPowerBernstein77_17_34Chunk8) + (boundaryPowerBernstein77_17_34Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_34Chunk0,boundaryPowerBernstein77_17_34Chunk8,boundaryPowerBernstein77_17_34Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_34Chunk0Norm.property,boundaryPowerBernstein77_17_34Chunk8Norm.property,boundaryPowerBernstein77_17_34Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_34Chunk0Norm,boundaryPowerBernstein77_17_34Chunk8Norm,boundaryPowerBernstein77_17_34Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_35Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_35Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_35Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_35Chunk0=boundaryPowerBernstein77_17_35Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_35Chunk0]

    rw [boundaryFullPowerScaled77_0_35Norm.property,boundaryFullPowerScaled77_1_35Norm.property,boundaryFullPowerScaled77_2_35Norm.property,boundaryFullPowerScaled77_3_35Norm.property,boundaryFullPowerScaled77_4_35Norm.property,boundaryFullPowerScaled77_5_35Norm.property,boundaryFullPowerScaled77_6_35Norm.property,boundaryFullPowerScaled77_7_35Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_35Norm,boundaryFullPowerScaled77_1_35Norm,boundaryFullPowerScaled77_2_35Norm,boundaryFullPowerScaled77_3_35Norm,boundaryFullPowerScaled77_4_35Norm,boundaryFullPowerScaled77_5_35Norm,boundaryFullPowerScaled77_6_35Norm,boundaryFullPowerScaled77_7_35Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_35Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_35Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_35Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_35Chunk8=boundaryPowerBernstein77_17_35Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_35Chunk8]

    rw [boundaryFullPowerScaled77_8_35Norm.property,boundaryFullPowerScaled77_9_35Norm.property,boundaryFullPowerScaled77_10_35Norm.property,boundaryFullPowerScaled77_11_35Norm.property,boundaryFullPowerScaled77_12_35Norm.property,boundaryFullPowerScaled77_13_35Norm.property,boundaryFullPowerScaled77_14_35Norm.property,boundaryFullPowerScaled77_15_35Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_35Norm,boundaryFullPowerScaled77_9_35Norm,boundaryFullPowerScaled77_10_35Norm,boundaryFullPowerScaled77_11_35Norm,boundaryFullPowerScaled77_12_35Norm,boundaryFullPowerScaled77_13_35Norm,boundaryFullPowerScaled77_14_35Norm,boundaryFullPowerScaled77_15_35Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_35Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 35)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_35Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_35Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_35Chunk16=boundaryPowerBernstein77_17_35Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_35Chunk16]

    rw [boundaryFullPowerScaled77_16_35Norm.property,boundaryFullPowerScaled77_17_35Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_35Norm,boundaryFullPowerScaled77_17_35Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_35Norm : {c : ℝ // boundaryFullCoefficient77 17 35=c} := by

  have he : boundaryFullCoefficient77 17 35=((boundaryPowerBernstein77_17_35Chunk0) + ((boundaryPowerBernstein77_17_35Chunk8) + (boundaryPowerBernstein77_17_35Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_35Chunk0,boundaryPowerBernstein77_17_35Chunk8,boundaryPowerBernstein77_17_35Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_35Chunk0Norm.property,boundaryPowerBernstein77_17_35Chunk8Norm.property,boundaryPowerBernstein77_17_35Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_35Chunk0Norm,boundaryPowerBernstein77_17_35Chunk8Norm,boundaryPowerBernstein77_17_35Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




def boundaryPowerBernstein77_17_36Chunk0 : ℝ :=
  ((((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 0 17) + (boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 1 17)) + ((boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 2 17) + (boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 3 17))) + (((boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 4 17) + (boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 5 17)) + ((boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 6 17) + (boundaryH77^7*boundaryFullPowerRow77 7 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 7 17))))

def boundaryPowerBernstein77_17_36Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_17_36Chunk0=c} := by

  have he : boundaryPowerBernstein77_17_36Chunk0=boundaryPowerBernstein77_17_36Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_36Chunk0]

    rw [boundaryFullPowerScaled77_0_36Norm.property,boundaryFullPowerScaled77_1_36Norm.property,boundaryFullPowerScaled77_2_36Norm.property,boundaryFullPowerScaled77_3_36Norm.property,boundaryFullPowerScaled77_4_36Norm.property,boundaryFullPowerScaled77_5_36Norm.property,boundaryFullPowerScaled77_6_36Norm.property,boundaryFullPowerScaled77_7_36Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_36Norm,boundaryFullPowerScaled77_1_36Norm,boundaryFullPowerScaled77_2_36Norm,boundaryFullPowerScaled77_3_36Norm,boundaryFullPowerScaled77_4_36Norm,boundaryFullPowerScaled77_5_36Norm,boundaryFullPowerScaled77_6_36Norm,boundaryFullPowerScaled77_7_36Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_36Chunk8 : ℝ :=
  ((((boundaryH77^8*boundaryFullPowerRow77 8 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 8 17) + (boundaryH77^9*boundaryFullPowerRow77 9 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 9 17)) + ((boundaryH77^10*boundaryFullPowerRow77 10 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 10 17) + (boundaryH77^11*boundaryFullPowerRow77 11 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 11 17))) + (((boundaryH77^12*boundaryFullPowerRow77 12 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 12 17) + (boundaryH77^13*boundaryFullPowerRow77 13 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 13 17)) + ((boundaryH77^14*boundaryFullPowerRow77 14 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 14 17) + (boundaryH77^15*boundaryFullPowerRow77 15 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 15 17))))

def boundaryPowerBernstein77_17_36Chunk8Norm : {c : ℝ // boundaryPowerBernstein77_17_36Chunk8=c} := by

  have he : boundaryPowerBernstein77_17_36Chunk8=boundaryPowerBernstein77_17_36Chunk8 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_36Chunk8]

    rw [boundaryFullPowerScaled77_8_36Norm.property,boundaryFullPowerScaled77_9_36Norm.property,boundaryFullPowerScaled77_10_36Norm.property,boundaryFullPowerScaled77_11_36Norm.property,boundaryFullPowerScaled77_12_36Norm.property,boundaryFullPowerScaled77_13_36Norm.property,boundaryFullPowerScaled77_14_36Norm.property,boundaryFullPowerScaled77_15_36Norm.property]

    dsimp only [boundaryFullPowerScaled77_8_36Norm,boundaryFullPowerScaled77_9_36Norm,boundaryFullPowerScaled77_10_36Norm,boundaryFullPowerScaled77_11_36Norm,boundaryFullPowerScaled77_12_36Norm,boundaryFullPowerScaled77_13_36Norm,boundaryFullPowerScaled77_14_36Norm,boundaryFullPowerScaled77_15_36Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_36Chunk16 : ℝ :=
  ((boundaryH77^16*boundaryFullPowerRow77 16 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 16 17) + (boundaryH77^17*boundaryFullPowerRow77 17 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 17 17))

def boundaryPowerBernstein77_17_36Chunk16Norm : {c : ℝ // boundaryPowerBernstein77_17_36Chunk16=c} := by

  have he : boundaryPowerBernstein77_17_36Chunk16=boundaryPowerBernstein77_17_36Chunk16 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_17_36Chunk16]

    rw [boundaryFullPowerScaled77_16_36Norm.property,boundaryFullPowerScaled77_17_36Norm.property]

    dsimp only [boundaryFullPowerScaled77_16_36Norm,boundaryFullPowerScaled77_17_36Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_17_36Norm : {c : ℝ // boundaryFullCoefficient77 17 36=c} := by

  have he : boundaryFullCoefficient77 17 36=((boundaryPowerBernstein77_17_36Chunk0) + ((boundaryPowerBernstein77_17_36Chunk8) + (boundaryPowerBernstein77_17_36Chunk16))) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 17 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_17_36Chunk0,boundaryPowerBernstein77_17_36Chunk8,boundaryPowerBernstein77_17_36Chunk16]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_17_36Chunk0Norm.property,boundaryPowerBernstein77_17_36Chunk8Norm.property,boundaryPowerBernstein77_17_36Chunk16Norm.property]

    dsimp only [boundaryPowerBernstein77_17_36Chunk0Norm,boundaryPowerBernstein77_17_36Chunk8Norm,boundaryPowerBernstein77_17_36Chunk16Norm]

    norm_num

  exact ⟨_,he⟩




end

end HTGeometry.ThetaRatioInfinity
