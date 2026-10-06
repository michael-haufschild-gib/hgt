import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerTruncation

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree0Scaled

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree1Scaled

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree2Scaled

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree3Scaled

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree4Scaled

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree5Scaled

import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree6Scaled

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryPowerBernstein77_6_36Chunk0 : ℝ :=
  (((boundaryH77^0*boundaryFullPowerRow77 0 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 0 6) + ((boundaryH77^1*boundaryFullPowerRow77 1 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 1 6) + (boundaryH77^2*boundaryFullPowerRow77 2 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 2 6))) + (((boundaryH77^3*boundaryFullPowerRow77 3 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 3 6) + (boundaryH77^4*boundaryFullPowerRow77 4 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 4 6)) + ((boundaryH77^5*boundaryFullPowerRow77 5 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 5 6) + (boundaryH77^6*boundaryFullPowerRow77 6 (fun q => boundaryS77^q*degreeElevationCoefficient 36 q 36)*degreeElevationCoefficient 96 6 6))))

def boundaryPowerBernstein77_6_36Chunk0Norm : {c : ℝ // boundaryPowerBernstein77_6_36Chunk0=c} := by

  have he : boundaryPowerBernstein77_6_36Chunk0=boundaryPowerBernstein77_6_36Chunk0 := rfl

  conv at he =>

    rhs

    dsimp only [boundaryPowerBernstein77_6_36Chunk0]

    rw [boundaryFullPowerScaled77_0_36Norm.property,boundaryFullPowerScaled77_1_36Norm.property,boundaryFullPowerScaled77_2_36Norm.property,boundaryFullPowerScaled77_3_36Norm.property,boundaryFullPowerScaled77_4_36Norm.property,boundaryFullPowerScaled77_5_36Norm.property,boundaryFullPowerScaled77_6_36Norm.property]

    dsimp only [boundaryFullPowerScaled77_0_36Norm,boundaryFullPowerScaled77_1_36Norm,boundaryFullPowerScaled77_2_36Norm,boundaryFullPowerScaled77_3_36Norm,boundaryFullPowerScaled77_4_36Norm,boundaryFullPowerScaled77_5_36Norm,boundaryFullPowerScaled77_6_36Norm]

    norm_num [degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

  exact ⟨_,he⟩

def boundaryPowerBernstein77_6_36Norm : {c : ℝ // boundaryFullCoefficient77 6 36=c} := by

  have he : boundaryFullCoefficient77 6 36=(boundaryPowerBernstein77_6_36Chunk0) := by

    rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_power_rows_truncated 6 _ (by norm_num)]

    dsimp only [boundaryPowerBernstein77_6_36Chunk0]

    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]

    ac_rfl

  conv at he =>

    rhs

    rw [boundaryPowerBernstein77_6_36Chunk0Norm.property]

    dsimp only [boundaryPowerBernstein77_6_36Chunk0Norm]

    norm_num

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
