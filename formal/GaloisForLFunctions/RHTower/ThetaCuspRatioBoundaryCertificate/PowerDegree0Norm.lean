import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree0Columns

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullPowerRow77Degree0Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullPowerRow77 0 x=c} := by

  have he : boundaryFullPowerRow77 0 x=boundaryFullPowerRow77 0 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryFullPowerRow77]

    rw [(boundaryRePowerRow77_0Degree0Norm x).property,
      (boundaryRePowerRow77_1Degree0Norm x).property,
      (boundaryRePowerRow77_2Degree0Norm x).property,
      (boundaryRePowerRow77_3Degree0Norm x).property,
      (boundaryRePowerRow77_4Degree0Norm x).property,
      (boundaryRePowerRow77_5Degree0Norm x).property,
      (boundaryRePowerRow77_6Degree0Norm x).property,
      (boundaryRePowerRow77_7Degree0Norm x).property,
      (boundaryRePowerRow77_8Degree0Norm x).property,
      (boundaryRePowerRow77_9Degree0Norm x).property,
      (boundaryRePowerRow77_10Degree0Norm x).property,
      (boundaryRePowerRow77_11Degree0Norm x).property,
      (boundaryRePowerRow77_12Degree0Norm x).property,
      (boundaryRePowerRow77_13Degree0Norm x).property,
      (boundaryRePowerRow77_14Degree0Norm x).property,
      (boundaryRePowerRow77_15Degree0Norm x).property,
      (boundaryRePowerRow77_16Degree0Norm x).property,
      (boundaryRePowerRow77_17Degree0Norm x).property,
      (boundaryRePowerRow77_18Degree0Norm x).property,
      (boundaryRePowerRow77_19Degree0Norm x).property,
      (boundaryRePowerRow77_20Degree0Norm x).property,
      (boundaryRePowerRow77_21Degree0Norm x).property,
      (boundaryRePowerRow77_22Degree0Norm x).property,
      (boundaryImPowerRow77_0Degree0Norm x).property,
      (boundaryImPowerRow77_1Degree0Norm x).property,
      (boundaryImPowerRow77_2Degree0Norm x).property,
      (boundaryImPowerRow77_3Degree0Norm x).property,
      (boundaryImPowerRow77_4Degree0Norm x).property,
      (boundaryImPowerRow77_5Degree0Norm x).property,
      (boundaryImPowerRow77_6Degree0Norm x).property,
      (boundaryImPowerRow77_7Degree0Norm x).property,
      (boundaryImPowerRow77_8Degree0Norm x).property,
      (boundaryImPowerRow77_9Degree0Norm x).property,
      (boundaryImPowerRow77_10Degree0Norm x).property,
      (boundaryImPowerRow77_11Degree0Norm x).property,
      (boundaryImPowerRow77_12Degree0Norm x).property,
      (boundaryImPowerRow77_13Degree0Norm x).property,
      (boundaryImPowerRow77_14Degree0Norm x).property,
      (boundaryImPowerRow77_15Degree0Norm x).property,
      (boundaryImPowerRow77_16Degree0Norm x).property,
      (boundaryImPowerRow77_17Degree0Norm x).property,
      (boundaryImPowerRow77_18Degree0Norm x).property,
      (boundaryImPowerRow77_19Degree0Norm x).property,
      (boundaryImPowerRow77_20Degree0Norm x).property,
      (boundaryImPowerRow77_21Degree0Norm x).property,
      (boundaryLowPowerRow77Degree0Norm x).property]

    dsimp only [boundaryRePowerRow77_0Degree0Norm,boundaryRePowerRow77_1Degree0Norm,boundaryRePowerRow77_2Degree0Norm,boundaryRePowerRow77_3Degree0Norm,boundaryRePowerRow77_4Degree0Norm,boundaryRePowerRow77_5Degree0Norm,boundaryRePowerRow77_6Degree0Norm,boundaryRePowerRow77_7Degree0Norm,boundaryRePowerRow77_8Degree0Norm,boundaryRePowerRow77_9Degree0Norm,boundaryRePowerRow77_10Degree0Norm,boundaryRePowerRow77_11Degree0Norm,boundaryRePowerRow77_12Degree0Norm,boundaryRePowerRow77_13Degree0Norm,boundaryRePowerRow77_14Degree0Norm,boundaryRePowerRow77_15Degree0Norm,boundaryRePowerRow77_16Degree0Norm,boundaryRePowerRow77_17Degree0Norm,boundaryRePowerRow77_18Degree0Norm,boundaryRePowerRow77_19Degree0Norm,boundaryRePowerRow77_20Degree0Norm,boundaryRePowerRow77_21Degree0Norm,boundaryRePowerRow77_22Degree0Norm,boundaryImPowerRow77_0Degree0Norm,boundaryImPowerRow77_1Degree0Norm,boundaryImPowerRow77_2Degree0Norm,boundaryImPowerRow77_3Degree0Norm,boundaryImPowerRow77_4Degree0Norm,boundaryImPowerRow77_5Degree0Norm,boundaryImPowerRow77_6Degree0Norm,boundaryImPowerRow77_7Degree0Norm,boundaryImPowerRow77_8Degree0Norm,boundaryImPowerRow77_9Degree0Norm,boundaryImPowerRow77_10Degree0Norm,boundaryImPowerRow77_11Degree0Norm,boundaryImPowerRow77_12Degree0Norm,boundaryImPowerRow77_13Degree0Norm,boundaryImPowerRow77_14Degree0Norm,boundaryImPowerRow77_15Degree0Norm,boundaryImPowerRow77_16Degree0Norm,boundaryImPowerRow77_17Degree0Norm,boundaryImPowerRow77_18Degree0Norm,boundaryImPowerRow77_19Degree0Norm,boundaryImPowerRow77_20Degree0Norm,boundaryImPowerRow77_21Degree0Norm,boundaryLowPowerRow77Degree0Norm]

    ring_nf

  exact ⟨_,he⟩



end

end HTGeometry.ThetaRatioInfinity
