import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaQuantumStressBounds
import Mathlib.Tactic

/-!
# Transported turning points of compiled elastica waves

A dimensionless amplitude turning point transports with the traveling wave.  At that spacetime
curve, density, velocity, quantum stress, and momentum flux all have zero spatial derivative; the
corresponding traveling time derivatives and hydrodynamic acceleration force vanish as well.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

structure AmplitudeTurningPoint (E : PositiveAmplitudeOscillator) where
  val : ℝ
  velocity_zero : E.amplitude₁ val = 0

noncomputable def compiledTurningPosition
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator)
    (x : AmplitudeTurningPoint E) (t : ℝ) : ℝ :=
  compiledWaveSpeed D k₀ E * t + x.val / compiledArclengthScale k₀ E

theorem compiledTurning_comovingCoordinate
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator)
    (x : AmplitudeTurningPoint E) (t : ℝ) :
    compiledTurningPosition D k₀ E x t - compiledWaveSpeed D k₀ E * t =
      x.val / compiledArclengthScale k₀ E := by
  rw [compiledTurningPosition]
  ring

theorem compiledTurning_argument
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator)
    (x : AmplitudeTurningPoint E) (t : ℝ) :
    compiledArgument k₀ E
        (compiledTurningPosition D k₀ E x t - compiledWaveSpeed D k₀ E * t) = x.val := by
  rw [compiledTurning_comovingCoordinate, compiledArgument]
  field_simp [ne_of_gt (compiledArclengthScale_pos k₀ E)]

theorem compiledCurvatureVelocity_at_turning
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator)
    (x : AmplitudeTurningPoint E) (t : ℝ) :
    compiledCurvatureVelocity k₀ E
      (compiledTurningPosition D k₀ E x t - compiledWaveSpeed D k₀ E * t) = 0 := by
  rw [compiledCurvatureVelocity, compiledTurning_argument, x.velocity_zero]
  ring

theorem compiledDensityX_at_turning
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator)
    (x : AmplitudeTurningPoint E) (t : ℝ) :
    travelingDensityX (compiledCurvatureProfileJet k₀ E) (compiledWaveSpeed D k₀ E) t
      (compiledTurningPosition D k₀ E x t) = 0 := by
  rw [travelingDensityX]
  simp only [compiledCurvatureProfileJet]
  rw [compiledCurvatureVelocity_at_turning]
  ring

theorem compiledDensityT_at_turning
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator)
    (x : AmplitudeTurningPoint E) (t : ℝ) :
    travelingDensityT (compiledCurvatureProfileJet k₀ E) (compiledWaveSpeed D k₀ E) t
      (compiledTurningPosition D k₀ E x t) = 0 := by
  rw [travelingDensityT]
  simp only [compiledCurvatureProfileJet]
  rw [compiledCurvatureVelocity_at_turning]
  ring

theorem compiledHydroVelocityX_at_turning
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator)
    (x : AmplitudeTurningPoint E) (t : ℝ) :
    travelingHydroVelocityX (D : ℝ) (k₀ : ℝ) (compiledTorsionScale k₀ E)
      (compiledWaveSpeed D k₀ E) (compiledCurvatureProfileJet k₀ E) t
      (compiledTurningPosition D k₀ E x t) = 0 := by
  rw [travelingHydroVelocityX]
  simp only [compiledCurvatureProfileJet]
  rw [compiledCurvatureVelocity_at_turning]
  ring

theorem compiledHydroVelocityT_at_turning
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator)
    (x : AmplitudeTurningPoint E) (t : ℝ) :
    travelingHydroVelocityT (D : ℝ) (k₀ : ℝ) (compiledTorsionScale k₀ E)
      (compiledWaveSpeed D k₀ E) (compiledCurvatureProfileJet k₀ E) t
      (compiledTurningPosition D k₀ E x t) = 0 := by
  rw [travelingHydroVelocityT]
  simp only [compiledCurvatureProfileJet]
  rw [compiledCurvatureVelocity_at_turning]
  ring

theorem compiledHydroAccelerationForce_at_turning
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator)
    (x : AmplitudeTurningPoint E) (t : ℝ) :
    travelingHydroAccelerationForce (D : ℝ) (k₀ : ℝ) (compiledTorsionScale k₀ E)
      (compiledWaveSpeed D k₀ E) (compiledCurvatureProfileJet k₀ E) t
      (compiledTurningPosition D k₀ E x t) = 0 := by
  rw [travelingHydroAccelerationForce]
  simp only [compiledCurvatureProfileJet]
  rw [compiledCurvatureVelocity_at_turning]
  ring

theorem compiledQuantumStressX_at_turning
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator)
    (x : AmplitudeTurningPoint E) (t : ℝ) :
    travelingQuantumStressX (D : ℝ) (k₀ : ℝ) (compiledTorsionScale k₀ E)
      (compiledWaveSpeed D k₀ E) (compiledCurvatureProfileJet k₀ E) t
      (compiledTurningPosition D k₀ E x t) = 0 := by
  rw [travelingQuantumStressX]
  simp only [compiledCurvatureProfileJet]
  rw [compiledCurvatureVelocity_at_turning]
  ring

theorem compiledMomentumDensityT_at_turning
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator)
    (x : AmplitudeTurningPoint E) (t : ℝ) :
    travelingMomentumDensityT (compiledCurvatureProfileJet k₀ E) (compiledWaveSpeed D k₀ E) t
      (compiledTurningPosition D k₀ E x t) = 0 := by
  rw [travelingMomentumDensityT, compiledDensityT_at_turning]
  ring

theorem compiledMomentumFluxX_at_turning
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator)
    (x : AmplitudeTurningPoint E) (t : ℝ) :
    travelingMomentumFluxX (D : ℝ) (k₀ : ℝ) (compiledTorsionScale k₀ E)
      (compiledWaveSpeed D k₀ E) (compiledCurvatureProfileJet k₀ E) t
      (compiledTurningPosition D k₀ E x t) = 0 := by
  rw [travelingMomentumFluxX, compiledDensityX_at_turning,
    compiledQuantumStressX_at_turning]
  ring

noncomputable def regionICenterTurningPoint
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) :
    AmplitudeTurningPoint (regionIAmplitudeOscillator P J) where
  val := 0
  velocity_zero := correctedJacobiAmplitudeVelocity_zero P J

theorem jacobiSnPeak_cn_zero {m : ℝ} (J : JacobiEllipticSystem m)
    (x : JacobiSnPeakPoint J) : J.cn x.val = 0 := by
  have hsq : J.cn x.val ^ 2 = 0 := by
    nlinarith [J.sn_sq_add_cn_sq x.val, x.sn_sq]
  exact sq_eq_zero_iff.mp hsq

theorem correctedJacobiAmplitudeVelocity_at_peak
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus)
    (x : JacobiSnPeakPoint J) : correctedJacobiAmplitudeVelocity P J x.val = 0 := by
  rw [correctedJacobiAmplitudeVelocity, jacobiSquaredCurvatureVelocity,
    jacobiSnPeak_cn_zero J x]
  ring

noncomputable def regionIPeakTurningPoint
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus)
    (x : JacobiSnPeakPoint J) : AmplitudeTurningPoint (regionIAmplitudeOscillator P J) where
  val := x.val
  velocity_zero := correctedJacobiAmplitudeVelocity_at_peak P J x

theorem regionIIJacobiAmplitudeVelocity_at_peak
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ))
    (x : JacobiSnPeakPoint J) : regionIIJacobiAmplitudeVelocity P J x.val = 0 := by
  rw [regionIIJacobiAmplitudeVelocity, regionIIJacobiSquaredCurvatureVelocity,
    sdSquaredCurvatureVelocity, jacobiSdVelocity, jacobiSnPeak_cn_zero J x]
  ring

noncomputable def regionIICenterTurningPoint
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) :
    AmplitudeTurningPoint (regionIIAmplitudeOscillator P J) where
  val := 0
  velocity_zero := regionIIJacobiAmplitudeVelocity_zero P J

noncomputable def regionIIPeakTurningPoint
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ))
    (x : JacobiSnPeakPoint J) : AmplitudeTurningPoint (regionIIAmplitudeOscillator P J) where
  val := x.val
  velocity_zero := regionIIJacobiAmplitudeVelocity_at_peak P J x

theorem regionICompiledPeakPosition_eq
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (x : JacobiSnPeakPoint J) (t : ℝ) :
    compiledTurningPosition D k₀ (regionIAmplitudeOscillator P J)
      (regionIPeakTurningPoint P J x) t = regionITravelingPeakPosition D k₀ P J x t := by
  rfl

theorem regionIICompiledPeakPosition_eq
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ))
    (x : JacobiSnPeakPoint J) (t : ℝ) :
    compiledTurningPosition D k₀ (regionIIAmplitudeOscillator P J)
      (regionIIPeakTurningPoint P J x) t = regionIITravelingPeakPosition D k₀ P J x t := by
  rfl

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
