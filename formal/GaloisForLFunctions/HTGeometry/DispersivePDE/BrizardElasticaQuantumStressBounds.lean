import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaRegionIFlowBounds
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaRegionIIFlowBounds
import Mathlib.Tactic

/-!
# Quantum-stress reciprocity and sharp Jacobi bounds

For every compiled oscillator the momentum equation's quantum stress is exactly reciprocal to
density.  The sharp Jacobi density bands therefore reverse into sharp stress bands.  Center and
`sn² = 1` endpoint values identify every equality case in Regions I and II.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

noncomputable def compiledTravelingQuantumStress
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator)
    (t s : ℝ) : ℝ :=
  travelingQuantumStress (D : ℝ) (k₀ : ℝ) (compiledTorsionScale k₀ E)
    (compiledWaveSpeed D k₀ E) (compiledCurvatureProfileJet k₀ E) t s

theorem compiledTravelingQuantumStress_eq
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator)
    (t s : ℝ) :
    compiledTravelingQuantumStress D k₀ E t s =
      (D : ℝ) ^ 2 * (k₀ : ℝ) ^ 4 * E.nu ^ 2 /
        E.amplitude (compiledArgument k₀ E (s - compiledWaveSpeed D k₀ E * t)) ^ 2 := by
  rw [compiledTravelingQuantumStress, travelingQuantumStress, compiledTorsionScale]
  change 4 * (D : ℝ) ^ 2 * (k₀ : ℝ) ^ 4 *
      ((k₀ : ℝ) * E.nu / 2) ^ 2 /
        compiledCurvature k₀ E (s - compiledWaveSpeed D k₀ E * t) ^ 2 = _
  rw [compiledCurvature]
  field_simp [ne_of_gt k₀.property,
    ne_of_gt (E.amplitude_pos
      (compiledArgument k₀ E (s - compiledWaveSpeed D k₀ E * t)))]
  ring

/-- Quantum stress times density is a spacetime-independent torsion charge. -/
theorem compiledQuantumStress_mul_density
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator)
    (t s : ℝ) :
    compiledTravelingQuantumStress D k₀ E t s *
        travelingDensity (compiledCurvatureProfileJet k₀ E)
          (compiledWaveSpeed D k₀ E) t s =
      (D : ℝ) ^ 2 * (k₀ : ℝ) ^ 6 * E.nu ^ 2 := by
  rw [compiledTravelingQuantumStress_eq, compiledTravelingDensity_eq_amplitude_sq]
  field_simp [ne_of_gt (E.amplitude_pos
    (compiledArgument k₀ E (s - compiledWaveSpeed D k₀ E * t)))]

theorem compiledTravelingQuantumStress_nonneg
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator)
    (t s : ℝ) : 0 ≤ compiledTravelingQuantumStress D k₀ E t s := by
  rw [compiledTravelingQuantumStress_eq]
  positivity

noncomputable def regionIQuantumStress
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t s : ℝ) : ℝ :=
  compiledTravelingQuantumStress D k₀ (regionIAmplitudeOscillator P J) t s

theorem regionIQuantumStress_eq
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t s : ℝ) :
    regionIQuantumStress D k₀ P J t s =
      (D : ℝ) ^ 2 * (k₀ : ℝ) ^ 4 * physicalNu P ^ 2 /
        correctedJacobiAmplitude P J
          (physicalJacobiArgument k₀ P (s - physicalJacobiWaveSpeed D k₀ P * t)) ^ 2 := by
  rw [regionIQuantumStress, compiledTravelingQuantumStress_eq]
  rfl

theorem regionIQuantumStress_mul_density
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t s : ℝ) :
    regionIQuantumStress D k₀ P J t s * regionIPhysicalDensity D k₀ P J t s =
      (D : ℝ) ^ 2 * (k₀ : ℝ) ^ 6 * physicalNu P ^ 2 := by
  rw [regionIQuantumStress, regionIPhysicalDensity]
  exact compiledQuantumStress_mul_density D k₀ (regionIAmplitudeOscillator P J) t s

noncomputable def regionIIQuantumStress
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (t s : ℝ) : ℝ :=
  compiledTravelingQuantumStress D k₀ (regionIIAmplitudeOscillator P J) t s

theorem regionIIQuantumStress_eq
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (t s : ℝ) :
    regionIIQuantumStress D k₀ P J t s =
      (D : ℝ) ^ 2 * (k₀ : ℝ) ^ 4 * regionIINu P ^ 2 /
        regionIIJacobiAmplitude P J
          (compiledArgument k₀ (regionIIAmplitudeOscillator P J)
            (s - regionIIPhysicalWaveSpeed D k₀ P * t)) ^ 2 := by
  rw [regionIIQuantumStress, compiledTravelingQuantumStress_eq,
    regionIIPhysicalWaveSpeed_eq_compiled D k₀ P J]
  rfl

theorem regionIIQuantumStress_mul_density
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (t s : ℝ) :
    regionIIQuantumStress D k₀ P J t s * regionIIPhysicalDensity D k₀ P J t s =
      (D : ℝ) ^ 2 * (k₀ : ℝ) ^ 6 * regionIINu P ^ 2 := by
  rw [regionIIQuantumStress, regionIIPhysicalDensity]
  exact compiledQuantumStress_mul_density D k₀ (regionIIAmplitudeOscillator P J) t s

theorem regionINonnegativeQuantumStress_lower
    (D : ℝˣ) (k₀ : PositiveCurvatureScale)
    (P : PhysicalRegionINonnegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) (t s : ℝ) :
    (D : ℝ) ^ 2 * (k₀ : ℝ) ^ 4 * physicalNu P.val ^ 2 ≤
      regionIQuantumStress D k₀ P.val J t s := by
  rw [regionIQuantumStress_eq]
  have hA := regionINonnegativeAmplitude_sq_upper P J
    (physicalJacobiArgument k₀ P.val (s - physicalJacobiWaveSpeed D k₀ P.val * t))
  have hApos : 0 < correctedJacobiAmplitude P.val J
      (physicalJacobiArgument k₀ P.val
        (s - physicalJacobiWaveSpeed D k₀ P.val * t)) ^ 2 :=
    sq_pos_of_pos (correctedJacobiAmplitude_pos P.val J _)
  have hc : 0 ≤ (D : ℝ) ^ 2 * (k₀ : ℝ) ^ 4 * physicalNu P.val ^ 2 := by positivity
  apply (le_div_iff₀ hApos).2
  nlinarith

theorem regionINonnegativeQuantumStress_upper
    (D : ℝˣ) (k₀ : PositiveCurvatureScale)
    (P : PhysicalRegionINonnegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) (t s : ℝ) :
    regionIQuantumStress D k₀ P.val J t s ≤
      (D : ℝ) ^ 2 * (k₀ : ℝ) ^ 4 * physicalNu P.val ^ 2 /
        regionIAmplitudeEndpoint P.val := by
  rw [regionIQuantumStress_eq]
  have hA := regionINonnegativeAmplitude_sq_lower P J
    (physicalJacobiArgument k₀ P.val (s - physicalJacobiWaveSpeed D k₀ P.val * t))
  have hApos : 0 < correctedJacobiAmplitude P.val J
      (physicalJacobiArgument k₀ P.val
        (s - physicalJacobiWaveSpeed D k₀ P.val * t)) ^ 2 :=
    sq_pos_of_pos (correctedJacobiAmplitude_pos P.val J _)
  have hBpos := regionIAmplitudeEndpoint_pos P.val
  have hc : 0 ≤ (D : ℝ) ^ 2 * (k₀ : ℝ) ^ 4 * physicalNu P.val ^ 2 := by positivity
  exact (div_le_div_iff₀ hApos hBpos).2 (mul_le_mul_of_nonneg_left hA hc)

theorem regionINegativeQuantumStress_lower
    (D : ℝˣ) (k₀ : PositiveCurvatureScale)
    (P : PhysicalRegionINegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) (t s : ℝ) :
    (D : ℝ) ^ 2 * (k₀ : ℝ) ^ 4 * physicalNu P.val ^ 2 /
        regionIAmplitudeEndpoint P.val ≤ regionIQuantumStress D k₀ P.val J t s := by
  rw [regionIQuantumStress_eq]
  have hA := regionINegativeAmplitude_sq_upper P J
    (physicalJacobiArgument k₀ P.val (s - physicalJacobiWaveSpeed D k₀ P.val * t))
  have hApos : 0 < correctedJacobiAmplitude P.val J
      (physicalJacobiArgument k₀ P.val
        (s - physicalJacobiWaveSpeed D k₀ P.val * t)) ^ 2 :=
    sq_pos_of_pos (correctedJacobiAmplitude_pos P.val J _)
  have hBpos := regionIAmplitudeEndpoint_pos P.val
  have hc : 0 ≤ (D : ℝ) ^ 2 * (k₀ : ℝ) ^ 4 * physicalNu P.val ^ 2 := by positivity
  exact (div_le_div_iff₀ hBpos hApos).2 (mul_le_mul_of_nonneg_left hA hc)

theorem regionINegativeQuantumStress_upper
    (D : ℝˣ) (k₀ : PositiveCurvatureScale)
    (P : PhysicalRegionINegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) (t s : ℝ) :
    regionIQuantumStress D k₀ P.val J t s ≤
      (D : ℝ) ^ 2 * (k₀ : ℝ) ^ 4 * physicalNu P.val ^ 2 := by
  rw [regionIQuantumStress_eq]
  have hA := regionINegativeAmplitude_sq_lower P J
    (physicalJacobiArgument k₀ P.val (s - physicalJacobiWaveSpeed D k₀ P.val * t))
  have hApos : 0 < correctedJacobiAmplitude P.val J
      (physicalJacobiArgument k₀ P.val
        (s - physicalJacobiWaveSpeed D k₀ P.val * t)) ^ 2 :=
    sq_pos_of_pos (correctedJacobiAmplitude_pos P.val J _)
  have hc : 0 ≤ (D : ℝ) ^ 2 * (k₀ : ℝ) ^ 4 * physicalNu P.val ^ 2 := by positivity
  apply (div_le_iff₀ hApos).2
  nlinarith

theorem regionIIQuantumStress_lower
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (t s : ℝ) :
    (D : ℝ) ^ 2 * (k₀ : ℝ) ^ 4 * regionIINu P ^ 2 / regionIIAmplitudeUpper P ≤
      regionIIQuantumStress D k₀ P J t s := by
  rw [regionIIQuantumStress_eq]
  have hA := regionIIJacobiAmplitude_sq_upper P J
    (compiledArgument k₀ (regionIIAmplitudeOscillator P J)
      (s - regionIIPhysicalWaveSpeed D k₀ P * t))
  rw [← regionIIAmplitudeUpper] at hA
  have hApos : 0 < regionIIJacobiAmplitude P J
      (compiledArgument k₀ (regionIIAmplitudeOscillator P J)
        (s - regionIIPhysicalWaveSpeed D k₀ P * t)) ^ 2 :=
    sq_pos_of_pos (regionIIJacobiAmplitude_pos P J _)
  have hBpos := regionIIAmplitudeUpper_pos P
  have hc : 0 ≤ (D : ℝ) ^ 2 * (k₀ : ℝ) ^ 4 * regionIINu P ^ 2 := by positivity
  exact (div_le_div_iff₀ hBpos hApos).2 (mul_le_mul_of_nonneg_left hA hc)

theorem regionIIQuantumStress_upper
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (t s : ℝ) :
    regionIIQuantumStress D k₀ P J t s ≤
      (D : ℝ) ^ 2 * (k₀ : ℝ) ^ 4 * regionIINu P ^ 2 := by
  rw [regionIIQuantumStress_eq]
  have hA := regionIIJacobiAmplitude_sq_lower P J
    (compiledArgument k₀ (regionIIAmplitudeOscillator P J)
      (s - regionIIPhysicalWaveSpeed D k₀ P * t))
  have hApos : 0 < regionIIJacobiAmplitude P J
      (compiledArgument k₀ (regionIIAmplitudeOscillator P J)
        (s - regionIIPhysicalWaveSpeed D k₀ P * t)) ^ 2 :=
    sq_pos_of_pos (regionIIJacobiAmplitude_pos P J _)
  have hc : 0 ≤ (D : ℝ) ^ 2 * (k₀ : ℝ) ^ 4 * regionIINu P ^ 2 := by positivity
  apply (div_le_iff₀ hApos).2
  nlinarith

theorem regionIQuantumStress_at_center
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t : ℝ) :
    regionIQuantumStress D k₀ P J t (physicalJacobiWaveSpeed D k₀ P * t) =
      (D : ℝ) ^ 2 * (k₀ : ℝ) ^ 4 * physicalNu P ^ 2 := by
  rw [regionIQuantumStress_eq, sub_self, physicalJacobiArgument, mul_zero,
    correctedJacobiAmplitude_zero]
  ring

theorem regionIQuantumStress_at_peak
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (x : JacobiSnPeakPoint J) (t : ℝ) :
    regionIQuantumStress D k₀ P J t (regionITravelingPeakPosition D k₀ P J x t) =
      (D : ℝ) ^ 2 * (k₀ : ℝ) ^ 4 * physicalNu P ^ 2 /
        regionIAmplitudeEndpoint P := by
  rw [regionIQuantumStress_eq, regionITravelingPeak_comovingCoordinate,
    regionIPhysicalPeak_argument, correctedJacobiAmplitude_sq_at_sn_peak]

theorem regionIIQuantumStress_at_center
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (t : ℝ) :
    regionIIQuantumStress D k₀ P J t (regionIIPhysicalWaveSpeed D k₀ P * t) =
      (D : ℝ) ^ 2 * (k₀ : ℝ) ^ 4 * regionIINu P ^ 2 := by
  rw [regionIIQuantumStress_eq, sub_self, compiledArgument, mul_zero,
    regionIIJacobiAmplitude_zero]
  ring

theorem regionIIQuantumStress_at_peak
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ))
    (x : JacobiSnPeakPoint J) (t : ℝ) :
    regionIIQuantumStress D k₀ P J t (regionIITravelingPeakPosition D k₀ P J x t) =
      (D : ℝ) ^ 2 * (k₀ : ℝ) ^ 4 * regionIINu P ^ 2 /
        regionIIAmplitudeUpper P := by
  rw [regionIIQuantumStress_eq, regionIITravelingPeak_comovingCoordinate,
    regionIIPhysicalPeak_argument, regionIIJacobiAmplitude_sq_at_peak,
    ← regionIIAmplitudeUpper]

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
