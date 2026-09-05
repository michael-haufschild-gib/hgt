import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaRegionIFlowBounds
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaRegionIIFlowBounds
import Mathlib.Tactic

/-!
# Node-free Jacobi NLS waves and sharp intensity bands

The curvature-density bounds transfer literally to the squared norm of the complex traveling NLS
solutions.  Both physical branches are globally node-free, with sharp chamber-dependent intensity
bands and exact center/endpoint values.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

theorem correctedJacobiNLS_intensity_pos
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t s : ℝ) :
    0 < ‖(travelingPolarJet (correctedJacobiPolarProfile k₀ P J)
      (physicalJacobiWaveSpeed D k₀ P)).u t s‖ ^ 2 := by
  rw [correctedJacobiNLS_normSq_eq_travelingDensity,
    correctedJacobiTravelingDensity_eq_curvature_sq]
  exact sq_pos_of_pos (physicalJacobiCurvature_pos k₀ P J _)

theorem correctedJacobiNLS_ne_zero
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t s : ℝ) :
    (travelingPolarJet (correctedJacobiPolarProfile k₀ P J)
      (physicalJacobiWaveSpeed D k₀ P)).u t s ≠ 0 := by
  intro hzero
  have hpos := correctedJacobiNLS_intensity_pos D k₀ P J t s
  norm_num [hzero] at hpos

theorem regionIINLS_intensity_pos
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (t s : ℝ) :
    0 < ‖(travelingPolarJet (regionIIPhysicalPolarProfile k₀ P J)
      (regionIIPhysicalWaveSpeed D k₀ P)).u t s‖ ^ 2 := by
  rw [regionIINLS_normSq_eq_density, regionIIPhysicalDensity,
    compiledTravelingDensity_eq_curvature_sq]
  exact sq_pos_of_pos (regionIIPhysicalCurvature_pos k₀ P J _)

theorem regionIINLS_ne_zero
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (t s : ℝ) :
    (travelingPolarJet (regionIIPhysicalPolarProfile k₀ P J)
      (regionIIPhysicalWaveSpeed D k₀ P)).u t s ≠ 0 := by
  intro hzero
  have hpos := regionIINLS_intensity_pos D k₀ P J t s
  norm_num [hzero] at hpos

theorem regionINonnegativeNLS_intensity_bounds
    (D : ℝˣ) (k₀ : PositiveCurvatureScale)
    (P : PhysicalRegionINonnegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) (t s : ℝ) :
    (k₀ : ℝ) ^ 2 * regionIAmplitudeEndpoint P.val ≤
        ‖(travelingPolarJet (correctedJacobiPolarProfile k₀ P.val J)
          (physicalJacobiWaveSpeed D k₀ P.val)).u t s‖ ^ 2 ∧
      ‖(travelingPolarJet (correctedJacobiPolarProfile k₀ P.val J)
          (physicalJacobiWaveSpeed D k₀ P.val)).u t s‖ ^ 2 ≤ (k₀ : ℝ) ^ 2 := by
  rw [correctedJacobiNLS_normSq_eq_travelingDensity]
  exact ⟨regionINonnegativeDensity_lower D k₀ P J t s,
    regionINonnegativeDensity_upper D k₀ P J t s⟩

theorem regionINegativeNLS_intensity_bounds
    (D : ℝˣ) (k₀ : PositiveCurvatureScale)
    (P : PhysicalRegionINegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) (t s : ℝ) :
    (k₀ : ℝ) ^ 2 ≤
        ‖(travelingPolarJet (correctedJacobiPolarProfile k₀ P.val J)
          (physicalJacobiWaveSpeed D k₀ P.val)).u t s‖ ^ 2 ∧
      ‖(travelingPolarJet (correctedJacobiPolarProfile k₀ P.val J)
          (physicalJacobiWaveSpeed D k₀ P.val)).u t s‖ ^ 2 ≤
        (k₀ : ℝ) ^ 2 * regionIAmplitudeEndpoint P.val := by
  rw [correctedJacobiNLS_normSq_eq_travelingDensity]
  exact ⟨regionINegativeDensity_lower D k₀ P J t s,
    regionINegativeDensity_upper D k₀ P J t s⟩

theorem regionIINLS_intensity_bounds
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (t s : ℝ) :
    (k₀ : ℝ) ^ 2 ≤
        ‖(travelingPolarJet (regionIIPhysicalPolarProfile k₀ P J)
          (regionIIPhysicalWaveSpeed D k₀ P)).u t s‖ ^ 2 ∧
      ‖(travelingPolarJet (regionIIPhysicalPolarProfile k₀ P J)
          (regionIIPhysicalWaveSpeed D k₀ P)).u t s‖ ^ 2 ≤
        (k₀ : ℝ) ^ 2 * regionIIAmplitudeUpper P := by
  rw [regionIINLS_normSq_eq_density]
  exact ⟨regionIIPhysicalDensity_lower D k₀ P J t s,
    by simpa only [regionIIAmplitudeUpper] using regionIIPhysicalDensity_upper D k₀ P J t s⟩

theorem correctedJacobiNLS_intensity_center
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t : ℝ) :
    ‖(travelingPolarJet (correctedJacobiPolarProfile k₀ P J)
        (physicalJacobiWaveSpeed D k₀ P)).u t (physicalJacobiWaveSpeed D k₀ P * t)‖ ^ 2 =
      (k₀ : ℝ) ^ 2 := by
  rw [correctedJacobiNLS_normSq_eq_travelingDensity,
    correctedJacobiDensity_at_center]

theorem correctedJacobiNLS_intensity_peak
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (x : JacobiSnPeakPoint J) (t : ℝ) :
    ‖(travelingPolarJet (correctedJacobiPolarProfile k₀ P J)
        (physicalJacobiWaveSpeed D k₀ P)).u t (regionITravelingPeakPosition D k₀ P J x t)‖ ^ 2 =
      (k₀ : ℝ) ^ 2 * regionIAmplitudeEndpoint P := by
  rw [correctedJacobiNLS_normSq_eq_travelingDensity,
    correctedJacobiDensity_at_peak]

theorem regionIINLS_intensity_center
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (t : ℝ) :
    ‖(travelingPolarJet (regionIIPhysicalPolarProfile k₀ P J)
        (regionIIPhysicalWaveSpeed D k₀ P)).u t (regionIIPhysicalWaveSpeed D k₀ P * t)‖ ^ 2 =
      (k₀ : ℝ) ^ 2 := by
  rw [regionIINLS_normSq_eq_density, regionIIPhysicalDensity,
    regionIIPhysicalWaveSpeed_eq_compiled D k₀ P J,
    compiledTravelingDensity_eq_amplitude_sq, sub_self, compiledArgument, mul_zero]
  change (k₀ : ℝ) ^ 2 * regionIIJacobiAmplitude P J 0 ^ 2 = (k₀ : ℝ) ^ 2
  rw [regionIIJacobiAmplitude_zero]
  ring

theorem regionIINLS_intensity_peak
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ))
    (x : JacobiSnPeakPoint J) (t : ℝ) :
    ‖(travelingPolarJet (regionIIPhysicalPolarProfile k₀ P J)
        (regionIIPhysicalWaveSpeed D k₀ P)).u t
          (regionIITravelingPeakPosition D k₀ P J x t)‖ ^ 2 =
      (k₀ : ℝ) ^ 2 * regionIIAmplitudeUpper P := by
  rw [regionIINLS_normSq_eq_density, regionIIPhysicalDensity_at_peak]

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
