import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaCorrectedJacobiHydrodynamics
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaRegionIIBounds
import Mathlib.Tactic

/-!
# Sharp Region I amplitude and density bounds

Region I crosses the Jacobi modulus wall `m = 0`.  On the nonnegative side the wave is centered at
a curvature crest; on the negative side the same center becomes a trough.  Packaging the two
closed parameter chambers makes both conclusions unconditional Lean theorems.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

abbrev PhysicalRegionINonnegativeModulus :=
  {P : PhysicalRegionI // 0 ≤ P.val.modulus}

abbrev PhysicalRegionINegativeModulus :=
  {P : PhysicalRegionI // P.val.modulus < 0}

noncomputable def regionIAmplitudeEndpoint (P : PhysicalRegionI) : ℝ :=
  1 - P.val.modulus / (P.val.q₀ : ℝ)

theorem regionIAmplitudeEndpoint_pos (P : PhysicalRegionI) :
    0 < regionIAmplitudeEndpoint P := by
  rw [regionIAmplitudeEndpoint]
  have hq := P.property.1
  have hm := P.property.2.1
  apply sub_pos.mpr
  exact (div_lt_one hq).2 hm

theorem regionINonnegativeAmplitude_sq_lower
    (P : PhysicalRegionINonnegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) (x : ℝ) :
    regionIAmplitudeEndpoint P.val ≤ correctedJacobiAmplitude P.val J x ^ 2 := by
  rw [regionIAmplitudeEndpoint, correctedJacobiAmplitude_sq]
  have hc : 0 ≤ P.val.val.modulus / (P.val.val.q₀ : ℝ) :=
    div_nonneg P.property P.val.property.1.le
  have h := mul_nonneg hc (sub_nonneg.mpr (J.sn_sq_le_one x))
  nlinarith

theorem regionINonnegativeAmplitude_sq_upper
    (P : PhysicalRegionINonnegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) (x : ℝ) :
    correctedJacobiAmplitude P.val J x ^ 2 ≤ 1 := by
  rw [correctedJacobiAmplitude_sq]
  have hc : 0 ≤ P.val.val.modulus / (P.val.val.q₀ : ℝ) :=
    div_nonneg P.property P.val.property.1.le
  exact sub_le_self _ (mul_nonneg hc (sq_nonneg _))

theorem regionINegativeAmplitude_sq_lower
    (P : PhysicalRegionINegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) (x : ℝ) :
    1 ≤ correctedJacobiAmplitude P.val J x ^ 2 := by
  rw [correctedJacobiAmplitude_sq]
  have hc : P.val.val.modulus / (P.val.val.q₀ : ℝ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg P.property.le P.val.property.1.le
  have h := mul_nonpos_of_nonpos_of_nonneg hc (sq_nonneg (J.sn x))
  linarith

theorem regionINegativeAmplitude_sq_upper
    (P : PhysicalRegionINegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) (x : ℝ) :
    correctedJacobiAmplitude P.val J x ^ 2 ≤ regionIAmplitudeEndpoint P.val := by
  rw [regionIAmplitudeEndpoint, correctedJacobiAmplitude_sq]
  have hc : 0 ≤ -(P.val.val.modulus / (P.val.val.q₀ : ℝ)) := by
    exact neg_nonneg.mpr
      (div_nonpos_of_nonpos_of_nonneg P.property.le P.val.property.1.le)
  have h := mul_nonneg hc (sub_nonneg.mpr (J.sn_sq_le_one x))
  nlinarith

theorem correctedJacobiAmplitude_sq_at_sn_peak
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus)
    (x : JacobiSnPeakPoint J) :
    correctedJacobiAmplitude P J x.val ^ 2 = regionIAmplitudeEndpoint P := by
  rw [correctedJacobiAmplitude_sq, x.sn_sq, regionIAmplitudeEndpoint]
  ring

theorem regionINonnegativeDensity_lower
    (D : ℝˣ) (k₀ : PositiveCurvatureScale)
    (P : PhysicalRegionINonnegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) (t s : ℝ) :
    (k₀ : ℝ) ^ 2 * regionIAmplitudeEndpoint P.val ≤
      travelingDensity (correctedJacobiCurvatureProfileJet k₀ P.val J)
        (physicalJacobiWaveSpeed D k₀ P.val) t s := by
  rw [correctedJacobiTravelingDensity_eq_amplitude_sq]
  exact mul_le_mul_of_nonneg_left
    (regionINonnegativeAmplitude_sq_lower P J _) (sq_nonneg (k₀ : ℝ))

theorem regionINonnegativeDensity_upper
    (D : ℝˣ) (k₀ : PositiveCurvatureScale)
    (P : PhysicalRegionINonnegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) (t s : ℝ) :
    travelingDensity (correctedJacobiCurvatureProfileJet k₀ P.val J)
        (physicalJacobiWaveSpeed D k₀ P.val) t s ≤ (k₀ : ℝ) ^ 2 := by
  rw [correctedJacobiTravelingDensity_eq_amplitude_sq]
  have hA := regionINonnegativeAmplitude_sq_upper P J
    (physicalJacobiArgument k₀ P.val
      (s - physicalJacobiWaveSpeed D k₀ P.val * t))
  have hmul := mul_le_mul_of_nonneg_left hA (sq_nonneg (k₀ : ℝ))
  nlinarith

theorem regionINegativeDensity_lower
    (D : ℝˣ) (k₀ : PositiveCurvatureScale)
    (P : PhysicalRegionINegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) (t s : ℝ) :
    (k₀ : ℝ) ^ 2 ≤
      travelingDensity (correctedJacobiCurvatureProfileJet k₀ P.val J)
        (physicalJacobiWaveSpeed D k₀ P.val) t s := by
  rw [correctedJacobiTravelingDensity_eq_amplitude_sq]
  have hA := regionINegativeAmplitude_sq_lower P J
    (physicalJacobiArgument k₀ P.val
      (s - physicalJacobiWaveSpeed D k₀ P.val * t))
  have hmul := mul_le_mul_of_nonneg_left hA (sq_nonneg (k₀ : ℝ))
  nlinarith

theorem regionINegativeDensity_upper
    (D : ℝˣ) (k₀ : PositiveCurvatureScale)
    (P : PhysicalRegionINegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) (t s : ℝ) :
    travelingDensity (correctedJacobiCurvatureProfileJet k₀ P.val J)
        (physicalJacobiWaveSpeed D k₀ P.val) t s ≤
      (k₀ : ℝ) ^ 2 * regionIAmplitudeEndpoint P.val := by
  rw [correctedJacobiTravelingDensity_eq_amplitude_sq]
  exact mul_le_mul_of_nonneg_left
    (regionINegativeAmplitude_sq_upper P J _) (sq_nonneg (k₀ : ℝ))

theorem correctedJacobiDensity_at_center
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t : ℝ) :
    travelingDensity (correctedJacobiCurvatureProfileJet k₀ P J)
        (physicalJacobiWaveSpeed D k₀ P) t
        (physicalJacobiWaveSpeed D k₀ P * t) = (k₀ : ℝ) ^ 2 := by
  rw [correctedJacobiTravelingDensity_eq_amplitude_sq, sub_self,
    physicalJacobiArgument, mul_zero, correctedJacobiAmplitude_zero]
  ring

noncomputable def regionIPhysicalPeakLocation
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (x : JacobiSnPeakPoint J) : ℝ :=
  x.val / jacobiArclengthScale k₀ P

theorem regionIPhysicalPeak_argument
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (x : JacobiSnPeakPoint J) :
    physicalJacobiArgument k₀ P (regionIPhysicalPeakLocation k₀ P J x) = x.val := by
  rw [physicalJacobiArgument, regionIPhysicalPeakLocation]
  field_simp [ne_of_gt (jacobiArclengthScale_pos k₀ P)]

noncomputable def regionITravelingPeakPosition
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (x : JacobiSnPeakPoint J) (t : ℝ) : ℝ :=
  physicalJacobiWaveSpeed D k₀ P * t + regionIPhysicalPeakLocation k₀ P J x

theorem regionITravelingPeak_comovingCoordinate
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (x : JacobiSnPeakPoint J) (t : ℝ) :
    regionITravelingPeakPosition D k₀ P J x t - physicalJacobiWaveSpeed D k₀ P * t =
      regionIPhysicalPeakLocation k₀ P J x := by
  rw [regionITravelingPeakPosition]
  ring

theorem correctedJacobiDensity_at_peak
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (x : JacobiSnPeakPoint J) (t : ℝ) :
    travelingDensity (correctedJacobiCurvatureProfileJet k₀ P J)
        (physicalJacobiWaveSpeed D k₀ P) t
        (regionITravelingPeakPosition D k₀ P J x t) =
      (k₀ : ℝ) ^ 2 * regionIAmplitudeEndpoint P := by
  rw [correctedJacobiTravelingDensity_eq_amplitude_sq,
    regionITravelingPeak_comovingCoordinate, regionIPhysicalPeak_argument,
    correctedJacobiAmplitude_sq_at_sn_peak]

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
