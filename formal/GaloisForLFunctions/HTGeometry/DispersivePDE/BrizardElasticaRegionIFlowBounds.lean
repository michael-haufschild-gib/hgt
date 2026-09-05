import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaRegionIBounds
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaRegionIIFlowBounds
import Mathlib.Tactic

/-!
# Sharp Region I phase, velocity, and current bounds

The inverse-square torsion term reverses the Region I density ordering.  Thus the `m ≥ 0` center
is densest but slowest, while the `m < 0` center is least dense but fastest.  The Galilean mass
current instead follows density because its variable part is a positive multiple of density.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

noncomputable def regionIPhysicalDensity
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t s : ℝ) : ℝ :=
  travelingDensity (correctedJacobiCurvatureProfileJet k₀ P J)
    (physicalJacobiWaveSpeed D k₀ P) t s

noncomputable def regionIPhysicalFluidVelocity
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t s : ℝ) : ℝ :=
  travelingHydroVelocity (D : ℝ) (k₀ : ℝ) (physicalJacobiTorsionScale k₀ P)
    (physicalJacobiWaveSpeed D k₀ P) (correctedJacobiCurvatureProfileJet k₀ P J) t s

noncomputable def regionIPhysicalMassCurrent
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t s : ℝ) : ℝ :=
  travelingMassCurrent (D : ℝ) (k₀ : ℝ) (physicalJacobiTorsionScale k₀ P)
    (physicalJacobiWaveSpeed D k₀ P) (correctedJacobiCurvatureProfileJet k₀ P J) t s

theorem regionIPhysicalDensity_eq
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t s : ℝ) :
    regionIPhysicalDensity D k₀ P J t s =
      (k₀ : ℝ) ^ 2 * correctedJacobiAmplitude P J
        (physicalJacobiArgument k₀ P (s - physicalJacobiWaveSpeed D k₀ P * t)) ^ 2 := by
  rw [regionIPhysicalDensity, correctedJacobiTravelingDensity_eq_amplitude_sq]

theorem regionIPhysicalVelocity_eq_phaseSlope
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t s : ℝ) :
    regionIPhysicalFluidVelocity D k₀ P J t s =
      2 * (D : ℝ) * physicalJacobiPhaseSlope k₀ P J
        (s - physicalJacobiWaveSpeed D k₀ P * t) := by
  rw [regionIPhysicalFluidVelocity, correctedJacobiHydroVelocity_eq_phaseSlope]

theorem regionIPhysicalMassCurrent_eq
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t s : ℝ) :
    regionIPhysicalMassCurrent D k₀ P J t s =
      physicalJacobiWaveSpeed D k₀ P * regionIPhysicalDensity D k₀ P J t s +
        (D : ℝ) * (k₀ : ℝ) ^ 3 * physicalNu P := by
  rw [regionIPhysicalMassCurrent, regionIPhysicalDensity,
    correctedJacobiTravelingMassCurrent_eq]

theorem regionINonnegativePhaseSlope_lower
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionINonnegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) (s : ℝ) :
    (k₀ : ℝ) * (physicalGamma P.val + physicalNu P.val) / 2 ≤
      physicalJacobiPhaseSlope k₀ P.val J s := by
  rw [physicalJacobiPhaseSlope]
  have hb : 0 ≤ (k₀ : ℝ) * physicalNu P.val / 2 :=
    div_nonneg (mul_nonneg k₀.property.le (physicalNu_pos P.val).le) (by norm_num)
  have hA := regionINonnegativeAmplitude_sq_upper P J (physicalJacobiArgument k₀ P.val s)
  have hApos : 0 < correctedJacobiAmplitude P.val J
      (physicalJacobiArgument k₀ P.val s) ^ 2 :=
    sq_pos_of_pos (correctedJacobiAmplitude_pos P.val J _)
  have hdiv : (k₀ : ℝ) * physicalNu P.val / 2 ≤
      ((k₀ : ℝ) * physicalNu P.val / 2) /
        correctedJacobiAmplitude P.val J (physicalJacobiArgument k₀ P.val s) ^ 2 := by
    apply (le_div_iff₀ hApos).2
    nlinarith
  calc
    (k₀ : ℝ) * (physicalGamma P.val + physicalNu P.val) / 2 =
        (k₀ : ℝ) * physicalGamma P.val / 2 +
          (k₀ : ℝ) * physicalNu P.val / 2 := by ring
    _ ≤ (k₀ : ℝ) * physicalGamma P.val / 2 +
        ((k₀ : ℝ) * physicalNu P.val / 2) /
          correctedJacobiAmplitude P.val J (physicalJacobiArgument k₀ P.val s) ^ 2 :=
      add_le_add_left hdiv _

theorem regionINonnegativePhaseSlope_upper
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionINonnegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) (s : ℝ) :
    physicalJacobiPhaseSlope k₀ P.val J s ≤
      (k₀ : ℝ) *
        (physicalGamma P.val + physicalNu P.val / regionIAmplitudeEndpoint P.val) / 2 := by
  rw [physicalJacobiPhaseSlope]
  have hb : 0 ≤ (k₀ : ℝ) * physicalNu P.val / 2 :=
    div_nonneg (mul_nonneg k₀.property.le (physicalNu_pos P.val).le) (by norm_num)
  have hA := regionINonnegativeAmplitude_sq_lower P J (physicalJacobiArgument k₀ P.val s)
  have hApos : 0 < correctedJacobiAmplitude P.val J
      (physicalJacobiArgument k₀ P.val s) ^ 2 :=
    sq_pos_of_pos (correctedJacobiAmplitude_pos P.val J _)
  have hBpos := regionIAmplitudeEndpoint_pos P.val
  have hdiv := (div_le_div_iff₀ hApos hBpos).2
    (mul_le_mul_of_nonneg_left hA hb)
  calc
    (k₀ : ℝ) * physicalGamma P.val / 2 +
        ((k₀ : ℝ) * physicalNu P.val / 2) /
          correctedJacobiAmplitude P.val J (physicalJacobiArgument k₀ P.val s) ^ 2 ≤
      (k₀ : ℝ) * physicalGamma P.val / 2 +
        ((k₀ : ℝ) * physicalNu P.val / 2) / regionIAmplitudeEndpoint P.val :=
      add_le_add_left hdiv _
    _ = (k₀ : ℝ) *
        (physicalGamma P.val + physicalNu P.val / regionIAmplitudeEndpoint P.val) / 2 := by ring

theorem regionINegativePhaseSlope_lower
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionINegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) (s : ℝ) :
    (k₀ : ℝ) *
        (physicalGamma P.val + physicalNu P.val / regionIAmplitudeEndpoint P.val) / 2 ≤
      physicalJacobiPhaseSlope k₀ P.val J s := by
  rw [physicalJacobiPhaseSlope]
  have hb : 0 ≤ (k₀ : ℝ) * physicalNu P.val / 2 :=
    div_nonneg (mul_nonneg k₀.property.le (physicalNu_pos P.val).le) (by norm_num)
  have hA := regionINegativeAmplitude_sq_upper P J (physicalJacobiArgument k₀ P.val s)
  have hApos : 0 < correctedJacobiAmplitude P.val J
      (physicalJacobiArgument k₀ P.val s) ^ 2 :=
    sq_pos_of_pos (correctedJacobiAmplitude_pos P.val J _)
  have hBpos := regionIAmplitudeEndpoint_pos P.val
  have hdiv := (div_le_div_iff₀ hBpos hApos).2
    (mul_le_mul_of_nonneg_left hA hb)
  calc
    (k₀ : ℝ) *
        (physicalGamma P.val + physicalNu P.val / regionIAmplitudeEndpoint P.val) / 2 =
      (k₀ : ℝ) * physicalGamma P.val / 2 +
        ((k₀ : ℝ) * physicalNu P.val / 2) / regionIAmplitudeEndpoint P.val := by ring
    _ ≤ (k₀ : ℝ) * physicalGamma P.val / 2 +
        ((k₀ : ℝ) * physicalNu P.val / 2) /
          correctedJacobiAmplitude P.val J (physicalJacobiArgument k₀ P.val s) ^ 2 :=
      add_le_add_left hdiv _

theorem regionINegativePhaseSlope_upper
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionINegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) (s : ℝ) :
    physicalJacobiPhaseSlope k₀ P.val J s ≤
      (k₀ : ℝ) * (physicalGamma P.val + physicalNu P.val) / 2 := by
  rw [physicalJacobiPhaseSlope]
  have hb : 0 ≤ (k₀ : ℝ) * physicalNu P.val / 2 :=
    div_nonneg (mul_nonneg k₀.property.le (physicalNu_pos P.val).le) (by norm_num)
  have hA := regionINegativeAmplitude_sq_lower P J (physicalJacobiArgument k₀ P.val s)
  have hApos : 0 < correctedJacobiAmplitude P.val J
      (physicalJacobiArgument k₀ P.val s) ^ 2 :=
    sq_pos_of_pos (correctedJacobiAmplitude_pos P.val J _)
  have hdiv : ((k₀ : ℝ) * physicalNu P.val / 2) /
      correctedJacobiAmplitude P.val J (physicalJacobiArgument k₀ P.val s) ^ 2 ≤
      (k₀ : ℝ) * physicalNu P.val / 2 := by
    apply (div_le_iff₀ hApos).2
    nlinarith
  calc
    (k₀ : ℝ) * physicalGamma P.val / 2 +
        ((k₀ : ℝ) * physicalNu P.val / 2) /
          correctedJacobiAmplitude P.val J (physicalJacobiArgument k₀ P.val s) ^ 2 ≤
      (k₀ : ℝ) * physicalGamma P.val / 2 +
        (k₀ : ℝ) * physicalNu P.val / 2 := add_le_add_left hdiv _
    _ = (k₀ : ℝ) * (physicalGamma P.val + physicalNu P.val) / 2 := by ring

theorem regionINonnegativeFluidVelocity_lower
    (D : PositiveDispersionScale) (k₀ : PositiveCurvatureScale)
    (P : PhysicalRegionINonnegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) (t s : ℝ) :
    (D : ℝ) * (k₀ : ℝ) * (physicalGamma P.val + physicalNu P.val) ≤
      regionIPhysicalFluidVelocity (positiveDispersionUnit D) k₀ P.val J t s := by
  rw [regionIPhysicalVelocity_eq_phaseSlope]
  have h := regionINonnegativePhaseSlope_lower k₀ P J
    (s - physicalJacobiWaveSpeed (positiveDispersionUnit D) k₀ P.val * t)
  have hD : 0 ≤ 2 * (D : ℝ) := mul_nonneg (by norm_num) D.property.le
  have hm := mul_le_mul_of_nonneg_left h hD
  calc
    (D : ℝ) * (k₀ : ℝ) * (physicalGamma P.val + physicalNu P.val) =
        2 * (D : ℝ) *
          ((k₀ : ℝ) * (physicalGamma P.val + physicalNu P.val) / 2) := by ring
    _ ≤ 2 * (D : ℝ) * physicalJacobiPhaseSlope k₀ P.val J
        (s - physicalJacobiWaveSpeed (positiveDispersionUnit D) k₀ P.val * t) := hm

theorem regionINonnegativeFluidVelocity_upper
    (D : PositiveDispersionScale) (k₀ : PositiveCurvatureScale)
    (P : PhysicalRegionINonnegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) (t s : ℝ) :
    regionIPhysicalFluidVelocity (positiveDispersionUnit D) k₀ P.val J t s ≤
      (D : ℝ) * (k₀ : ℝ) *
        (physicalGamma P.val + physicalNu P.val / regionIAmplitudeEndpoint P.val) := by
  rw [regionIPhysicalVelocity_eq_phaseSlope]
  have h := regionINonnegativePhaseSlope_upper k₀ P J
    (s - physicalJacobiWaveSpeed (positiveDispersionUnit D) k₀ P.val * t)
  have hD : 0 ≤ 2 * (D : ℝ) := mul_nonneg (by norm_num) D.property.le
  have hm := mul_le_mul_of_nonneg_left h hD
  calc
    2 * (D : ℝ) * physicalJacobiPhaseSlope k₀ P.val J
        (s - physicalJacobiWaveSpeed (positiveDispersionUnit D) k₀ P.val * t) ≤
      2 * (D : ℝ) * ((k₀ : ℝ) *
        (physicalGamma P.val + physicalNu P.val / regionIAmplitudeEndpoint P.val) / 2) := hm
    _ = (D : ℝ) * (k₀ : ℝ) *
        (physicalGamma P.val + physicalNu P.val / regionIAmplitudeEndpoint P.val) := by ring

theorem regionINegativeFluidVelocity_lower
    (D : PositiveDispersionScale) (k₀ : PositiveCurvatureScale)
    (P : PhysicalRegionINegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) (t s : ℝ) :
    (D : ℝ) * (k₀ : ℝ) *
        (physicalGamma P.val + physicalNu P.val / regionIAmplitudeEndpoint P.val) ≤
      regionIPhysicalFluidVelocity (positiveDispersionUnit D) k₀ P.val J t s := by
  rw [regionIPhysicalVelocity_eq_phaseSlope]
  have h := regionINegativePhaseSlope_lower k₀ P J
    (s - physicalJacobiWaveSpeed (positiveDispersionUnit D) k₀ P.val * t)
  have hD : 0 ≤ 2 * (D : ℝ) := mul_nonneg (by norm_num) D.property.le
  have hm := mul_le_mul_of_nonneg_left h hD
  calc
    (D : ℝ) * (k₀ : ℝ) *
        (physicalGamma P.val + physicalNu P.val / regionIAmplitudeEndpoint P.val) =
      2 * (D : ℝ) * ((k₀ : ℝ) *
        (physicalGamma P.val + physicalNu P.val / regionIAmplitudeEndpoint P.val) / 2) := by ring
    _ ≤ 2 * (D : ℝ) * physicalJacobiPhaseSlope k₀ P.val J
        (s - physicalJacobiWaveSpeed (positiveDispersionUnit D) k₀ P.val * t) := hm

theorem regionINegativeFluidVelocity_upper
    (D : PositiveDispersionScale) (k₀ : PositiveCurvatureScale)
    (P : PhysicalRegionINegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) (t s : ℝ) :
    regionIPhysicalFluidVelocity (positiveDispersionUnit D) k₀ P.val J t s ≤
      (D : ℝ) * (k₀ : ℝ) * (physicalGamma P.val + physicalNu P.val) := by
  rw [regionIPhysicalVelocity_eq_phaseSlope]
  have h := regionINegativePhaseSlope_upper k₀ P J
    (s - physicalJacobiWaveSpeed (positiveDispersionUnit D) k₀ P.val * t)
  have hD : 0 ≤ 2 * (D : ℝ) := mul_nonneg (by norm_num) D.property.le
  have hm := mul_le_mul_of_nonneg_left h hD
  calc
    2 * (D : ℝ) * physicalJacobiPhaseSlope k₀ P.val J
        (s - physicalJacobiWaveSpeed (positiveDispersionUnit D) k₀ P.val * t) ≤
      2 * (D : ℝ) *
        ((k₀ : ℝ) * (physicalGamma P.val + physicalNu P.val) / 2) := hm
    _ = (D : ℝ) * (k₀ : ℝ) * (physicalGamma P.val + physicalNu P.val) := by ring

theorem regionINonnegativeMassCurrent_lower
    (D : PositiveDispersionScale) (k₀ : PositiveCurvatureScale)
    (P : PhysicalRegionINonnegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) (t s : ℝ) :
    (D : ℝ) * (k₀ : ℝ) ^ 3 *
        (physicalGamma P.val * regionIAmplitudeEndpoint P.val + physicalNu P.val) ≤
      regionIPhysicalMassCurrent (positiveDispersionUnit D) k₀ P.val J t s := by
  rw [regionIPhysicalMassCurrent_eq, physicalJacobiWaveSpeed]
  have hd := regionINonnegativeDensity_lower (positiveDispersionUnit D) k₀ P J t s
  have hc : 0 ≤ (D : ℝ) * (k₀ : ℝ) * physicalGamma P.val := by positivity
  have hm := mul_le_mul_of_nonneg_left hd hc
  simp only [positiveDispersionUnit_val]
  nlinarith

theorem regionINonnegativeMassCurrent_upper
    (D : PositiveDispersionScale) (k₀ : PositiveCurvatureScale)
    (P : PhysicalRegionINonnegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) (t s : ℝ) :
    regionIPhysicalMassCurrent (positiveDispersionUnit D) k₀ P.val J t s ≤
      (D : ℝ) * (k₀ : ℝ) ^ 3 * (physicalGamma P.val + physicalNu P.val) := by
  rw [regionIPhysicalMassCurrent_eq, physicalJacobiWaveSpeed]
  have hd := regionINonnegativeDensity_upper (positiveDispersionUnit D) k₀ P J t s
  have hc : 0 ≤ (D : ℝ) * (k₀ : ℝ) * physicalGamma P.val := by positivity
  have hm := mul_le_mul_of_nonneg_left hd hc
  simp only [positiveDispersionUnit_val]
  nlinarith

theorem regionINegativeMassCurrent_lower
    (D : PositiveDispersionScale) (k₀ : PositiveCurvatureScale)
    (P : PhysicalRegionINegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) (t s : ℝ) :
    (D : ℝ) * (k₀ : ℝ) ^ 3 * (physicalGamma P.val + physicalNu P.val) ≤
      regionIPhysicalMassCurrent (positiveDispersionUnit D) k₀ P.val J t s := by
  rw [regionIPhysicalMassCurrent_eq, physicalJacobiWaveSpeed]
  have hd := regionINegativeDensity_lower (positiveDispersionUnit D) k₀ P J t s
  have hc : 0 ≤ (D : ℝ) * (k₀ : ℝ) * physicalGamma P.val := by positivity
  have hm := mul_le_mul_of_nonneg_left hd hc
  simp only [positiveDispersionUnit_val]
  nlinarith

theorem regionINegativeMassCurrent_upper
    (D : PositiveDispersionScale) (k₀ : PositiveCurvatureScale)
    (P : PhysicalRegionINegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) (t s : ℝ) :
    regionIPhysicalMassCurrent (positiveDispersionUnit D) k₀ P.val J t s ≤
      (D : ℝ) * (k₀ : ℝ) ^ 3 *
        (physicalGamma P.val * regionIAmplitudeEndpoint P.val + physicalNu P.val) := by
  rw [regionIPhysicalMassCurrent_eq, physicalJacobiWaveSpeed]
  have hd := regionINegativeDensity_upper (positiveDispersionUnit D) k₀ P J t s
  have hc : 0 ≤ (D : ℝ) * (k₀ : ℝ) * physicalGamma P.val := by positivity
  have hm := mul_le_mul_of_nonneg_left hd hc
  simp only [positiveDispersionUnit_val]
  nlinarith

theorem regionIPhysicalFluidVelocity_at_center
    (D : PositiveDispersionScale) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t : ℝ) :
    regionIPhysicalFluidVelocity (positiveDispersionUnit D) k₀ P J t
        (physicalJacobiWaveSpeed (positiveDispersionUnit D) k₀ P * t) =
      (D : ℝ) * (k₀ : ℝ) * (physicalGamma P + physicalNu P) := by
  rw [regionIPhysicalFluidVelocity, correctedJacobiHydroVelocity_center]

theorem regionIPhysicalFluidVelocity_at_peak
    (D : PositiveDispersionScale) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (x : JacobiSnPeakPoint J) (t : ℝ) :
    regionIPhysicalFluidVelocity (positiveDispersionUnit D) k₀ P J t
        (regionITravelingPeakPosition (positiveDispersionUnit D) k₀ P J x t) =
      (D : ℝ) * (k₀ : ℝ) *
        (physicalGamma P + physicalNu P / regionIAmplitudeEndpoint P) := by
  rw [regionIPhysicalVelocity_eq_phaseSlope, regionITravelingPeak_comovingCoordinate,
    physicalJacobiPhaseSlope, regionIPhysicalPeak_argument,
    correctedJacobiAmplitude_sq_at_sn_peak]
  ring

theorem regionIPhysicalMassCurrent_at_center
    (D : PositiveDispersionScale) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (t : ℝ) :
    regionIPhysicalMassCurrent (positiveDispersionUnit D) k₀ P J t
        (physicalJacobiWaveSpeed (positiveDispersionUnit D) k₀ P * t) =
      (D : ℝ) * (k₀ : ℝ) ^ 3 * (physicalGamma P + physicalNu P) := by
  rw [regionIPhysicalMassCurrent_eq, correctedJacobiDensity_at_center,
    physicalJacobiWaveSpeed]
  simp only [positiveDispersionUnit_val]
  ring

theorem regionIPhysicalMassCurrent_at_peak
    (D : PositiveDispersionScale) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (x : JacobiSnPeakPoint J) (t : ℝ) :
    regionIPhysicalMassCurrent (positiveDispersionUnit D) k₀ P J t
        (regionITravelingPeakPosition (positiveDispersionUnit D) k₀ P J x t) =
      (D : ℝ) * (k₀ : ℝ) ^ 3 *
        (physicalGamma P * regionIAmplitudeEndpoint P + physicalNu P) := by
  rw [regionIPhysicalMassCurrent_eq, correctedJacobiDensity_at_peak,
    physicalJacobiWaveSpeed]
  simp only [positiveDispersionUnit_val]
  ring

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
