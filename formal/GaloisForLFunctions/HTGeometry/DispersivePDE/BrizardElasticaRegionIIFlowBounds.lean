import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaRegionIIBounds
import Mathlib.Tactic

/-!
# Sharp Region II phase and current bounds

The curvature-density bounds reverse under the inverse-square torsion law: curvature troughs carry
maximal fluid velocity, while curvature peaks carry minimal fluid velocity.  For positive
dispersion this also gives exact bounds on the Galilean-complete mass current.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

noncomputable def regionIIAmplitudeUpper (P : PhysicalRegionII) : ℝ :=
  1 + 1 / (-(P.val.q₀ : ℝ))

theorem regionIIAmplitudeUpper_pos (P : PhysicalRegionII) :
    0 < regionIIAmplitudeUpper P := by
  rw [regionIIAmplitudeUpper]
  have hq : 0 < -(P.val.q₀ : ℝ) := neg_pos.mpr P.property.1
  positivity

theorem regionIICompiledPhaseSlope_lower
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (s : ℝ) :
    (k₀ : ℝ) * regionIIGamma P / 2 +
        ((k₀ : ℝ) * regionIINu P / 2) / regionIIAmplitudeUpper P ≤
      compiledPhaseSlope k₀ (regionIIAmplitudeOscillator P J) s := by
  rw [compiledPhaseSlope]
  change (k₀ : ℝ) * regionIIGamma P / 2 +
      ((k₀ : ℝ) * regionIINu P / 2) / regionIIAmplitudeUpper P ≤
    (k₀ : ℝ) * regionIIGamma P / 2 +
      ((k₀ : ℝ) * regionIINu P / 2) /
        regionIIJacobiAmplitude P J
          (compiledArgument k₀ (regionIIAmplitudeOscillator P J) s) ^ 2
  have ha : 0 ≤ (k₀ : ℝ) * regionIINu P / 2 := by
    exact div_nonneg
      (mul_nonneg k₀.property.le (regionIINu_pos P).le) (by norm_num)
  have hupper := regionIIJacobiAmplitude_sq_upper P J
    (compiledArgument k₀ (regionIIAmplitudeOscillator P J) s)
  rw [← regionIIAmplitudeUpper] at hupper
  have hA : 0 < regionIIJacobiAmplitude P J
      (compiledArgument k₀ (regionIIAmplitudeOscillator P J) s) ^ 2 :=
    sq_pos_of_pos (regionIIJacobiAmplitude_pos P J _)
  have hdiv := (div_le_div_iff₀ (regionIIAmplitudeUpper_pos P) hA).2
    (mul_le_mul_of_nonneg_left hupper ha)
  linarith

theorem regionIICompiledPhaseSlope_upper
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (s : ℝ) :
    compiledPhaseSlope k₀ (regionIIAmplitudeOscillator P J) s ≤
      (k₀ : ℝ) * (regionIIGamma P + regionIINu P) / 2 := by
  rw [compiledPhaseSlope]
  change (k₀ : ℝ) * regionIIGamma P / 2 +
      ((k₀ : ℝ) * regionIINu P / 2) /
        regionIIJacobiAmplitude P J
          (compiledArgument k₀ (regionIIAmplitudeOscillator P J) s) ^ 2 ≤ _
  have ha : 0 ≤ (k₀ : ℝ) * regionIINu P / 2 := by
    exact div_nonneg
      (mul_nonneg k₀.property.le (regionIINu_pos P).le) (by norm_num)
  have hlower := regionIIJacobiAmplitude_sq_lower P J
    (compiledArgument k₀ (regionIIAmplitudeOscillator P J) s)
  have hA : 0 < regionIIJacobiAmplitude P J
      (compiledArgument k₀ (regionIIAmplitudeOscillator P J) s) ^ 2 :=
    sq_pos_of_pos (regionIIJacobiAmplitude_pos P J _)
  have hdiv : ((k₀ : ℝ) * regionIINu P / 2) /
      regionIIJacobiAmplitude P J
        (compiledArgument k₀ (regionIIAmplitudeOscillator P J) s) ^ 2 ≤
      (k₀ : ℝ) * regionIINu P / 2 := by
    apply (div_le_iff₀ hA).2
    nlinarith
  linarith

theorem regionIICompiledPhaseSlope_pos
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (s : ℝ) :
    0 < compiledPhaseSlope k₀ (regionIIAmplitudeOscillator P J) s := by
  rw [compiledPhaseSlope]
  change 0 < (k₀ : ℝ) * regionIIGamma P / 2 +
    ((k₀ : ℝ) * regionIINu P / 2) /
      regionIIJacobiAmplitude P J
        (compiledArgument k₀ (regionIIAmplitudeOscillator P J) s) ^ 2
  have hfirst : 0 < (k₀ : ℝ) * regionIIGamma P / 2 :=
    div_pos (mul_pos k₀.property (regionIIGamma_pos P)) (by norm_num)
  have hsecond : 0 ≤ ((k₀ : ℝ) * regionIINu P / 2) /
      regionIIJacobiAmplitude P J
        (compiledArgument k₀ (regionIIAmplitudeOscillator P J) s) ^ 2 := by
    exact div_nonneg
      (div_nonneg (mul_nonneg k₀.property.le (regionIINu_pos P).le) (by norm_num))
      (sq_nonneg _)
  exact add_pos_of_pos_of_nonneg hfirst hsecond

abbrev PositiveDispersionScale := {D : ℝ // 0 < D}

noncomputable def positiveDispersionUnit (D : PositiveDispersionScale) : ℝˣ :=
  Units.mk0 (D : ℝ) (ne_of_gt D.property)

@[simp] theorem positiveDispersionUnit_val (D : PositiveDispersionScale) :
    (positiveDispersionUnit D : ℝ) = (D : ℝ) := rfl

theorem regionIIPhysicalFluidVelocity_lower
    (D : PositiveDispersionScale) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (t s : ℝ) :
    (D : ℝ) * (k₀ : ℝ) *
        (regionIIGamma P + regionIINu P / regionIIAmplitudeUpper P) ≤
      regionIIPhysicalFluidVelocity (positiveDispersionUnit D) k₀ P J t s := by
  rw [regionIIPhysicalVelocity_eq_phaseSlope]
  change (D : ℝ) * (k₀ : ℝ) *
      (regionIIGamma P + regionIINu P / regionIIAmplitudeUpper P) ≤
    2 * (D : ℝ) * compiledPhaseSlope k₀ (regionIIAmplitudeOscillator P J)
      (s - regionIIPhysicalWaveSpeed (positiveDispersionUnit D) k₀ P * t)
  have h := regionIICompiledPhaseSlope_lower k₀ P J
    (s - regionIIPhysicalWaveSpeed (positiveDispersionUnit D) k₀ P * t)
  have hD2 : 0 ≤ 2 * (D : ℝ) :=
    mul_nonneg (by norm_num) D.property.le
  have hmul := mul_le_mul_of_nonneg_left h hD2
  calc
    (D : ℝ) * (k₀ : ℝ) *
        (regionIIGamma P + regionIINu P / regionIIAmplitudeUpper P) =
      2 * (D : ℝ) * ((k₀ : ℝ) * regionIIGamma P / 2 +
        ((k₀ : ℝ) * regionIINu P / 2) / regionIIAmplitudeUpper P) := by ring
    _ ≤ 2 * (D : ℝ) * compiledPhaseSlope k₀ (regionIIAmplitudeOscillator P J)
        (s - regionIIPhysicalWaveSpeed (positiveDispersionUnit D) k₀ P * t) := hmul

theorem regionIIPhysicalFluidVelocity_upper
    (D : PositiveDispersionScale) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (t s : ℝ) :
    regionIIPhysicalFluidVelocity (positiveDispersionUnit D) k₀ P J t s ≤
      (D : ℝ) * (k₀ : ℝ) * (regionIIGamma P + regionIINu P) := by
  rw [regionIIPhysicalVelocity_eq_phaseSlope]
  change 2 * (D : ℝ) * compiledPhaseSlope k₀ (regionIIAmplitudeOscillator P J)
      (s - regionIIPhysicalWaveSpeed (positiveDispersionUnit D) k₀ P * t) ≤
    (D : ℝ) * (k₀ : ℝ) * (regionIIGamma P + regionIINu P)
  have h := regionIICompiledPhaseSlope_upper k₀ P J
    (s - regionIIPhysicalWaveSpeed (positiveDispersionUnit D) k₀ P * t)
  have hD2 : 0 ≤ 2 * (D : ℝ) :=
    mul_nonneg (by norm_num) D.property.le
  have hmul := mul_le_mul_of_nonneg_left h hD2
  calc
    2 * (D : ℝ) * compiledPhaseSlope k₀ (regionIIAmplitudeOscillator P J)
        (s - regionIIPhysicalWaveSpeed (positiveDispersionUnit D) k₀ P * t) ≤
      2 * (D : ℝ) * ((k₀ : ℝ) * (regionIIGamma P + regionIINu P) / 2) := hmul
    _ = (D : ℝ) * (k₀ : ℝ) * (regionIIGamma P + regionIINu P) := by ring

theorem regionIIPhysicalMassCurrent_lower
    (D : PositiveDispersionScale) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (t s : ℝ) :
    (D : ℝ) * (k₀ : ℝ) ^ 3 * (regionIIGamma P + regionIINu P) ≤
      regionIIPhysicalMassCurrent (positiveDispersionUnit D) k₀ P J t s := by
  rw [regionIIPhysicalMassCurrent_eq, regionIIPhysicalWaveSpeed]
  have hdensity := regionIIPhysicalDensity_lower
    (positiveDispersionUnit D) k₀ P J t s
  have hcoef : 0 ≤ (D : ℝ) * (k₀ : ℝ) * regionIIGamma P :=
    mul_nonneg (mul_nonneg D.property.le k₀.property.le) (regionIIGamma_pos P).le
  have hmul := mul_le_mul_of_nonneg_left hdensity hcoef
  simp only [positiveDispersionUnit_val]
  calc
    (D : ℝ) * (k₀ : ℝ) ^ 3 * (regionIIGamma P + regionIINu P) =
      ((D : ℝ) * (k₀ : ℝ) * regionIIGamma P) * (k₀ : ℝ) ^ 2 +
        (D : ℝ) * (k₀ : ℝ) ^ 3 * regionIINu P := by ring
    _ ≤ ((D : ℝ) * (k₀ : ℝ) * regionIIGamma P) *
          regionIIPhysicalDensity (positiveDispersionUnit D) k₀ P J t s +
        (D : ℝ) * (k₀ : ℝ) ^ 3 * regionIINu P :=
      add_le_add_left hmul _

theorem regionIIPhysicalMassCurrent_upper
    (D : PositiveDispersionScale) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (t s : ℝ) :
    regionIIPhysicalMassCurrent (positiveDispersionUnit D) k₀ P J t s ≤
      (D : ℝ) * (k₀ : ℝ) ^ 3 *
        (regionIIGamma P * regionIIAmplitudeUpper P + regionIINu P) := by
  rw [regionIIPhysicalMassCurrent_eq, regionIIPhysicalWaveSpeed]
  have hdensity := regionIIPhysicalDensity_upper
    (positiveDispersionUnit D) k₀ P J t s
  rw [← regionIIAmplitudeUpper] at hdensity
  have hcoef : 0 ≤ (D : ℝ) * (k₀ : ℝ) * regionIIGamma P :=
    mul_nonneg (mul_nonneg D.property.le k₀.property.le) (regionIIGamma_pos P).le
  have hmul := mul_le_mul_of_nonneg_left hdensity hcoef
  simp only [positiveDispersionUnit_val]
  calc
    ((D : ℝ) * (k₀ : ℝ) * regionIIGamma P) *
          regionIIPhysicalDensity (positiveDispersionUnit D) k₀ P J t s +
        (D : ℝ) * (k₀ : ℝ) ^ 3 * regionIINu P ≤
      ((D : ℝ) * (k₀ : ℝ) * regionIIGamma P) *
          ((k₀ : ℝ) ^ 2 * regionIIAmplitudeUpper P) +
        (D : ℝ) * (k₀ : ℝ) ^ 3 * regionIINu P :=
      add_le_add_left hmul _
    _ = (D : ℝ) * (k₀ : ℝ) ^ 3 *
        (regionIIGamma P * regionIIAmplitudeUpper P + regionIINu P) := by ring

theorem regionIIPhysicalFluidVelocity_center_is_max
    (D : PositiveDispersionScale) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (t : ℝ) :
    regionIIPhysicalFluidVelocity (positiveDispersionUnit D) k₀ P J t
        (regionIIPhysicalWaveSpeed (positiveDispersionUnit D) k₀ P * t) =
      (D : ℝ) * (k₀ : ℝ) * (regionIIGamma P + regionIINu P) := by
  rw [regionIIPhysicalVelocity_eq_phaseSlope]
  have hz : regionIIPhysicalWaveSpeed (positiveDispersionUnit D) k₀ P * t -
      regionIIPhysicalWaveSpeed (positiveDispersionUnit D) k₀ P * t = 0 := by ring
  rw [hz, compiledPhaseSlope, compiledArgument, mul_zero]
  change 2 * (D : ℝ) * ((k₀ : ℝ) * regionIIGamma P / 2 +
      ((k₀ : ℝ) * regionIINu P / 2) / regionIIJacobiAmplitude P J 0 ^ 2) = _
  rw [regionIIJacobiAmplitude_zero]
  ring

noncomputable def regionIITravelingPeakPosition
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ))
    (x : JacobiSnPeakPoint J) (t : ℝ) : ℝ :=
  regionIIPhysicalWaveSpeed D k₀ P * t + regionIIPhysicalPeakLocation k₀ P J x

theorem regionIITravelingPeak_comovingCoordinate
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ))
    (x : JacobiSnPeakPoint J) (t : ℝ) :
    regionIITravelingPeakPosition D k₀ P J x t -
        regionIIPhysicalWaveSpeed D k₀ P * t =
      regionIIPhysicalPeakLocation k₀ P J x := by
  rw [regionIITravelingPeakPosition]
  ring

theorem regionIIPhysicalDensity_at_peak
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ))
    (x : JacobiSnPeakPoint J) (t : ℝ) :
    regionIIPhysicalDensity D k₀ P J t
        (regionIITravelingPeakPosition D k₀ P J x t) =
      (k₀ : ℝ) ^ 2 * regionIIAmplitudeUpper P := by
  rw [regionIIPhysicalDensity_eq, regionIITravelingPeak_comovingCoordinate,
    regionIIPhysicalPeak_argument, jacobiSd_sq_at_peak,
    regionIIAmplitudeUpper]
  have hn := regionIITransformedModulus_pos P
  have hq := neg_pos.mpr P.property.1
  change (k₀ : ℝ) ^ 2 *
      (1 + regionIITransformedModulus P / (-(P.val.q₀ : ℝ)) *
        (1 / regionIITransformedModulus P)) = _
  field_simp [ne_of_gt hn, ne_of_gt hq]

theorem regionIIPhysicalFluidVelocity_at_peak
    (D : PositiveDispersionScale) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ))
    (x : JacobiSnPeakPoint J) (t : ℝ) :
    regionIIPhysicalFluidVelocity (positiveDispersionUnit D) k₀ P J t
        (regionIITravelingPeakPosition (positiveDispersionUnit D) k₀ P J x t) =
      (D : ℝ) * (k₀ : ℝ) *
        (regionIIGamma P + regionIINu P / regionIIAmplitudeUpper P) := by
  rw [regionIIPhysicalVelocity_eq_phaseSlope,
    regionIITravelingPeak_comovingCoordinate, compiledPhaseSlope,
    regionIIPhysicalPeak_argument]
  change 2 * (D : ℝ) * ((k₀ : ℝ) * regionIIGamma P / 2 +
      ((k₀ : ℝ) * regionIINu P / 2) /
        regionIIJacobiAmplitude P J x.val ^ 2) = _
  rw [regionIIJacobiAmplitude_sq_at_peak, ← regionIIAmplitudeUpper]
  ring

theorem regionIIPhysicalMassCurrent_center_is_min
    (D : PositiveDispersionScale) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (t : ℝ) :
    regionIIPhysicalMassCurrent (positiveDispersionUnit D) k₀ P J t
        (regionIIPhysicalWaveSpeed (positiveDispersionUnit D) k₀ P * t) =
      (D : ℝ) * (k₀ : ℝ) ^ 3 * (regionIIGamma P + regionIINu P) := by
  rw [regionIIPhysicalMassCurrent_eq, regionIIPhysicalDensity,
    regionIIPhysicalWaveSpeed_eq_compiled (positiveDispersionUnit D) k₀ P J,
    compiledTravelingDensity_eq_curvature_sq, sub_self, compiledCurvature,
    compiledWaveSpeed]
  change (D : ℝ) * (k₀ : ℝ) * regionIIGamma P *
      ((k₀ : ℝ) * regionIIJacobiAmplitude P J
        (compiledArgument k₀ (regionIIAmplitudeOscillator P J) 0)) ^ 2 +
      (D : ℝ) * (k₀ : ℝ) ^ 3 * regionIINu P = _
  rw [compiledArgument, mul_zero, regionIIJacobiAmplitude_zero]
  ring

theorem regionIIPhysicalMassCurrent_at_peak
    (D : PositiveDispersionScale) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ))
    (x : JacobiSnPeakPoint J) (t : ℝ) :
    regionIIPhysicalMassCurrent (positiveDispersionUnit D) k₀ P J t
        (regionIITravelingPeakPosition (positiveDispersionUnit D) k₀ P J x t) =
      (D : ℝ) * (k₀ : ℝ) ^ 3 *
        (regionIIGamma P * regionIIAmplitudeUpper P + regionIINu P) := by
  rw [regionIIPhysicalMassCurrent_eq, regionIIPhysicalWaveSpeed,
    regionIIPhysicalDensity_at_peak]
  simp only [positiveDispersionUnit_val]
  ring

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
