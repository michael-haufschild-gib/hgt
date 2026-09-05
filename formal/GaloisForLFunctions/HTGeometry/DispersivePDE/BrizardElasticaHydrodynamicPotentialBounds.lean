import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaQuantumStressBounds
import Mathlib.Tactic

/-!
# Hydrodynamic-potential reciprocity and bands

After removing the constant spectral term, the paper's hydrodynamic potential is reciprocal to the
fourth power of curvature.  A reusable positive-amplitude band therefore compiles directly into
sharp potential bounds, instantiated here on both Region I chambers and Region II.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

noncomputable def compiledHydrodynamicPotential
    (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) (s : ℝ) : ℝ :=
  compiledCurvature k₀ E s ^ 2 + 2 * compiledBohmTerm k₀ E s

theorem compiledHydrodynamicPotential_eq_amplitude
    (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) (s : ℝ) :
    compiledHydrodynamicPotential k₀ E s =
      (k₀ : ℝ) ^ 2 / 2 *
        (-E.gamma ^ 2 + E.nu ^ 2 / E.amplitude (compiledArgument k₀ E s) ^ 4) := by
  rw [compiledHydrodynamicPotential, compiledHydrodynamicPotential_eq,
    waveLambda, compiledTorsionScale, compiledCurvature]
  field_simp [ne_of_gt k₀.property,
    ne_of_gt (E.amplitude_pos (compiledArgument k₀ E s))]

/-- Spectral-shifted potential times curvature⁴ is a constant torsion charge. -/
theorem compiledHydrodynamicPotential_gap_mul_curvature_fourth
    (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) (s : ℝ) :
    (compiledHydrodynamicPotential k₀ E s -
        (k₀ : ℝ) ^ 2 * waveLambda E.gamma) * compiledCurvature k₀ E s ^ 4 =
      (k₀ : ℝ) ^ 6 * E.nu ^ 2 / 2 := by
  rw [compiledHydrodynamicPotential, compiledHydrodynamicPotential_eq,
    compiledTorsionScale]
  field_simp [ne_of_gt (compiledCurvature_pos k₀ E s)]
  ring

structure PositiveAmplitudeBand (E : PositiveAmplitudeOscillator) where
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  lower_bound : ∀ x, lower ≤ E.amplitude x ^ 2
  upper_bound : ∀ x, E.amplitude x ^ 2 ≤ upper

theorem compiledHydrodynamicPotential_band
    (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator)
    (B : PositiveAmplitudeBand E) (s : ℝ) :
    (k₀ : ℝ) ^ 2 / 2 * (-E.gamma ^ 2 + E.nu ^ 2 / B.upper ^ 2) ≤
        compiledHydrodynamicPotential k₀ E s ∧
      compiledHydrodynamicPotential k₀ E s ≤
        (k₀ : ℝ) ^ 2 / 2 * (-E.gamma ^ 2 + E.nu ^ 2 / B.lower ^ 2) := by
  rw [compiledHydrodynamicPotential_eq_amplitude]
  have hApos : 0 < E.amplitude (compiledArgument k₀ E s) ^ 2 :=
    sq_pos_of_pos (E.amplitude_pos _)
  have hlo := B.lower_bound (compiledArgument k₀ E s)
  have hup := B.upper_bound (compiledArgument k₀ E s)
  have huppos : 0 < B.upper := lt_of_lt_of_le B.lower_pos (hlo.trans hup)
  have hloSq : B.lower ^ 2 ≤ E.amplitude (compiledArgument k₀ E s) ^ 4 := by
    rw [show E.amplitude (compiledArgument k₀ E s) ^ 4 =
      (E.amplitude (compiledArgument k₀ E s) ^ 2) ^ 2 by ring]
    nlinarith [mul_nonneg (sub_nonneg.mpr hlo)
      (add_nonneg hApos.le B.lower_pos.le)]
  have hupSq : E.amplitude (compiledArgument k₀ E s) ^ 4 ≤ B.upper ^ 2 := by
    rw [show E.amplitude (compiledArgument k₀ E s) ^ 4 =
      (E.amplitude (compiledArgument k₀ E s) ^ 2) ^ 2 by ring]
    nlinarith [mul_nonneg (sub_nonneg.mpr hup)
      (add_nonneg huppos.le hApos.le)]
  have hA4pos : 0 < E.amplitude (compiledArgument k₀ E s) ^ 4 :=
    pow_pos (E.amplitude_pos _) 4
  have hnu : 0 ≤ E.nu ^ 2 := sq_nonneg E.nu
  have hlowerDiv : E.nu ^ 2 / B.upper ^ 2 ≤
      E.nu ^ 2 / E.amplitude (compiledArgument k₀ E s) ^ 4 :=
    (div_le_div_iff₀ (sq_pos_of_pos huppos) hA4pos).2
      (mul_le_mul_of_nonneg_left hupSq hnu)
  have hupperDiv : E.nu ^ 2 / E.amplitude (compiledArgument k₀ E s) ^ 4 ≤
      E.nu ^ 2 / B.lower ^ 2 :=
    (div_le_div_iff₀ hA4pos (sq_pos_of_pos B.lower_pos)).2
      (mul_le_mul_of_nonneg_left hloSq hnu)
  have hk : 0 ≤ (k₀ : ℝ) ^ 2 / 2 := by positivity
  exact ⟨mul_le_mul_of_nonneg_left (add_le_add_right hlowerDiv _) hk,
    mul_le_mul_of_nonneg_left (add_le_add_right hupperDiv _) hk⟩

noncomputable def regionINonnegativeAmplitudeBand
    (P : PhysicalRegionINonnegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) :
    PositiveAmplitudeBand (regionIAmplitudeOscillator P.val J) where
  lower := regionIAmplitudeEndpoint P.val
  upper := 1
  lower_pos := regionIAmplitudeEndpoint_pos P.val
  lower_bound := regionINonnegativeAmplitude_sq_lower P J
  upper_bound := regionINonnegativeAmplitude_sq_upper P J

noncomputable def regionINegativeAmplitudeBand
    (P : PhysicalRegionINegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) :
    PositiveAmplitudeBand (regionIAmplitudeOscillator P.val J) where
  lower := 1
  upper := regionIAmplitudeEndpoint P.val
  lower_pos := by norm_num
  lower_bound := regionINegativeAmplitude_sq_lower P J
  upper_bound := regionINegativeAmplitude_sq_upper P J

noncomputable def regionIIAmplitudeBand
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) :
    PositiveAmplitudeBand (regionIIAmplitudeOscillator P J) where
  lower := 1
  upper := regionIIAmplitudeUpper P
  lower_pos := by norm_num
  lower_bound := regionIIJacobiAmplitude_sq_lower P J
  upper_bound := by
    intro x
    change regionIIJacobiAmplitude P J x ^ 2 ≤ regionIIAmplitudeUpper P
    simpa only [regionIIAmplitudeUpper] using regionIIJacobiAmplitude_sq_upper P J x

theorem regionINonnegativeHydrodynamicPotential_bounds
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionINonnegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) (s : ℝ) :
    (k₀ : ℝ) ^ 2 / 2 *
        (-physicalGamma P.val ^ 2 + physicalNu P.val ^ 2) ≤
      compiledHydrodynamicPotential k₀ (regionIAmplitudeOscillator P.val J) s ∧
    compiledHydrodynamicPotential k₀ (regionIAmplitudeOscillator P.val J) s ≤
      (k₀ : ℝ) ^ 2 / 2 *
        (-physicalGamma P.val ^ 2 +
          physicalNu P.val ^ 2 / regionIAmplitudeEndpoint P.val ^ 2) := by
  simpa only [regionINonnegativeAmplitudeBand, regionIAmplitudeOscillator,
    one_pow, div_one] using
    compiledHydrodynamicPotential_band k₀ (regionIAmplitudeOscillator P.val J)
      (regionINonnegativeAmplitudeBand P J) s

theorem regionINegativeHydrodynamicPotential_bounds
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionINegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) (s : ℝ) :
    (k₀ : ℝ) ^ 2 / 2 *
        (-physicalGamma P.val ^ 2 +
          physicalNu P.val ^ 2 / regionIAmplitudeEndpoint P.val ^ 2) ≤
      compiledHydrodynamicPotential k₀ (regionIAmplitudeOscillator P.val J) s ∧
    compiledHydrodynamicPotential k₀ (regionIAmplitudeOscillator P.val J) s ≤
      (k₀ : ℝ) ^ 2 / 2 *
        (-physicalGamma P.val ^ 2 + physicalNu P.val ^ 2) := by
  simpa only [regionINegativeAmplitudeBand, regionIAmplitudeOscillator,
    one_pow, div_one] using
    compiledHydrodynamicPotential_band k₀ (regionIAmplitudeOscillator P.val J)
      (regionINegativeAmplitudeBand P J) s

theorem regionIIHydrodynamicPotential_bounds
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (s : ℝ) :
    (k₀ : ℝ) ^ 2 / 2 *
        (-regionIIGamma P ^ 2 + regionIINu P ^ 2 / regionIIAmplitudeUpper P ^ 2) ≤
      compiledHydrodynamicPotential k₀ (regionIIAmplitudeOscillator P J) s ∧
    compiledHydrodynamicPotential k₀ (regionIIAmplitudeOscillator P J) s ≤
      (k₀ : ℝ) ^ 2 / 2 * (-regionIIGamma P ^ 2 + regionIINu P ^ 2) := by
  simpa only [regionIIAmplitudeBand, regionIIAmplitudeOscillator,
    one_pow, div_one] using
    compiledHydrodynamicPotential_band k₀ (regionIIAmplitudeOscillator P J)
      (regionIIAmplitudeBand P J) s

theorem regionIHydrodynamicPotential_center
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) :
    compiledHydrodynamicPotential k₀ (regionIAmplitudeOscillator P J) 0 =
      (k₀ : ℝ) ^ 2 / 2 * (-physicalGamma P ^ 2 + physicalNu P ^ 2) := by
  rw [compiledHydrodynamicPotential_eq_amplitude, compiledArgument, mul_zero]
  change (k₀ : ℝ) ^ 2 / 2 *
      (-physicalGamma P ^ 2 + physicalNu P ^ 2 / correctedJacobiAmplitude P J 0 ^ 4) = _
  rw [correctedJacobiAmplitude_zero]
  ring

theorem regionIHydrodynamicPotential_peak
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (x : JacobiSnPeakPoint J) :
    compiledHydrodynamicPotential k₀ (regionIAmplitudeOscillator P J)
        (regionIPhysicalPeakLocation k₀ P J x) =
      (k₀ : ℝ) ^ 2 / 2 *
        (-physicalGamma P ^ 2 + physicalNu P ^ 2 / regionIAmplitudeEndpoint P ^ 2) := by
  rw [compiledHydrodynamicPotential_eq_amplitude]
  change (k₀ : ℝ) ^ 2 / 2 *
      (-physicalGamma P ^ 2 + physicalNu P ^ 2 /
        correctedJacobiAmplitude P J
          (physicalJacobiArgument k₀ P (regionIPhysicalPeakLocation k₀ P J x)) ^ 4) = _
  rw [regionIPhysicalPeak_argument]
  have hsq := correctedJacobiAmplitude_sq_at_sn_peak P J x
  rw [show correctedJacobiAmplitude P J x.val ^ 4 =
    (correctedJacobiAmplitude P J x.val ^ 2) ^ 2 by ring, hsq]

theorem regionIIHydrodynamicPotential_center
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) :
    compiledHydrodynamicPotential k₀ (regionIIAmplitudeOscillator P J) 0 =
      (k₀ : ℝ) ^ 2 / 2 * (-regionIIGamma P ^ 2 + regionIINu P ^ 2) := by
  rw [compiledHydrodynamicPotential_eq_amplitude, compiledArgument, mul_zero]
  change (k₀ : ℝ) ^ 2 / 2 *
      (-regionIIGamma P ^ 2 + regionIINu P ^ 2 / regionIIJacobiAmplitude P J 0 ^ 4) = _
  rw [regionIIJacobiAmplitude_zero]
  ring

theorem regionIIHydrodynamicPotential_peak
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ))
    (x : JacobiSnPeakPoint J) :
    compiledHydrodynamicPotential k₀ (regionIIAmplitudeOscillator P J)
        (regionIIPhysicalPeakLocation k₀ P J x) =
      (k₀ : ℝ) ^ 2 / 2 *
        (-regionIIGamma P ^ 2 + regionIINu P ^ 2 / regionIIAmplitudeUpper P ^ 2) := by
  rw [compiledHydrodynamicPotential_eq_amplitude, regionIIPhysicalPeak_argument]
  change (k₀ : ℝ) ^ 2 / 2 *
      (-regionIIGamma P ^ 2 + regionIINu P ^ 2 / regionIIJacobiAmplitude P J x.val ^ 4) = _
  have hsq := regionIIJacobiAmplitude_sq_at_peak P J x
  rw [show regionIIJacobiAmplitude P J x.val ^ 4 =
    (regionIIJacobiAmplitude P J x.val ^ 2) ^ 2 by ring, hsq, ← regionIIAmplitudeUpper]

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
