import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaAmplitudeCompiler
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaTravelingMomentum
import Mathlib.Tactic

/-!
# Hydrodynamic compiler for positive amplitude oscillators

The universal oscillator-to-NLS construction also compiles to the paper's complete Madelung flow:
density, velocity, continuity, acceleration, momentum balance, Bohm potential, and doubled WKB
phase.  Consequently every oscillator instance receives all hydrodynamic laws at once.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

noncomputable def compiledCurvatureProfileJet
    (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) : CurvatureProfileJet where
  κ := fun s => Units.mk0 (compiledCurvature k₀ E s)
    (ne_of_gt (compiledCurvature_pos k₀ E s))
  κ₁ := compiledCurvatureVelocity k₀ E
  hasDerivAt := by
    intro s
    convert compiledCurvature_hasDerivAt k₀ E s using 1
    funext y
    rfl

noncomputable def compiledTorsionScale
    (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) : ℝ :=
  (k₀ : ℝ) * E.nu / 2

theorem compiledTravelingDensity_eq_curvature_sq
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator)
    (t s : ℝ) :
    travelingDensity (compiledCurvatureProfileJet k₀ E)
        (compiledWaveSpeed D k₀ E) t s =
      compiledCurvature k₀ E (s - compiledWaveSpeed D k₀ E * t) ^ 2 := by
  rfl

theorem compiledTravelingDensity_eq_amplitude_sq
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator)
    (t s : ℝ) :
    travelingDensity (compiledCurvatureProfileJet k₀ E)
        (compiledWaveSpeed D k₀ E) t s =
      (k₀ : ℝ) ^ 2 * E.amplitude
        (compiledArgument k₀ E (s - compiledWaveSpeed D k₀ E * t)) ^ 2 := by
  rw [compiledTravelingDensity_eq_curvature_sq, compiledCurvature]
  ring

theorem compiledNLS_normSq_eq_travelingDensity
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator)
    (t s : ℝ) :
    ‖(travelingPolarJet (compiledPolarProfile k₀ E)
        (compiledWaveSpeed D k₀ E)).u t s‖ ^ 2 =
      travelingDensity (compiledCurvatureProfileJet k₀ E)
        (compiledWaveSpeed D k₀ E) t s := by
  change ‖polarProfile (compiledPolarProfile k₀ E)
      (s - compiledWaveSpeed D k₀ E * t)‖ ^ 2 = _
  rw [compiledPolarProfile_normSq, compiledTravelingDensity_eq_curvature_sq]

theorem compiledHydroVelocity_eq_phaseSlope
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator)
    (t s : ℝ) :
    travelingHydroVelocity (D : ℝ) (k₀ : ℝ) (compiledTorsionScale k₀ E)
        (compiledWaveSpeed D k₀ E) (compiledCurvatureProfileJet k₀ E) t s =
      2 * (D : ℝ) * compiledPhaseSlope k₀ E
        (s - compiledWaveSpeed D k₀ E * t) := by
  rw [travelingHydroVelocity, fluidSpeed, torsion, compiledTorsionScale,
    compiledWaveSpeed, compiledPhaseSlope]
  change (D : ℝ) * (k₀ : ℝ) * E.gamma +
      2 * (D : ℝ) * ((k₀ : ℝ) ^ 2 * ((k₀ : ℝ) * E.nu / 2) /
        compiledCurvature k₀ E
          (s - (D : ℝ) * (k₀ : ℝ) * E.gamma * t) ^ 2) = _
  rw [compiledCurvature]
  field_simp [ne_of_gt k₀.property,
    ne_of_gt (E.amplitude_pos
      (compiledArgument k₀ E (s - (D : ℝ) * (k₀ : ℝ) * E.gamma * t)))]

theorem compiledTravelingMassCurrent_eq
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator)
    (t s : ℝ) :
    travelingMassCurrent (D : ℝ) (k₀ : ℝ) (compiledTorsionScale k₀ E)
        (compiledWaveSpeed D k₀ E) (compiledCurvatureProfileJet k₀ E) t s =
      compiledWaveSpeed D k₀ E *
          travelingDensity (compiledCurvatureProfileJet k₀ E)
            (compiledWaveSpeed D k₀ E) t s +
        (D : ℝ) * (k₀ : ℝ) ^ 3 * E.nu := by
  rw [travelingMassCurrent_eq, compiledTorsionScale]
  ring

theorem compiledUnboostedMassCurrent_eq
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator)
    (t s : ℝ) :
    unboostedMassCurrent (D : ℝ) (k₀ : ℝ) (compiledTorsionScale k₀ E)
        (compiledWaveSpeed D k₀ E) (compiledCurvatureProfileJet k₀ E) t s =
      (D : ℝ) * (k₀ : ℝ) ^ 3 * E.nu := by
  rw [unboostedMassCurrent_eq, compiledTorsionScale]
  ring

theorem compiledContinuityEquation
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator)
    (t s : ℝ) :
    travelingDensityT (compiledCurvatureProfileJet k₀ E)
          (compiledWaveSpeed D k₀ E) t s +
        compiledWaveSpeed D k₀ E *
          travelingDensityX (compiledCurvatureProfileJet k₀ E)
            (compiledWaveSpeed D k₀ E) t s = 0 := by
  rw [travelingDensityT, travelingDensityX]
  ring

theorem compiledAccelerationEquation
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator)
    (t s : ℝ) :
    travelingHydroVelocityT (D : ℝ) (k₀ : ℝ) (compiledTorsionScale k₀ E)
          (compiledWaveSpeed D k₀ E) (compiledCurvatureProfileJet k₀ E) t s +
        travelingHydroVelocity (D : ℝ) (k₀ : ℝ) (compiledTorsionScale k₀ E)
          (compiledWaveSpeed D k₀ E) (compiledCurvatureProfileJet k₀ E) t s *
        travelingHydroVelocityX (D : ℝ) (k₀ : ℝ) (compiledTorsionScale k₀ E)
          (compiledWaveSpeed D k₀ E) (compiledCurvatureProfileJet k₀ E) t s =
      travelingHydroAccelerationForce (D : ℝ) (k₀ : ℝ) (compiledTorsionScale k₀ E)
        (compiledWaveSpeed D k₀ E) (compiledCurvatureProfileJet k₀ E) t s :=
  (travelingHydroAccelerationEquation (D : ℝ) (k₀ : ℝ)
    (compiledTorsionScale k₀ E) (compiledWaveSpeed D k₀ E)
    (compiledCurvatureProfileJet k₀ E) t s).1

theorem compiledMomentumEquation
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator)
    (t s : ℝ) :
    travelingMomentumDensityT (compiledCurvatureProfileJet k₀ E)
          (compiledWaveSpeed D k₀ E) t s +
        travelingMomentumFluxX (D : ℝ) (k₀ : ℝ) (compiledTorsionScale k₀ E)
          (compiledWaveSpeed D k₀ E) (compiledCurvatureProfileJet k₀ E) t s =
      travelingQuantumStressX (D : ℝ) (k₀ : ℝ) (compiledTorsionScale k₀ E)
        (compiledWaveSpeed D k₀ E) (compiledCurvatureProfileJet k₀ E) t s :=
  (travelingMomentumEquation (D : ℝ) (k₀ : ℝ)
    (compiledTorsionScale k₀ E) (compiledWaveSpeed D k₀ E)
    (compiledCurvatureProfileJet k₀ E) t s).1

noncomputable def compiledBohmTerm
    (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) (s : ℝ) : ℝ :=
  compiledCurvatureAcceleration k₀ E s / compiledCurvature k₀ E s

theorem compiledBohmTerm_eq
    (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) (s : ℝ) :
    compiledBohmTerm k₀ E s =
      -compiledCurvature k₀ E s ^ 2 / 2 -
        (k₀ : ℝ) ^ 2 * E.gamma ^ 2 / 4 +
        (k₀ : ℝ) ^ 6 * E.nu ^ 2 / (4 * compiledCurvature k₀ E s ^ 4) := by
  rw [compiledBohmTerm, compiledCurvature_equation]
  field_simp [ne_of_gt (compiledCurvature_pos k₀ E s)]

theorem compiledHydrodynamicPotential_eq
    (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) (s : ℝ) :
    compiledCurvature k₀ E s ^ 2 + 2 * compiledBohmTerm k₀ E s =
      (k₀ : ℝ) ^ 2 * waveLambda E.gamma +
        2 * (k₀ : ℝ) ^ 4 * compiledTorsionScale k₀ E ^ 2 /
          compiledCurvature k₀ E s ^ 4 := by
  rw [compiledBohmTerm_eq, waveLambda, compiledTorsionScale]
  ring

noncomputable def compiledHydroPhase
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator)
    (t s : ℝ) : ℝ :=
  2 * compiledPhase k₀ E (s - compiledWaveSpeed D k₀ E * t)

noncomputable def compiledHydroPhaseT
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator)
    (t s : ℝ) : ℝ :=
  -2 * compiledWaveSpeed D k₀ E *
    compiledPhaseSlope k₀ E (s - compiledWaveSpeed D k₀ E * t)

noncomputable def compiledHydroPhaseX
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator)
    (t s : ℝ) : ℝ :=
  2 * compiledPhaseSlope k₀ E (s - compiledWaveSpeed D k₀ E * t)

theorem hasDerivAt_compiledHydroPhase_time
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator)
    (t s : ℝ) :
    HasDerivAt (fun r : ℝ => compiledHydroPhase D k₀ E r s)
      (compiledHydroPhaseT D k₀ E t s) t := by
  have hinner : HasDerivAt (fun r : ℝ => s - compiledWaveSpeed D k₀ E * r)
      (-compiledWaveSpeed D k₀ E) t := by
    simpa using! ((hasDerivAt_id t).const_mul (compiledWaveSpeed D k₀ E)).const_sub s
  have hcomp := (compiledPhase_hasDerivAt k₀ E
    (s - compiledWaveSpeed D k₀ E * t)).scomp t hinner
  have h := hcomp.const_mul 2
  change HasDerivAt
    (fun r : ℝ => 2 * compiledPhase k₀ E (s - compiledWaveSpeed D k₀ E * r))
    (compiledHydroPhaseT D k₀ E t s) t
  apply h.congr_deriv
  rw [compiledHydroPhaseT]
  simp only [smul_eq_mul]
  ring

theorem hasDerivAt_compiledHydroPhase_space
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator)
    (t s : ℝ) :
    HasDerivAt (compiledHydroPhase D k₀ E t) (compiledHydroPhaseX D k₀ E t s) s := by
  have hinner : HasDerivAt (fun y : ℝ => y - compiledWaveSpeed D k₀ E * t) 1 s :=
    (hasDerivAt_id s).sub_const _
  have hcomp := (compiledPhase_hasDerivAt k₀ E
    (s - compiledWaveSpeed D k₀ E * t)).scomp s hinner
  have h := hcomp.const_mul 2
  change HasDerivAt
    (fun y : ℝ => 2 * compiledPhase k₀ E (y - compiledWaveSpeed D k₀ E * t))
    (compiledHydroPhaseX D k₀ E t s) s
  apply h.congr_deriv
  rw [compiledHydroPhaseX]
  simp only [one_smul]

theorem compiledHydroVelocity_eq_phaseDerivative
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator)
    (t s : ℝ) :
    travelingHydroVelocity (D : ℝ) (k₀ : ℝ) (compiledTorsionScale k₀ E)
        (compiledWaveSpeed D k₀ E) (compiledCurvatureProfileJet k₀ E) t s =
      (D : ℝ) * compiledHydroPhaseX D k₀ E t s := by
  rw [compiledHydroVelocity_eq_phaseSlope, compiledHydroPhaseX]
  ring

theorem compiledHydroPhaseEquation
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator)
    (t s : ℝ) :
    compiledHydroPhaseT D k₀ E t s +
        travelingHydroVelocity (D : ℝ) (k₀ : ℝ) (compiledTorsionScale k₀ E)
          (compiledWaveSpeed D k₀ E) (compiledCurvatureProfileJet k₀ E) t s ^ 2 /
            (2 * (D : ℝ)) =
      (D : ℝ) *
        (travelingDensity (compiledCurvatureProfileJet k₀ E)
            (compiledWaveSpeed D k₀ E) t s +
          2 * compiledBohmTerm k₀ E (s - compiledWaveSpeed D k₀ E * t)) := by
  rw [compiledHydroPhaseT, compiledHydroVelocity_eq_phaseSlope,
    compiledTravelingDensity_eq_curvature_sq, compiledHydrodynamicPotential_eq,
    compiledWaveSpeed, compiledPhaseSlope, compiledTorsionScale, waveLambda,
    compiledCurvature]
  field_simp [D.ne_zero, ne_of_gt k₀.property,
    ne_of_gt (E.amplitude_pos
      (compiledArgument k₀ E (s - (D : ℝ) * (k₀ : ℝ) * E.gamma * t)))]
  ring

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
