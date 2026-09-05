import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaJacobiAmplitude
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaTravelingPolar
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Positive amplitude oscillator compiler

Any everywhere-positive solution of the paper's dimensionless inverse-cubic amplitude oscillator
canonically produces an arclength curvature, inverse-square phase, and exact traveling focusing-NLS
solution.  This isolates the analytic compiler shared by Regions I and II.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

structure PositiveAmplitudeOscillator where
  q : ℝ
  q_pos : 0 < q
  gamma : ℝ
  nu : ℝ
  amplitude : ℝ → ℝ
  amplitude₁ : ℝ → ℝ
  amplitude₂ : ℝ → ℝ
  amplitude_pos : ∀ x, 0 < amplitude x
  amplitude_deriv : ∀ x, HasDerivAt amplitude (amplitude₁ x) x
  amplitude₁_deriv : ∀ x, HasDerivAt amplitude₁ (amplitude₂ x) x
  oscillator : ∀ x,
    amplitude₂ x =
      -2 * q * amplitude x ^ 3 - q * gamma ^ 2 * amplitude x +
        q * nu ^ 2 / amplitude x ^ 3

noncomputable def compiledArclengthScale
    (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) : ℝ :=
  (k₀ : ℝ) / (2 * Real.sqrt E.q)

theorem compiledArclengthScale_pos
    (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) :
    0 < compiledArclengthScale k₀ E := by
  rw [compiledArclengthScale]
  exact div_pos k₀.property (mul_pos (by norm_num) (Real.sqrt_pos.2 E.q_pos))

theorem compiledArclengthScale_sq
    (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) :
    compiledArclengthScale k₀ E ^ 2 = (k₀ : ℝ) ^ 2 / (4 * E.q) := by
  rw [compiledArclengthScale, div_pow,
    show (2 * Real.sqrt E.q) ^ 2 = 4 * E.q by
      rw [mul_pow, Real.sq_sqrt E.q_pos.le]
      ring]

noncomputable def compiledArgument
    (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) (s : ℝ) : ℝ :=
  compiledArclengthScale k₀ E * s

noncomputable def compiledCurvature
    (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) (s : ℝ) : ℝ :=
  (k₀ : ℝ) * E.amplitude (compiledArgument k₀ E s)

noncomputable def compiledCurvatureVelocity
    (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) (s : ℝ) : ℝ :=
  (k₀ : ℝ) * compiledArclengthScale k₀ E *
    E.amplitude₁ (compiledArgument k₀ E s)

noncomputable def compiledCurvatureAcceleration
    (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) (s : ℝ) : ℝ :=
  (k₀ : ℝ) * compiledArclengthScale k₀ E ^ 2 *
    E.amplitude₂ (compiledArgument k₀ E s)

theorem compiledCurvature_pos
    (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) (s : ℝ) :
    0 < compiledCurvature k₀ E s :=
  mul_pos k₀.property (E.amplitude_pos _)

theorem compiledCurvature_hasDerivAt
    (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) (s : ℝ) :
    HasDerivAt (compiledCurvature k₀ E) (compiledCurvatureVelocity k₀ E s) s := by
  have hinner : HasDerivAt (compiledArgument k₀ E) (compiledArclengthScale k₀ E) s := by
    simpa only [compiledArgument, id_eq, mul_one] using!
      (hasDerivAt_id s).const_mul (compiledArclengthScale k₀ E)
  have hcomp := (E.amplitude_deriv (compiledArgument k₀ E s)).scomp s hinner
  have h := hcomp.const_mul (k₀ : ℝ)
  change HasDerivAt
    (fun y => (k₀ : ℝ) * E.amplitude (compiledArgument k₀ E y))
    (compiledCurvatureVelocity k₀ E s) s
  apply h.congr_deriv
  rw [compiledCurvatureVelocity]
  simp only [smul_eq_mul]
  ring

theorem compiledCurvatureVelocity_hasDerivAt
    (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) (s : ℝ) :
    HasDerivAt (compiledCurvatureVelocity k₀ E)
      (compiledCurvatureAcceleration k₀ E s) s := by
  have hinner : HasDerivAt (compiledArgument k₀ E) (compiledArclengthScale k₀ E) s := by
    simpa only [compiledArgument, id_eq, mul_one] using!
      (hasDerivAt_id s).const_mul (compiledArclengthScale k₀ E)
  have hcomp := (E.amplitude₁_deriv (compiledArgument k₀ E s)).scomp s hinner
  have h := hcomp.const_mul ((k₀ : ℝ) * compiledArclengthScale k₀ E)
  change HasDerivAt
    (fun y => ((k₀ : ℝ) * compiledArclengthScale k₀ E) *
      E.amplitude₁ (compiledArgument k₀ E y))
    (compiledCurvatureAcceleration k₀ E s) s
  apply h.congr_deriv
  rw [compiledCurvatureAcceleration]
  simp only [smul_eq_mul]
  ring

theorem compiledCurvature_equation
    (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) (s : ℝ) :
    compiledCurvatureAcceleration k₀ E s =
      -compiledCurvature k₀ E s ^ 3 / 2 -
        (k₀ : ℝ) ^ 2 * E.gamma ^ 2 * compiledCurvature k₀ E s / 4 +
        (k₀ : ℝ) ^ 6 * E.nu ^ 2 / (4 * compiledCurvature k₀ E s ^ 3) := by
  rw [compiledCurvatureAcceleration, E.oscillator,
    compiledCurvature, compiledArclengthScale_sq]
  field_simp [ne_of_gt k₀.property, ne_of_gt E.q_pos,
    ne_of_gt (E.amplitude_pos (compiledArgument k₀ E s))]
  ring

noncomputable def compiledWaveSpeed
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) : ℝ :=
  (D : ℝ) * (k₀ : ℝ) * E.gamma

noncomputable def compiledPhaseSlope
    (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) (s : ℝ) : ℝ :=
  (k₀ : ℝ) * E.gamma / 2 +
    ((k₀ : ℝ) * E.nu / 2) / E.amplitude (compiledArgument k₀ E s) ^ 2

noncomputable def compiledPhaseAcceleration
    (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) (s : ℝ) : ℝ :=
  -(k₀ : ℝ) * E.nu * compiledArclengthScale k₀ E *
      E.amplitude₁ (compiledArgument k₀ E s) /
    E.amplitude (compiledArgument k₀ E s) ^ 3

theorem compiledArgument_hasDerivAt
    (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) (s : ℝ) :
    HasDerivAt (compiledArgument k₀ E) (compiledArclengthScale k₀ E) s := by
  simpa only [compiledArgument, id_eq, mul_one] using!
    (hasDerivAt_id s).const_mul (compiledArclengthScale k₀ E)

theorem compiledPhaseSlope_hasDerivAt
    (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) (s : ℝ) :
    HasDerivAt (compiledPhaseSlope k₀ E) (compiledPhaseAcceleration k₀ E s) s := by
  have hA := (E.amplitude_deriv (compiledArgument k₀ E s)).scomp s
    (compiledArgument_hasDerivAt k₀ E s)
  have hsq := hA.fun_pow 2
  norm_num at hsq
  have hA_ne : E.amplitude (compiledArgument k₀ E s) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (ne_of_gt (E.amplitude_pos _))
  have hdiv := (hasDerivAt_const s ((k₀ : ℝ) * E.nu / 2)).div hsq hA_ne
  have h := hdiv.const_add ((k₀ : ℝ) * E.gamma / 2)
  change HasDerivAt
    (fun y => (k₀ : ℝ) * E.gamma / 2 +
      ((k₀ : ℝ) * E.nu / 2) /
        E.amplitude (compiledArgument k₀ E y) ^ 2)
    (compiledPhaseAcceleration k₀ E s) s
  apply h.congr_deriv
  rw [compiledPhaseAcceleration]
  field_simp [ne_of_gt (E.amplitude_pos (compiledArgument k₀ E s))]
  ring

theorem compiledPhaseSlope_continuous
    (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) :
    Continuous (compiledPhaseSlope k₀ E) := by
  rw [continuous_iff_continuousAt]
  intro s
  exact (compiledPhaseSlope_hasDerivAt k₀ E s).continuousAt

noncomputable def compiledPhase
    (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) (s : ℝ) : ℝ :=
  ∫ x in 0..s, compiledPhaseSlope k₀ E x

theorem compiledPhase_hasDerivAt
    (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) (s : ℝ) :
    HasDerivAt (compiledPhase k₀ E) (compiledPhaseSlope k₀ E s) s := by
  have hcont := compiledPhaseSlope_continuous k₀ E
  exact intervalIntegral.integral_hasDerivAt_right
    (hcont.intervalIntegrable 0 s)
    hcont.aestronglyMeasurable.stronglyMeasurableAtFilter
    hcont.continuousAt

noncomputable def compiledPolarProfile
    (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) : TravelingPolarProfile where
  amplitude := compiledCurvature k₀ E
  amplitude₁ := compiledCurvatureVelocity k₀ E
  amplitude₂ := compiledCurvatureAcceleration k₀ E
  phase := compiledPhase k₀ E
  phase₁ := compiledPhaseSlope k₀ E
  phase₂ := compiledPhaseAcceleration k₀ E
  amplitude_deriv := compiledCurvature_hasDerivAt k₀ E
  amplitude₁_deriv := compiledCurvatureVelocity_hasDerivAt k₀ E
  phase_deriv := compiledPhase_hasDerivAt k₀ E
  phase₁_deriv := compiledPhaseSlope_hasDerivAt k₀ E

theorem compiled_real_balance
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) (s : ℝ) :
    compiledWaveSpeed D k₀ E * compiledCurvature k₀ E s * compiledPhaseSlope k₀ E s +
      (D : ℝ) * (compiledCurvatureAcceleration k₀ E s -
        compiledCurvature k₀ E s * compiledPhaseSlope k₀ E s ^ 2 +
        compiledCurvature k₀ E s ^ 3 / 2) = 0 := by
  rw [compiledCurvature_equation, compiledWaveSpeed,
    compiledCurvature, compiledPhaseSlope]
  field_simp [D.ne_zero, ne_of_gt k₀.property,
    ne_of_gt (E.amplitude_pos (compiledArgument k₀ E s))]
  ring_nf

theorem compiled_imaginary_balance
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) (s : ℝ) :
    -compiledWaveSpeed D k₀ E * compiledCurvatureVelocity k₀ E s +
      (D : ℝ) * (2 * compiledCurvatureVelocity k₀ E s * compiledPhaseSlope k₀ E s +
        compiledCurvature k₀ E s * compiledPhaseAcceleration k₀ E s) = 0 := by
  rw [compiledWaveSpeed, compiledCurvatureVelocity, compiledPhaseSlope,
    compiledCurvature, compiledPhaseAcceleration]
  field_simp [D.ne_zero, ne_of_gt k₀.property,
    ne_of_gt (E.amplitude_pos (compiledArgument k₀ E s))]
  ring

noncomputable def compiledPolarNLSData
    (D : ℝˣ) (k₀ : PositiveCurvatureScale)
    (E : PositiveAmplitudeOscillator) : TravelingPolarNLSData where
  toTravelingPolarProfile := compiledPolarProfile k₀ E
  dispersion := D
  speed := compiledWaveSpeed D k₀ E
  real_balance := compiled_real_balance D k₀ E
  imaginary_balance := compiled_imaginary_balance D k₀ E

/-- Universal oscillator-to-NLS compiler for the paper's inverse-cubic amplitude law. -/
theorem compiledNLS_solves
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) :
    SolvesNLS (D : ℝ)
      (travelingPolarJet (compiledPolarProfile k₀ E) (compiledWaveSpeed D k₀ E)) :=
  travelingPolarNLSData_solves (compiledPolarNLSData D k₀ E)

theorem compiledPolarProfile_normSq
    (k₀ : PositiveCurvatureScale) (E : PositiveAmplitudeOscillator) (s : ℝ) :
    ‖polarProfile (compiledPolarProfile k₀ E) s‖ ^ 2 = compiledCurvature k₀ E s ^ 2 :=
  norm_polarProfile_sq (compiledPolarProfile k₀ E) s

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
