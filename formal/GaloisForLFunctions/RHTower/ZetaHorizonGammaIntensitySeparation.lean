import GaloisForLFunctions.HTGeometry.HorizonBogoliubovGammaObservability
import GaloisForLFunctions.HTGeometry.ThermalCFTGammaResponseBoundary
import GaloisForLFunctions.HTGeometry.FiniteGeneratorDifferentialEscape
import GaloisForLFunctions.RHTower.ZetaGammaPhaseIntensityObservability
import GaloisForLFunctions.RHTower.ZetaChiHypertranscendentalClock
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances

/-!
# Zeta--horizon Gamma intensity separation

Conjugate-frequency multiplication has opposite differential outcomes for two exact physical
Gamma clocks.  The thermal-horizon carrier of `HorizonBogoliubovGammaObservability` is centered at
zero, and its intensity `Gamma(z)*Gamma(-z)` is differentially algebraic.  The centered zeta
completion is shifted by `1/4`; its corresponding intensity is

`Gamma(z+1/4) * Gamma(-z+1/4)`.

The general opposite-orientation classification sees the difference exactly: the horizon shifts
sum to the integer `0`, whereas the zeta shifts sum to the noninteger `1/2`.  Hence the zeta
intensity remains hypertranscendental.

This has a direct observability consequence for the RH corpus.  No scalar-aware finite
differential circuit can manufacture the zeta intensity from the horizon intensity, and no DA
multiplicative calibration identifies the zeta phase with its intensity.  Modulus-square
coarse-graining therefore does not have a universal differential effect; the affine center read
by the observable is decisive.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace RHTower

open GaloisForLFunctions Bottcher Polynomial

noncomputable section

open scoped UnivMeroFieldInstances

/-- Conjugate-frequency Gamma intensity of zeta's centered archimedean completion clock. -/
def centeredZetaGammaIntensityCoreMero : meroField Set.univ :=
  gammaReflectionProductMero (1 / 4)

/-- The zeta intensity is the quarter-weight specialization of both the thermal-CFT symmetric
kernel and the general opposite-orientation Gamma product. -/
theorem centeredZetaGammaIntensityCoreMero_eq_oppositeProduct :
    centeredZetaGammaIntensityCoreMero =
      gammaOppositeShiftProductMero (1 / 4) (1 / 4) := rfl

private theorem complex_half_ne_integer (k : ℤ) :
    (1 / 2 : ℂ) ≠ (k : ℂ) := by
  intro h
  have htwo := congrArg (fun z : ℂ => 2 * z) h
  norm_num at htwo
  have htwoZ : (1 : ℤ) = 2 * k := by exact_mod_cast htwo
  omega

/-- **Zeta intensity survival.**  The quarter-shifted conjugate-frequency pair is HT because its
physical shift sum is `1/2`, outside the integer cancellation lattice. -/
theorem hypertranscendentalOver_centeredZetaGammaIntensityCoreMero :
    HypertranscendentalOver (RatFunc ℂ)
      centeredZetaGammaIntensityCoreMero := by
  rw [centeredZetaGammaIntensityCoreMero,
    hypertranscendentalOver_gammaReflectionProductMero_iff_nonintegerWeight]
  intro k
  norm_num
  exact complex_half_ne_integer k

private theorem gammaNegativeQuarterMero_ne_zero :
    gammaNegativeShiftMero (1 / 4) ≠ 0 := by
  rw [gammaNegativeShiftMero_reflection]
  exact mul_ne_zero (gammaReflectionGaugeMero_ne_zero (1 / 4))
    (inv_ne_zero (gammaShiftMero_ne_zero (1 - 1 / 4)))

/-- Multiplying the centered reflection clock by the quarter-shifted Gamma intensity recovers the
square of the negative-frequency Gamma amplitude. -/
theorem centeredZetaGammaReflection_mul_intensity_eq_negativeSquare :
    centeredZetaGammaReflectionMero * centeredZetaGammaIntensityCoreMero =
      gammaNegativeShiftMero (1 / 4) ^ 2 := by
  rw [centeredZetaGammaReflectionMero, gammaReflectionRatioMero,
    centeredZetaGammaIntensityCoreMero, gammaReflectionProductMero]
  field_simp [gammaShiftMero_ne_zero (1 / 4), gammaNegativeQuarterMero_ne_zero]
  exact mul_div_cancel_right₀ _ (gammaShiftMero_ne_zero (1 / 4))

/-- Dividing the centered zeta phase by its intensity cancels the negative-frequency factor and
leaves the inverse square of the positive-frequency Gamma carrier. -/
theorem centeredZetaGammaReflection_div_intensity_eq_inv_positivePair :
    centeredZetaGammaReflectionMero /
        centeredZetaGammaIntensityCoreMero =
      (gammaPositiveShiftPairMero (1 / 4) (1 / 4))⁻¹ := by
  rw [centeredZetaGammaReflectionMero, gammaReflectionRatioMero,
    centeredZetaGammaIntensityCoreMero, gammaReflectionProductMero,
    gammaPositiveShiftPairMero]
  have hp : gammaShiftMero (1 / 4) ≠ 0 :=
    gammaShiftMero_ne_zero (1 / 4)
  have hn : gammaNegativeShiftMero (1 / 4) ≠ 0 :=
    gammaNegativeQuarterMero_ne_zero
  field_simp [hp, hn, mul_ne_zero hn (pow_ne_zero 2 hp)]

/-- Dividing the quarter-shifted Gamma intensity by the centered reflection clock recovers the
square of the positive-frequency Gamma amplitude. -/
theorem centeredZetaGammaIntensity_div_reflection_eq_positiveSquare :
    centeredZetaGammaIntensityCoreMero / centeredZetaGammaReflectionMero =
      gammaPositiveShiftPairMero (1 / 4) (1 / 4) := by
  rw [centeredZetaGammaReflectionMero, gammaReflectionRatioMero,
    centeredZetaGammaIntensityCoreMero, gammaReflectionProductMero,
    gammaPositiveShiftPairMero]
  field_simp [gammaShiftMero_ne_zero (1 / 4), gammaNegativeQuarterMero_ne_zero]
  exact mul_div_cancel_right₀ _ gammaNegativeQuarterMero_ne_zero

/-- Zeta's phase and intensity retain inequivalent HT information: their quotient is itself HT. -/
theorem hypertranscendentalOver_centeredZetaGammaReflection_div_intensity :
    HypertranscendentalOver (RatFunc ℂ)
      (centeredZetaGammaReflectionMero /
        centeredZetaGammaIntensityCoreMero) := by
  rw [centeredZetaGammaReflection_div_intensity_eq_inv_positivePair,
    HTGeometry.hypertranscendentalOver_inv_iff]
  exact hypertranscendentalOver_gammaPositiveShiftPairMero (1 / 4) (1 / 4)

/-- **Joint phase--intensity negative-amplitude recovery.**  The observable squared phase and
the shifted Gamma intensity recover the fourth power of the negative-frequency Gamma amplitude. -/
theorem centeredZetaGammaPhase_mul_intensity_sq_eq_negativeFourth :
    centeredZetaGammaPhaseObservationMero *
        centeredZetaGammaIntensityCoreMero ^ 2 =
      gammaNegativeShiftMero (1 / 4) ^ 4 := by
  rw [centeredZetaGammaPhaseObservationMero_eq_square]
  calc
    centeredZetaGammaReflectionMero ^ 2 *
          centeredZetaGammaIntensityCoreMero ^ 2 =
        (centeredZetaGammaReflectionMero *
          centeredZetaGammaIntensityCoreMero) ^ 2 := by ring
    _ = gammaNegativeShiftMero (1 / 4) ^ 4 := by
      rw [centeredZetaGammaReflection_mul_intensity_eq_negativeSquare]
      ring

/-- **Joint phase--intensity positive-amplitude recovery.**  Dividing the squared shifted
intensity by phase recovers the fourth power of the positive-frequency Gamma amplitude. -/
theorem centeredZetaGammaIntensity_sq_div_phase_eq_positiveFourth :
    centeredZetaGammaIntensityCoreMero ^ 2 /
        centeredZetaGammaPhaseObservationMero =
      gammaShiftMero (1 / 4) ^ 4 := by
  rw [centeredZetaGammaPhaseObservationMero_eq_square]
  calc
    centeredZetaGammaIntensityCoreMero ^ 2 /
          centeredZetaGammaReflectionMero ^ 2 =
        (centeredZetaGammaIntensityCoreMero /
          centeredZetaGammaReflectionMero) ^ 2 := by
            field_simp [centeredZetaGammaReflectionMero_ne_zero]
    _ = gammaShiftMero (1 / 4) ^ 4 := by
      rw [centeredZetaGammaIntensity_div_reflection_eq_positiveSquare,
        gammaPositiveShiftPairMero]
      ring

/-- The negative-frequency amplitude recovered from joint phase--intensity data remains
hypertranscendental. -/
theorem hypertranscendentalOver_centeredZetaGammaPhase_mul_intensity_sq :
    HypertranscendentalOver (RatFunc ℂ)
      (centeredZetaGammaPhaseObservationMero *
        centeredZetaGammaIntensityCoreMero ^ 2) := by
  rw [centeredZetaGammaPhase_mul_intensity_sq_eq_negativeFourth]
  have h := hypertranscendentalOver_gammaFintypeNegativeOrbitProductMero_of_pos
    (fun _ : Fin 1 => (1 / 4 : ℂ)) (fun _ : Fin 1 => (4 : ℤ))
    (by intro i; norm_num)
  simpa [gammaFintypeNegativeOrbitProductMero] using! h

/-- The positive-frequency amplitude recovered from joint phase--intensity data remains
hypertranscendental. -/
theorem hypertranscendentalOver_centeredZetaGammaIntensity_sq_div_phase :
    HypertranscendentalOver (RatFunc ℂ)
      (centeredZetaGammaIntensityCoreMero ^ 2 /
        centeredZetaGammaPhaseObservationMero) := by
  rw [centeredZetaGammaIntensity_sq_div_phase_eq_positiveFourth]
  have h := hypertranscendentalOver_gammaFintypeOrbitProductMero_of_pos
    (fun _ : Fin 1 => (1 / 4 : ℂ)) (fun _ : Fin 1 => (4 : ℤ))
    (by intro i; norm_num)
  simpa [gammaFintypeOrbitProductMero] using! h

/-- **Centered Gamma joint tomography profile.**  Phase and shifted intensity together recover
both oriented quarter-shifted Gamma amplitudes up to fourth power, and neither recovered channel
becomes differentially algebraic. -/
theorem centeredZetaGamma_phaseCoreIntensity_amplitudeTomographyProfile :
    centeredZetaGammaPhaseObservationMero *
          centeredZetaGammaIntensityCoreMero ^ 2 =
        gammaNegativeShiftMero (1 / 4) ^ 4 ∧
      centeredZetaGammaIntensityCoreMero ^ 2 /
          centeredZetaGammaPhaseObservationMero =
        gammaShiftMero (1 / 4) ^ 4 ∧
      HypertranscendentalOver (RatFunc ℂ)
        (centeredZetaGammaPhaseObservationMero *
          centeredZetaGammaIntensityCoreMero ^ 2) ∧
      HypertranscendentalOver (RatFunc ℂ)
        (centeredZetaGammaIntensityCoreMero ^ 2 /
          centeredZetaGammaPhaseObservationMero) := by
  exact ⟨centeredZetaGammaPhase_mul_intensity_sq_eq_negativeFourth,
    centeredZetaGammaIntensity_sq_div_phase_eq_positiveFourth,
    hypertranscendentalOver_centeredZetaGammaPhase_mul_intensity_sq,
    hypertranscendentalOver_centeredZetaGammaIntensity_sq_div_phase⟩

/-- **Positive finite-generator intensity escape.**  Every finite rational state packet containing
the quarter-shifted zeta Gamma intensity loses differential closure at a chosen generator. -/
theorem exists_generator_deriv_escape_of_centeredZetaGammaIntensityCoreMero
    {ι : Type*} [Fintype ι] (s : ι → meroField Set.univ)
    (hmem : centeredZetaGammaIntensityCoreMero ∈
      IntermediateField.adjoin (RatFunc ℂ) (Set.range s)) :
    ∃ i, (s i)′ ∉ IntermediateField.adjoin (RatFunc ℂ) (Set.range s) :=
  GaloisForLFunctions.HTGeometry.exists_generator_deriv_escape_of_hypertranscendentalOver
    s hypertranscendentalOver_centeredZetaGammaIntensityCoreMero hmem

/-- **Positive finite-generator calibration escape.**  Every finite rational state packet
containing the quotient of zeta's oriented Gamma clock by its intensity loses differential closure
at a chosen generator. -/
theorem exists_generator_deriv_escape_of_centeredZetaGammaReflection_div_intensity
    {ι : Type*} [Fintype ι] (s : ι → meroField Set.univ)
    (hmem : centeredZetaGammaReflectionMero / centeredZetaGammaIntensityCoreMero ∈
      IntermediateField.adjoin (RatFunc ℂ) (Set.range s)) :
    ∃ i, (s i)′ ∉ IntermediateField.adjoin (RatFunc ℂ) (Set.range s) :=
  GaloisForLFunctions.HTGeometry.exists_generator_deriv_escape_of_hypertranscendentalOver
    s hypertranscendentalOver_centeredZetaGammaReflection_div_intensity hmem

/-- No DA multiplicative calibration converts the zeta intensity into its oriented Gamma phase. -/
theorem centeredZetaGammaReflectionMero_ne_da_mul_intensity
    (g : meroField Set.univ)
    (hg : DifferentialAlgebraicOver (RatFunc ℂ) g) :
    centeredZetaGammaReflectionMero ≠
      g * centeredZetaGammaIntensityCoreMero := by
  intro heq
  apply hypertranscendentalOver_centeredZetaGammaReflection_div_intensity
  have hintensity : centeredZetaGammaIntensityCoreMero ≠ 0 := by
    rw [centeredZetaGammaIntensityCoreMero, gammaReflectionProductMero]
    exact mul_ne_zero (gammaShiftMero_ne_zero (1 / 4))
      gammaNegativeQuarterMero_ne_zero
  rw [heq]
  simpa [hintensity] using hg

/-- **Direct `HTGeometry` to `RHTower` obstruction.**  Rational clock data together with the DA
horizon intensity, closed under finitely many field operations and differentiations, cannot
produce zeta's HT quarter-shifted archimedean intensity. -/
theorem no_scalarAwareFiniteDifferentialCircuit_centeredZetaIntensity_from_horizonIntensity :
    ¬ HTGeometry.FiniteDifferentialCircuit
      (HTGeometry.BaseScalarOrAtom (RatFunc ℂ) (meroField Set.univ)
        (fun a => a = horizonBogoliubovGammaIntensityCoreMero))
      centeredZetaGammaIntensityCoreMero := by
  intro hcircuit
  obtain ⟨a, ha, hHT⟩ :=
    HTGeometry.exists_hypertranscendental_atom_of_scalarAwareFiniteDifferentialCircuit
      hypertranscendentalOver_centeredZetaGammaIntensityCoreMero hcircuit
  rw [ha] at hHT
  exact hHT differentialAlgebraicOver_horizonBogoliubovGammaIntensityCoreMero

end

end RHTower
