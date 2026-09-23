import GaloisForLFunctions.HTGeometry.WignerSmithLogClockObservability
import GaloisForLFunctions.HTGeometry.FiniteGeneratorDifferentialEscape
import GaloisForLFunctions.HTGeometry.ScalarLogCurrentReconstruction
import GaloisForLFunctions.HTGeometry.DifferentialAdjoinPairClassification
import GaloisForLFunctions.HTGeometry.SchwarzianHypertranscendence
import GaloisForLFunctions.RHTower.ProjectiveHorizonWardSeam
import GaloisForLFunctions.RHTower.ZetaChiHypertranscendentalClock
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances

/-!
# Phase--intensity observability of the centered zeta Gamma clock

The centered archimedean Gamma clock is

`R(w) = Gamma(1/4-w) / Gamma(1/4+w)`.

Frequency reflection gives `R(-w)=R(w)^{-1}` at the meromorphic level.  Consequently its
intensity channel is exactly one, whereas the phase channel is `R(w)^(2 : ℕ)`.  The general
opposite-orientation phase theorem proves that this square remains hypertranscendental.

The capstone is an exact blindness theorem: rational clocks and the complete unit intensity,
closed under finitely many field operations and differentiations, cannot recover the centered
Gamma phase.  This sharpens the role of the archimedean factor in RH searches without asserting
anything about zeta zeros.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace RHTower

open GaloisForLFunctions Bottcher Polynomial

noncomputable section

open scoped UnivMeroFieldInstances

/-- Frequency reflection of the centered zeta Gamma clock. -/
def centeredZetaGammaReflectedFrequencyMero : meroField Set.univ :=
  gammaOppositeShiftQuotientMero (1 / 4 : ℂ) (1 / 4 : ℂ)

/-- Reflected-frequency intensity of the centered zeta Gamma clock. -/
def centeredZetaGammaIntensityObservationMero : meroField Set.univ :=
  centeredZetaGammaReflectionMero * centeredZetaGammaReflectedFrequencyMero

/-- Orientation-sensitive phase of the centered zeta Gamma clock. -/
def centeredZetaGammaPhaseObservationMero : meroField Set.univ :=
  (gammaOppositeShiftPhaseMero (1 / 4 : ℂ) (1 / 4 : ℂ))⁻¹

/-- Logarithmic phase current of the centered zeta Gamma clock. -/
def centeredZetaGammaWignerSmithLogClockMero : meroField Set.univ :=
  HTGeometry.wignerSmithLogClock centeredZetaGammaReflectionMero

/-- Relative logarithmic connection between the reflected-frequency and reflection-clock jet
frames. -/
def centeredZetaGammaProjectiveHorizonConnectionMero : meroField Set.univ :=
  centeredZetaGammaReflectedFrequencyMero′′ /
      centeredZetaGammaReflectedFrequencyMero′ -
    centeredZetaGammaReflectionMero′′ / centeredZetaGammaReflectionMero′

/-- Projectively invariant curvature of the centered Gamma reflection clock. -/
def centeredZetaGammaProjectiveSchwarzianMero : meroField Set.univ :=
  schwarzian centeredZetaGammaReflectionMero

/-- The centered clock and its reflected-frequency carrier are exact reciprocals. -/
theorem centeredZetaGammaReflectionMero_eq_inv_reflectedFrequency :
    centeredZetaGammaReflectionMero =
      (centeredZetaGammaReflectedFrequencyMero)⁻¹ := by
  exact gammaReflectionRatioMero_eq_inv_oppositeShiftQuotient (1 / 4 : ℂ)

theorem centeredZetaGammaReflectedFrequencyMero_ne_zero :
    centeredZetaGammaReflectedFrequencyMero ≠ 0 := by
  exact gammaOppositeShiftQuotientMero_ne_zero _ _

/-- The centered zeta Gamma reflection clock is nonzero in the meromorphic field. -/
theorem centeredZetaGammaReflectionMero_ne_zero :
    centeredZetaGammaReflectionMero ≠ 0 := by
  rw [centeredZetaGammaReflectionMero_eq_inv_reflectedFrequency]
  exact inv_ne_zero centeredZetaGammaReflectedFrequencyMero_ne_zero

/-- **Centered Gamma projective-horizon complementarity.**  The actual frequency-reflected Gamma
carrier and the original reflection clock define distinct first-jet horizons.  Jointly they recover
the complete differential source field, while their common part retains the Schwarzian curvature.
All abstract HT hypotheses are discharged by the centered Gamma clock theorem. -/
theorem centeredZetaGamma_projectiveHorizon_complementarityProfile :
    jetTailField (RatFunc ℂ) centeredZetaGammaReflectedFrequencyMero 1 ≠
        jetTailField (RatFunc ℂ) centeredZetaGammaReflectionMero 1 ∧
      jetTailField (RatFunc ℂ) centeredZetaGammaReflectionMero 1 ⊔
          jetTailField (RatFunc ℂ) centeredZetaGammaReflectedFrequencyMero 1 =
        jetTailField (RatFunc ℂ) centeredZetaGammaReflectionMero 0 ∧
      schwarzian centeredZetaGammaReflectionMero ∈
        jetTailField (RatFunc ℂ) centeredZetaGammaReflectionMero 1 ⊓
          jetTailField (RatFunc ℂ) centeredZetaGammaReflectedFrequencyMero 1 := by
  have hinv : centeredZetaGammaReflectionMero⁻¹ =
      centeredZetaGammaReflectedFrequencyMero := by
    rw [centeredZetaGammaReflectionMero_eq_inv_reflectedFrequency, inv_inv]
  simpa only [hinv] using
    GaloisForLFunctions.hypertranscendentalOver_projectiveHorizon_complementarityProfile
      centeredZetaGammaReflectionMero
      hypertranscendentalOver_centeredZetaGammaReflectionMero

/-- **Shared centered Gamma horizon clock.**  The common Schwarzian observable of the opposite
first Gamma horizons is itself hypertranscendental, strengthening mere nontriviality of their
intersection. -/
theorem centeredZetaGamma_projectiveHorizon_sharedSchwarzianProfile :
    HypertranscendentalOver (RatFunc ℂ)
        centeredZetaGammaProjectiveSchwarzianMero ∧
      centeredZetaGammaProjectiveSchwarzianMero ∈
        jetTailField (RatFunc ℂ) centeredZetaGammaReflectionMero 1 ⊓
          jetTailField (RatFunc ℂ) centeredZetaGammaReflectedFrequencyMero 1 := by
  have hinv : centeredZetaGammaReflectionMero⁻¹ =
      centeredZetaGammaReflectedFrequencyMero := by
    rw [centeredZetaGammaReflectionMero_eq_inv_reflectedFrequency, inv_inv]
  simpa only [centeredZetaGammaProjectiveSchwarzianMero, hinv] using
    GaloisForLFunctions.hypertranscendentalOver_projectiveHorizon_sharedSchwarzianProfile
      centeredZetaGammaReflectionMero
      hypertranscendentalOver_centeredZetaGammaReflectionMero

/-- **Sharp centered Gamma horizon transition.** The opposite first Gamma horizons share a
nontrivial curvature field, whereas every positive-depth pair has only rational clocks in common
as soon as either horizon reaches depth two.  All ambient-generation and abstract HT hypotheses
are discharged. -/
theorem centeredZetaGamma_projectiveHorizon_sharpDepthTransition :
    jetTailField (RatFunc ℂ) centeredZetaGammaReflectionMero 1 ⊓
          jetTailField (RatFunc ℂ) centeredZetaGammaReflectedFrequencyMero 1 ≠ ⊥ ∧
      ∀ {m n : ℕ}, 1 ≤ m → 1 ≤ n → (2 ≤ m ∨ 2 ≤ n) →
        jetTailField (RatFunc ℂ) centeredZetaGammaReflectionMero m ⊓
            jetTailField (RatFunc ℂ) centeredZetaGammaReflectedFrequencyMero n = ⊥ := by
  have hinv : centeredZetaGammaReflectionMero⁻¹ =
      centeredZetaGammaReflectedFrequencyMero := by
    rw [centeredZetaGammaReflectionMero_eq_inv_reflectedFrequency, inv_inv]
  simpa only [hinv] using
    GaloisForLFunctions.hypertranscendentalOver_projectiveHorizon_sharpDepthTransition
      centeredZetaGammaReflectionMero
      hypertranscendentalOver_centeredZetaGammaReflectionMero

/-- **Centered Gamma log-current value relation.**  The Wigner--Smith current of the centered
reflection clock is the negative current of its reciprocal frequency-reflected carrier. -/
theorem centeredZetaGammaWignerSmithLogClockMero_eq_neg_reflectedFrequency :
    centeredZetaGammaWignerSmithLogClockMero =
      -gammaOppositeShiftWignerSmithLogMero (1 / 4 : ℂ) (1 / 4 : ℂ) := by
  unfold centeredZetaGammaWignerSmithLogClockMero HTGeometry.wignerSmithLogClock
  rw [centeredZetaGammaReflectionMero_eq_inv_reflectedFrequency, inv_eq_one_div,
    Differential.logDeriv_div]
  · simp only [Differential.logDeriv_one, zero_sub]
    rfl
  · exact one_ne_zero
  · exact centeredZetaGammaReflectedFrequencyMero_ne_zero

/-- **Exact intensity collapse.**  The complete reflected-frequency intensity of the centered
zeta Gamma clock is the unit meromorphic function. -/
theorem centeredZetaGammaIntensityObservationMero_eq_one :
    centeredZetaGammaIntensityObservationMero = 1 := by
  rw [centeredZetaGammaIntensityObservationMero,
    centeredZetaGammaReflectionMero_eq_inv_reflectedFrequency]
  exact inv_mul_cancel₀ centeredZetaGammaReflectedFrequencyMero_ne_zero

/-- The chosen phase is exactly the original clock divided by its frequency reflection. -/
theorem centeredZetaGammaPhaseObservationMero_eq_ratio :
    centeredZetaGammaPhaseObservationMero =
      centeredZetaGammaReflectionMero /
        centeredZetaGammaReflectedFrequencyMero := by
  rw [centeredZetaGammaPhaseObservationMero,
    gammaOppositeShiftPhaseMero_eq_symmetricProduct,
    centeredZetaGammaReflectionMero_eq_inv_reflectedFrequency]
  unfold centeredZetaGammaReflectedFrequencyMero
  field_simp [gammaOppositeShiftQuotientMero_ne_zero
    (1 / 4 : ℂ) (1 / 4 : ℂ)]

/-- **Phase value relation.**  The orientation-sensitive observation is the square of the
centered zeta Gamma reflection clock. -/
theorem centeredZetaGammaPhaseObservationMero_eq_square :
    centeredZetaGammaPhaseObservationMero =
      centeredZetaGammaReflectionMero ^ (2 : ℕ) := by
  rw [centeredZetaGammaPhaseObservationMero_eq_ratio,
    centeredZetaGammaReflectionMero_eq_inv_reflectedFrequency]
  field_simp [centeredZetaGammaReflectedFrequencyMero_ne_zero]

/-- **Phase--current connector.**  The logarithmic derivative of the complete centered Gamma
phase is exactly twice its Wigner--Smith current.  Intensity loses the clock, but phase and current
retain the same oriented logarithmic information. -/
theorem centeredZetaGammaPhaseObservationMero_logDeriv_eq_two_mul_wignerSmith :
    Differential.logDeriv centeredZetaGammaPhaseObservationMero =
      2 * centeredZetaGammaWignerSmithLogClockMero := by
  rw [centeredZetaGammaPhaseObservationMero_eq_square]
  unfold centeredZetaGammaWignerSmithLogClockMero HTGeometry.wignerSmithLogClock
  exact HTGeometry.differential_logDeriv_pow
    centeredZetaGammaReflectionMero centeredZetaGammaReflectionMero_ne_zero 2

/-- **Centered Gamma projective-connection observability.** The reciprocal-horizon connection is
exactly minus twice the Wigner--Smith current, hence also the negative logarithmic derivative of
the observed phase.  Hypertranscendence discharges both source-jet nonvanishing conditions. -/
theorem centeredZetaGamma_projectiveHorizonConnection_observabilityProfile :
    centeredZetaGammaProjectiveHorizonConnectionMero =
        -2 * centeredZetaGammaWignerSmithLogClockMero ∧
      centeredZetaGammaProjectiveHorizonConnectionMero =
        -Differential.logDeriv centeredZetaGammaPhaseObservationMero := by
  have hconn :=
    GaloisForLFunctions.hypertranscendentalOver_projectiveHorizon_reciprocalConnection
      centeredZetaGammaReflectionMero
      hypertranscendentalOver_centeredZetaGammaReflectionMero
  have hinv : centeredZetaGammaReflectionMero⁻¹ =
      centeredZetaGammaReflectedFrequencyMero := by
    rw [centeredZetaGammaReflectionMero_eq_inv_reflectedFrequency, inv_inv]
  rw [hinv] at hconn
  have hcurrent : centeredZetaGammaProjectiveHorizonConnectionMero =
      -2 * centeredZetaGammaWignerSmithLogClockMero := by
    unfold centeredZetaGammaProjectiveHorizonConnectionMero
      centeredZetaGammaWignerSmithLogClockMero HTGeometry.wignerSmithLogClock
      Differential.logDeriv
    exact hconn
  refine ⟨hcurrent, ?_⟩
  rw [hcurrent,
    centeredZetaGammaPhaseObservationMero_logDeriv_eq_two_mul_wignerSmith]
  ring

/-- **Phase-current field invariance.**  Logarithmic differentiation of the observed squared
phase generates exactly the same differential field as the Wigner--Smith current of the original
reflection clock.  The square observation loses only an ordinary amplitude sign, not differential
current information. -/
theorem differentialAdjoin_centeredZetaGammaPhase_logDeriv_eq_wignerSmith :
    differentialAdjoin (RatFunc ℂ)
        ({Differential.logDeriv centeredZetaGammaPhaseObservationMero} :
          Set (meroField Set.univ)) =
      differentialAdjoin (RatFunc ℂ)
        ({centeredZetaGammaWignerSmithLogClockMero} :
          Set (meroField Set.univ)) := by
  rw [centeredZetaGammaPhaseObservationMero_eq_square]
  unfold centeredZetaGammaWignerSmithLogClockMero HTGeometry.wignerSmithLogClock
  exact HTGeometry.differentialAdjoin_logDeriv_pow_eq
    (F := RatFunc ℂ) centeredZetaGammaReflectionMero_ne_zero
      (N := 2) (by norm_num)

/-- The reciprocal projective-horizon connection, the observed phase current, and the original
Wigner--Smith current generate exactly the same differential field. -/
theorem differentialAdjoin_centeredZetaGammaProjectiveHorizonConnection_eq_wignerSmith :
    differentialAdjoin (RatFunc ℂ)
        ({centeredZetaGammaProjectiveHorizonConnectionMero} :
          Set (meroField Set.univ)) =
      differentialAdjoin (RatFunc ℂ)
        ({centeredZetaGammaWignerSmithLogClockMero} :
          Set (meroField Set.univ)) := by
  rw [centeredZetaGamma_projectiveHorizonConnection_observabilityProfile.2,
    GaloisForLFunctions.differentialAdjoin_neg_singleton,
    differentialAdjoin_centeredZetaGammaPhase_logDeriv_eq_wignerSmith]

/-- **Exact phase-current finite-cover reconstruction.**  The differential field generated by
the centered Gamma phase is the ordinary field obtained by adjoining that phase coordinate to the
Wigner--Smith current field.  Thus no further differential generators are hidden in the square
phase channel. -/
theorem differentialAdjoin_centeredZetaGammaPhase_eq_current_adjoin_phase :
    differentialAdjoin (RatFunc ℂ)
        ({centeredZetaGammaPhaseObservationMero} : Set (meroField Set.univ)) =
      IntermediateField.adjoin (RatFunc ℂ)
        (((differentialAdjoin (RatFunc ℂ)
          ({centeredZetaGammaWignerSmithLogClockMero} :
            Set (meroField Set.univ)) :
              IntermediateField (RatFunc ℂ) (meroField Set.univ)) :
            Set (meroField Set.univ)) ∪
          {centeredZetaGammaPhaseObservationMero}) := by
  rw [centeredZetaGammaPhaseObservationMero_eq_square]
  unfold centeredZetaGammaWignerSmithLogClockMero HTGeometry.wignerSmithLogClock
  exact HTGeometry.differentialAdjoin_pow_eq_logCurrentOrdinaryExtension
    (F := RatFunc ℂ) centeredZetaGammaReflectionMero_ne_zero
      (N := 2) (by norm_num)

/-- Every differential observable of the centered Gamma Wigner--Smith current is reconstructible
from the phase channel.  Together with intensity blindness, this gives the exact one-way
observability order `intensity < phase`. -/
theorem centeredZetaGammaCurrentField_le_phaseField :
    differentialAdjoin (RatFunc ℂ)
        ({centeredZetaGammaWignerSmithLogClockMero} :
          Set (meroField Set.univ)) ≤
      differentialAdjoin (RatFunc ℂ)
        ({centeredZetaGammaPhaseObservationMero} :
          Set (meroField Set.univ)) := by
  intro z hz
  rw [differentialAdjoin_centeredZetaGammaPhase_eq_current_adjoin_phase]
  exact IntermediateField.subset_adjoin (RatFunc ℂ) _
    (Set.mem_union_left _ hz)

/-- Squaring the centered zeta Gamma clock does not remove its HT source. -/
theorem hypertranscendentalOver_centeredZetaGammaPhaseObservationMero :
    HypertranscendentalOver (RatFunc ℂ)
      centeredZetaGammaPhaseObservationMero := by
  unfold centeredZetaGammaPhaseObservationMero
  exact HTGeometry.hypertranscendentalOver_inv_iff.mpr
    (hypertranscendentalOver_gammaOppositeShiftPhaseMero
      (1 / 4 : ℂ) (1 / 4 : ℂ))

/-- The centered Gamma intensity is DA because it is exactly one. -/
theorem differentialAlgebraicOver_centeredZetaGammaIntensityObservationMero :
    DifferentialAlgebraicOver (RatFunc ℂ)
      centeredZetaGammaIntensityObservationMero := by
  rw [centeredZetaGammaIntensityObservationMero_eq_one]
  simpa only [map_one] using
    (HTGeometry.differentialAlgebraicOver_algebraMap (1 : RatFunc ℂ) :
      DifferentialAlgebraicOver (RatFunc ℂ)
        (algebraMap (RatFunc ℂ) (meroField Set.univ) 1))

/-- The centered archimedean logarithmic phase current retains the HT Gamma source. -/
theorem hypertranscendentalOver_centeredZetaGammaWignerSmithLogClockMero :
    HypertranscendentalOver (RatFunc ℂ)
      centeredZetaGammaWignerSmithLogClockMero := by
  rw [centeredZetaGammaWignerSmithLogClockMero,
    HTGeometry.hypertranscendentalOver_wignerSmithLogClock_iff]
  exact hypertranscendentalOver_centeredZetaGammaReflectionMero

/-- The reciprocal projective-horizon connection retains the HT Gamma current. -/
theorem hypertranscendentalOver_centeredZetaGammaProjectiveHorizonConnectionMero :
    HypertranscendentalOver (RatFunc ℂ)
      centeredZetaGammaProjectiveHorizonConnectionMero := by
  rw [centeredZetaGamma_projectiveHorizonConnection_observabilityProfile.1]
  have hscale : DifferentialAlgebraicOver (RatFunc ℂ)
      (-2 : meroField Set.univ) := by
    simpa only [map_neg, map_ofNat] using
      (HTGeometry.differentialAlgebraicOver_algebraMap (-2 : RatFunc ℂ) :
        DifferentialAlgebraicOver (RatFunc ℂ)
          (algebraMap (RatFunc ℂ) (meroField Set.univ) (-2 : RatFunc ℂ)))
  have hscaled :=
    (HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
      hscale (by norm_num : (-2 : meroField Set.univ) ≠ 0)).2
        hypertranscendentalOver_centeredZetaGammaWignerSmithLogClockMero
  simpa only [mul_comm] using hscaled

/-- The shared projective Schwarzian curvature retains the HT Gamma source. -/
theorem hypertranscendentalOver_centeredZetaGammaProjectiveSchwarzianMero :
    HypertranscendentalOver (RatFunc ℂ)
      centeredZetaGammaProjectiveSchwarzianMero :=
  centeredZetaGamma_projectiveHorizon_sharedSchwarzianProfile.1

/-- **Complete centered Gamma observability profile.**  Intensity is identically one, phase is
the squared reflection clock, its logarithmic derivative is twice the Wigner--Smith current, and
the reciprocal projective connection is its negative; all three oriented observables remain
hypertranscendental over rational clocks. -/
theorem centeredZetaGamma_phaseIntensityCurrent_observabilityProfile :
    centeredZetaGammaIntensityObservationMero = 1 ∧
      centeredZetaGammaPhaseObservationMero =
        centeredZetaGammaReflectionMero ^ (2 : ℕ) ∧
      Differential.logDeriv centeredZetaGammaPhaseObservationMero =
        2 * centeredZetaGammaWignerSmithLogClockMero ∧
      HypertranscendentalOver (RatFunc ℂ)
        centeredZetaGammaPhaseObservationMero ∧
      HypertranscendentalOver (RatFunc ℂ)
        centeredZetaGammaWignerSmithLogClockMero ∧
      centeredZetaGammaProjectiveHorizonConnectionMero =
        -Differential.logDeriv centeredZetaGammaPhaseObservationMero ∧
      HypertranscendentalOver (RatFunc ℂ)
        centeredZetaGammaProjectiveHorizonConnectionMero := by
  exact ⟨centeredZetaGammaIntensityObservationMero_eq_one,
    centeredZetaGammaPhaseObservationMero_eq_square,
    centeredZetaGammaPhaseObservationMero_logDeriv_eq_two_mul_wignerSmith,
    hypertranscendentalOver_centeredZetaGammaPhaseObservationMero,
    hypertranscendentalOver_centeredZetaGammaWignerSmithLogClockMero,
    centeredZetaGamma_projectiveHorizonConnection_observabilityProfile.2,
    hypertranscendentalOver_centeredZetaGammaProjectiveHorizonConnectionMero⟩

/-- **Positive finite-generator phase escape.**  Every finite rational state packet containing the
centered zeta Gamma phase loses differential closure at one of its chosen generators. -/
theorem exists_generator_deriv_escape_of_centeredZetaGammaPhaseObservationMero
    {ι : Type*} [Fintype ι] (s : ι → meroField Set.univ)
    (hmem : centeredZetaGammaPhaseObservationMero ∈
      IntermediateField.adjoin (RatFunc ℂ) (Set.range s)) :
    ∃ i, (s i)′ ∉ IntermediateField.adjoin (RatFunc ℂ) (Set.range s) :=
  GaloisForLFunctions.HTGeometry.exists_generator_deriv_escape_of_hypertranscendentalOver
    s hypertranscendentalOver_centeredZetaGammaPhaseObservationMero hmem

/-- **Positive finite-generator current escape.**  Every finite rational state packet containing
the centered archimedean Wigner--Smith logarithmic current loses differential closure at one of its
chosen generators. -/
theorem exists_generator_deriv_escape_of_centeredZetaGammaWignerSmithLogClockMero
    {ι : Type*} [Fintype ι] (s : ι → meroField Set.univ)
    (hmem : centeredZetaGammaWignerSmithLogClockMero ∈
      IntermediateField.adjoin (RatFunc ℂ) (Set.range s)) :
    ∃ i, (s i)′ ∉ IntermediateField.adjoin (RatFunc ℂ) (Set.range s) :=
  GaloisForLFunctions.HTGeometry.exists_generator_deriv_escape_of_hypertranscendentalOver
    s hypertranscendentalOver_centeredZetaGammaWignerSmithLogClockMero hmem

/-- **Positive finite-generator projective-connection escape.** Every finite rational state packet
containing the centered Gamma reciprocal-horizon connection loses differential closure at one of
its chosen generators. -/
theorem exists_generator_deriv_escape_of_centeredZetaGammaProjectiveHorizonConnectionMero
    {ι : Type*} [Fintype ι] (s : ι → meroField Set.univ)
    (hmem : centeredZetaGammaProjectiveHorizonConnectionMero ∈
      IntermediateField.adjoin (RatFunc ℂ) (Set.range s)) :
    ∃ i, (s i)′ ∉ IntermediateField.adjoin (RatFunc ℂ) (Set.range s) :=
  GaloisForLFunctions.HTGeometry.exists_generator_deriv_escape_of_hypertranscendentalOver
    s hypertranscendentalOver_centeredZetaGammaProjectiveHorizonConnectionMero hmem

/-- **Positive finite-generator Schwarzian escape.** Every finite rational state packet containing
the shared centered Gamma projective curvature loses differential closure at one generator. -/
theorem exists_generator_deriv_escape_of_centeredZetaGammaProjectiveSchwarzianMero
    {I : Type*} [Fintype I] (s : I → meroField Set.univ)
    (hmem : centeredZetaGammaProjectiveSchwarzianMero ∈
      IntermediateField.adjoin (RatFunc ℂ) (Set.range s)) :
    ∃ i, (s i)′ ∉ IntermediateField.adjoin (RatFunc ℂ) (Set.range s) :=
  GaloisForLFunctions.HTGeometry.exists_generator_deriv_escape_of_hypertranscendentalOver
    s hypertranscendentalOver_centeredZetaGammaProjectiveSchwarzianMero hmem

/-- **RH-search observability boundary.**  Rational clocks and the unit intensity, closed under
finite field operations and differentiation, cannot reconstruct the centered Gamma phase. -/
theorem no_scalarAwareFiniteDifferentialCircuit_centeredZetaGammaPhase_from_intensity :
    ¬ HTGeometry.FiniteDifferentialCircuit
      (HTGeometry.BaseScalarOrAtom (RatFunc ℂ) (meroField Set.univ)
        (fun a => a = centeredZetaGammaIntensityObservationMero))
      centeredZetaGammaPhaseObservationMero := by
  intro hcircuit
  obtain ⟨a, ha, hHT⟩ :=
    HTGeometry.exists_hypertranscendental_atom_of_scalarAwareFiniteDifferentialCircuit
      hypertranscendentalOver_centeredZetaGammaPhaseObservationMero hcircuit
  rw [ha] at hHT
  exact hHT differentialAlgebraicOver_centeredZetaGammaIntensityObservationMero

/-- **RH-search logarithmic observability boundary.**  Rational clocks and the complete unit
intensity cannot finitely reconstruct the HT logarithmic phase current of the centered Gamma
factor. -/
theorem no_scalarAwareFiniteDifferentialCircuit_centeredZetaGammaWignerSmith_from_intensity :
    ¬ HTGeometry.FiniteDifferentialCircuit
      (HTGeometry.BaseScalarOrAtom (RatFunc ℂ) (meroField Set.univ)
        (fun a => a = centeredZetaGammaIntensityObservationMero))
      centeredZetaGammaWignerSmithLogClockMero := by
  exact HTGeometry.no_scalarAwareFiniteDifferentialCircuit_wignerSmith_from_daObservation
    centeredZetaGammaReflectionMero
    centeredZetaGammaIntensityObservationMero
    hypertranscendentalOver_centeredZetaGammaReflectionMero
    differentialAlgebraicOver_centeredZetaGammaIntensityObservationMero

/-- Rational clocks and the complete unit intensity cannot finitely reconstruct the HT reciprocal
projective-horizon connection of the centered Gamma factor. -/
theorem no_scalarAwareFiniteDifferentialCircuit_centeredZetaGammaProjectiveConnection_from_intensity :
    ¬ HTGeometry.FiniteDifferentialCircuit
      (HTGeometry.BaseScalarOrAtom (RatFunc ℂ) (meroField Set.univ)
        (fun a => a = centeredZetaGammaIntensityObservationMero))
      centeredZetaGammaProjectiveHorizonConnectionMero := by
  intro hcircuit
  obtain ⟨a, ha, hHT⟩ :=
    HTGeometry.exists_hypertranscendental_atom_of_scalarAwareFiniteDifferentialCircuit
      hypertranscendentalOver_centeredZetaGammaProjectiveHorizonConnectionMero hcircuit
  rw [ha] at hHT
  exact hHT differentialAlgebraicOver_centeredZetaGammaIntensityObservationMero

/-- Rational clocks and the complete unit intensity cannot finitely reconstruct the shared HT
Schwarzian curvature of the opposite centered Gamma horizons. -/
theorem no_scalarAwareFiniteDifferentialCircuit_centeredZetaGammaProjectiveSchwarzian_from_intensity :
    ¬ HTGeometry.FiniteDifferentialCircuit
      (HTGeometry.BaseScalarOrAtom (RatFunc ℂ) (meroField Set.univ)
        (fun a => a = centeredZetaGammaIntensityObservationMero))
      centeredZetaGammaProjectiveSchwarzianMero := by
  intro hcircuit
  obtain ⟨a, ha, hHT⟩ :=
    HTGeometry.exists_hypertranscendental_atom_of_scalarAwareFiniteDifferentialCircuit
      hypertranscendentalOver_centeredZetaGammaProjectiveSchwarzianMero hcircuit
  rw [ha] at hHT
  exact hHT differentialAlgebraicOver_centeredZetaGammaIntensityObservationMero

end

end RHTower
