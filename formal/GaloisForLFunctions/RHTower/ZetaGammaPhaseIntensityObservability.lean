import GaloisForLFunctions.HTGeometry.GammaReflectedFrequencyObservability
import GaloisForLFunctions.RHTower.ZetaChiHypertranscendentalClock

/-!
# Phase--intensity observability of the centered zeta Gamma clock

The centered archimedean Gamma clock is

`R(w) = Gamma(1/4-w) / Gamma(1/4+w)`.

Frequency reflection gives `R(-w)=R(w)^{-1}` at the meromorphic level.  Consequently its
intensity channel is exactly one, whereas the phase channel is `R(w)^2`.  The general
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

local instance zetaGammaObservabilityDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance zetaGammaObservabilityDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance zetaGammaObservabilityRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField Set.univ) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

local instance zetaGammaObservabilityRatFuncDifferential :
    Differential (RatFunc ℂ) := ratFuncCoordinateDifferential

local instance zetaGammaObservabilityDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField Set.univ) :=
  { deriv_algebraMap := fun r => meroField_deriv_ratfuncToMero r }

local instance zetaGammaObservabilityCharZero :
    CharZero (meroField Set.univ) :=
  charZero_of_injective_algebraMap
    (algebraMap (RatFunc ℂ) (meroField Set.univ)).injective

/-- Frequency reflection of the centered zeta Gamma clock. -/
def centeredZetaGammaReflectedFrequencyMero : meroField Set.univ :=
  gammaOppositeShiftQuotientMero (1 / 4 : ℂ) (1 / 4 : ℂ)

/-- Reflected-frequency intensity of the centered zeta Gamma clock. -/
def centeredZetaGammaIntensityObservationMero : meroField Set.univ :=
  centeredZetaGammaReflectionMero * centeredZetaGammaReflectedFrequencyMero

/-- Orientation-sensitive phase of the centered zeta Gamma clock. -/
def centeredZetaGammaPhaseObservationMero : meroField Set.univ :=
  (gammaOppositeShiftPhaseMero (1 / 4 : ℂ) (1 / 4 : ℂ))⁻¹

/-- The centered clock and its reflected-frequency carrier are exact reciprocals. -/
theorem centeredZetaGammaReflectionMero_eq_inv_reflectedFrequency :
    centeredZetaGammaReflectionMero =
      (centeredZetaGammaReflectedFrequencyMero)⁻¹ := by
  exact gammaReflectionRatioMero_eq_inv_oppositeShiftQuotient (1 / 4 : ℂ)

theorem centeredZetaGammaReflectedFrequencyMero_ne_zero :
    centeredZetaGammaReflectedFrequencyMero ≠ 0 := by
  exact gammaOppositeShiftQuotientMero_ne_zero _ _

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
      centeredZetaGammaReflectionMero ^ 2 := by
  rw [centeredZetaGammaPhaseObservationMero_eq_ratio,
    centeredZetaGammaReflectionMero_eq_inv_reflectedFrequency]
  field_simp [centeredZetaGammaReflectedFrequencyMero_ne_zero]

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

end

end RHTower
