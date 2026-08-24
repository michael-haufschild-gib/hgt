import GaloisForLFunctions.RHTower.TransverseRelocationCarrierAnalyticCompletion
import GaloisForLFunctions.RHTower.TransverseRelocationCarrierDifferentialField
import GaloisForLFunctions.RHTower.TransverseRelocationCarrierOrdinateMultiplicity

open Complex Set
open scoped Differential

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.NymanUpper

noncomputable section

local instance positiveDensityFieldDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance positiveDensityFieldDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance positiveDensityFieldComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance positiveDensityFieldRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

local instance positiveDensityFieldRatDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance positiveDensityFieldRatDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncDifferentialAlgebra

local instance positiveDensityFieldCharZero : CharZero upperEndMeroField :=
  charZero_of_injective_algebraMap upperEndComplexToMero.injective

/-- A fixed positive parameter satisfying the reflected-Gamma separation condition. -/
def positiveDensityTransverseBeta : ℝ := 1 / 3

/-- The card's undisplaced critical-line carrier. -/
def positiveDensityTransverseBaseCarrier : ℂ → ℂ :=
  transverseRelocationCarrier positiveDensityTransverseBeta 0

/-- The card's concretely displaced positive-density carrier. -/
def positiveDensityTransverseRelocatedCarrier : ℂ → ℂ :=
  transverseRelocationCarrier positiveDensityTransverseBeta 1

theorem positiveDensityTransverseBeta_pos : 0 < positiveDensityTransverseBeta := by
  norm_num [positiveDensityTransverseBeta]

theorem positiveDensityTransverseBeta_separated :
    ∀ k : ℤ, (2 * positiveDensityTransverseBeta - 1 : ℂ) ≠ (k : ℂ) := by
  intro k hk
  have hre := congrArg Complex.re hk
  norm_num [positiveDensityTransverseBeta] at hre
  have hthree : (3 * k : ℤ) = -1 := by
    exact_mod_cast (show (3 : ℝ) * (k : ℝ) = -1 by nlinarith [hre])
  omega

theorem positiveDensityTransverseBase_exactOrderOne :
    HasExactEntireOrderOne positiveDensityTransverseBaseCarrier := by
  simpa [positiveDensityTransverseBaseCarrier] using
    transverseRelocationCarrier_hasExactEntireOrderOne
      positiveDensityTransverseBeta_pos 0

theorem positiveDensityTransverseRelocated_exactOrderOne :
    HasExactEntireOrderOne positiveDensityTransverseRelocatedCarrier := by
  simpa [positiveDensityTransverseRelocatedCarrier] using
    transverseRelocationCarrier_hasExactEntireOrderOne
      positiveDensityTransverseBeta_pos 1

theorem positiveDensityTransverseBase_hypertranscendental :
    Hypertranscendental positiveDensityTransverseBaseCarrier := by
  simpa [positiveDensityTransverseBaseCarrier] using
    transverseRelocationCarrier_hypertranscendental_of_two_mul_sub_one
      (a := 0) positiveDensityTransverseBeta_separated

theorem positiveDensityTransverseRelocated_hypertranscendental :
    Hypertranscendental positiveDensityTransverseRelocatedCarrier := by
  simpa [positiveDensityTransverseRelocatedCarrier] using
    transverseRelocationCarrier_hypertranscendental_of_two_mul_sub_one
      (a := 1) positiveDensityTransverseBeta_separated

theorem positiveDensityTransverseBase_one_sub (s : ℂ) :
    positiveDensityTransverseBaseCarrier (1 - s) =
      positiveDensityTransverseBaseCarrier s := by
  exact transverseRelocationCarrier_one_sub positiveDensityTransverseBeta 0 s

theorem positiveDensityTransverseRelocated_one_sub (s : ℂ) :
    positiveDensityTransverseRelocatedCarrier (1 - s) =
      positiveDensityTransverseRelocatedCarrier s := by
  exact transverseRelocationCarrier_one_sub positiveDensityTransverseBeta 1 s

theorem positiveDensityTransverseBase_conj (s : ℂ) :
    positiveDensityTransverseBaseCarrier (starRingEnd ℂ s) =
      starRingEnd ℂ (positiveDensityTransverseBaseCarrier s) := by
  exact transverseRelocationCarrier_conj positiveDensityTransverseBeta 0 s

theorem positiveDensityTransverseRelocated_conj (s : ℂ) :
    positiveDensityTransverseRelocatedCarrier (starRingEnd ℂ s) =
      starRingEnd ℂ (positiveDensityTransverseRelocatedCarrier s) := by
  exact transverseRelocationCarrier_conj positiveDensityTransverseBeta 1 s

theorem positiveDensityTransverseBase_zero_re_eq_half
    {s : ℂ} (hs : positiveDensityTransverseBaseCarrier s = 0) :
    s.re = 1 / 2 := by
  exact transverseRelocationCarrier_zero_re_eq_half hs

theorem positiveDensityTransverseRelocated_exists_offCritical_zero :
    ∃ s : ℂ, positiveDensityTransverseRelocatedCarrier s = 0 ∧ s.re ≠ 1 / 2 := by
  refine ⟨transverseOffCriticalLatticePoint 1 true 0, ?_, ?_⟩
  · exact transverseRelocationCarrier_offCriticalLatticePoint_zero
      positiveDensityTransverseBeta 1 true 0
  · rw [transverseOffCriticalLatticePoint_re]
    norm_num

theorem positiveDensityTransverseRelocated_envelope_pos (y : ℝ) :
    ∃ r : ℝ, 0 < r ∧
      coshQuartetEnvelope 1 ((y : ℂ) * Complex.I) = (r : ℂ) := by
  exact coshQuartetEnvelope_mul_I_pos_real one_ne_zero

theorem positiveDensityTransverse_zeroOrdinateMass_eq (y : ℝ) :
    transverseRelocationCarrier_zeroOrdinateMass
        positiveDensityTransverseBeta 1 y =
      transverseRelocationCarrier_zeroOrdinateMass
        positiveDensityTransverseBeta 0 y := by
  exact transverseRelocationCarrier_zeroOrdinateMass_eq
    positiveDensityTransverseBeta one_ne_zero y

theorem positiveDensityTransverse_zeroHeightBandMass_eq
    (T : ℝ) (hT : 0 ≤ T) :
    transverseRelocationCarrier_zeroHeightBandMass
        positiveDensityTransverseBeta 1 T positiveDensityTransverseBeta_pos hT =
      transverseRelocationCarrier_zeroHeightBandMass
        positiveDensityTransverseBeta 0 T positiveDensityTransverseBeta_pos hT := by
  exact transverseRelocationCarrier_zeroHeightBandMass_eq
    positiveDensityTransverseBeta one_ne_zero positiveDensityTransverseBeta_pos hT

theorem positiveDensityTransverse_offCriticalCount_error_le_ten
    {T : ℝ} (hT : Real.pi ≤ T) :
    |↑(transverseOffCriticalZeroHeightCount positiveDensityTransverseBeta 1 T
          positiveDensityTransverseBeta_pos (le_trans Real.pi_pos.le hT)) -
        4 * T / Real.pi| ≤ 10 := by
  exact transverseOffCriticalZeroHeightCount_error_le_ten
    positiveDensityTransverseBeta one_ne_zero positiveDensityTransverseBeta_pos hT

theorem positiveDensityTransverse_offCriticalCount_positiveDensity
    {T : ℝ} (hT : 2 * Real.pi ≤ T) :
    (2 / Real.pi) * T ≤
      ↑(transverseOffCriticalZeroHeightCount positiveDensityTransverseBeta 1 T
        positiveDensityTransverseBeta_pos (le_trans (by positivity) hT)) := by
  exact transverseOffCriticalZeroHeightCount_positiveDensity
    positiveDensityTransverseBeta one_ne_zero positiveDensityTransverseBeta_pos hT

/-- Equality of the complete translated all-jet fields over `ℂ(s, exp(2s))`. -/
def PositiveDensityTransverseAllJetsInvariant : Prop :=
    letI : Differential transverseExponentialBase :=
      derivationClosedDifferential transverseExponentialBase
        (derivationClosed_differentialAdjoin (RatFunc ℂ)
          ({expMero 2} : Set upperEndMeroField))
    letI : DifferentialAlgebra transverseExponentialBase upperEndMeroField :=
      derivationClosed_differentialAlgebra transverseExponentialBase
        (derivationClosed_differentialAdjoin (RatFunc ℂ)
          ({expMero 2} : Set upperEndMeroField))
    IntermediateField.adjoin transverseExponentialBase
        (Set.range fun p : ℂ × ℕ => differentialJet p.2
          (transverseCarrierTranslateFamily positiveDensityTransverseBeta 0 p.1)) =
      IntermediateField.adjoin transverseExponentialBase
        (Set.range fun p : ℂ × ℕ => differentialJet p.2
          (transverseCarrierTranslateFamily positiveDensityTransverseBeta 1 p.1))

theorem positiveDensityTransverse_allJets_adjoin_eq :
    PositiveDensityTransverseAllJetsInvariant := by
  exact transverseCarrierTranslateFamily_two_displacements_allJets_adjoin_eq
    positiveDensityTransverseBeta 0 1

/-- Equality of differential-translation matroid rank over the rational-function base. -/
def PositiveDensityTransverseDifferentialMatroidInvariant : Prop :=
    (differentialMatroid (RatFunc ℂ) upperEndMeroField).eRk
        (Set.range (transverseCarrierTranslateFamily positiveDensityTransverseBeta 0)) =
      (differentialMatroid (RatFunc ℂ) upperEndMeroField).eRk
        (Set.range (transverseCarrierTranslateFamily positiveDensityTransverseBeta 1))

theorem positiveDensityTransverse_differentialMatroid_eRk_eq :
    PositiveDensityTransverseDifferentialMatroidInvariant := by
  exact transverseCarrierTranslateFamily_differentialMatroid_eRk_eq
    positiveDensityTransverseBeta 0 1

/-- Equality of logarithmic source classes modulo `ℂ(s, exp(2s))`. -/
def PositiveDensityTransverseLogSourceInvariant : Prop :=
    transverseUpperEndLogDeriv
          (transverseCarrierUpperEndMero positiveDensityTransverseBeta 1) -
        transverseUpperEndLogDeriv
          (transverseCarrierUpperEndMero positiveDensityTransverseBeta 0) ∈
      transverseExponentialBase

theorem positiveDensityTransverse_logSourceClass_eq :
    PositiveDensityTransverseLogSourceInvariant := by
  exact transverseCarrierUpperEndLogDeriv_sourceClass_eq
    positiveDensityTransverseBeta 1 0

/-- Closed witness that the complete preserved package cannot determine critical-line location. -/
theorem positiveDensityTransverseDivisorRelocation_noGo :
    (HasExactEntireOrderOne positiveDensityTransverseBaseCarrier ∧
      HasExactEntireOrderOne positiveDensityTransverseRelocatedCarrier) ∧
    (Hypertranscendental positiveDensityTransverseBaseCarrier ∧
      Hypertranscendental positiveDensityTransverseRelocatedCarrier) ∧
    (∀ s : ℂ, positiveDensityTransverseBaseCarrier (1 - s) =
        positiveDensityTransverseBaseCarrier s) ∧
    (∀ s : ℂ, positiveDensityTransverseRelocatedCarrier (1 - s) =
        positiveDensityTransverseRelocatedCarrier s) ∧
    (∀ s : ℂ, positiveDensityTransverseBaseCarrier (starRingEnd ℂ s) =
        starRingEnd ℂ (positiveDensityTransverseBaseCarrier s)) ∧
    (∀ s : ℂ, positiveDensityTransverseRelocatedCarrier (starRingEnd ℂ s) =
        starRingEnd ℂ (positiveDensityTransverseRelocatedCarrier s)) ∧
    (∀ {s : ℂ}, positiveDensityTransverseBaseCarrier s = 0 → s.re = 1 / 2) ∧
    (∃ s : ℂ, positiveDensityTransverseRelocatedCarrier s = 0 ∧ s.re ≠ 1 / 2) ∧
    (∀ y : ℝ, transverseRelocationCarrier_zeroOrdinateMass
        positiveDensityTransverseBeta 1 y =
      transverseRelocationCarrier_zeroOrdinateMass
        positiveDensityTransverseBeta 0 y) ∧
    (∀ T : ℝ, ∀ hT : 0 ≤ T,
      transverseRelocationCarrier_zeroHeightBandMass
          positiveDensityTransverseBeta 1 T positiveDensityTransverseBeta_pos hT =
        transverseRelocationCarrier_zeroHeightBandMass
          positiveDensityTransverseBeta 0 T positiveDensityTransverseBeta_pos hT) ∧
    PositiveDensityTransverseAllJetsInvariant ∧
    PositiveDensityTransverseDifferentialMatroidInvariant ∧
    PositiveDensityTransverseLogSourceInvariant ∧
    (∀ T : ℝ, ∀ hT : 2 * Real.pi ≤ T,
      (2 / Real.pi) * T ≤
        ↑(transverseOffCriticalZeroHeightCount positiveDensityTransverseBeta 1 T
          positiveDensityTransverseBeta_pos
            (le_trans (by positivity) hT))) := by
  refine ⟨⟨positiveDensityTransverseBase_exactOrderOne,
      positiveDensityTransverseRelocated_exactOrderOne⟩,
    ⟨positiveDensityTransverseBase_hypertranscendental,
      positiveDensityTransverseRelocated_hypertranscendental⟩,
    positiveDensityTransverseBase_one_sub,
    positiveDensityTransverseRelocated_one_sub,
    positiveDensityTransverseBase_conj,
    positiveDensityTransverseRelocated_conj,
    ?_, positiveDensityTransverseRelocated_exists_offCritical_zero,
    positiveDensityTransverse_zeroOrdinateMass_eq,
    positiveDensityTransverse_zeroHeightBandMass_eq,
    positiveDensityTransverse_allJets_adjoin_eq,
    positiveDensityTransverse_differentialMatroid_eRk_eq,
    positiveDensityTransverse_logSourceClass_eq, ?_⟩
  · intro s hs
    exact positiveDensityTransverseBase_zero_re_eq_half hs
  · intro T hT
    exact positiveDensityTransverse_offCriticalCount_positiveDensity hT

end
end RHTower
