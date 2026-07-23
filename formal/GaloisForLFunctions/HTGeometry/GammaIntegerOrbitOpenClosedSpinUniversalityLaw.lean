import GaloisForLFunctions.HTGeometry.GeneralizedSpinTowerDifferentialBoundary
import GaloisForLFunctions.HTGeometry.VirasoroShapiroDifferentialBoundary

/-!
# Integer-orbit universality of spin-tower and string Gamma channels

The analytically continued generalized finite-spin multiplier and the reduced open- and
closed-string four-point Gamma channels arise from different normal forms.  Their terminal exact
boundary theorems nevertheless expose one common selector: membership of the channel parameter in
an integer translation orbit.  This module records the simultaneous three-channel law and rules
out mixed differential phases.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

local instance gammaIntegerOrbitUniversalityDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance gammaIntegerOrbitUniversalityDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance gammaIntegerOrbitUniversalityRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField Set.univ) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

local instance gammaIntegerOrbitUniversalityRatFuncDifferential :
    Differential (RatFunc ℂ) := ratFuncCoordinateDifferential

local instance gammaIntegerOrbitUniversalityDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField Set.univ) :=
  { deriv_algebraMap := fun r => meroField_deriv_ratfuncToMero r }

local instance gammaIntegerOrbitUniversalityCharZero :
    CharZero (meroField Set.univ) :=
  charZero_of_injective_algebraMap
    (algebraMap (RatFunc ℂ) (meroField Set.univ)).injective

/-- **Simultaneous collapse law.**  One integer-orbit selector is equivalent to DA collapse of
the generalized spin-tower multiplier and both reduced string channels. -/
theorem gammaIntegerOrbit_openClosedSpin_simultaneousCollapse
    (a N : ℂ) :
    (∃ k : ℤ, N = (k : ℂ)) ↔
      DifferentialAlgebraicOver (RatFunc ℂ) (generalizedSpinTowerChannelMero N) ∧
        DifferentialAlgebraicOver (RatFunc ℂ) (reducedVenezianoAmplitudeMero a N) ∧
        DifferentialAlgebraicOver (RatFunc ℂ)
          (reducedVirasoroShapiroAmplitudeMero a N) := by
  constructor
  · intro hN
    exact ⟨(differentiallyAlgebraicOver_generalizedSpinTowerChannelMero_iff_integer N).2 hN,
      (differentiallyAlgebraicOver_reducedVenezianoAmplitudeMero_iff_integerShift a N).2 hN,
      (differentiallyAlgebraicOver_reducedVirasoroShapiroAmplitudeMero_iff_integerShift
        a N).2 hN⟩
  · intro h
    exact (differentiallyAlgebraicOver_generalizedSpinTowerChannelMero_iff_integer N).1 h.1

/-- **Simultaneous noncollapse law.**  Off the integer orbit, all three channels are HT. -/
theorem gammaIntegerOrbit_openClosedSpin_simultaneousHypertranscendence
    (a N : ℂ) :
    (∀ k : ℤ, N ≠ (k : ℂ)) ↔
      HypertranscendentalOver (RatFunc ℂ) (generalizedSpinTowerChannelMero N) ∧
        HypertranscendentalOver (RatFunc ℂ) (reducedVenezianoAmplitudeMero a N) ∧
        HypertranscendentalOver (RatFunc ℂ)
          (reducedVirasoroShapiroAmplitudeMero a N) := by
  constructor
  · intro hN
    exact ⟨(hypertranscendentalOver_generalizedSpinTowerChannelMero_iff_noninteger N).2 hN,
      (hypertranscendentalOver_reducedVenezianoAmplitudeMero_iff_nonintegerShift a N).2 hN,
      (hypertranscendentalOver_reducedVirasoroShapiroAmplitudeMero_iff_nonintegerShift
        a N).2 hN⟩
  · intro h
    exact (hypertranscendentalOver_generalizedSpinTowerChannelMero_iff_noninteger N).1 h.1

/-- Pairwise DA and HT phase equivalence: no mixed spin/open/closed differential phase exists. -/
theorem gammaIntegerOrbit_openClosedSpin_phaseUniversality
    (a N : ℂ) :
    (DifferentialAlgebraicOver (RatFunc ℂ) (generalizedSpinTowerChannelMero N) ↔
        DifferentialAlgebraicOver (RatFunc ℂ) (reducedVenezianoAmplitudeMero a N)) ∧
      (DifferentialAlgebraicOver (RatFunc ℂ) (generalizedSpinTowerChannelMero N) ↔
        DifferentialAlgebraicOver (RatFunc ℂ)
          (reducedVirasoroShapiroAmplitudeMero a N)) ∧
      (HypertranscendentalOver (RatFunc ℂ) (generalizedSpinTowerChannelMero N) ↔
        HypertranscendentalOver (RatFunc ℂ) (reducedVenezianoAmplitudeMero a N)) ∧
      (HypertranscendentalOver (RatFunc ℂ) (generalizedSpinTowerChannelMero N) ↔
        HypertranscendentalOver (RatFunc ℂ)
          (reducedVirasoroShapiroAmplitudeMero a N)) := by
  constructor
  · rw [differentiallyAlgebraicOver_generalizedSpinTowerChannelMero_iff_integer,
      differentiallyAlgebraicOver_reducedVenezianoAmplitudeMero_iff_integerShift]
  constructor
  · rw [differentiallyAlgebraicOver_generalizedSpinTowerChannelMero_iff_integer,
      differentiallyAlgebraicOver_reducedVirasoroShapiroAmplitudeMero_iff_integerShift]
  constructor
  · rw [hypertranscendentalOver_generalizedSpinTowerChannelMero_iff_noninteger,
      hypertranscendentalOver_reducedVenezianoAmplitudeMero_iff_nonintegerShift]
  · rw [hypertranscendentalOver_generalizedSpinTowerChannelMero_iff_noninteger,
      hypertranscendentalOver_reducedVirasoroShapiroAmplitudeMero_iff_nonintegerShift]

end

end GaloisForLFunctions
