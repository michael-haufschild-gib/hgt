import GaloisForLFunctions.HTGeometry.UniversalObserverActionLaw

/-!
# Universal observer-action conversion of constraints into time

For every finite projective carrier, every valid observer-action limit law
splits the same complete character capacity into exposed temporal dimension
and zero-action relation rank. Therefore any two observers, clocks, scaling
limits, or dynamical regimes obey one exact conservation law. Whenever the
second law exposes at least as much temporal dimension, its gain is exactly
the first law's loss of zero-action constraints.

No Hamiltonian realization, analytic parameter, interaction model, inverse
power clock, genericity, or arithmetic independence is used.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Universal observer-action temporal-capacity conservation.** Any two
valid action profiles on the same finite projective carrier divide one
fixed capacity between temporal dimension and zero-action constraints. -/
theorem observerAction_temporalCapacity_conserved
    {d : Type*} [Fintype d]
    (μ ν : ProbabilityMeasure (UnitAddTorus d))
    (profileμ profileν : (d → ℤ) → ObserverActionRegime)
    (hμ : ∀ n : d → ℤ,
      (∫ y, UnitAddTorus.mFourier n y
          ∂(μ : Measure (UnitAddTorus d))) =
        observerActionRegimeCoefficient (profileμ n))
    (hν : ∀ n : d → ℤ,
      (∫ y, UnitAddTorus.mFourier n y
          ∂(ν : Measure (UnitAddTorus d))) =
        observerActionRegimeCoefficient (profileν n)) :
    phaseLawTemporalDimension μ +
        Module.finrank ℚ
          (observerActionZeroConstraintRationalSpace profileμ) =
      phaseLawTemporalDimension ν +
        Module.finrank ℚ
          (observerActionZeroConstraintRationalSpace profileν) := by
  rw [observerAction_temporalDimension_add_zeroConstraintRank
      μ profileμ hμ,
    observerAction_temporalDimension_add_zeroConstraintRank
      ν profileν hν]

/-- **Universal observer-action constraint conversion.** If a second valid
observer-action law exposes at least as much temporal dimension as the
first, its exact gain equals the loss of zero-action relation rank. -/
theorem observerAction_temporalDimension_sub_eq_zeroConstraintRank_sub
    {d : Type*} [Fintype d]
    (μ ν : ProbabilityMeasure (UnitAddTorus d))
    (profileμ profileν : (d → ℤ) → ObserverActionRegime)
    (hμ : ∀ n : d → ℤ,
      (∫ y, UnitAddTorus.mFourier n y
          ∂(μ : Measure (UnitAddTorus d))) =
        observerActionRegimeCoefficient (profileμ n))
    (hν : ∀ n : d → ℤ,
      (∫ y, UnitAddTorus.mFourier n y
          ∂(ν : Measure (UnitAddTorus d))) =
        observerActionRegimeCoefficient (profileν n))
    (hmono :
      phaseLawTemporalDimension μ ≤ phaseLawTemporalDimension ν) :
    phaseLawTemporalDimension ν -
        phaseLawTemporalDimension μ =
      Module.finrank ℚ
          (observerActionZeroConstraintRationalSpace profileμ) -
        Module.finrank ℚ
          (observerActionZeroConstraintRationalSpace profileν) := by
  have hcapacity :=
    observerAction_temporalCapacity_conserved
      μ ν profileμ profileν hμ hν
  have hrank :
      Module.finrank ℚ
          (observerActionZeroConstraintRationalSpace profileν) ≤
        Module.finrank ℚ
          (observerActionZeroConstraintRationalSpace profileμ) := by
    omega
  omega

/-- The relation-space form of the same conservation law. Zero-action
constraints are not proxies: they are exactly the almost-sure phase
relations of the completed observer law. -/
theorem observerAction_phaseConstraintCapacity_conserved
    {d : Type*} [Fintype d]
    (μ ν : ProbabilityMeasure (UnitAddTorus d))
    (profileμ profileν : (d → ℤ) → ObserverActionRegime)
    (hμ : ∀ n : d → ℤ,
      (∫ y, UnitAddTorus.mFourier n y
          ∂(μ : Measure (UnitAddTorus d))) =
        observerActionRegimeCoefficient (profileμ n))
    (hν : ∀ n : d → ℤ,
      (∫ y, UnitAddTorus.mFourier n y
          ∂(ν : Measure (UnitAddTorus d))) =
        observerActionRegimeCoefficient (profileν n)) :
    phaseLawTemporalDimension μ +
        Module.finrank ℚ (phaseLawConstraintRationalSpace μ) =
      phaseLawTemporalDimension ν +
        Module.finrank ℚ (phaseLawConstraintRationalSpace ν) := by
  rw [phaseLawConstraintRationalSpace_eq_observerActionZero
      μ profileμ hμ,
    phaseLawConstraintRationalSpace_eq_observerActionZero
      ν profileν hν]
  exact observerAction_temporalCapacity_conserved
    μ ν profileμ profileν hμ hν

end

end GaloisForLFunctions.HTGeometry
