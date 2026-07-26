import GaloisForLFunctions.HTGeometry.FiniteDifferentialCircuitBoundary

/-!
# Family differential-circuit blindness universality

Finite differential circuits cannot manufacture hypertranscendence from an arbitrary palette of
differentially algebraic observations.  Unlike a one-observation no-go, this statement permits
every leaf of one expression tree to choose a different observation from the family.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A hypertranscendental target cannot be assembled by a scalar-aware finite differential
circuit from any family whose observations are all differentially algebraic.  The observation
index need not be finite: every particular circuit uses only finitely many leaves. -/
theorem no_scalarAwareFiniteDifferentialCircuit_from_differentialAlgebraic_family
    {F E ι : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (observation : ι → E)
    (hObservation : ∀ i, DifferentialAlgebraicOver F (observation i))
    {target : E} (hTarget : HypertranscendentalOver F target) :
    ¬ FiniteDifferentialCircuit
      (BaseScalarOrAtom F E (fun a => a ∈ Set.range observation)) target := by
  intro hCircuit
  apply hTarget
  apply hCircuit.differentialAlgebraicOver
  intro a ha
  rcases ha with ha | ⟨c, rfl⟩
  · obtain ⟨i, rfl⟩ := ha
    exact hObservation i
  · exact differentialAlgebraicOver_algebraMap c

/-- Family-output form: an entire hypertranscendental target atlas remains blind to a shared
palette of differentially algebraic observations, even when each circuit may mix the palette. -/
theorem no_scalarAwareFiniteDifferentialCircuit_from_differentialAlgebraic_family_all
    {F E ι κ : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (observation : ι → E)
    (hObservation : ∀ i, DifferentialAlgebraicOver F (observation i))
    (target : κ → E)
    (hTarget : ∀ j, HypertranscendentalOver F (target j)) :
    ∀ j, ¬ FiniteDifferentialCircuit
      (BaseScalarOrAtom F E (fun a => a ∈ Set.range observation)) (target j) := by
  intro j
  exact no_scalarAwareFiniteDifferentialCircuit_from_differentialAlgebraic_family
    observation hObservation (hTarget j)

end

end GaloisForLFunctions.HTGeometry
