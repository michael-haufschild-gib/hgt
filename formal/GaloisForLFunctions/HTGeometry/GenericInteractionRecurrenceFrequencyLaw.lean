import GaloisForLFunctions.HTGeometry.FiniteSpectralRecurrenceFrequencyLaw
import GaloisForLFunctions.HTGeometry.SeparableInteractionProjectiveGenericityLaw

/-!
# Generic interaction law for long-time recurrence frequency

Almost every separable rank-one diagonal interaction removes all balanced
spectral relations. The resulting product spectrum has full projective
temporal rank, and each anchored deterministic phase flow realizes the Haar
recurrence-frequency law on all of those temporal directions.
-/

open Filter MeasureTheory Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Canonically reindexed anchored frequency packet of a separably coupled
finite product spectrum. -/
def genericSeparableInteractionProjectiveFrequency
    {m n : ℕ}
    (left : Fin (m + 1) → ℝ)
    (right : Fin (n + 1) → ℝ)
    (q : Fin (Fintype.card
      (SeparableInteractionParameterIndex m n)) → ℝ)
    (reference : Fin (m * n + m + n + 1)) :
    Fin (Fintype.card
      {i : Fin (m * n + m + n + 1) // i ≠ reference}) → ℝ :=
  finReindexedFrequency
    (projectiveFrequency
      (reindexedSeparableInteractionEnergy left right
        (finReindexedSeparableParameter q))
      reference)

/-- **Generic interaction recurrence-frequency law.** Every generic
separable rank-one interaction on an `(m+1)` by `(n+1)` product spectrum has
exactly `m*n+m+n` projective temporal directions. For every anchor, every
weighted recurrence probe and every positive tolerance, its deterministic
completed-time return frequency is trapped between the Haar volumes of the
half- and full-tolerance targets.

The input spectra are arbitrary; genericity is imposed only on the
interaction parameters. -/
theorem mem_separableInteractionProjectiveGenericSet_recurrenceFrequency
    {m n : ℕ}
    (left : Fin (m + 1) → ℝ)
    (right : Fin (n + 1) → ℝ)
    (q : Fin (Fintype.card
      (SeparableInteractionParameterIndex m n)) → ℝ)
    (hq : q ∈ separableInteractionProjectiveGenericSet left right)
    (reference : Fin (m * n + m + n + 1))
    (weight : Fin (Fintype.card
      {i : Fin (m * n + m + n + 1) // i ≠ reference}) → ℝ)
    {η : ℝ} (hη : 0 < η) :
    Fintype.card
        {i : Fin (m * n + m + n + 1) // i ≠ reference} =
      m * n + m + n ∧
    projectiveTemporalRank
        (reindexedSeparableInteractionEnergy left right
          (finReindexedSeparableParameter q)) =
      m * n + m + n ∧
    volume
        (RHTower.torusProjectiveWeightedCoherenceTarget weight (η / 2)) ≤
      atTop.liminf (fun A ↦
        (finiteTorusPhaseProbabilityMeasure
            (genericSeparableInteractionProjectiveFrequency
              left right q reference) A :
          Measure (UnitAddTorus
            (Fin (Fintype.card
              {i : Fin (m * n + m + n + 1) // i ≠ reference}))))
          (strictProjectiveWeightedCoherenceTarget weight η)) ∧
    atTop.limsup (fun A ↦
        (finiteTorusPhaseProbabilityMeasure
            (genericSeparableInteractionProjectiveFrequency
              left right q reference) A :
          Measure (UnitAddTorus
            (Fin (Fintype.card
              {i : Fin (m * n + m + n + 1) // i ≠ reference}))))
          (RHTower.torusProjectiveWeightedCoherenceTarget weight η)) ≤
      volume
        (RHTower.torusProjectiveWeightedCoherenceTarget weight η) := by
  have hmax :=
    mem_separableInteractionProjectiveGenericSet_maximallyProjective
      left right q hq
  have hindependent :=
    maximallyProjectiveEnergy_projectiveFrequency_independent
      (reindexedSeparableInteractionEnergy left right
        (finReindexedSeparableParameter q))
      hmax reference
  have hreindexed :
      RationallyIndependentFrequency
        (genericSeparableInteractionProjectiveFrequency
          left right q reference) :=
    rationallyIndependentFrequency_finReindexed _ hindependent
  have hfrequency :=
    rationallyIndependent_projectiveCoherenceFrequency_sandwich
      (genericSeparableInteractionProjectiveFrequency
        left right q reference)
      weight hreindexed hη
  exact ⟨by simp, projectiveTemporalRank_eq hmax,
    hfrequency.1, hfrequency.2⟩

end

end GaloisForLFunctions.HTGeometry
