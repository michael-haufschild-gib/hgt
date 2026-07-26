import GaloisForLFunctions.HTGeometry.AnalyticNevanlinnaCarrierRelationFree
import GaloisForLFunctions.HTGeometry.LinftyPositiveAperture

/-!
# Realizations for the Nevanlinna carrier relation interfaces

The zero coefficient family satisfies every expanded pattern relation, actual or weighted, and the
constant density one is strictly positive.  What no realization supplies is the relation-freeness
premise itself: that every relation has zero coefficients is the analytic content of the carrier
theorem, not an interface that a witness can discharge.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-- The constant density one is strictly positive. -/
theorem linftyStrictlyPositive_linftyOne {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] :
    LinftyStrictlyPositive μ (linftyOne μ) := by
  have h := linftyOne_add_strictlyPositive_of_norm_lt_one μ 0 (by simp)
  simpa using h

theorem actualNevanlinnaExpandedPatternRelationHolds_zero
    {row κ ι : Type} [Fintype row] [Fintype κ] [Fintype ι]
    (m0 a q : ℂ → ℂ) (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu]
    (baseDensity : Lp ℝ (⊤ : ENNReal) mu)
    (S : Submodule ℝ (Lp ℝ (⊤ : ENNReal) mu)) (w : S)
    (shift : InjectiveShiftConfiguration ι) :
    actualNevanlinnaExpandedPatternRelationHolds (row := row) m0 a q degree orders exponent
      mu baseDensity S w shift 0 := by
  intro packet _ r
  simp

end GaloisForLFunctions.HTGeometry
