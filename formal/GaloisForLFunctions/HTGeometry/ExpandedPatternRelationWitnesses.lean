import GaloisForLFunctions.HTGeometry.HerglotzFullTranslationRankGenericity
import GaloisForLFunctions.HTGeometry.MovingCanonicalFullTranslationRankGenericity
import GaloisForLFunctions.HTGeometry.MovingEvenCanonicalFullTranslationFreeness
import GaloisForLFunctions.HTGeometry.AnalyticNevanlinnaCarrierRelationFree

/-!
# The expanded pattern relations hold for the zero coefficient family

Each translation-rank genericity law assumes a coefficient family satisfying the expanded
differential pattern relation on every admissible row packet.  The zero coefficient family
satisfies all four of them, on every packet and at every row, since each relation is a linear
functional of the coefficients.

So each rigidity theorem says exactly that the zero relation is the only one, rather than that
there is no relation at all.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The zero coefficient family satisfies the Herglotz expanded pattern relation. -/
theorem herglotzExpandedPatternRelationHolds_zero
    {row κ ι : Type} [Fintype row] [DecidableEq row] [Fintype κ] [Fintype ι] [DecidableEq ι]
    (μ : MeasureTheory.Measure ℝ) (w : ℝ → ℝ) (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (u : MeasureTheory.Lp ℝ ⊤ μ) (shift : InjectiveShiftConfiguration ι) :
    herglotzExpandedPatternRelationHolds (row := row) μ w degree orders exponent u shift 0 := by
  intro packet _ _ r
  simp

/-- The zero coefficient family satisfies the moving canonical expanded pattern relation. -/
theorem movingCanonicalExpandedPatternRelationHolds_zero
    {row κ ι : Type} [Fintype row] [DecidableEq row] [Fintype κ] [Fintype ι] [DecidableEq ι]
    (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (θ : BoundedRealSequence) (shift : InjectiveShiftConfiguration ι) :
    movingCanonicalExpandedPatternRelationHolds (row := row) degree orders exponent θ shift 0 := by
  intro packet _ _ r
  simp

/-- The zero coefficient family satisfies the moving even canonical expanded pattern relation. -/
theorem movingEvenCanonicalExpandedPatternRelationHolds_zero
    {row κ ι : Type} [Fintype row] [DecidableEq row] [Fintype κ] [Fintype ι] [DecidableEq ι]
    (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (θ : BoundedRealSequence) (shift : InjectiveShiftConfiguration ι) :
    movingEvenCanonicalExpandedPatternRelationHolds (row := row) degree orders exponent θ shift
      0 := by
  intro packet _ _ _ r
  simp

namespace ClassicalAnalyticNevanlinnaCarrierFamily

variable {s : ℕ → ℝ} (F : ClassicalAnalyticNevanlinnaCarrierFamily s)

/-- The zero coefficient family satisfies the weighted boundary carrier expanded pattern
relation. -/
theorem weightedBoundaryCarrierExpandedPatternRelationHolds_zero
    {row κ ι : Type} [Fintype κ] [Fintype ι]
    (eta : MeasureTheory.Measure (OnePoint ℝ))
    (density : MeasureTheory.Lp ℝ (⊤ : ENNReal) eta)
    (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (shift : InjectiveShiftConfiguration ι) :
    F.weightedBoundaryCarrierExpandedPatternRelationHolds (row := row) eta density degree orders
      exponent shift 0 := by
  intro packet _ r
  simp

end ClassicalAnalyticNevanlinnaCarrierFamily

end GaloisForLFunctions.HTGeometry
