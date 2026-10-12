import GaloisForLFunctions.HTGeometry.PaperFiniteNegativePart
import GaloisForLFunctions.HTGeometry.PaperCompactIdealTrace

/-!
# Infinite spectral sign sectors forced by compact irreparability

The canonical negative part is itself a positivity repair. If no compact
repair exists it is noncompact and has infinite-dimensional range. The
positive part obeys the same law by reversing the source orientation.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open scoped CStarAlgebra ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Canonical positive spectral part, paired with `PaperNegativePart.repair`. -/
def paperPositiveSpectralPart (Q : E →L[ℂ] E) : E →L[ℂ] E := Q⁺

omit [CompleteSpace E] in
theorem paperNoncompact_infiniteRange (A : E →L[ℂ] E) (hA : ¬ IsCompactOperator A) :
    ¬ FiniteDimensional ℂ A.toLinearMap.range := by
  intro h
  letI := h
  have hc := isCompactOperator_of_locallyCompactSpace_dom A.rangeRestrict
  exact hA (hc.clm_comp A.toLinearMap.range.subtypeL)

theorem paperNegativePart_not_compact_of_no_repair (Q : E →L[ℂ] E) (hQ : IsSelfAdjoint Q)
    (h : ¬ ∃ K : compactOperatorStarAlgebra E, (Q + K.1).IsPositive) :
    ¬ IsCompactOperator (PaperNegativePart.repair Q) := by
  intro hc
  exact h ⟨⟨Q⁻, hc⟩, PaperNegativePart.repaired_positive Q hQ⟩

theorem paperNegativePart_infiniteRange_of_no_repair (Q : E →L[ℂ] E) (hQ : IsSelfAdjoint Q)
    (h : ¬ ∃ K : compactOperatorStarAlgebra E, (Q + K.1).IsPositive) :
    ¬ FiniteDimensional ℂ (PaperNegativePart.repair Q).toLinearMap.range :=
  paperNoncompact_infiniteRange _ (paperNegativePart_not_compact_of_no_repair Q hQ h)

theorem paperPositivePart_not_compact_of_no_repair (Q : E →L[ℂ] E) (hQ : IsSelfAdjoint Q)
    (h : ¬ ∃ K : compactOperatorStarAlgebra E, (-Q + K.1).IsPositive) :
    ¬ IsCompactOperator (paperPositiveSpectralPart Q) := by
  simpa only [paperPositiveSpectralPart, PaperNegativePart.repair, CFC.negPart_neg] using
    paperNegativePart_not_compact_of_no_repair (-Q) hQ.neg h

theorem paperPositivePart_infiniteRange_of_no_repair (Q : E →L[ℂ] E) (hQ : IsSelfAdjoint Q)
    (h : ¬ ∃ K : compactOperatorStarAlgebra E, (-Q + K.1).IsPositive) :
    ¬ FiniteDimensional ℂ (paperPositiveSpectralPart Q).toLinearMap.range :=
  paperNoncompact_infiniteRange _ (paperPositivePart_not_compact_of_no_repair Q hQ h)

theorem paperNegativePart_traceCost_of_no_repair (Q : E →L[ℂ] E) (hQ : IsSelfAdjoint Q)
    (h : ¬ ∃ K : compactOperatorStarAlgebra E, (Q + K.1).IsPositive) :
    compactOperatorTraceCost E (PaperNegativePart.repair Q) = ∞ := by
  rw [compactOperatorTraceCost_eq,
    if_neg (paperNegativePart_not_compact_of_no_repair Q hQ h)]

theorem paperPositivePart_traceCost_of_no_repair (Q : E →L[ℂ] E) (hQ : IsSelfAdjoint Q)
    (h : ¬ ∃ K : compactOperatorStarAlgebra E, (-Q + K.1).IsPositive) :
    compactOperatorTraceCost E (paperPositiveSpectralPart Q) = ∞ := by
  rw [compactOperatorTraceCost_eq,
    if_neg (paperPositivePart_not_compact_of_no_repair Q hQ h)]

end
end GaloisForLFunctions.HTGeometry
