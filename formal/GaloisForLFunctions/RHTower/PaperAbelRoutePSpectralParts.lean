import GaloisForLFunctions.RHTower.PaperAbelRoutePOrder
import GaloisForLFunctions.HTGeometry.PaperIrreparableSpectralParts

/-!
# Infinite positive and negative sectors of both full source tails

Canonical spectral sign parts of the bounded, sign-faithful FU and RP sources
are noncompact on every physical tail. Both ranges are infinite-dimensional
and both have infinite TraceCone compact-ideal cost.
-/

namespace RHTower
noncomputable section
open MeasureTheory
open scoped ENNReal
open GaloisForLFunctions.HTGeometry

private abbrev PaperAbelPartsL2 := Lp ℂ 2 halfLineMeasure

abbrev paperAbelSignedTail (T : ℝ) (ε : ℝˣ) :=
  paperHalfLineSignedCayley paperCompletedAbelSource T (ε : ℝ)

abbrev paperRoutePSignedTail (T : ℝ) (ε : ℝˣ) :=
  paperHalfLineSignedCayley paperRoutePSource T (ε : ℝ)

private theorem negative_orientation (T : ℝ) (ε : ℝˣ) :
    (¬ ∃ K : compactOperatorStarAlgebra PaperAbelPartsL2,
      (-paperAbelSignedTail T ε + K.1).IsPositive) ∧
    (¬ ∃ K : compactOperatorStarAlgebra PaperAbelPartsL2,
      (-paperRoutePSignedTail T ε + K.1).IsPositive) := by
  simpa only [Units.val_neg, paperHalfLineSignedCayley_neg] using
    paperAbelRouteP_signed_compact_repair_impossible T (-ε)

theorem paperAbelRouteP_spectral_parts_noncompact (T : ℝ) (ε : ℝˣ) :
    ¬ IsCompactOperator (PaperNegativePart.repair (paperAbelSignedTail T ε)) ∧
    ¬ IsCompactOperator (paperPositiveSpectralPart (paperAbelSignedTail T ε)) ∧
    ¬ IsCompactOperator (PaperNegativePart.repair (paperRoutePSignedTail T ε)) ∧
    ¬ IsCompactOperator (paperPositiveSpectralPart (paperRoutePSignedTail T ε)) := by
  have h := paperAbelRouteP_signed_compact_repair_impossible T ε
  have hn := negative_orientation T ε
  exact ⟨paperNegativePart_not_compact_of_no_repair _ (paperHalfLineSignedCayley_selfAdjoint _ T _) h.1,
    paperPositivePart_not_compact_of_no_repair _ (paperHalfLineSignedCayley_selfAdjoint _ T _) hn.1,
    paperNegativePart_not_compact_of_no_repair _ (paperHalfLineSignedCayley_selfAdjoint _ T _) h.2,
    paperPositivePart_not_compact_of_no_repair _ (paperHalfLineSignedCayley_selfAdjoint _ T _) hn.2⟩

/-- Both exact spectral sign sectors have infinite-dimensional range on every tail. -/
theorem paperAbelRouteP_spectral_parts_infiniteRange (T : ℝ) (ε : ℝˣ) :
    ¬ FiniteDimensional ℂ (PaperNegativePart.repair (paperAbelSignedTail T ε)).toLinearMap.range ∧
    ¬ FiniteDimensional ℂ (paperPositiveSpectralPart (paperAbelSignedTail T ε)).toLinearMap.range ∧
    ¬ FiniteDimensional ℂ (PaperNegativePart.repair (paperRoutePSignedTail T ε)).toLinearMap.range ∧
    ¬ FiniteDimensional ℂ (paperPositiveSpectralPart (paperRoutePSignedTail T ε)).toLinearMap.range := by
  obtain ⟨hAN, hAP, hRN, hRP⟩ := paperAbelRouteP_spectral_parts_noncompact T ε
  exact ⟨paperNoncompact_infiniteRange _ hAN, paperNoncompact_infiniteRange _ hAP,
    paperNoncompact_infiniteRange _ hRN, paperNoncompact_infiniteRange _ hRP⟩

theorem paperAbelRouteP_spectral_parts_traceCost (T : ℝ) (ε : ℝˣ) :
    compactOperatorTraceCost PaperAbelPartsL2 (PaperNegativePart.repair (paperAbelSignedTail T ε)) = ∞ ∧
    compactOperatorTraceCost PaperAbelPartsL2 (paperPositiveSpectralPart (paperAbelSignedTail T ε)) = ∞ ∧
    compactOperatorTraceCost PaperAbelPartsL2 (PaperNegativePart.repair (paperRoutePSignedTail T ε)) = ∞ ∧
    compactOperatorTraceCost PaperAbelPartsL2 (paperPositiveSpectralPart (paperRoutePSignedTail T ε)) = ∞ := by
  obtain ⟨hAN, hAP, hRN, hRP⟩ := paperAbelRouteP_spectral_parts_noncompact T ε
  simp only [compactOperatorTraceCost_eq, if_neg hAN, if_neg hAP, if_neg hRN, if_neg hRP,
    and_self]

end
end RHTower
