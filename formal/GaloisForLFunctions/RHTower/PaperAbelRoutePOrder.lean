import GaloisForLFunctions.RHTower.PaperAbelRoutePSource
import GaloisForLFunctions.HTGeometry.PaperHalfLineSignedCayley

/-!
# Both full source tails retain their signed obstruction modulo compacts

Every nonzero real orientation of the bounded signed Cayley observable
remains nonpositive after any compact correction. This applies to both
complete native sources and every tail, with no arithmetic-bound premise.
-/

namespace RHTower
noncomputable section
open MeasureTheory
open scoped ENNReal
open GaloisForLFunctions.HTGeometry

private abbrev PaperAbelOrderL2 := Lp ℂ 2 halfLineMeasure

/-- No compact correction makes either entire signed source tail positive, in any orientation. -/
theorem paperAbelRouteP_signed_compact_repair_impossible (T : ℝ) (ε : ℝˣ) :
    (¬ ∃ K : compactOperatorStarAlgebra PaperAbelOrderL2,
      (paperHalfLineSignedCayley paperCompletedAbelSource T (ε : ℝ) + K.1).IsPositive) ∧
    (¬ ∃ K : compactOperatorStarAlgebra PaperAbelOrderL2,
      (paperHalfLineSignedCayley paperRoutePSource T (ε : ℝ) + K.1).IsPositive) := by
  obtain ⟨δ, hδ, h⟩ := paperAbelRouteP_common_tail_interval
  exact ⟨paperHalfLineSignedCayley_no_repair_of_interval _ T hδ (h T).1 ε,
    paperHalfLineSignedCayley_no_repair_of_interval _ T hδ (h T).2 ε⟩

private theorem traceCost_of_no_repair (F : C(ℝ, ℝ)) (T ε : ℝ)
    (h : ¬ ∃ K : compactOperatorStarAlgebra PaperAbelOrderL2,
      (paperHalfLineSignedCayley F T ε + K.1).IsPositive) :
    compactOperatorTraceCost PaperAbelOrderL2 (paperHalfLineSignedCayley F T ε) = ∞ := by
  rw [paperHalfLine_traceCost (paperHalfLineSignedCayley_coeFn F T ε)]
  split_ifs with hz
  · exfalso
    apply h
    refine ⟨0, ?_⟩
    simpa only [hz, ZeroMemClass.coe_zero, add_zero] using
      (ContinuousLinearMap.isPositive_zero : (0 : PaperAbelOrderL2 →L[ℂ] PaperAbelOrderL2).IsPositive)
  · rfl

theorem paperAbelRouteP_signed_traceCost (T : ℝ) (ε : ℝˣ) :
    compactOperatorTraceCost PaperAbelOrderL2
        (paperHalfLineSignedCayley paperCompletedAbelSource T (ε : ℝ)) = ∞ ∧
      compactOperatorTraceCost PaperAbelOrderL2
        (paperHalfLineSignedCayley paperRoutePSource T (ε : ℝ)) = ∞ := by
  have h := paperAbelRouteP_signed_compact_repair_impossible T ε
  exact ⟨traceCost_of_no_repair _ T _ h.1, traceCost_of_no_repair _ T _ h.2⟩

theorem paperAbelRouteP_signed_essentialNorm (T : ℝ) (ε : ℝ) :
    compactIdealDistance (paperHalfLineSignedCayley paperCompletedAbelSource T ε) =
        ‖paperHalfLineSignedCayley paperCompletedAbelSource T ε‖ ∧
      compactIdealDistance (paperHalfLineSignedCayley paperRoutePSource T ε) =
        ‖paperHalfLineSignedCayley paperRoutePSource T ε‖ :=
  ⟨paperHalfLine_compactIdealDistance (paperHalfLineSignedCayley_coeFn _ T ε),
    paperHalfLine_compactIdealDistance (paperHalfLineSignedCayley_coeFn _ T ε)⟩

end
end RHTower
