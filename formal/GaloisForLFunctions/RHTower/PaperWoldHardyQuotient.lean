import GaloisForLFunctions.RHTower.PaperWoldHardyDefect
import GaloisForLFunctions.RHTower.PaperWoldCompositeIdeal

/-! # The exact Hardy compact-equivalence class of the critical composite operator

The literal logarithmic matrix differs from an actual half Hardy operator by
the Hilbert–Schmidt operator of its exact arithmetic deficit.
-/

namespace RHTower
noncomputable section
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped ENNReal

theorem paperWoldHardyEntry_bound (n j : ℕ) :
    ‖paperWoldHardyEntry n j‖ ≤ DeletionPrimitiveHardy.tailKernel (3 / 4) n j := by
  rw [paperWoldHardyEntry]
  by_cases h : n < j
  · rw [if_pos h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (one_div_le_one_div_of_le (by positivity : 0 < (j : ℝ) + 1)
      (by linarith [Nat.cast_nonneg (α := ℝ) j])).trans (PaperHardy.inverse_le_tail n j h.le)
  · rw [if_neg h, norm_zero]
    unfold DeletionPrimitiveHardy.tailKernel
    split_ifs <;> positivity

def paperWoldHardyKernel : PaperHardy.Kernel where
  entry := paperWoldHardyEntry
  bound := paperWoldHardyEntry_bound

def paperWoldHardyOperator : PaperWoldHistory →L[ℂ] PaperWoldHistory :=
  paperWoldHardyKernel.toOperator

theorem paperWoldHardyOperator_apply (f : PaperWoldHistory) (n : ℕ) :
    paperWoldHardyOperator f n = ∑' j, paperWoldHardyEntry n j * f j := rfl

theorem paperWoldHardyOperator_single (n j : ℕ) :
    paperWoldHardyOperator (lp.single 2 j (1 : ℂ)) n = paperWoldHardyEntry n j :=
  paperWoldHardyKernel.toOperator_single n j

theorem paperWoldHardyOperator_norm_le : ‖paperWoldHardyOperator‖ ≤ 5 :=
  paperWoldHardyKernel.norm_toOperator_le

/-- Exact operator equality; the original logarithmic discrepancy is not discarded. -/
theorem paperWoldHardyOperator_sub_composite :
    paperWoldHardyOperator - paperWoldCriticalCompositeOperator =
      HilbertSchmidt.toOperator paperWoldHardyDefect_isHS := by
  apply HasLpMatrix.ext (K := fun n j => paperWoldHardyDefect (n, j))
  · intro n j
    change (paperWoldHardyOperator - paperWoldCriticalCompositeOperator)
      (lp.single 2 j (1 : ℂ)) n = _
    simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply,
      paperWoldHardyOperator_single, paperWoldCriticalCompositeOperator_single, paperWoldHardyDefect]
  · intro n j
    exact HilbertSchmidt.toOperator_single paperWoldHardyDefect_isHS n j

theorem paperWoldHardyOperator_sub_composite_isHilbertSchmidt :
    (paperWoldHardyOperator - paperWoldCriticalCompositeOperator).IsHilbertSchmidt := by
  rw [paperWoldHardyOperator_sub_composite]
  exact HilbertSchmidt.isHilbertSchmidt_toOperator paperWoldHardyDefect_isHS

theorem paperWoldHardyOperator_sub_composite_compact :
    IsCompactOperator (paperWoldHardyOperator - paperWoldCriticalCompositeOperator) :=
  paperWoldHardyOperator_sub_composite_isHilbertSchmidt.isCompactOperator

/-- Every added bounded interaction sees the same exact ideal cost in the two completions. -/
theorem paperWoldHardyOperator_add_traceCost (T : PaperWoldHistory →L[ℂ] PaperWoldHistory) :
    compactOperatorTraceCost PaperWoldHistory (T + paperWoldHardyOperator) =
      compactOperatorTraceCost PaperWoldHistory (T + paperWoldCriticalCompositeOperator) := by
  have h := compactOperatorTraceCost_add_compact (T + paperWoldCriticalCompositeOperator)
    ⟨paperWoldHardyOperator - paperWoldCriticalCompositeOperator,
      paperWoldHardyOperator_sub_composite_compact⟩
  convert h using 1
  congr 1
  module

theorem paperWoldHardyOperator_add_distance (T : PaperWoldHistory →L[ℂ] PaperWoldHistory) :
    compactIdealDistance (T + paperWoldHardyOperator) =
      compactIdealDistance (T + paperWoldCriticalCompositeOperator) := by
  have h := paperCompactIdealDistance_add_compact (T + paperWoldCriticalCompositeOperator)
    ⟨paperWoldHardyOperator - paperWoldCriticalCompositeOperator,
      paperWoldHardyOperator_sub_composite_compact⟩
  convert h using 1
  congr 1
  module

theorem paperWoldHardyOperator_distance :
    compactIdealDistance paperWoldHardyOperator = compactIdealDistance paperWoldCriticalCompositeOperator := by
  simpa only [zero_add] using paperWoldHardyOperator_add_distance 0

theorem paperWoldHardyOperator_traceCost :
    compactOperatorTraceCost PaperWoldHistory paperWoldHardyOperator = ∞ := by
  have h := paperWoldHardyOperator_add_traceCost 0
  simpa only [zero_add, paperWoldCriticalCompositeOperator_traceCost] using h

theorem paperWoldHardyOperator_not_compact : ¬ IsCompactOperator paperWoldHardyOperator :=
  (compactOperatorTraceCost_eq_top_iff _).mp paperWoldHardyOperator_traceCost

end
end RHTower
