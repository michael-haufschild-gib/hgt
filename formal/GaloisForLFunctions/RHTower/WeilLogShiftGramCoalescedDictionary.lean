import GaloisForLFunctions.RHTower.WeilLogShiftGramNodeCoalescing
import GaloisForLFunctions.RHTower.WeilLogShiftGramCoordinateReencoding

/-! Minimal actual dictionaries can use distinct nodes in every test, preserving
all Gram forms and canonical weights while decreasing every native gauge. -/

open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable section
namespace RHTower
namespace FiniteWeilGramCoordinates

variable {s : Finset ℕ} (D : FiniteWeilGramCoordinates s)

theorem exists_distinct_node_reencoding :
    ∃ E : FiniteWeilGramCoordinates s, ∃ e : D.tests ≃ E.tests,
      (∀ v : E.tests, FiniteWeilGramDistinctNodes v.1) ∧
      (∀ s' : Finset ℕ, ∀ w : D.tests,
        finiteWeilGramForm s' (e w).1 = finiteWeilGramForm s' w.1) ∧
      (∀ w, E.balance (e w) = D.balance w) ∧
      (∀ L w, E.weights L (e w) = D.weights L w) ∧
      (∀ B : NNReal, ∀ w : D.tests,
        finiteWeilGramTailCost (B : ℝ) (e w).1 ≤ finiteWeilGramTailCost (B : ℝ) w.1) ∧
      ∀ L, E.nativeGauge L ≤ D.nativeGauge L := by
  obtain ⟨E, e, he, hb, hw⟩ := D.exists_form_preserving_reencoding
    (fun w => finiteWeilGramCoalesce w.1) (fun w => finiteWeilGramForm_coalesce s w.1)
  refine ⟨E, e, ?_, ?_, hb, hw, ?_, ?_⟩
  · intro v
    have hv := finiteWeilGramCoalesce_distinct (e.symm v).1
    rwa [← he (e.symm v), e.apply_symm_apply v] at hv
  · intro s' w
    rw [he]
    exact finiteWeilGramForm_coalesce s' w.1
  · intro B w
    rw [he]
    exact finiteWeilGramTailCost_coalesce_le (NNReal.coe_nonneg B) w.1
  · intro L
    calc
      E.nativeGauge L = ∑ w : D.tests, D.weights L w *
          finiteWeilGramTailCost 1 (finiteWeilGramCoalesce w.1) := by
        unfold nativeGauge
        rw [← e.sum_comp (fun v : E.tests =>
          E.weights L v * finiteWeilGramTailCost 1 v.1)]
        apply Finset.sum_congr rfl
        intro w _
        rw [hw, he]
      _ ≤ D.nativeGauge L := Finset.sum_le_sum fun w _ =>
        mul_le_mul_of_nonneg_left (finiteWeilGramTailCost_coalesce_le zero_le_one w.1)
          (D.weights_nonneg L w)

end FiniteWeilGramCoordinates

/-- Unconditional distinct-node minimal dictionary, with gauge bounded by the
existing unconditional dictionary factory on every functional. -/
theorem exists_finiteWeilGram_distinct_node_dictionary (s : Finset ℕ) :
    ∃ D : FiniteWeilGramCoordinates s,
      (∀ w : D.tests, FiniteWeilGramDistinctNodes w.1) ∧
      ∀ L, D.nativeGauge L ≤ (finiteWeilGramCoordinates s).nativeGauge L := by
  obtain ⟨D, _, hd, _, _, _, _, hg⟩ :=
    (finiteWeilGramCoordinates s).exists_distinct_node_reencoding
  exact ⟨D, hd, hg⟩

end RHTower
