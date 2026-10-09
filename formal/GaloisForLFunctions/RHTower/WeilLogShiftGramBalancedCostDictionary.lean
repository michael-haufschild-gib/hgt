import GaloisForLFunctions.RHTower.WeilLogShiftGramCostInflation
import GaloisForLFunctions.RHTower.WeilLogShiftGramCoordinateReencoding
import GaloisForLFunctions.RHTower.WeilLogShiftGramReversalRigidity

/-! Balanced actual-cost dictionaries exist: signed redundancy changes costs while
preserving the Gram functionals, then the full coordinate record is transported. -/

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace RHTower
namespace FiniteWeilGramCoordinates

variable {s : Finset ℕ} (D : FiniteWeilGramCoordinates s)

theorem exists_cost_balanced_reencoding :
    ∃ E : FiniteWeilGramCoordinates s, ∃ e : D.tests ≃ E.tests,
      (∀ w, finiteWeilGramForm s (e w).1 = finiteWeilGramForm s w.1) ∧
      (∀ w, E.balance (e w) = D.balance w) ∧
      (∀ w, finiteWeilGramTailCost 1 (e w).1 = D.balanceCost / D.balance w) ∧
      ∀ v, E.balance v * finiteWeilGramTailCost 1 v.1 = D.balanceCost := by
  have hex (w : D.tests) : ∃ z : FiniteWeilGramTest,
      (∀ t : Finset ℕ, finiteWeilGramForm t z = finiteWeilGramForm t w.1) ∧
      finiteWeilGramTailCost 1 z = D.balanceCost / D.balance w := by
    have ht : D.balance w * finiteWeilGramTailCost 1 w.1 ≤ D.balanceCost :=
      Finset.single_le_sum
        (fun v _ => (mul_pos (D.balance_pos v) (D.unit_tailCost_pos v)).le)
        (Finset.mem_univ w)
    have hC : finiteWeilGramTailCost 1 w.1 ≤ D.balanceCost / D.balance w :=
      (le_div_iff₀ (D.balance_pos w)).mpr (by simpa only [mul_comm] using ht)
    exact exists_finiteWeilGram_cost_inflation w.1 _ (D.unit_tailCost_pos w) hC
  choose f hf hk using hex
  obtain ⟨E, e, he, hb, _⟩ :=
    D.exists_form_preserving_reencoding f (fun w => hf w s)
  have hc (w : D.tests) : finiteWeilGramTailCost 1 (e w).1 =
      D.balanceCost / D.balance w := by rw [he w, hk w]
  have hp (w : D.tests) : E.balance (e w) * finiteWeilGramTailCost 1 (e w).1 =
      D.balanceCost := by
    rw [hb w, hc w]
    calc
      D.balance w * (D.balanceCost / D.balance w) =
          (D.balanceCost / D.balance w) * D.balance w := mul_comm _ _
      _ = D.balanceCost := div_mul_cancel₀ _ (D.balance_pos w).ne'
  refine ⟨E, e, ?_, hb, hc, ?_⟩
  · intro w
    rw [he w, hf w s]
  · intro v
    simpa only [e.apply_symm_apply] using hp (e.symm v)

end FiniteWeilGramCoordinates

/-- Every support has an actual minimal dictionary with equal balance-weighted
tail costs. Its optimal nonnegative uniform reversal factor is exactly the
coefficient dimension, including the zero-dimensional case. -/
theorem exists_finiteWeilGram_balanced_cost_dictionary (s : Finset ℕ) :
    ∃ D : FiniteWeilGramCoordinates s,
      (∀ v w, D.balance v * finiteWeilGramTailCost 1 v.1 =
        D.balance w * finiteWeilGramTailCost 1 w.1) ∧
      (∀ L, D.nativeGauge (-L) ≤ (s.card : ℝ) * D.nativeGauge L) ∧
      ∀ r : NNReal, (∀ L, D.nativeGauge (-L) ≤ (r : ℝ) * D.nativeGauge L) →
        (s.card : ℝ) ≤ (r : ℝ) := by
  let D := finiteWeilGramCoordinates s
  obtain ⟨E, _, _, _, _, hp⟩ := D.exists_cost_balanced_reencoding
  have hb : ∀ v w, E.balance v * finiteWeilGramTailCost 1 v.1 =
      E.balance w * finiteWeilGramTailCost 1 w.1 :=
    fun v w => (hp v).trans (hp w).symm
  exact ⟨E, hb, E.nativeGauge_dimension_bound_iff_equal_atom_costs.mpr hb,
    E.nativeGauge_reversal_dimension_le⟩

end RHTower
