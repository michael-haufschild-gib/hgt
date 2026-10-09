import GaloisForLFunctions.RHTower.WeilLogShiftGramReversalCost

/-! The sharp reversal factor is attained by precisely the least balance-cost atoms. -/

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace RHTower
namespace FiniteWeilGramCoordinates

variable {s : Finset ℕ} (D : FiniteWeilGramCoordinates s)

noncomputable def atomReversalRatio (w : D.tests) : ℝ :=
  D.balanceCost / (D.balance w * finiteWeilGramTailCost 1 w.1) - 1

theorem atomReversalRatio_eq (w : D.tests) :
    D.atomReversalRatio w = D.nativeGauge (-finiteWeilGramForm s w.1) /
      D.nativeGauge (finiteWeilGramForm s w.1) := by
  unfold atomReversalRatio
  rw [D.nativeGauge_neg_atom, D.nativeGauge_atom]
  field_simp [(D.balance_pos w).ne', (D.unit_tailCost_pos w).ne']

theorem atomReversalRatio_nonneg (w : D.tests) : 0 ≤ D.atomReversalRatio w := by
  rw [D.atomReversalRatio_eq, D.nativeGauge_atom]
  exact div_nonneg (D.nativeGauge_nonneg _) (D.unit_tailCost_pos w).le

theorem nativeGauge_atom_ratio_identity (w : D.tests) :
    D.nativeGauge (-finiteWeilGramForm s w.1) =
      D.atomReversalRatio w * D.nativeGauge (finiteWeilGramForm s w.1) := by
  have hp : 0 < D.nativeGauge (finiteWeilGramForm s w.1) := by
    rw [D.nativeGauge_atom]
    exact D.unit_tailCost_pos w
  rw [D.atomReversalRatio_eq, div_mul_cancel₀ _ hp.ne']

theorem nativeGauge_neg_le_iff_atomRatios (r : ℝ) :
    (∀ L, D.nativeGauge (-L) ≤ r * D.nativeGauge L) ↔
      ∀ w, D.atomReversalRatio w ≤ r := by
  rw [D.nativeGauge_neg_le_iff_atoms]
  constructor
  · intro h w
    have hp : 0 < D.nativeGauge (finiteWeilGramForm s w.1) := by
      rw [D.nativeGauge_atom]
      exact D.unit_tailCost_pos w
    rw [D.atomReversalRatio_eq]
    exact (div_le_iff₀ hp).mpr (h w)
  · intro h w
    have hp : 0 < D.nativeGauge (finiteWeilGramForm s w.1) := by
      rw [D.nativeGauge_atom]
      exact D.unit_tailCost_pos w
    have hw := h w
    rw [D.atomReversalRatio_eq] at hw
    exact (div_le_iff₀ hp).mp hw

/-- All attaining atoms are exactly the minimizers of balance-weighted actual cost. -/
theorem nativeGauge_atom_ratio_controls_iff (w : D.tests) :
    (∀ L, D.nativeGauge (-L) ≤ D.atomReversalRatio w * D.nativeGauge L) ↔
      ∀ v, D.balance w * finiteWeilGramTailCost 1 w.1 ≤
        D.balance v * finiteWeilGramTailCost 1 v.1 := by
  rw [D.nativeGauge_neg_le_iff]
  have hp : 0 < D.balance w * finiteWeilGramTailCost 1 w.1 :=
    mul_pos (D.balance_pos w) (D.unit_tailCost_pos w)
  have hS : 0 < D.balanceCost := D.balanceCost_pos w
  have he : D.atomReversalRatio w + 1 =
      D.balanceCost / (D.balance w * finiteWeilGramTailCost 1 w.1) := by
    unfold atomReversalRatio
    ring
  constructor
  · intro h v
    have hv := h v
    rw [he] at hv
    have hv' : D.balanceCost ≤
        (D.balanceCost * (D.balance v * finiteWeilGramTailCost 1 v.1)) /
          (D.balance w * finiteWeilGramTailCost 1 w.1) := by
      simpa only [div_mul_eq_mul_div, mul_assoc] using hv
    exact (mul_le_mul_iff_of_pos_left hS).mp ((le_div_iff₀ hp).mp hv')
  · intro h v
    have hm := mul_le_mul_of_nonneg_left (h v) hS.le
    have hv := (le_div_iff₀ hp).mpr hm
    rw [he]
    simpa only [div_mul_eq_mul_div, mul_assoc] using hv

/-- The optimum is realized by an atom. The empty dictionary is explicit because
its zero gauge admits every real constant, with no least real constant. -/
theorem exists_optimal_reversal_atom :
    D.tests = ∅ ∨ ∃ w : D.tests,
      (∀ v, D.balance w * finiteWeilGramTailCost 1 w.1 ≤
        D.balance v * finiteWeilGramTailCost 1 v.1) ∧
      (s.card : ℝ) ≤ D.atomReversalRatio w ∧
      D.nativeGauge (-finiteWeilGramForm s w.1) =
        D.atomReversalRatio w * D.nativeGauge (finiteWeilGramForm s w.1) ∧
      ∀ r : ℝ, (∀ L, D.nativeGauge (-L) ≤ r * D.nativeGauge L) ↔
        D.atomReversalRatio w ≤ r := by
  by_cases he : D.tests = ∅
  · exact Or.inl he
  right
  obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr he
  have hu : (Finset.univ : Finset D.tests).Nonempty := ⟨⟨v, hv⟩, Finset.mem_univ _⟩
  obtain ⟨w, _, hw⟩ := Finset.exists_min_image Finset.univ
    (fun w : D.tests => D.balance w * finiteWeilGramTailCost 1 w.1) hu
  have hm : ∀ v, D.balance w * finiteWeilGramTailCost 1 w.1 ≤
      D.balance v * finiteWeilGramTailCost 1 v.1 := fun v => hw v (Finset.mem_univ v)
  have hb := (D.nativeGauge_atom_ratio_controls_iff w).mpr hm
  have hd := D.nativeGauge_reversal_dimension_le
    ⟨D.atomReversalRatio w, D.atomReversalRatio_nonneg w⟩ hb
  refine ⟨w, hm, hd, D.nativeGauge_atom_ratio_identity w, ?_⟩
  intro r
  constructor
  · intro h
    exact (D.nativeGauge_neg_le_iff_atomRatios r).mp h w
  · intro h L
    exact le_trans (hb L) (mul_le_mul_of_nonneg_right h (D.nativeGauge_nonneg L))

end FiniteWeilGramCoordinates
end RHTower
