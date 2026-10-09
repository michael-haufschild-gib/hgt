import GaloisForLFunctions.RHTower.WeilLogShiftGramNativeGauge

/-! Exact canonical coordinates and actual costs of dictionary atoms and their negatives. -/

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace RHTower
namespace FiniteWeilGramCoordinates

variable {s : Finset ℕ} (D : FiniteWeilGramCoordinates s)

private theorem gram_card_gt_one (w : D.tests) : 1 < D.tests.card := by
  have ht : 0 < D.tests.card := Finset.card_pos.mpr ⟨w.1, w.2⟩
  have hs : s ≠ ∅ := by
    intro he
    have hc : D.tests.card = 0 := by simpa only [if_pos he] using D.cardinality
    omega
  have hspos : 0 < s.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
  have hc : D.tests.card = s.card + 1 := by
    simpa only [if_neg hs] using D.cardinality
  omega

theorem weights_atom (w : D.tests) :
    D.weights (finiteWeilGramForm s w.1) = fun v => if v = w then 1 else 0 := by
  symm
  apply D.weights_eq_of_boundary
  · intro v
    split_ifs <;> norm_num
  · intro c
    simp [ite_mul]
  · obtain ⟨v, hv, hne⟩ := Finset.exists_mem_ne (gram_card_gt_one D w) w.1
    have hne' : (⟨v, hv⟩ : D.tests) ≠ w := fun he => hne (congrArg Subtype.val he)
    exact ⟨⟨v, hv⟩, by simp [hne']⟩

theorem weights_neg_atom (w : D.tests) :
    D.weights (-finiteWeilGramForm s w.1) =
      fun v => D.balance v / D.balance w - if v = w then 1 else 0 := by
  symm
  apply D.weights_eq_of_boundary
  · intro v
    by_cases hv : v = w
    · subst v
      simp [(D.balance_pos w).ne']
    · simp only [if_neg hv, sub_zero]
      exact div_nonneg (D.balance_pos v).le (D.balance_pos w).le
  · intro c
    simp_rw [sub_mul, div_mul_eq_mul_div]
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, D.balance_zero]
    simp [ite_mul]
  · exact ⟨w, by simp [(D.balance_pos w).ne']⟩

theorem exists_weights_antipodal_balance (L : (s → ℝ) →ₗ[ℝ] ℝ) :
    ∃ t : ℝ, 0 ≤ t ∧ ∀ w,
      D.weights L w + D.weights (-L) w = t * D.balance w := by
  simpa only [add_neg_cancel, D.weights_zero, Pi.zero_apply, zero_add] using
    D.exists_weights_add_defect L (-L)

noncomputable def balanceCost : ℝ :=
  ∑ w, D.balance w * finiteWeilGramTailCost 1 w.1

theorem balanceCost_pos (w : D.tests) : 0 < D.balanceCost := by
  exact lt_of_lt_of_le (mul_pos (D.balance_pos w) (D.unit_tailCost_pos w))
    (Finset.single_le_sum
      (fun v _ => (mul_pos (D.balance_pos v) (D.unit_tailCost_pos v)).le)
      (Finset.mem_univ w))

theorem nativeGauge_atom (w : D.tests) :
    D.nativeGauge (finiteWeilGramForm s w.1) = finiteWeilGramTailCost 1 w.1 := by
  simp [nativeGauge, D.weights_atom, ite_mul]

theorem nativeGauge_neg_atom (w : D.tests) :
    D.nativeGauge (-finiteWeilGramForm s w.1) =
      D.balanceCost / D.balance w - finiteWeilGramTailCost 1 w.1 := by
  unfold nativeGauge
  rw [D.weights_neg_atom]
  simp_rw [sub_mul, div_mul_eq_mul_div]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div]
  simp [balanceCost, ite_mul]

theorem balance_mul_nativeGauge_atom_pair (w : D.tests) :
    D.balance w * (D.nativeGauge (finiteWeilGramForm s w.1) +
      D.nativeGauge (-finiteWeilGramForm s w.1)) = D.balanceCost := by
  rw [D.nativeGauge_atom, D.nativeGauge_neg_atom]
  field_simp [(D.balance_pos w).ne']
  ring

theorem exists_nativeGauge_antipodal_balance (L : (s → ℝ) →ₗ[ℝ] ℝ) :
    ∃ t : ℝ, 0 ≤ t ∧
      (∀ w, D.weights L w + D.weights (-L) w = t * D.balance w) ∧
      D.nativeGauge L + D.nativeGauge (-L) = t * D.balanceCost := by
  obtain ⟨t, ht, hw⟩ := D.exists_weights_antipodal_balance L
  refine ⟨t, ht, hw, ?_⟩
  unfold nativeGauge balanceCost
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  calc
    D.weights L w * finiteWeilGramTailCost 1 w.1 +
        D.weights (-L) w * finiteWeilGramTailCost 1 w.1 =
        (D.weights L w + D.weights (-L) w) * finiteWeilGramTailCost 1 w.1 := by ring
    _ = t * (D.balance w * finiteWeilGramTailCost 1 w.1) := by rw [hw]; ring

end FiniteWeilGramCoordinates
end RHTower
