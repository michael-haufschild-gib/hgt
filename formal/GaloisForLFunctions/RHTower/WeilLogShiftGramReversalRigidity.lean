import GaloisForLFunctions.RHTower.WeilLogShiftGramOptimalReversal

/-! Equality in the dimension bound forces equality of all balance-weighted atom costs. -/

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace RHTower
namespace FiniteWeilGramCoordinates

variable {s : Finset ℕ} (D : FiniteWeilGramCoordinates s)

private theorem gram_card_of_atom (w : D.tests) : D.tests.card = s.card + 1 := by
  have ht : 0 < D.tests.card := Finset.card_pos.mpr ⟨w.1, w.2⟩
  have hs : s ≠ ∅ := by
    intro he
    have hc : D.tests.card = 0 := by simpa only [if_pos he] using D.cardinality
    omega
  simpa only [if_neg hs] using D.cardinality

theorem nativeGauge_dimension_bound_iff_atom_balance :
    (∀ L, D.nativeGauge (-L) ≤ (s.card : ℝ) * D.nativeGauge L) ↔
      ∀ w, ((s.card : ℝ) + 1) * D.balance w * finiteWeilGramTailCost 1 w.1 =
        D.balanceCost := by
  constructor
  · intro h w
    have hr := (D.nativeGauge_neg_le_iff (s.card : ℝ)).mp h
    have hc := gram_card_of_atom D w
    have hp : (∑ v, ((s.card : ℝ) + 1) * D.balance v * finiteWeilGramTailCost 1 v.1) =
        ((s.card : ℝ) + 1) * D.balanceCost := by
      unfold balanceCost
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring
    have hsum : (∑ v, (((s.card : ℝ) + 1) * D.balance v *
        finiteWeilGramTailCost 1 v.1 - D.balanceCost)) = 0 := by
      rw [Finset.sum_sub_distrib, hp]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_coe, hc, Nat.cast_add, Nat.cast_one, sub_self]
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun v _ => sub_nonneg.mpr (hr v))).mp hsum w (Finset.mem_univ w)
    linarith only [hz]
  · intro h
    apply (D.nativeGauge_neg_le_iff (s.card : ℝ)).mpr
    intro w
    exact (h w).symm.le

/-- The best possible dimension factor is valid exactly when all atoms have equal
balance-weighted actual cost. This does not assume that such a dictionary exists. -/
theorem nativeGauge_dimension_bound_iff_equal_atom_costs :
    (∀ L, D.nativeGauge (-L) ≤ (s.card : ℝ) * D.nativeGauge L) ↔
      ∀ v w, D.balance v * finiteWeilGramTailCost 1 v.1 =
        D.balance w * finiteWeilGramTailCost 1 w.1 := by
  rw [D.nativeGauge_dimension_bound_iff_atom_balance]
  constructor
  · intro h v w
    have hp : 0 < (s.card : ℝ) + 1 := by positivity
    apply mul_left_cancel₀ hp.ne'
    calc
      ((s.card : ℝ) + 1) * (D.balance v * finiteWeilGramTailCost 1 v.1) =
          D.balanceCost := by simpa only [mul_assoc] using h v
      _ = ((s.card : ℝ) + 1) * (D.balance w * finiteWeilGramTailCost 1 w.1) := by
        simpa only [mul_assoc] using (h w).symm
  · intro h w
    have hc := gram_card_of_atom D w
    have hsum : D.balanceCost =
        (D.tests.card : ℝ) * (D.balance w * finiteWeilGramTailCost 1 w.1) := by
      unfold balanceCost
      calc
        (∑ v, D.balance v * finiteWeilGramTailCost 1 v.1) =
            ∑ _v : D.tests, D.balance w * finiteWeilGramTailCost 1 w.1 :=
          Finset.sum_congr rfl (fun v _ => h v w)
        _ = (D.tests.card : ℝ) * (D.balance w * finiteWeilGramTailCost 1 w.1) := by
          simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe]
    rw [hc, Nat.cast_add, Nat.cast_one] at hsum
    simpa only [mul_assoc] using hsum.symm

end FiniteWeilGramCoordinates

/-- Optimal reversal is attained on an actual atom; equality with the dimension
lower bound is rigid. The dictionary exists without a new model premise. -/
theorem exists_finiteWeilGram_optimal_reversal_rigidity (s : Finset ℕ) :
    ∃ D : FiniteWeilGramCoordinates s,
      (D.tests = ∅ ∨ ∃ w : D.tests,
        (∀ v, D.balance w * finiteWeilGramTailCost 1 w.1 ≤
          D.balance v * finiteWeilGramTailCost 1 v.1) ∧
        (s.card : ℝ) ≤ D.atomReversalRatio w ∧
        D.nativeGauge (-finiteWeilGramForm s w.1) =
          D.atomReversalRatio w * D.nativeGauge (finiteWeilGramForm s w.1) ∧
        ∀ r : ℝ, (∀ L, D.nativeGauge (-L) ≤ r * D.nativeGauge L) ↔
          D.atomReversalRatio w ≤ r) ∧
      ((∀ L, D.nativeGauge (-L) ≤ (s.card : ℝ) * D.nativeGauge L) ↔
        ∀ v w, D.balance v * finiteWeilGramTailCost 1 v.1 =
          D.balance w * finiteWeilGramTailCost 1 w.1) := by
  let D := finiteWeilGramCoordinates s
  exact ⟨D, D.exists_optimal_reversal_atom, D.nativeGauge_dimension_bound_iff_equal_atom_costs⟩

end RHTower
