import GaloisForLFunctions.RHTower.WeilLogShiftGramReversalRigidity

/-! Exact reversal defect and quantitative stability of balance-weighted actual costs. -/

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace RHTower
namespace FiniteWeilGramCoordinates

variable {s : Finset ℕ} (D : FiniteWeilGramCoordinates s)

theorem tests_card_of_atom (w : D.tests) : D.tests.card = s.card + 1 := by
  have ht : 0 < D.tests.card := Finset.card_pos.mpr ⟨w.1, w.2⟩
  have hs : s ≠ ∅ := by
    intro he
    have hc : D.tests.card = 0 := by simpa only [if_pos he] using D.cardinality
    omega
  simpa only [if_neg hs] using D.cardinality

/-- At a minimizing atom, the reversal gap is an exact sum of nonnegative cost
imbalances, normalized by that atom's balance-weighted cost. -/
theorem atomReversalRatio_gap_mul (w : D.tests) :
    (D.atomReversalRatio w - (s.card : ℝ)) *
        (D.balance w * finiteWeilGramTailCost 1 w.1) =
      ∑ v, (D.balance v * finiteWeilGramTailCost 1 v.1 -
        D.balance w * finiteWeilGramTailCost 1 w.1) := by
  have hp : 0 < D.balance w * finiteWeilGramTailCost 1 w.1 :=
    mul_pos (D.balance_pos w) (D.unit_tailCost_pos w)
  rw [Finset.sum_sub_distrib]
  change (D.atomReversalRatio w - (s.card : ℝ)) *
      (D.balance w * finiteWeilGramTailCost 1 w.1) =
    D.balanceCost - ∑ _v : D.tests, D.balance w * finiteWeilGramTailCost 1 w.1
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe,
    D.tests_card_of_atom w, Nat.cast_add, Nat.cast_one]
  unfold atomReversalRatio
  rw [sub_mul, sub_mul, div_mul_cancel₀ _ hp.ne']
  ring

/-- A reversal factor within epsilon of dimension forces every pair of atom costs
to have multiplicative spread at most one plus epsilon. -/
theorem atom_cost_spread_of_nativeGauge_bound (ε : NNReal)
    (h : ∀ L, D.nativeGauge (-L) ≤ ((s.card : ℝ) + (ε : ℝ)) * D.nativeGauge L) :
    ∀ u v, D.balance u * finiteWeilGramTailCost 1 u.1 ≤
      (1 + (ε : ℝ)) * (D.balance v * finiteWeilGramTailCost 1 v.1) := by
  intro u v
  rcases D.exists_optimal_reversal_atom with he | ⟨w, hm, _, _, hbest⟩
  · exact False.elim ((Finset.nonempty_iff_ne_empty.mp
      (show D.tests.Nonempty from ⟨u.1, u.2⟩)) he)
  have hb : D.atomReversalRatio w ≤ (s.card : ℝ) + (ε : ℝ) := (hbest _).mp h
  have hterm : D.balance u * finiteWeilGramTailCost 1 u.1 -
      D.balance w * finiteWeilGramTailCost 1 w.1 ≤
      (D.atomReversalRatio w - (s.card : ℝ)) *
        (D.balance w * finiteWeilGramTailCost 1 w.1) := by
    have hsum := Finset.single_le_sum (fun t _ => sub_nonneg.mpr (hm t))
      (Finset.mem_univ u)
    rwa [← D.atomReversalRatio_gap_mul w] at hsum
  have hgap : D.atomReversalRatio w - (s.card : ℝ) ≤ (ε : ℝ) := by linarith only [hb]
  have hmul := mul_le_mul_of_nonneg_right hgap
    (mul_nonneg (D.balance_pos w).le (D.unit_tailCost_pos w).le)
  have hu : D.balance u * finiteWeilGramTailCost 1 u.1 ≤
      (1 + (ε : ℝ)) * (D.balance w * finiteWeilGramTailCost 1 w.1) := by
    nlinarith only [hterm, hmul]
  exact le_trans hu (mul_le_mul_of_nonneg_left (hm v) (by positivity))

/-- Pairwise spread at most one plus epsilon gives a uniform reversal factor
dimension times one plus epsilon; the distinguished atom is counted exactly. -/
theorem nativeGauge_bound_of_atom_cost_spread (ε : NNReal)
    (h : ∀ u v, D.balance u * finiteWeilGramTailCost 1 u.1 ≤
      (1 + (ε : ℝ)) * (D.balance v * finiteWeilGramTailCost 1 v.1)) :
    ∀ L, D.nativeGauge (-L) ≤
      ((s.card : ℝ) * (1 + (ε : ℝ))) * D.nativeGauge L := by
  apply (D.nativeGauge_neg_le_iff ((s.card : ℝ) * (1 + (ε : ℝ)))).mpr
  intro w
  let p : D.tests → ℝ := fun v => D.balance v * finiteWeilGramTailCost 1 v.1
  have hc : (Finset.univ.erase w).card = s.card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ w), Finset.card_univ,
      Fintype.card_coe, D.tests_card_of_atom w]
    omega
  have hsum := Finset.sum_le_card_nsmul (Finset.univ.erase w) p
    ((1 + (ε : ℝ)) * p w) (fun v _ => h v w)
  rw [nsmul_eq_mul, hc] at hsum
  have he := Finset.sum_erase_add Finset.univ p (Finset.mem_univ w)
  have htotal : D.balanceCost ≤
      (s.card : ℝ) * ((1 + (ε : ℝ)) * p w) + p w := by
    change (∑ v, p v) ≤ _
    rw [← he]
    linarith only [hsum]
  calc
    D.balanceCost ≤ (s.card : ℝ) * ((1 + (ε : ℝ)) * p w) + p w := htotal
    _ = ((s.card : ℝ) * (1 + (ε : ℝ)) + 1) *
        D.balance w * finiteWeilGramTailCost 1 w.1 := by dsimp [p]; ring

end FiniteWeilGramCoordinates

/-- Quantitative reversal stability exists on every support without a new model
premise; the dictionary is chosen before every tolerance and functional. -/
theorem exists_finiteWeilGram_reversal_stability (s : Finset ℕ) :
    ∃ D : FiniteWeilGramCoordinates s,
      (∀ w, (D.atomReversalRatio w - (s.card : ℝ)) *
          (D.balance w * finiteWeilGramTailCost 1 w.1) =
        ∑ v, (D.balance v * finiteWeilGramTailCost 1 v.1 -
          D.balance w * finiteWeilGramTailCost 1 w.1)) ∧
      (∀ ε : NNReal,
        (∀ L, D.nativeGauge (-L) ≤ ((s.card : ℝ) + (ε : ℝ)) * D.nativeGauge L) →
        ∀ u v, D.balance u * finiteWeilGramTailCost 1 u.1 ≤
          (1 + (ε : ℝ)) * (D.balance v * finiteWeilGramTailCost 1 v.1)) ∧
      (∀ ε : NNReal,
        (∀ u v, D.balance u * finiteWeilGramTailCost 1 u.1 ≤
          (1 + (ε : ℝ)) * (D.balance v * finiteWeilGramTailCost 1 v.1)) →
        ∀ L, D.nativeGauge (-L) ≤
          ((s.card : ℝ) * (1 + (ε : ℝ))) * D.nativeGauge L) := by
  let D := finiteWeilGramCoordinates s
  exact ⟨D, D.atomReversalRatio_gap_mul, D.atom_cost_spread_of_nativeGauge_bound,
    D.nativeGauge_bound_of_atom_cost_spread⟩

end RHTower
