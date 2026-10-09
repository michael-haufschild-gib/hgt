import GaloisForLFunctions.RHTower.WeilLogShiftGramAntipodal

/-! Sharp finite criteria and dimension obstruction for reversal of actual Gram cost. -/

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace RHTower
namespace FiniteWeilGramCoordinates

variable {s : Finset ℕ} (D : FiniteWeilGramCoordinates s)

private theorem gram_nativeGauge_empty (he : D.tests = ∅)
    (L : (s → ℝ) →ₗ[ℝ] ℝ) : D.nativeGauge L = 0 := by
  apply Finset.sum_eq_zero
  intro w _
  exact False.elim ((Finset.nonempty_iff_ne_empty.mp
    (show D.tests.Nonempty from ⟨w.1, w.2⟩)) he)

/-- Every universal reversal bound is equivalent to finitely many actual-cost inequalities. -/
theorem nativeGauge_neg_le_iff (r : ℝ) :
    (∀ L, D.nativeGauge (-L) ≤ r * D.nativeGauge L) ↔
      ∀ w, D.balanceCost ≤ (r + 1) * D.balance w * finiteWeilGramTailCost 1 w.1 := by
  constructor
  · intro h w
    have hm := mul_le_mul_of_nonneg_left (h (finiteWeilGramForm s w.1))
      (D.balance_pos w).le
    have hp := D.balance_mul_nativeGauge_atom_pair w
    rw [D.nativeGauge_atom] at hm hp
    nlinarith only [hm, hp]
  · intro h L
    by_cases he : D.tests = ∅
    · rw [gram_nativeGauge_empty D he (-L), gram_nativeGauge_empty D he L, mul_zero]
    obtain ⟨t, ht, hw, hg⟩ := D.exists_nativeGauge_antipodal_balance L
    rcases D.weights_boundary (-L) with hc | ⟨j, hj⟩
    · exact False.elim (he hc)
    have hq : D.weights L j = t * D.balance j := by
      simpa only [hj, add_zero] using hw j
    let p : ℝ := D.balance j * finiteWeilGramTailCost 1 j.1
    have hp : 0 < p := mul_pos (D.balance_pos j) (D.unit_tailCost_pos j)
    have hS : 0 < D.balanceCost := D.balanceCost_pos j
    have ha : D.balanceCost ≤ (r + 1) * p := by
      simpa only [p, mul_assoc] using h j
    have hr : 0 ≤ r + 1 := by nlinarith only [hp, hS, ha]
    have hterm : t * p ≤ D.nativeGauge L := by
      have hle := Finset.single_le_sum
        (fun w _ => mul_nonneg (D.weights_nonneg L w) (D.unit_tailCost_pos w).le)
        (Finset.mem_univ j)
      rw [hq] at hle
      simpa only [nativeGauge, p, mul_assoc] using hle
    have hfirst : t * D.balanceCost ≤ (r + 1) * (t * p) := by
      calc
        t * D.balanceCost ≤ t * ((r + 1) * p) := mul_le_mul_of_nonneg_left ha ht
        _ = (r + 1) * (t * p) := by ring
    have hsecond := mul_le_mul_of_nonneg_left hterm hr
    nlinarith only [hg, hfirst, hsecond]

theorem nativeGauge_neg_le_iff_atoms (r : ℝ) :
    (∀ L, D.nativeGauge (-L) ≤ r * D.nativeGauge L) ↔
      ∀ w : D.tests, D.nativeGauge (-finiteWeilGramForm s w.1) ≤
        r * D.nativeGauge (finiteWeilGramForm s w.1) := by
  constructor
  · intro h w
    exact h (finiteWeilGramForm s w.1)
  · intro h
    apply (D.nativeGauge_neg_le_iff r).mpr
    intro w
    have hm := mul_le_mul_of_nonneg_left (h w) (D.balance_pos w).le
    have hp := D.balance_mul_nativeGauge_atom_pair w
    rw [D.nativeGauge_atom] at hm hp
    nlinarith only [hm, hp]

/-- The weighted aggregate reverse cost is exactly the coefficient dimension times
the weighted aggregate forward cost, including dimension zero. -/
theorem nativeGauge_reverse_sum :
    (∑ w, D.balance w * D.nativeGauge (-finiteWeilGramForm s w.1)) =
      (s.card : ℝ) * D.balanceCost := by
  by_cases hs : s = ∅
  · have he : D.tests = ∅ := Finset.card_eq_zero.mp
      (by simpa only [if_pos hs] using D.cardinality)
    have hc : s.card = 0 := Finset.card_eq_zero.mpr hs
    rw [hc, Nat.cast_zero, zero_mul]
    apply Finset.sum_eq_zero
    intro w _
    exact False.elim ((Finset.nonempty_iff_ne_empty.mp
      (show D.tests.Nonempty from ⟨w.1, w.2⟩)) he)
  · have hc : D.tests.card = s.card + 1 := by
      simpa only [if_neg hs] using D.cardinality
    have hp := Finset.sum_congr (s₁ := Finset.univ) rfl
      (fun w _ => D.balance_mul_nativeGauge_atom_pair w)
    have hf : (∑ w, D.balance w * D.nativeGauge (finiteWeilGramForm s w.1)) =
        D.balanceCost := by simp only [D.nativeGauge_atom]; rfl
    simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      Finset.card_univ, Fintype.card_coe] at hp
    rw [hf, hc, Nat.cast_add, Nat.cast_one] at hp
    linarith

/-- A nonnegative uniform reversal constant cannot be smaller than the dimension. -/
theorem nativeGauge_reversal_dimension_le (r : NNReal)
    (hr : ∀ L, D.nativeGauge (-L) ≤ (r : ℝ) * D.nativeGauge L) :
    (s.card : ℝ) ≤ (r : ℝ) := by
  by_cases hs : s = ∅
  · have hc : s.card = 0 := Finset.card_eq_zero.mpr hs
    calc
      (s.card : ℝ) = 0 := by exact_mod_cast hc
      _ ≤ (r : ℝ) := r.property
  have hc : D.tests.card = s.card + 1 := by
    simpa only [if_neg hs] using D.cardinality
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (show 0 < D.tests.card by omega)
  have hpos := D.balanceCost_pos ⟨w, hw⟩
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun v _ =>
    mul_le_mul_of_nonneg_left (hr (finiteWeilGramForm s v.1)) (D.balance_pos v).le)
  have he : (∑ v, D.balance v * ((r : ℝ) * D.nativeGauge (finiteWeilGramForm s v.1))) =
      (r : ℝ) * D.balanceCost := by
    unfold balanceCost
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [D.nativeGauge_atom]
    ring
  rw [D.nativeGauge_reverse_sum, he] at hsum
  nlinarith only [hsum, hpos]

/-- In dimension at least two, some actual dictionary atom is strictly dearer to reverse. -/
theorem nativeGauge_small_or_asymmetric :
    s.card ≤ 1 ∨ ∃ w : D.tests,
      D.nativeGauge (finiteWeilGramForm s w.1) <
        D.nativeGauge (-finiteWeilGramForm s w.1) := by
  by_cases hs : s.card ≤ 1
  · exact Or.inl hs
  right
  by_contra h
  push Not at h
  have hr : ∀ L, D.nativeGauge (-L) ≤ (1 : ℝ) * D.nativeGauge L :=
    (D.nativeGauge_neg_le_iff_atoms 1).mpr (by intro w; simpa only [one_mul] using h w)
  have hd := D.nativeGauge_reversal_dimension_le 1 hr
  have hd' : s.card ≤ 1 := by exact_mod_cast hd
  exact hs hd'

end FiniteWeilGramCoordinates

/-- Sharp reversal geometry exists for every support, with no new model premise.
The dictionary is fixed before any reversal constant or functional is supplied. -/
theorem exists_finiteWeilGram_reversal_geometry (s : Finset ℕ) :
    ∃ D : FiniteWeilGramCoordinates s,
      (∀ r : ℝ, (∀ L, D.nativeGauge (-L) ≤ r * D.nativeGauge L) ↔
        ∀ w, D.balanceCost ≤ (r + 1) * D.balance w * finiteWeilGramTailCost 1 w.1) ∧
      (∑ w, D.balance w * D.nativeGauge (-finiteWeilGramForm s w.1)) =
        (s.card : ℝ) * D.balanceCost ∧
      (∀ r : NNReal, (∀ L, D.nativeGauge (-L) ≤ (r : ℝ) * D.nativeGauge L) →
        (s.card : ℝ) ≤ (r : ℝ)) ∧
      (s.card ≤ 1 ∨ ∃ w : D.tests,
        D.nativeGauge (finiteWeilGramForm s w.1) <
          D.nativeGauge (-finiteWeilGramForm s w.1)) := by
  let D := finiteWeilGramCoordinates s
  exact ⟨D, D.nativeGauge_neg_le_iff, D.nativeGauge_reverse_sum,
    D.nativeGauge_reversal_dimension_le, D.nativeGauge_small_or_asymmetric⟩

end RHTower
