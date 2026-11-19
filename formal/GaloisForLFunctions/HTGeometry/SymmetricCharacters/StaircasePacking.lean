import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Staircase bounds for distinct multiplicities and rook placements

Slonim's Lemma 8.3 (arXiv:2611.11593) prices distinct row lengths by a
triangular number. More generally each represented integer level contributes
its binomial weight. Additional occurrences cost at least the bottom weight.
-/

namespace GaloisForLFunctions.StaircasePacking

open Finset

/-- The minimum binomial weight of distinct levels above a fixed floor is
attained by consecutive levels. The additive constant avoids natural subtraction. -/
theorem distinct_binomial_bound (s : Finset ℕ) (b j : ℕ) (hb : ∀ x ∈ s, b ≤ x) :
    (b + s.card).choose (j + 1) ≤ b.choose (j + 1) + ∑ x ∈ s, x.choose j := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hmax ih =>
    have ha : a ∉ s := fun h => (hmax a h).false
    have hlo : ∀ x ∈ s, b ≤ x := fun x hx => hb x (mem_insert_of_mem hx)
    have hcard := card_le_card (show s ⊆ Ico b a from fun x hx =>
      mem_Ico.mpr ⟨hlo x hx, hmax x hx⟩)
    rw [Nat.card_Ico] at hcard
    have hba := hb a (mem_insert_self a s)
    have hstep := Nat.choose_le_choose j (show b + s.card ≤ a by omega)
    rw [card_insert_of_notMem ha, ← Nat.add_assoc, Nat.choose_succ_succ,
      sum_insert ha]
    have hprev := ih hlo
    simp only [Nat.succ_eq_add_one] at *
    omega

/-- Binomial weights on the extremal consecutive spectrum. -/
theorem consecutive_binomial_mass (b k j : ℕ) :
    b.choose (j + 1) + ∑ i ∈ range k, (b + i).choose j = (b + k).choose (j + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ← Nat.add_assoc, ih, ← Nat.add_assoc, Nat.choose_succ_succ, Nat.add_comm]

/-- Summing the excess over the minimum once per occupied level pays for
distinct levels; summing the minimum pays for every occurrence. -/
theorem multiplicity_binomial_bound {α : Type*} (s : Finset α) (m : α → ℕ)
    (b j : ℕ) (hb : ∀ x ∈ s, b ≤ m x) :
    (b + (s.image m).card).choose (j + 1) +
        (s.card - (s.image m).card) * b.choose j ≤
      b.choose (j + 1) + ∑ x ∈ s, (m x).choose j := by
  classical
  let excess (n : ℕ) := n.choose j - b.choose j
  have expand {ι : Type*} (t : Finset ι) (f : ι → ℕ) (hf : ∀ x ∈ t, b ≤ f x) :
      ∑ x ∈ t, (f x).choose j = t.card * b.choose j + ∑ x ∈ t, excess (f x) := by
    rw [show t.card * b.choose j = ∑ _x ∈ t, b.choose j by simp, ← sum_add_distrib]
    exact sum_congr rfl fun x hx => (Nat.add_sub_of_le (Nat.choose_le_choose j (hf x hx))).symm
  have hd : ∀ n ∈ s.image m, b ≤ n := by
    rintro _ hn
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hn
    exact hb x hx
  have he : ∑ n ∈ s.image m, excess n ≤ ∑ x ∈ s, excess (m x) := by
    clear hb hd
    induction s using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      rw [image_insert, sum_insert ha]
      by_cases hm : m a ∈ t.image m
      · rw [insert_eq_of_mem hm]
        omega
      · rw [sum_insert hm]
        exact Nat.add_le_add_left ih _
  have h := distinct_binomial_bound (s.image m) b j hd
  have hsplit := @expand ℕ (s.image m) (fun n : ℕ => n) (fun n hn => hd n hn)
  rw [hsplit] at h
  rw [expand s m hb, Nat.sub_mul]
  have hcard := Nat.mul_le_mul_right (b.choose j) (card_image_le (s := s) (f := m))
  omega

/-- A placement of nonattacking rooks inside a finite board. -/
def HoldsRooks (B : Finset (ℕ × ℕ)) (k : ℕ) : Prop :=
  ∃ R ⊆ B, R.card = k ∧ Set.InjOn Prod.fst (R : Set (ℕ × ℕ)) ∧
    Set.InjOn Prod.snd (R : Set (ℕ × ℕ))

/-- The first i rows and the first rowLen(i) columns cover every cell. -/
private theorem rook_cover {μ : YoungDiagram} {k : ℕ} (h : HoldsRooks μ.cells k) (i : ℕ) :
    k ≤ i + μ.rowLen i := by
  obtain ⟨R, hR, rfl, hr, hc⟩ := h
  let top := R.filter fun p => p.1 < i
  let bot := R.filter fun p => ¬p.1 < i
  have ht : top.card ≤ i := by
    simpa only [card_range] using card_le_card_of_injOn (t := range i) Prod.fst
      (fun p (hp : p ∈ top) => mem_range.mpr (mem_filter.mp hp).2)
      (hr.mono (filter_subset _ _))
  have hb : bot.card ≤ μ.rowLen i := by
    simpa only [card_range] using card_le_card_of_injOn (t := range (μ.rowLen i)) Prod.snd
      (fun p (hp : p ∈ bot) => mem_range.mpr (YoungDiagram.mem_iff_lt_rowLen.mp
        (μ.up_left_mem (Nat.le_of_not_gt (mem_filter.mp hp).2) le_rfl
          (hR (mem_filter.mp hp).1))))
      (hc.mono (filter_subset _ _))
  have hsum := R.card_filter_add_card_filter_not (fun p => p.1 < i)
  change top.card + bot.card = R.card at hsum
  omega

/-- The largest staircase contained in a Young diagram is its rook number.
The antidiagonal constructs a simultaneous placement from all row bounds. -/
theorem holdsRooks_iff_staircase (μ : YoungDiagram) (k : ℕ) :
    HoldsRooks μ.cells k ↔ ∀ i < k, k ≤ i + μ.rowLen i := by
  constructor
  · exact fun h i _ => rook_cover h i
  · intro h
    let cell (i : ℕ) := (i, k - 1 - i)
    refine ⟨(range k).image cell, ?_, ?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
      have hi' := mem_range.mp hi
      have hlen := h i hi'
      exact YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    · rw [card_image_of_injective _ (fun x y he => congrArg Prod.fst he), card_range]
    · rintro p hp q hq he
      obtain ⟨i, _, rfl⟩ := mem_image.mp hp
      obtain ⟨j, _, rfl⟩ := mem_image.mp hq
      exact congrArg cell he
    · rintro p hp q hq he
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hq
      change k - 1 - i = k - 1 - j at he
      have hi' := mem_range.mp hi
      have hj' := mem_range.mp hj
      exact congrArg cell (by omega)

/-- Slonim's area bound extends to every placement inside the outer shape,
including rooks on an arbitrary skew subdiagram. -/
theorem rook_area {μ : YoungDiagram} {k : ℕ} (h : HoldsRooks μ.cells k) :
    (k + 1).choose 2 ≤ μ.card := by
  obtain ⟨R, hR, rfl, hr, hc⟩ := h
  let rows (p : ℕ × ℕ) := μ.row p.1
  have hdis : (R : Set (ℕ × ℕ)).PairwiseDisjoint rows := by
    intro p hp q hq hpq
    apply Finset.disjoint_left.mpr
    intro x hxp hxq
    exact hpq (hr hp hq ((YoungDiagram.mem_row_iff.mp hxp).2.symm.trans
      (YoungDiagram.mem_row_iff.mp hxq).2))
  have hsum : ∑ p ∈ R, (p.2 + 1) ≤ μ.card := by
    calc
      _ ≤ ∑ p ∈ R, (rows p).card := sum_le_sum fun p hp => by
        rw [← YoungDiagram.rowLen_eq_card]
        exact YoungDiagram.mem_iff_lt_rowLen.mp (hR hp)
      _ = (R.biUnion rows).card := (card_biUnion hdis).symm
      _ ≤ μ.card := card_le_card fun x hx => by
        obtain ⟨_,_,hm⟩ := mem_biUnion.mp hx
        exact (YoungDiagram.mem_row_iff.mp hm).1
  let len (p : ℕ × ℕ) := p.2 + 1
  have hinj : Set.InjOn len (R : Set (ℕ × ℕ)) :=
    fun _ hx _ hy he => hc hx hy (Nat.add_right_cancel he)
  have hbound := distinct_binomial_bound (R.image len) 1 1 (by
    rintro _ hn
    obtain ⟨p, _, rfl⟩ := mem_image.mp hn
    exact Nat.succ_pos _)
  simpa only [card_image_of_injOn hinj, Nat.add_comm 1 R.card, Nat.choose_one_right,
    Nat.choose_succ_self, zero_add, sum_image hinj] using hbound.trans (by
      simpa [len, Nat.choose_one_right, sum_image hinj] using hsum)

#print axioms multiplicity_binomial_bound
#print axioms holdsRooks_iff_staircase
#print axioms rook_area

end GaloisForLFunctions.StaircasePacking
