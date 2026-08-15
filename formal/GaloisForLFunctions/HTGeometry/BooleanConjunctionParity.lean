import Mathlib

/-!
# Parity of coordinate-conjunction counts on Boolean point sets

For a finite set of Boolean points and a set `S` of coordinates, the conjunction fibre of `S` is the
set of points whose `S`-coordinates are all `true`.  If every conjunction fibre of at most `m`
coordinates has even cardinality and the point set is nonempty, then the point set has at least
`2^(m+1)` elements.  Splitting on a coordinate at which two points differ halves the problem: the
`true` half is itself a conjunction fibre of the original set, and the `false` half inherits
evenness by difference, so both halves satisfy the hypothesis one order lower.

This is the minimum-distance statement for the dual of the order-`m` Reed–Muller code, proved
directly from the recursion rather than through the duality theorem.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {ι : Type*} [DecidableEq ι]

/-- The points of `T` all of whose coordinates in `S` are `true`. -/
def conjunctionFiber (S : Finset ι) (T : Finset (ι → Bool)) : Finset (ι → Bool) :=
  T.filter fun x => ∀ i ∈ S, x i = true

theorem mem_conjunctionFiber {S : Finset ι} {T : Finset (ι → Bool)} {x : ι → Bool} :
    x ∈ conjunctionFiber S T ↔ x ∈ T ∧ ∀ i ∈ S, x i = true := by
  rw [conjunctionFiber, Finset.mem_filter]

theorem conjunctionFiber_empty (T : Finset (ι → Bool)) :
    conjunctionFiber (∅ : Finset ι) T = T := by
  ext x
  rw [mem_conjunctionFiber]
  simp

/-- The `true` half of a conjunction fibre is the conjunction fibre of the enlarged coordinate
set. -/
theorem conjunctionFiber_filter_true (S : Finset ι) (T : Finset (ι → Bool)) (i : ι) :
    conjunctionFiber S (T.filter fun x => x i = true) = conjunctionFiber (insert i S) T := by
  ext x
  rw [mem_conjunctionFiber, Finset.mem_filter, mem_conjunctionFiber]
  constructor
  · rintro ⟨⟨hxT, hxi⟩, hS⟩
    refine ⟨hxT, fun j hj => ?_⟩
    rcases Finset.mem_insert.mp hj with hji | hjS
    · rw [hji]; exact hxi
    · exact hS j hjS
  · rintro ⟨hxT, hS⟩
    exact ⟨⟨hxT, hS i (Finset.mem_insert_self i S)⟩, fun j hj =>
      hS j (Finset.mem_insert_of_mem hj)⟩

theorem conjunctionFiber_filter_eq (S : Finset ι) (T : Finset (ι → Bool)) (i : ι) (b : Bool) :
    conjunctionFiber S (T.filter fun x => x i = b) =
      (conjunctionFiber S T).filter fun x => x i = b := by
  ext x
  rw [mem_conjunctionFiber, Finset.mem_filter, Finset.mem_filter, mem_conjunctionFiber]
  tauto

/-- **A nonempty Boolean point set with even conjunction counts up to order `m` has at least
`2^(m+1)` points.** -/
theorem two_pow_le_card_of_even_conjunctionFiber (m : ℕ) :
    ∀ T : Finset (ι → Bool), T.Nonempty →
      (∀ S : Finset ι, S.card ≤ m → Even (conjunctionFiber S T).card) →
      2 ^ (m + 1) ≤ T.card := by
  induction m with
  | zero =>
    intro T hT heven
    have h0 := heven ∅ (by simp)
    rw [conjunctionFiber_empty] at h0
    obtain ⟨c, hc⟩ := h0
    have hpos : 0 < T.card := Finset.card_pos.mpr hT
    omega
  | succ m ih =>
    intro T hT heven
    have h0 := heven ∅ (by simp)
    rw [conjunctionFiber_empty] at h0
    obtain ⟨c0, hc0⟩ := h0
    have hpos : 0 < T.card := Finset.card_pos.mpr hT
    have h2 : 1 < T.card := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h2
    obtain ⟨i, hi⟩ : ∃ i : ι, a i ≠ b i := by
      by_contra hcon
      exact hab (funext fun i => not_not.mp (fun h => hcon ⟨i, h⟩))
    set T₁ : Finset (ι → Bool) := T.filter fun x => x i = true with hT₁
    set T₀ : Finset (ι → Bool) := T.filter fun x => x i = false with hT₀
    have hsplit : T₁.card + T₀.card = T.card := by
      rw [hT₁, hT₀]
      have hcongr : (T.filter fun x => x i = false) = T.filter fun x => ¬ (x i = true) := by
        refine Finset.filter_congr fun x _ => ?_
        simp
      rw [hcongr]
      exact Finset.card_filter_add_card_filter_not _
    have hne : ∀ x : ι → Bool, x i = true ∨ x i = false := by
      intro x
      cases hx : x i
      · exact Or.inr rfl
      · exact Or.inl rfl
    have hT₁ne : T₁.Nonempty := by
      rcases hne a with hat | haf
      · exact ⟨a, Finset.mem_filter.mpr ⟨ha, hat⟩⟩
      · have hbt : b i = true := by
          rcases hne b with h | h
          · exact h
          · exact absurd (haf.trans h.symm) hi
        exact ⟨b, Finset.mem_filter.mpr ⟨hb, hbt⟩⟩
    have hT₀ne : T₀.Nonempty := by
      rcases hne a with hat | haf
      · have hbf : b i = false := by
          rcases hne b with h | h
          · exact absurd (hat.trans h.symm) hi
          · exact h
        exact ⟨b, Finset.mem_filter.mpr ⟨hb, hbf⟩⟩
      · exact ⟨a, Finset.mem_filter.mpr ⟨ha, haf⟩⟩
    have heven₁ : ∀ S : Finset ι, S.card ≤ m → Even (conjunctionFiber S T₁).card := by
      intro S hS
      rw [hT₁, conjunctionFiber_filter_true]
      refine heven (insert i S) ?_
      exact le_trans (Finset.card_insert_le i S) (by omega)
    have heven₀ : ∀ S : Finset ι, S.card ≤ m → Even (conjunctionFiber S T₀).card := by
      intro S hS
      have hsum : (conjunctionFiber S T₁).card + (conjunctionFiber S T₀).card =
          (conjunctionFiber S T).card := by
        rw [hT₁, hT₀, conjunctionFiber_filter_eq, conjunctionFiber_filter_eq]
        have hcongr : ((conjunctionFiber S T).filter fun x => x i = false) =
            (conjunctionFiber S T).filter fun x => ¬ (x i = true) := by
          refine Finset.filter_congr fun x _ => ?_
          simp
        rw [hcongr]
        exact Finset.card_filter_add_card_filter_not _
      obtain ⟨u, hu⟩ := heven₁ S hS
      obtain ⟨v, hv⟩ := heven S (le_trans hS (by omega))
      refine ⟨v - u, ?_⟩
      omega
    have h1 := ih T₁ hT₁ne heven₁
    have h0' := ih T₀ hT₀ne heven₀
    have hpow : 2 ^ (m + 1 + 1) = 2 ^ (m + 1) + 2 ^ (m + 1) := by ring
    omega

/-- **Contrapositive form.**  A nonempty Boolean point set with fewer than `2^(m+1)` points has a
coordinate set of size at most `m` whose conjunction fibre has odd cardinality. -/
theorem exists_odd_conjunctionFiber {m : ℕ} {T : Finset (ι → Bool)} (hT : T.Nonempty)
    (hcard : T.card < 2 ^ (m + 1)) :
    ∃ S : Finset ι, S.card ≤ m ∧ ¬ Even (conjunctionFiber S T).card := by
  by_contra hcon
  have heven : ∀ S : Finset ι, S.card ≤ m → Even (conjunctionFiber S T).card := by
    intro S hS
    by_contra hodd
    exact hcon ⟨S, hS, hodd⟩
  exact absurd (two_pow_le_card_of_even_conjunctionFiber m T hT heven) (by omega)

end GaloisForLFunctions.HTGeometry
