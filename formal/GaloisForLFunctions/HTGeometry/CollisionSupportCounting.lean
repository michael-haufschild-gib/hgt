import Mathlib
import GaloisForLFunctions.HTGeometry.PermutationCollisionInertia

/-!
# One lost point bounds the collision support

A label map on a finite set collides at most two points as soon as it loses at most one point:

```text
card α ≤ card (image r) + 1   ⟹   (collisionSupport r).ncard ≤ 2 .
```

The counting is exact.  Writing the source as the disjoint union of the fibres,
`Σ_{b ∈ image} (|fibre b| − 1) = card α − card (image r) ≤ 1`, and every colliding fibre
contributes at least `1` to that sum.  So at most one fibre collides, and it has exactly two
elements.

This converts a *degree* statement — the reduction loses one point — into the hypothesis the
transposition criterion consumes, without any further information about the map.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

/-- **One lost point bounds the collision support by two.** -/
theorem collisionSupport_ncard_le_two_of_card_le_card_image
    {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β] (r : α → β)
    (h : Fintype.card α ≤ (Finset.univ.image r).card + 1) :
    (collisionSupport r).ncard ≤ 2 := by
  classical
  set t : Finset β := Finset.univ.image r with ht
  set F : β → Finset α := fun b => Finset.univ.filter fun x => r x = b with hF
  have hmemF : ∀ (x : α) (b : β), x ∈ F b ↔ r x = b := by
    intro x b
    simp [hF]
  have hmemt : ∀ b : β, b ∈ t ↔ ∃ x : α, r x = b := by
    intro b
    simp [ht]
  -- the total fibre count
  have hsum : Fintype.card α = ∑ b ∈ t, (F b).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise fun x _ => Finset.mem_image_of_mem r (mem_univ x)
  have hone : ∀ b ∈ t, 1 ≤ (F b).card := by
    intro b hb
    obtain ⟨x, hx⟩ := (hmemt b).1 hb
    exact Finset.card_pos.2 ⟨x, (hmemF x b).2 hx⟩
  have hsplit : ∑ b ∈ t, (F b).card = ∑ b ∈ t, ((F b).card - 1) + t.card := by
    rw [Finset.card_eq_sum_ones t, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b hb => (Nat.sub_add_cancel (hone b hb)).symm
  have hexcess : ∑ b ∈ t, ((F b).card - 1) ≤ 1 := by omega
  -- the collision set as a finset
  set C : Finset α := Finset.univ.filter fun x => 2 ≤ (F (r x)).card with hC
  have hcoll : collisionSupport r = (C : Set α) := by
    ext x
    constructor
    · rintro ⟨y, hyx, hry⟩
      have hxy : ({x, y} : Finset α) ⊆ F (r x) := by
        intro z hz
        rcases Finset.mem_insert.1 hz with rfl | hz'
        · exact (hmemF z (r z)).2 rfl
        · rcases Finset.mem_singleton.1 hz' with rfl
          exact (hmemF z (r x)).2 hry
      have hcard : 2 ≤ (F (r x)).card := by
        have hpair : ({x, y} : Finset α).card = 2 := by
          rw [Finset.card_insert_of_notMem (by simpa using fun hh => hyx hh.symm),
            Finset.card_singleton]
        rw [← hpair]
        exact Finset.card_le_card hxy
      simpa [hC] using hcard
    · intro hx
      have hcard : 2 ≤ (F (r x)).card := by simpa [hC] using hx
      obtain ⟨y, hy, hyx⟩ := Finset.one_lt_card.1 (by omega : 1 < (F (r x)).card)
      obtain ⟨z, hz, hzy⟩ := hyx
      by_cases hxy : y = x
      · refine ⟨z, ?_, (hmemF z (r x)).1 hz⟩
        rw [← hxy]
        exact fun hh => hzy hh.symm
      · exact ⟨y, hxy, (hmemF y (r x)).1 hy⟩
  -- count the collision set fibrewise
  have himg : C.image r ⊆ t := by
    intro b hb
    obtain ⟨x, _, hx⟩ := Finset.mem_image.1 hb
    exact (hmemt b).2 ⟨x, hx⟩
  have hfibC : ∀ b ∈ C.image r, C.filter (fun x => r x = b) = F b := by
    intro b hb
    obtain ⟨x₀, hx₀C, hx₀⟩ := Finset.mem_image.1 hb
    have hx₀card : 2 ≤ (F (r x₀)).card := by simpa [hC] using hx₀C
    ext z
    simp only [Finset.mem_filter, hC, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, hz⟩
      exact (hmemF z b).2 hz
    · intro hz
      have hrz : r z = b := (hmemF z b).1 hz
      refine ⟨?_, hrz⟩
      rw [hrz, ← hx₀]
      exact hx₀card
  have hCcard : C.card = ∑ b ∈ C.image r, (F b).card := by
    have := Finset.card_eq_sum_card_fiberwise
      (f := r) (s := C) (t := C.image r) fun x hx => Finset.mem_image_of_mem r hx
    rw [this]
    exact Finset.sum_congr rfl fun b hb => congrArg Finset.card (hfibC b hb)
  have htwo : ∀ b ∈ C.image r, 2 ≤ (F b).card := by
    intro b hb
    obtain ⟨x₀, hx₀C, hx₀⟩ := Finset.mem_image.1 hb
    have hx₀card : 2 ≤ (F (r x₀)).card := by simpa [hC] using hx₀C
    rwa [hx₀] at hx₀card
  have hsub : ∑ b ∈ C.image r, ((F b).card - 1) ≤ ∑ b ∈ t, ((F b).card - 1) :=
    Finset.sum_le_sum_of_subset_of_nonneg himg fun _ _ _ => Nat.zero_le _
  have hcardimg : (C.image r).card ≤ ∑ b ∈ C.image r, ((F b).card - 1) := by
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_le_sum fun b hb => ?_
    have := htwo b hb
    omega
  have hCsplit : ∑ b ∈ C.image r, (F b).card
      = ∑ b ∈ C.image r, ((F b).card - 1) + (C.image r).card := by
    rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b hb => ?_
    have := htwo b hb
    omega
  have hfinal : C.card ≤ 2 := by omega
  rw [hcoll, Set.ncard_coe_finset]
  exact hfinal

/-- The same, stated with cardinals so that no decidability data is needed at the use site. -/
theorem collisionSupport_ncard_le_two_of_natCard_le_ncard_range
    {α β : Type*} [Finite α] (r : α → β)
    (h : Nat.card α ≤ (Set.range r).ncard + 1) :
    (collisionSupport r).ncard ≤ 2 := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  have hrange : (Set.range r).ncard = (Finset.univ.image r).card := by
    have hcoe : (↑(Finset.univ.image r) : Set β) = Set.range r := by
      ext b
      simp [Set.mem_range]
    rw [← hcoe, Set.ncard_coe_finset]
  have hcard : Fintype.card α = Nat.card α := (Nat.card_eq_fintype_card).symm
  refine collisionSupport_ncard_le_two_of_card_le_card_image r ?_
  rw [hcard, ← hrange]
  exact h

end GaloisForLFunctions.HTGeometry
