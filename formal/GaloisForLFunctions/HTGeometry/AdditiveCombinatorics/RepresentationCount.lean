import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.Convolution
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# `i`-representable products, and the representation lower bound

`repSet A B i` is the set `A ·_i B` of elements of a finite commutative group having at least `i`
representations as a product of an element of `A` and an element of `B`; `repSum A B t` is
`∑_{i=1}^t #(A ·_i B)`, the quantity appearing in Pollard-type theorems.

The main theorem here is `card_add_card_le_rep_add_card_mul`: every element of `A · B` has at
least `#A + #B − #(A · B)` representations.  Grynkiewicz records this as a consequence of Kneser's
theorem; the argument used here restricts to a single coset pair of the stabiliser of `A · B`,
where the convolution lower bound `card_add_card_le_rep_add_card_coset` applies, and compares the
resulting bound with the hole count supplied by Kneser's theorem.
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [DecidableEq G]

theorem rep_pos_iff_mem_mul (A B : Finset G) (c : G) : 0 < rep A B c ↔ c ∈ A * B := by
  classical
  rw [rep, Finset.card_pos]
  constructor
  · rintro ⟨p, hp⟩
    rw [Finset.mem_filter, Finset.mem_product] at hp
    exact mem_mul.2 ⟨p.1, hp.1.1, p.2, hp.1.2, hp.2⟩
  · intro hc
    obtain ⟨a, ha, b, hb, hab⟩ := mem_mul.1 hc
    exact ⟨(a, b), by rw [Finset.mem_filter, Finset.mem_product]; exact ⟨⟨ha, hb⟩, hab⟩⟩

variable [Fintype G]

/-- **Every element of `A · B` has at least `#A + #B − #(A · B)` representations.**
This is Grynkiewicz's Proposition A(i); it follows from Kneser's theorem together with the
convolution lower bound inside a coset of the stabiliser. -/
theorem card_add_card_le_rep_add_card_mul {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty)
    {x : G} (hx : x ∈ A * B) :
    A.card + B.card ≤ rep A B x + (A * B).card := by
  classical
  have hHgrp : IsSubgroupFinset (mulStab (A * B)) := isSubgroupFinset_mulStab (A * B)
  obtain ⟨α, hα, β, hβ, hxab⟩ := mem_mul.1 hx
  have hAα : A ∩ (α • mulStab (A * B)) ⊆ α • mulStab (A * B) := Finset.inter_subset_right
  have hBβ : B ∩ (β • mulStab (A * B)) ⊆ β • mulStab (A * B) := Finset.inter_subset_right
  have hxcoset : x ∈ (α * β) • mulStab (A * B) := by
    rw [← hxab]; exact hHgrp.mem_smul_self _
  have hcoset := card_add_card_le_rep_add_card_coset hHgrp hAα hBβ hxcoset
  have hmono : rep (A ∩ (α • mulStab (A * B))) (B ∩ (β • mulStab (A * B))) x ≤ rep A B x :=
    rep_mono Finset.inter_subset_left Finset.inter_subset_left x
  -- the coset slice of `A` through `α` misses no more points than `A` misses inside `A * H`
  have hholeA : (mulStab (A * B)).card + A.card
      ≤ (A ∩ (α • mulStab (A * B))).card + (A * mulStab (A * B)).card := by
    have hsub : (α • mulStab (A * B)) \ (A ∩ (α • mulStab (A * B)))
        ⊆ (A * mulStab (A * B)) \ A := by
      intro z hz
      rw [Finset.mem_sdiff, Finset.mem_inter] at hz
      refine Finset.mem_sdiff.2 ⟨?_, fun hzA => hz.2 ⟨hzA, hz.1⟩⟩
      obtain ⟨h, hh, rfl⟩ := mem_smul_finset.1 hz.1
      exact mul_mem_mul hα hh
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_sdiff_add_card_eq_card
      (Finset.inter_subset_right : A ∩ (α • mulStab (A * B)) ⊆ α • mulStab (A * B))
    have h3 := Finset.card_sdiff_add_card_eq_card (hHgrp.subset_mul A)
    have h4 : (α • mulStab (A * B)).card = (mulStab (A * B)).card :=
      Finset.card_smul_finset _ _
    omega
  have hholeB : (mulStab (A * B)).card + B.card
      ≤ (B ∩ (β • mulStab (A * B))).card + (B * mulStab (A * B)).card := by
    have hsub : (β • mulStab (A * B)) \ (B ∩ (β • mulStab (A * B)))
        ⊆ (B * mulStab (A * B)) \ B := by
      intro z hz
      rw [Finset.mem_sdiff, Finset.mem_inter] at hz
      refine Finset.mem_sdiff.2 ⟨?_, fun hzB => hz.2 ⟨hzB, hz.1⟩⟩
      obtain ⟨h, hh, rfl⟩ := mem_smul_finset.1 hz.1
      exact mul_mem_mul hβ hh
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_sdiff_add_card_eq_card
      (Finset.inter_subset_right : B ∩ (β • mulStab (A * B)) ⊆ β • mulStab (A * B))
    have h3 := Finset.card_sdiff_add_card_eq_card (hHgrp.subset_mul B)
    have h4 : (β • mulStab (A * B)).card = (mulStab (A * B)).card :=
      Finset.card_smul_finset _ _
    omega
  have hkneser := card_mul_le_card_mul_mulStab A B hA hB
  omega

/-- If `#A + #B` exceeds `#G` then `A · B` is everything.  (Grynkiewicz's Proposition A(ii).) -/
theorem mul_eq_univ_of_card_lt {A B : Finset G} (h : Fintype.card G < A.card + B.card) :
    A * B = univ := by
  apply Finset.eq_univ_of_forall
  intro c
  rw [← rep_pos_iff_mem_mul]
  have := card_add_card_le_rep_add_card A B c
  omega


/-! ### The sets of `i`-representable products -/

/-- `repSet A B i = A +_i B` is the set of elements with at least `i` representations. -/
def repSet (A B : Finset G) (i : ℕ) : Finset G := univ.filter (fun g => i ≤ rep A B g)

@[simp] theorem mem_repSet {A B : Finset G} {i : ℕ} {g : G} :
    g ∈ repSet A B i ↔ i ≤ rep A B g := by simp [repSet]

theorem repSet_one (A B : Finset G) : repSet A B 1 = A * B := by
  ext g
  rw [mem_repSet, Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, rep_pos_iff_mem_mul]

theorem repSet_antitone (A B : Finset G) {i j : ℕ} (h : i ≤ j) : repSet A B j ⊆ repSet A B i := by
  intro g hg
  rw [mem_repSet] at hg ⊢
  omega

theorem repSet_subset_mul (A B : Finset G) {i : ℕ} (hi : 1 ≤ i) : repSet A B i ⊆ A * B := by
  rw [← repSet_one]
  exact repSet_antitone A B hi

/-- `repSum A B t = ∑_{i=1}^t |A +_i B|`. -/
def repSum (A B : Finset G) (t : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 t, (repSet A B i).card

private theorem sum_indicator_Icc (r t : ℕ) :
    (∑ i ∈ Finset.Icc 1 t, if i ≤ r then 1 else 0) = min r t := by
  rw [← Finset.card_filter]
  have hset : (Finset.Icc 1 t).filter (fun i => i ≤ r) = Finset.Icc 1 (min t r) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc, le_min_iff]
    omega
  rw [hset, Nat.card_Icc]
  omega

/-- The layer-cake identity `∑_{i=1}^t |A +_i B| = ∑_g min (r_{A,B}(g), t)`. -/
theorem repSum_eq_sum_min (A B : Finset G) (t : ℕ) :
    repSum A B t = ∑ g : G, min (rep A B g) t := by
  classical
  rw [repSum]
  have hcard : ∀ i, (repSet A B i).card = ∑ g : G, if i ≤ rep A B g then 1 else 0 := by
    intro i
    rw [repSet, Finset.card_filter]
  simp only [hcard]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  exact sum_indicator_Icc _ _

/-- The total mass `∑_g r_{A,B}(g) = #A · #B`. -/
theorem sum_rep (A B : Finset G) : ∑ g : G, rep A B g = A.card * B.card := by
  classical
  have h : (A ×ˢ B).card = ∑ g : G, ((A ×ˢ B).filter (fun p => p.1 * p.2 = g)).card :=
    Finset.card_eq_sum_card_fiberwise (fun p _ => Finset.mem_univ (p.1 * p.2))
  rw [Finset.card_product] at h
  simpa [rep] using h.symm

theorem repSum_le (A B : Finset G) (t : ℕ) : repSum A B t ≤ A.card * B.card := by
  rw [repSum_eq_sum_min, ← sum_rep A B]
  exact Finset.sum_le_sum (fun g _ => min_le_left _ _)

theorem repSum_le_mul_card (A B : Finset G) (t : ℕ) :
    repSum A B t ≤ t * (A * B).card := by
  rw [repSum]
  calc ∑ i ∈ Finset.Icc 1 t, (repSet A B i).card
      ≤ ∑ _i ∈ Finset.Icc 1 t, (A * B).card := by
        refine Finset.sum_le_sum (fun i hi => Finset.card_le_card ?_)
        exact repSet_subset_mul A B (Finset.mem_Icc.1 hi).1
    _ = t * (A * B).card := by
        rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul]
        simp

end GaloisForLFunctions.HTGeometry.AddComb
