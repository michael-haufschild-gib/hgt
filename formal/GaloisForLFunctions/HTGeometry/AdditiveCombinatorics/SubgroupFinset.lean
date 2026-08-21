import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Tactic.Group

/-!
# Subgroups as `Finset`s, cosets, and the stabiliser of a finite set

This file provides the elementary group-theoretic layer needed for Kneser's addition theorem
and its consequences in `ℤ_q^×`.

* `IsSubgroupFinset H` says that a `Finset` of a commutative group is a subgroup.
* `mulStab s` is the stabiliser `{g : g • s = s}` of a finite set, as a `Finset`;
  `stabSubgroup s` is the same thing as a bundled `Subgroup`.
* `IsSubgroupFinset.card_dvd_card_mul` is Lagrange's theorem in the form we need:
  `#H ∣ #(t * H)`, proved by partitioning `t * H` into cosets.
* `card_mul_subgroupFinset_eq` computes `#(t * H)` as `#H` times the number of points of the
  quotient group hit by `t`; this is what powers the quotient reduction in Kneser's theorem.

Everything is stated for a *finite* commutative group, which is the setting of the intended
applications (`G = ℤ_q^×`).
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [DecidableEq G] {H : Finset G}

/-- A `Finset` of a commutative group that happens to be a subgroup. -/
structure IsSubgroupFinset (H : Finset G) : Prop where
  one_mem : (1 : G) ∈ H
  mul_mem : ∀ {a b : G}, a ∈ H → b ∈ H → a * b ∈ H
  inv_mem : ∀ {a : G}, a ∈ H → a⁻¹ ∈ H

namespace IsSubgroupFinset

omit [DecidableEq G] in
theorem nonempty (h : IsSubgroupFinset H) : H.Nonempty := ⟨1, h.one_mem⟩

omit [DecidableEq G] in
theorem card_pos' (h : IsSubgroupFinset H) : 0 < H.card := Finset.card_pos.2 h.nonempty

theorem mul_self (h : IsSubgroupFinset H) : H * H = H := by
  refine Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
  · rw [mem_mul] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    exact h.mul_mem ha hb
  · rw [mem_mul]
    exact ⟨x, hx, 1, h.one_mem, mul_one x⟩

theorem smul_eq (h : IsSubgroupFinset H) {a : G} (ha : a ∈ H) : a • H = H := by
  refine Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
  · rw [mem_smul_finset] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact h.mul_mem ha hy
  · rw [mem_smul_finset]
    exact ⟨a⁻¹ * x, h.mul_mem (h.inv_mem ha) hx, by simp⟩

theorem mem_of_smul_eq (h : IsSubgroupFinset H) {a : G} (ha : a • H = H) : a ∈ H := by
  have : a * 1 ∈ a • H := mem_smul_finset.2 ⟨1, h.one_mem, rfl⟩
  rw [ha, mul_one] at this
  exact this

theorem smul_eq_iff (h : IsSubgroupFinset H) {a : G} : a • H = H ↔ a ∈ H :=
  ⟨h.mem_of_smul_eq, h.smul_eq⟩

theorem mem_smul_self (h : IsSubgroupFinset H) (x : G) : x ∈ x • H :=
  mem_smul_finset.2 ⟨1, h.one_mem, mul_one x⟩

/-- Every element of a coset generates the same coset. -/
theorem smul_eq_smul_of_mem (h : IsSubgroupFinset H) {x z : G} (hz : z ∈ x • H) :
    z • H = x • H := by
  simp only [mem_smul_finset, smul_eq_mul] at hz
  obtain ⟨u, hu, rfl⟩ := hz
  rw [mul_smul, h.smul_eq hu]

/-- Two cosets that meet are equal. -/
theorem smul_coset_eq_of_mem (h : IsSubgroupFinset H) {x y z : G}
    (hx : z ∈ x • H) (hy : z ∈ y • H) : x • H = y • H := by
  rw [← h.smul_eq_smul_of_mem hx, h.smul_eq_smul_of_mem hy]

/-- Distinct cosets are disjoint. -/
theorem smul_coset_disjoint (h : IsSubgroupFinset H) {x y : G} (hxy : x • H ≠ y • H) :
    Disjoint (x • H) (y • H) := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  exact hxy (h.smul_coset_eq_of_mem hz hz')

theorem mul_stable (h : IsSubgroupFinset H) (t : Finset G) : t * H * H = t * H := by
  rw [mul_assoc, h.mul_self]

theorem subset_mul (h : IsSubgroupFinset H) (t : Finset G) : t ⊆ t * H := by
  intro x hx
  rw [mem_mul]
  exact ⟨x, hx, 1, h.one_mem, mul_one x⟩

theorem smul_subset_mul (h : IsSubgroupFinset H) {t : Finset G} {x : G} (hx : x ∈ t * H) :
    x • H ⊆ t * H := by
  intro z hz
  rw [mem_smul_finset] at hz
  obtain ⟨u, hu, rfl⟩ := hz
  have : x • u ∈ t * H * H := mul_mem_mul hx hu
  rwa [h.mul_stable] at this

/-- **Lagrange's theorem**, in the shape we need: the order of a subgroup divides the size of
any union of its cosets. -/
theorem card_dvd_card_mul (h : IsSubgroupFinset H) (t : Finset G) : H.card ∣ (t * H).card := by
  classical
  set S : Finset (Finset G) := (t * H).image (fun x => x • H) with hSdef
  have hcover : S.biUnion id = t * H := by
    ext z
    simp only [hSdef, mem_biUnion, mem_image, id]
    constructor
    · rintro ⟨u, ⟨x, hx, rfl⟩, hz⟩
      exact h.smul_subset_mul hx hz
    · intro hz
      exact ⟨z • H, ⟨z, hz, rfl⟩, h.mem_smul_self z⟩
  have hdisj : (S : Set (Finset G)).PairwiseDisjoint id := by
    intro u hu v hv huv
    simp only [hSdef, coe_image, Set.mem_image, mem_coe] at hu hv
    obtain ⟨x, _, rfl⟩ := hu
    obtain ⟨y, _, rfl⟩ := hv
    simp only [Function.onFun, id]
    exact h.smul_coset_disjoint huv
  have hsum : (t * H).card = ∑ u ∈ S, (id u).card := by
    rw [← hcover, Finset.card_biUnion hdisj]
  have hconst : ∀ u ∈ S, (id u).card = H.card := by
    intro u hu
    simp only [hSdef, mem_image] at hu
    obtain ⟨x, _, rfl⟩ := hu
    simp [Finset.card_smul_finset]
  rw [hsum, Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
  exact ⟨S.card, mul_comm _ _⟩

/-- A subgroup finset absorbs any subgroup finset it contains. -/
theorem mul_eq_self_of_subset (h : IsSubgroupFinset H) {K : Finset G} (hK : IsSubgroupFinset K)
    (hKH : K ⊆ H) : H * K = H := by
  refine Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
  · rw [mem_mul] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    exact h.mul_mem ha (hKH hb)
  · rw [mem_mul]
    exact ⟨x, hx, 1, hK.one_mem, mul_one x⟩

/-- Lagrange's theorem for a subgroup of a subgroup. -/
theorem card_dvd_card_of_subset {K : Finset G} (h : IsSubgroupFinset H) (hK : IsSubgroupFinset K)
    (hKH : K ⊆ H) : K.card ∣ H.card := by
  have := hK.card_dvd_card_mul H
  rwa [h.mul_eq_self_of_subset hK hKH] at this

end IsSubgroupFinset

/-! ### The stabiliser of a finite set -/

section Stab

variable [Fintype G]

/-- The stabiliser `{g : g • s = s}` of a finite set, as a `Finset`. -/
def mulStab (s : Finset G) : Finset G := univ.filter (fun g => g • s = s)

@[simp] theorem mem_mulStab {g : G} {s : Finset G} : g ∈ mulStab s ↔ g • s = s := by
  simp [mulStab]

/-- The stabiliser of a finite set, as a bundled subgroup. -/
def stabSubgroup (s : Finset G) : Subgroup G where
  carrier := {g | g • s = s}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [mul_smul, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    have h2 : a⁻¹ • (a • s) = s := inv_smul_smul a s
    rwa [ha] at h2

omit [Fintype G] in
@[simp] theorem mem_stabSubgroup {g : G} {s : Finset G} : g ∈ stabSubgroup s ↔ g • s = s := Iff.rfl

theorem isSubgroupFinset_mulStab (s : Finset G) : IsSubgroupFinset (mulStab s) where
  one_mem := by simp
  mul_mem := by
    intro a b ha hb
    simp only [mem_mulStab] at *
    rw [mul_smul, hb, ha]
  inv_mem := by
    intro a ha
    simp only [mem_mulStab] at *
    have h2 : a⁻¹ • (a • s) = s := inv_smul_smul a s
    rwa [ha] at h2

/-- A finite set absorbs its own stabiliser. -/
@[simp] theorem mul_mulStab (s : Finset G) : s * mulStab s = s := by
  refine Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
  · rw [mem_mul] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    rw [mem_mulStab] at hb
    rw [mul_comm, ← hb]
    exact mem_smul_finset.2 ⟨a, ha, rfl⟩
  · rw [mem_mul]
    exact ⟨x, hx, 1, by simp, mul_one x⟩

theorem card_mulStab_pos (s : Finset G) : 0 < (mulStab s).card :=
  (isSubgroupFinset_mulStab s).card_pos'

theorem card_mulStab_le (s : Finset G) (hs : s.Nonempty) : (mulStab s).card ≤ s.card := by
  obtain ⟨x, hx⟩ := hs
  have : x • mulStab s ⊆ s := by
    intro z hz
    have := (isSubgroupFinset_mulStab s).smul_subset_mul (t := s) (x := x)
      ((isSubgroupFinset_mulStab s).subset_mul s hx)
    rw [mul_mulStab] at this
    exact this hz
  calc (mulStab s).card = (x • mulStab s).card := (Finset.card_smul_finset x _).symm
    _ ≤ s.card := Finset.card_le_card this

/-- A coset of the stabiliser through a point of the set stays inside the set. -/
theorem smul_mulStab_subset {s : Finset G} {x : G} (hx : x ∈ s) : x • mulStab s ⊆ s := by
  intro z hz
  have h := (isSubgroupFinset_mulStab s).smul_subset_mul (t := s) (x := x)
    ((isSubgroupFinset_mulStab s).subset_mul s hx)
  rw [mul_mulStab] at h
  exact h hz

theorem mulStab_subgroupFinset_self (h : IsSubgroupFinset H) : mulStab H = H := by
  ext g
  rw [mem_mulStab]
  exact h.smul_eq_iff

/-- Translation invariance of the stabiliser. -/
@[simp] theorem mulStab_smul (g : G) (s : Finset G) : mulStab (g • s) = mulStab s := by
  ext x
  simp only [mem_mulStab]
  constructor
  · intro hx
    have hgx : g • (x • s) = g • s := by rw [smul_comm]; exact hx
    have := congrArg (fun t : Finset G => g⁻¹ • t) hgx
    simpa only [inv_smul_smul] using this
  · intro hx
    rw [smul_comm, hx]

end Stab

/-! ### Counting a union of cosets through the quotient group -/

section QuotientCount

variable [Fintype G]

/-- If `HN` is the underlying finset of a subgroup `N`, then `#(t * HN) = #HN` times the number
of points of `G ⧸ N` hit by `t`. -/
theorem card_mul_subgroupFinset_eq (N : Subgroup G) [DecidableEq (G ⧸ N)] (t HN : Finset G)
    (hHN : ∀ g : G, g ∈ HN ↔ g ∈ N) :
    (t * HN).card = HN.card * (t.image (fun g : G => (QuotientGroup.mk g : G ⧸ N))).card := by
  classical
  set φ : G → G ⧸ N := fun g => (QuotientGroup.mk g : G ⧸ N) with hφ
  set fib : G ⧸ N → Finset G := fun x => univ.filter (fun g => φ g = x) with hfib
  have hfibcard : ∀ x : G ⧸ N, (fib x).card = HN.card := by
    intro x
    obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective x
    have hEq : fib (φ g₀) = g₀ • HN := by
      ext g
      simp only [hfib, mem_filter, mem_univ, true_and, mem_smul_finset, smul_eq_mul, hφ]
      constructor
      · intro h
        refine ⟨g₀⁻¹ * g, (hHN _).2 ?_, by group⟩
        rw [← QuotientGroup.eq (s := N)]
        exact h.symm
      · rintro ⟨y, hy, rfl⟩
        have : (QuotientGroup.mk (g₀ * y) : G ⧸ N) = QuotientGroup.mk g₀ := by
          rw [QuotientGroup.eq]
          simpa using N.inv_mem ((hHN y).1 hy)
        simpa using this
    rw [hEq, card_smul_finset]
  have hcover : t * HN = (t.image φ).biUnion fib := by
    ext g
    simp only [mem_biUnion, mem_image, hfib, mem_filter, mem_univ, true_and]
    constructor
    · intro hg
      rw [mem_mul] at hg
      obtain ⟨a, ha, b, hb, rfl⟩ := hg
      refine ⟨φ a, ⟨a, ha, rfl⟩, ?_⟩
      simp only [hφ]
      rw [QuotientGroup.eq]
      simpa using N.inv_mem ((hHN b).1 hb)
    · rintro ⟨x, ⟨a, ha, rfl⟩, hgx⟩
      rw [mem_mul]
      refine ⟨a, ha, a⁻¹ * g, (hHN _).2 ?_, by group⟩
      rw [← QuotientGroup.eq (s := N)]
      exact hgx.symm
  have hdisj : ((t.image φ : Finset (G ⧸ N)) : Set (G ⧸ N)).PairwiseDisjoint fib := by
    intro x _ y _ hxy
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro g hgx hgy
    simp only [hfib, mem_filter] at hgx hgy
    exact hxy (hgx.2 ▸ hgy.2)
  rw [hcover, Finset.card_biUnion hdisj]
  rw [Finset.sum_congr rfl (fun x _ => hfibcard x), Finset.sum_const, smul_eq_mul, mul_comm]

end QuotientCount

end GaloisForLFunctions.HTGeometry.AddComb
