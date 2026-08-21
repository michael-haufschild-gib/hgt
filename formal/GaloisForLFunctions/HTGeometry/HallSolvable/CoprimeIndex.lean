import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring

/-!
# Subgroups of coprime index

Two subgroups of a finite group whose indices are coprime intersect in a subgroup of index the
product of the indices, and their product set is the whole group.
-/

namespace GaloisForLFunctions.HTGeometry.HallSolvable

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem index_inf_eq_mul {H K : Subgroup G} (h : Nat.Coprime H.index K.index) :
    (H ⊓ K).index = H.index * K.index := by
  refine le_antisymm Subgroup.index_inf_le ?_
  have h1 : H.index ∣ (H ⊓ K).index := Subgroup.index_dvd_of_le inf_le_left
  have h2 : K.index ∣ (H ⊓ K).index := Subgroup.index_dvd_of_le inf_le_right
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (Nat.Coprime.mul_dvd_of_dvd_of_dvd h h1 h2)

omit [Finite G] in
theorem card_dvd_card_mul_left (H K : Subgroup G) :
    Nat.card ↥K ∣ Nat.card ((↑H : Set G) * (↑K : Set G) : Set G) := by
  rw [Subgroup.card_mul_eq_card_subgroup_mul_card_quotient K (↑H : Set G)]
  exact Dvd.intro _ rfl

omit [Finite G] in
theorem card_mul_comm (H K : Subgroup G) :
    Nat.card ((↑K : Set G) * (↑H : Set G) : Set G)
      = Nat.card ((↑H : Set G) * (↑K : Set G) : Set G) := by
  have hmem1 : ∀ x : G, x ∈ (↑K : Set G) * (↑H : Set G) →
      x⁻¹ ∈ (↑H : Set G) * (↑K : Set G) := by
    intro x hx
    obtain ⟨k, hk, h', hh', rfl⟩ := Set.mem_mul.mp hx
    exact Set.mem_mul.mpr ⟨h'⁻¹, H.inv_mem hh', k⁻¹, K.inv_mem hk, by group⟩
  have hmem2 : ∀ x : G, x ∈ (↑H : Set G) * (↑K : Set G) →
      x⁻¹ ∈ (↑K : Set G) * (↑H : Set G) := by
    intro x hx
    obtain ⟨h', hh', k, hk, rfl⟩ := Set.mem_mul.mp hx
    exact Set.mem_mul.mpr ⟨k⁻¹, K.inv_mem hk, h'⁻¹, H.inv_mem hh', by group⟩
  refine Nat.card_congr ⟨fun x => ⟨(x : G)⁻¹, hmem1 x x.2⟩, fun y => ⟨(y : G)⁻¹, hmem2 y y.2⟩,
    fun x => by simp, fun y => by simp⟩

omit [Finite G] in
theorem card_dvd_card_mul_right (H K : Subgroup G) :
    Nat.card ↥H ∣ Nat.card ((↑H : Set G) * (↑K : Set G) : Set G) := by
  rw [← card_mul_comm H K]
  exact card_dvd_card_mul_left K H

/-- **Two subgroups of coprime index cover the group.** -/
theorem mul_eq_univ_of_coprime_index {H K : Subgroup G} (h : Nat.Coprime H.index K.index) :
    (↑H : Set G) * (↑K : Set G) = Set.univ := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  set c : ℕ := Nat.card ((↑H : Set G) * (↑K : Set G) : Set G) with hc
  have hHc : Nat.card ↥H ∣ c := card_dvd_card_mul_right H K
  have hKc : Nat.card ↥K ∣ c := card_dvd_card_mul_left H K
  have hle : c ≤ Nat.card G := by
    rw [hc]
    exact Nat.card_le_card_of_injective (Subtype.val) Subtype.val_injective
  have hLdvd : Nat.lcm (Nat.card ↥H) (Nat.card ↥K) ∣ c := Nat.lcm_dvd hHc hKc
  have hGdvd : Nat.card G ∣ Nat.lcm (Nat.card ↥H) (Nat.card ↥K) := by
    obtain ⟨e, he⟩ : Nat.lcm (Nat.card ↥H) (Nat.card ↥K) ∣ Nat.card G :=
      Nat.lcm_dvd (Subgroup.card_subgroup_dvd_card H) (Subgroup.card_subgroup_dvd_card K)
    obtain ⟨s, hs⟩ : Nat.card ↥H ∣ Nat.lcm (Nat.card ↥H) (Nat.card ↥K) := Nat.dvd_lcm_left _ _
    obtain ⟨t, ht⟩ : Nat.card ↥K ∣ Nat.lcm (Nat.card ↥H) (Nat.card ↥K) := Nat.dvd_lcm_right _ _
    have heH : e ∣ H.index := by
      refine ⟨s, Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥H)) ?_⟩
      rw [Subgroup.card_mul_index H, he, hs]
      ring
    have heK : e ∣ K.index := by
      refine ⟨t, Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥K)) ?_⟩
      rw [Subgroup.card_mul_index K, he, ht]
      ring
    have he1 : e = 1 := Nat.eq_one_of_dvd_one (h ▸ Nat.dvd_gcd heH heK)
    exact ⟨1, by rw [he, he1, mul_one, mul_one]⟩
  have hone : (1 : G) ∈ ((↑H : Set G) * (↑K : Set G) : Set G) :=
    Set.mem_mul.mpr ⟨1, H.one_mem, 1, K.one_mem, by group⟩
  haveI : Nonempty ((↑H : Set G) * (↑K : Set G) : Set G) := ⟨⟨1, hone⟩⟩
  have hcpos : 0 < c := by rw [hc]; exact Nat.card_pos
  have hceq : c = Nat.card G := Nat.le_antisymm hle (Nat.le_of_dvd hcpos (hGdvd.trans hLdvd))
  have hfinset : ((↑H : Set G) * (↑K : Set G) : Set G).toFinset = Finset.univ := by
    refine Finset.eq_univ_of_card _ ?_
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card, ← hc, hceq, Nat.card_eq_fintype_card]
  have hfin := congrArg (fun (s : Finset G) => (s : Set G)) hfinset
  simpa using hfin

end GaloisForLFunctions.HTGeometry.HallSolvable
