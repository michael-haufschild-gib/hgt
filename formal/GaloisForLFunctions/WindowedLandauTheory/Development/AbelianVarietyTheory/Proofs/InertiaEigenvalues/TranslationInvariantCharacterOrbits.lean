import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! A finite set stable under translation by a group element is a union
of whole cosets of the cyclic subgroup it generates. -/

open Finset

namespace GlobalTheory.EllipticCharacters

variable {G : Type*} [CommGroup G] [Finite G]

open Classical in
theorem card_eq_orderOf_mul_card_image_quotient
    (A : Finset G) (τ : G) (hA : ∀ x ∈ A, x * τ ∈ A) :
    #A = orderOf τ * #(A.image (QuotientGroup.mk' (Subgroup.zpowers τ))) := by
  let H := Subgroup.zpowers τ
  let q := QuotientGroup.mk' H
  have hmove (x : G) (hx : x ∈ A) (u : H) : x * (u : G) ∈ A := by
    obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr u.2)
    rw [← hm]
    clear hm u
    induction m with
    | zero => simpa using hx
    | succ m ih => simpa only [pow_succ, ← mul_assoc] using hA _ ih
  have hcard (y : G ⧸ H) (hy : y ∈ A.image q) :
      #(A.filter fun x => q x = y) = orderOf τ := by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    let j : H → {x // x ∈ A.filter (fun u => q u = q a)} := fun u => ⟨a * (u : G), by
      refine Finset.mem_filter.mpr ⟨hmove a ha u, ?_⟩
      rw [map_mul, show q (u : G) = 1 from (QuotientGroup.eq_one_iff _).mpr u.2, mul_one]⟩
    have hji : Function.Injective j := fun u v huv => Subtype.ext
      (mul_left_cancel (congrArg Subtype.val huv))
    have hjs : Function.Surjective j := by
      intro x
      have hx := (Finset.mem_filter.mp x.2).2
      have heu : q (a⁻¹ * (x : G)) = 1 := by rw [map_mul, map_inv, hx, inv_mul_cancel]
      refine ⟨⟨a⁻¹ * (x : G), (QuotientGroup.eq_one_iff _).mp heu⟩, Subtype.ext ?_⟩
      change a * (a⁻¹ * (x : G)) = x
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    letI : Fintype H := Fintype.ofFinite H
    calc
      #(A.filter fun x => q x = q a) = Fintype.card H := by
        rw [← Fintype.card_coe]
        exact (Fintype.card_congr (Equiv.ofBijective j ⟨hji, hjs⟩)).symm
      _ = orderOf τ := by rw [← Nat.card_eq_fintype_card, Nat.card_zpowers]
  calc
    #A = ∑ y ∈ A.image q, #(A.filter (fun x => q x = y)) := Finset.card_eq_sum_card_image q A
    _ = ∑ _y ∈ A.image q, orderOf τ := Finset.sum_congr rfl hcard
    _ = orderOf τ * #(A.image q) := by simp [Nat.mul_comm]

end GlobalTheory.EllipticCharacters
