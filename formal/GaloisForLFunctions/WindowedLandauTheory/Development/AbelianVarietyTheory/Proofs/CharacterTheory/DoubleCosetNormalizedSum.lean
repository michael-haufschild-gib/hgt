import GaloisForLFunctions.RHTower.Artin.ArtinLocalEulerPolynomialOfAnInducedCharacter
import Mathlib.GroupTheory.DoubleCoset

/-! A sum over a finite group with subgroup-intersection weights
reduces to a sum over double cosets. -/

noncomputable section
open scoped Classical

namespace GaloisForLFunctions

variable {G : Type*} [Group G] [Fintype G] (H K : Subgroup G)

/-- The elements of the left subgroup whose conjugates lie in the right subgroup. -/
abbrev doubleCosetOverlap (x : G) : Subgroup H :=
  (K.map (MulAut.conj x).toMonoidHom).subgroupOf H

omit [Fintype G] in
theorem mem_doubleCosetOverlap (x : G) (u : H) :
    u ∈ doubleCosetOverlap H K x ↔ x⁻¹ * u.val * x ∈ K := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

/-- The quotient by two subgroups is finite because it is an image of the group. -/
abbrev mixedDoubleCosetFintype : Fintype (DoubleCoset.Quotient (H : Set G) K) :=
  Fintype.ofSurjective (DoubleCoset.mk H K) fun q => ⟨q.out, DoubleCoset.out_eq' H K q⟩

/-- On each double coset the sum of the overlap cardinalities is the product of the subgroup orders. -/
theorem sum_card_overlap_in_fibre (q : DoubleCoset.Quotient (H : Set G) K) :
    (∑ x : G, if DoubleCoset.mk H K x = q then (Nat.card (doubleCosetOverlap H K x) : ℂ) else 0) =
      (Nat.card H : ℂ) * Nat.card K := by
  rw [← Nat.cast_mul, ← sum_card_decomposition_doubleCoset H K q.out, Nat.cast_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Nat.cast_ite, Nat.cast_zero]
  refine if_congr ?_ rfl rfl
  have hq := DoubleCoset.out_eq' H K q
  exact ⟨fun h => (DoubleCoset.eq H K _ _).mp (hq.trans h.symm),
    fun h => ((DoubleCoset.eq H K _ _).mpr h).symm.trans hq⟩

/-- Double-coset sums use the overlap size to compensate for the size of the fibre. -/
theorem sum_over_doubleCosets (f : DoubleCoset.Quotient (H : Set G) K → ℂ) :
    letI := mixedDoubleCosetFintype H K
    (Nat.card H : ℂ)⁻¹ * ((Nat.card K : ℂ)⁻¹ *
      ∑ x : G, (Nat.card (doubleCosetOverlap H K x) : ℂ) * f (DoubleCoset.mk H K x)) =
      ∑ q, f q := by
  let Q := DoubleCoset.Quotient (H : Set G) K
  letI : Fintype Q := mixedDoubleCosetFintype H K
  let p := DoubleCoset.mk H K
  let w (x : G) : ℂ := Nat.card (doubleCosetOverlap H K x)
  let h : ℂ := Nat.card H
  let k : ℂ := Nat.card K
  have hne : h ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have kne : k ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hF (x : G) : w x * f (p x) = ∑ q : Q, if p x = q then w x * f q else 0 := by
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  have hsum (q : Q) : (∑ x : G, if p x = q then w x * f q else 0) = h * k * f q := by
    rw [← sum_card_overlap_in_fibre H K q, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs
    · rfl
    · exact (zero_mul (f q)).symm
  change h⁻¹ * (k⁻¹ * ∑ x : G, w x * f (p x)) = _
  simp_rw [hF]
  rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hsum q]
  calc
    h⁻¹ * (k⁻¹ * (h * k * f q)) = (h⁻¹ * h) * (k⁻¹ * k) * f q := by ring
    _ = _ := by rw [inv_mul_cancel₀ hne, inv_mul_cancel₀ kne, one_mul, one_mul]

end GaloisForLFunctions
