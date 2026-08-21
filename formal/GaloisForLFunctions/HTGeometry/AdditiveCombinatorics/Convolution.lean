import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.Kneser
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Convolutions of indicator functions on a finite commutative group

`rep A B c` counts the representations `c = x * y` with `x ∈ A`, `y ∈ B`; it is the convolution
`(𝟙_A ∗ 𝟙_B)(c)`.  `rep3 A B C a` is the triple convolution.

The two lower bounds proved here are Lemma 3.10 of Matomäki--Teräväinen, *Linnik's problem for
multiplicative functions* (arXiv:2605.27833) — equivalently Lemma 3.4 of their *Products of primes
in arithmetic progressions* (arXiv:2301.07679):

* `card_add_card_le_rep_add_card` — `#A + #B ≤ (𝟙_A ∗ 𝟙_B)(c) + #G`;
* `card_add_card_le_rep_add_card_coset` — the same with `#G` replaced by `#H` when `A`, `B` lie in
  cosets of a subgroup `H` and `c` lies in the product coset.
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [DecidableEq G]

/-- The number of representations of `c` as a product `x * y` with `x ∈ A` and `y ∈ B`.
This is the convolution `(𝟙_A ∗ 𝟙_B)(c)` of the indicator functions. -/
def rep (A B : Finset G) (c : G) : ℕ := ((A ×ˢ B).filter (fun p => p.1 * p.2 = c)).card

theorem rep_eq_card_inter (A B : Finset G) (c : G) : rep A B c = (A ∩ (c • B⁻¹)).card := by
  classical
  rw [rep]
  apply Finset.card_nbij (fun p => p.1)
  · rintro ⟨x, y⟩ hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product] at hp
    obtain ⟨⟨hx, hy⟩, hxy⟩ := hp
    simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe]
    refine ⟨hx, ?_⟩
    rw [Finset.mem_smul_finset]
    exact ⟨y⁻¹, Finset.inv_mem_inv hy, by rw [smul_eq_mul, ← hxy]; group⟩
  · rintro ⟨x, y⟩ hp ⟨x', y'⟩ hp' h
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product] at hp hp'
    simp only at h
    subst h
    have : y = y' := by
      have := hp.2.trans hp'.2.symm
      exact mul_left_cancel this
    simp [this]
  · intro x hx
    simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe] at hx
    obtain ⟨hxA, hxS⟩ := hx
    rw [Finset.mem_smul_finset] at hxS
    obtain ⟨z, hz, hzx⟩ := hxS
    rw [Finset.mem_inv'] at hz
    refine ⟨(x, z⁻¹), ?_, rfl⟩
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product]
    refine ⟨⟨hxA, hz⟩, ?_⟩
    simp only [smul_eq_mul] at hzx
    rw [← hzx]
    group

omit [CommGroup G] in
/-- Any two subsets of a common ambient set intersect in at least the excess of their sizes. -/
theorem card_add_card_le_card_add_card_inter {U A S : Finset G} (hA : A ⊆ U) (hS : S ⊆ U) :
    A.card + S.card ≤ U.card + (A ∩ S).card := by
  have h := Finset.card_union_add_card_inter A S
  have h2 : (A ∪ S).card ≤ U.card := Finset.card_le_card (Finset.union_subset hA hS)
  omega

/-- **Convolution lower bound, ambient form.**  (Matomäki--Teräväinen, Lemma 3.10(i).) -/
theorem card_add_card_le_rep_add_card [Fintype G] (A B : Finset G) (c : G) :
    A.card + B.card ≤ rep A B c + Fintype.card G := by
  rw [rep_eq_card_inter]
  have hcard : (c • B⁻¹).card = B.card := by
    rw [Finset.card_smul_finset, Finset.card_inv]
  have h := card_add_card_le_card_add_card_inter (U := (univ : Finset G))
    (Finset.subset_univ A) (Finset.subset_univ (c • B⁻¹))
  rw [Finset.card_univ] at h
  omega

/-- **Convolution lower bound, coset form.**  (Matomäki--Teräväinen, Lemma 3.10(ii).) -/
theorem card_add_card_le_rep_add_card_coset {H A B : Finset G} {a b c : G}
    (hH : IsSubgroupFinset H) (hA : A ⊆ a • H) (hB : B ⊆ b • H) (hc : c ∈ (a * b) • H) :
    A.card + B.card ≤ rep A B c + H.card := by
  rw [rep_eq_card_inter]
  have hinvH : H⁻¹ = H := by
    ext x
    simp only [Finset.mem_inv']
    exact ⟨fun h => by simpa using hH.inv_mem h, fun h => by simpa using hH.inv_mem h⟩
  have hBinv : B⁻¹ ⊆ b⁻¹ • H := by
    intro x hx
    rw [Finset.mem_inv'] at hx
    have := hB hx
    rw [Finset.mem_smul_finset] at this ⊢
    obtain ⟨h, hh, hbh⟩ := this
    refine ⟨h⁻¹, hH.inv_mem hh, ?_⟩
    simp only [smul_eq_mul] at hbh ⊢
    have hxe : (b * h)⁻¹ = x := by rw [hbh, inv_inv]
    rw [← hxe, mul_inv_rev]
    exact mul_comm _ _
  have hS : c • B⁻¹ ⊆ a • H := by
    have hcb : c * b⁻¹ ∈ a • H := by
      rw [Finset.mem_smul_finset] at hc ⊢
      obtain ⟨h, hh, hch⟩ := hc
      refine ⟨h, hh, ?_⟩
      simp only [smul_eq_mul] at hch ⊢
      have key : a * h * b = c := by
        rw [← hch, mul_assoc, mul_assoc, mul_comm h b]
      exact eq_mul_inv_iff_mul_eq.2 key
    have hcbH : (c * b⁻¹) • H = a • H := hH.smul_eq_smul_of_mem hcb
    intro x hx
    rw [Finset.mem_smul_finset] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    have hy' := hBinv hy
    rw [Finset.mem_smul_finset] at hy'
    obtain ⟨h, hh, hbh⟩ := hy'
    rw [← hcbH, Finset.mem_smul_finset]
    refine ⟨h, hh, ?_⟩
    simp only [smul_eq_mul] at hxy hbh ⊢
    rw [← hxy, ← hbh, mul_assoc]
  have hcard : (c • B⁻¹).card = B.card := by
    rw [Finset.card_smul_finset, Finset.card_inv]
  have hcardaH : (a • H).card = H.card := Finset.card_smul_finset _ _
  have h := card_add_card_le_card_add_card_inter (U := a • H) hA hS
  omega


theorem rep_eq_card_filter_right (A B : Finset G) (c : G) :
    rep A B c = (B.filter (fun y => c * y⁻¹ ∈ A)).card := by
  classical
  rw [rep]
  apply Finset.card_nbij (fun p => p.2)
  · rintro ⟨x, y⟩ hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product] at hp
    obtain ⟨⟨hx, hy⟩, hxy⟩ := hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq]
    refine ⟨hy, ?_⟩
    have : c * y⁻¹ = x := by rw [← hxy, mul_inv_cancel_right]
    rw [this]; exact hx
  · rintro ⟨x, y⟩ hp ⟨x', y'⟩ hp' h
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product] at hp hp'
    simp only at h
    subst h
    have : x = x' := mul_right_cancel (hp.2.trans hp'.2.symm)
    simp [this]
  · intro y hy
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hy
    refine ⟨(c * y⁻¹, y), ?_, rfl⟩
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product]
    exact ⟨⟨hy.2, hy.1⟩, by rw [inv_mul_cancel_right]⟩

theorem rep_mono {A A' B B' : Finset G} (hA : A ⊆ A') (hB : B ⊆ B') (c : G) :
    rep A B c ≤ rep A' B' c := by
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
  exact ⟨⟨hA hp.1.1, hB hp.1.2⟩, hp.2⟩

/-- The triple convolution `(𝟙_A ∗ 𝟙_B ∗ 𝟙_C)(a)`. -/
def rep3 (A B C : Finset G) (a : G) : ℕ := ∑ z ∈ C, rep A B (a * z⁻¹)

theorem rep3_mono {A A' B B' C C' : Finset G} (hA : A ⊆ A') (hB : B ⊆ B') (hC : C ⊆ C') (a : G) :
    rep3 A B C a ≤ rep3 A' B' C' a := by
  refine le_trans (Finset.sum_le_sum (fun z _ => rep_mono hA hB _)) ?_
  exact Finset.sum_le_sum_of_subset hC

/-- If `𝟙_A ∗ 𝟙_B` is at least `u` on a set `T`, then the triple convolution with `C` dominates
`u` times the convolution of `𝟙_T` with `𝟙_C`. -/
theorem rep3_ge_of_le_on {A B C T : Finset G} {u : ℕ}
    (hT : ∀ c ∈ T, u ≤ rep A B c) (a : G) :
    u * rep T C a ≤ rep3 A B C a := by
  classical
  have hfilter : rep T C a = (C.filter (fun z => a * z⁻¹ ∈ T)).card :=
    rep_eq_card_filter_right T C a
  rw [rep3, hfilter]
  calc u * (C.filter (fun z => a * z⁻¹ ∈ T)).card
      = ∑ _z ∈ C.filter (fun z => a * z⁻¹ ∈ T), u := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ z ∈ C.filter (fun z => a * z⁻¹ ∈ T), rep A B (a * z⁻¹) := by
        refine Finset.sum_le_sum (fun z hz => ?_)
        rw [Finset.mem_filter] at hz
        exact hT _ hz.2
    _ ≤ ∑ z ∈ C, rep A B (a * z⁻¹) :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

end GaloisForLFunctions.HTGeometry.AddComb
