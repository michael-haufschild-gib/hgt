import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.Kneser
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Cosets, index, and the structure of sets with small doubling

`indexF H` is the index of a subgroup finset `H` of a finite commutative group, and
`card_mul_eq_card_image_mul` computes `#(t * H)` as the number of cosets of `H` met by `t` times
`#H`.

`small_doubling_index` is the consequence of Kneser's theorem used in Matomäki--Teräväinen,
*Linnik's problem for multiplicative functions* (arXiv:2605.27833), Lemma 3.13: if `A` and `B` have
density at least `α` and meet at least proportion `α'` of the cosets of every subgroup of index
below `1/(2α − β)`, then either `#(A · B) ≥ β·#G` or the stabiliser of `A · B` has index strictly
between `1` and `1/(2α' − β)`.
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] {H : Finset G}

omit [Fintype G] in
/-- `#(t * H)` is the number of cosets of `H` met by `t`, times `#H`. -/
theorem card_mul_eq_card_image_mul (h : IsSubgroupFinset H) (t : Finset G) :
    (t * H).card = (t.image (fun x => x • H)).card * H.card := by
  classical
  set S : Finset (Finset G) := t.image (fun x => x • H) with hSdef
  have hcover : S.biUnion id = t * H := by
    ext z
    simp only [hSdef, mem_biUnion, mem_image, id]
    constructor
    · rintro ⟨u, ⟨x, hx, rfl⟩, hz⟩
      rw [mem_smul_finset] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact mul_mem_mul hx hw
    · intro hz
      rw [mem_mul] at hz
      obtain ⟨x, hx, w, hw, rfl⟩ := hz
      exact ⟨x • H, ⟨x, hx, rfl⟩, mem_smul_finset.2 ⟨w, hw, rfl⟩⟩
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

/-- The index of a subgroup finset. -/
def indexF (H : Finset G) : ℕ := ((univ : Finset G).image (fun x => x • H)).card

theorem univ_mul_eq (h : IsSubgroupFinset H) : (univ : Finset G) * H = univ := by
  apply Finset.eq_univ_of_forall
  intro x
  rw [mem_mul]
  exact ⟨x, Finset.mem_univ x, 1, h.one_mem, mul_one x⟩

theorem indexF_mul_card (h : IsSubgroupFinset H) : indexF H * H.card = Fintype.card G := by
  have hm := card_mul_eq_card_image_mul h (univ : Finset G)
  rw [univ_mul_eq h, Finset.card_univ] at hm
  exact hm.symm

theorem indexF_pos (h : IsSubgroupFinset H) : 0 < indexF H := by
  have := indexF_mul_card h
  have hG : 0 < Fintype.card G := Fintype.card_pos
  rcases Nat.eq_zero_or_pos (indexF H) with h0 | hp
  · rw [h0] at this; omega
  · exact hp

/-- **Small doubling forces a small-index stabiliser.**  (Matomäki--Teräväinen, Lemma 3.13.) -/
theorem small_doubling_index {A B : Finset G} {α α' β : ℝ}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hβ1 : β ≤ 1) (hβα : β < 2 * α) (hαα' : α ≤ α')
    (hA : α * (Fintype.card G : ℝ) ≤ (A.card : ℝ))
    (hB : α * (Fintype.card G : ℝ) ≤ (B.card : ℝ))
    (hmeet : ∀ H₀ : Finset G, IsSubgroupFinset H₀ → ((indexF H₀ : ℝ) < 1 / (2 * α - β)) →
       α' * (indexF H₀ : ℝ) ≤ (((A.image (fun x => x • H₀)).card : ℝ)) ∧
       α' * (indexF H₀ : ℝ) ≤ (((B.image (fun x => x • H₀)).card : ℝ))) :
    β * (Fintype.card G : ℝ) ≤ ((A * B).card : ℝ)
    ∨ (1 < indexF (mulStab (A * B)) ∧
        (indexF (mulStab (A * B)) : ℝ) < 1 / (2 * α' - β)) := by
  classical
  set H := mulStab (A * B) with hHdef
  have hHgrp : IsSubgroupFinset H := isSubgroupFinset_mulStab (A * B)
  have hYH : (indexF H : ℝ) * (H.card : ℝ) = (Fintype.card G : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (indexF_mul_card hHgrp)
  have hNpos : (0 : ℝ) < (Fintype.card G : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := G)
  have hYpos : (0 : ℝ) < (indexF H : ℝ) := by
    exact_mod_cast indexF_pos hHgrp
  have hHpos : (0 : ℝ) < (H.card : ℝ) := by
    exact_mod_cast hHgrp.card_pos'
  have hab : 0 < 2 * α - β := by linarith
  have hab' : 0 < 2 * α' - β := by linarith
  by_cases hY1 : indexF H = 1
  · -- the stabiliser is everything, so `A * B` is the whole group
    left
    have hHcard : (H.card : ℝ) = (Fintype.card G : ℝ) := by
      rw [hY1] at hYH; simpa using hYH
    have hHuniv : H = univ := by
      apply Finset.eq_univ_of_card
      exact_mod_cast hHcard
    have hABuniv : A * B = univ := by
      have := mul_mulStab (A * B)
      rw [← hHdef, hHuniv] at this
      rw [← this]
      obtain ⟨x, hx⟩ := hAne
      obtain ⟨y, hy⟩ := hBne
      apply Finset.eq_univ_of_forall
      intro z
      rw [mem_mul]
      exact ⟨x * y, mul_mem_mul hx hy, (x * y)⁻¹ * z, Finset.mem_univ _, by group⟩
    rw [hABuniv, Finset.card_univ]
    nlinarith
  · have hY2 : (2 : ℝ) ≤ (indexF H : ℝ) := by
      have : 1 ≤ indexF H := indexF_pos hHgrp
      have : 2 ≤ indexF H := by omega
      exact_mod_cast this
    by_cases hbig : β * (Fintype.card G : ℝ) ≤ ((A * B).card : ℝ)
    · exact Or.inl hbig
    push Not at hbig
    -- weak Kneser gives a first bound on the index
    have hkw : (A.card : ℝ) + (B.card : ℝ) ≤ ((A * B).card : ℝ) + (H.card : ℝ) := by
      exact_mod_cast card_add_card_le_card_mul_add_card_mulStab A B hAne hBne
    have hHval : (H.card : ℝ) = (Fintype.card G : ℝ) / (indexF H : ℝ) := by
      field_simp at hYH ⊢
      linarith [hYH]
    have hstep1 : (indexF H : ℝ) < 1 / (2 * α - β) := by
      rw [hHval] at hkw
      have h2 : 2 * α * (Fintype.card G : ℝ)
          ≤ ((A * B).card : ℝ) + (Fintype.card G : ℝ) / (indexF H : ℝ) := by linarith
      have h3 : (2 * α - β) * (Fintype.card G : ℝ)
          < (Fintype.card G : ℝ) / (indexF H : ℝ) := by linarith
      have h3' : (2 * α - β) * (Fintype.card G : ℝ)
          < (indexF H : ℝ)⁻¹ * (Fintype.card G : ℝ) := by
        rw [div_eq_mul_inv, mul_comm ((Fintype.card G : ℝ))] at h3
        linarith
      have h4 : (2 * α - β) < (indexF H : ℝ)⁻¹ :=
        lt_of_mul_lt_mul_right h3' (le_of_lt hNpos)
      rw [lt_div_iff₀ hab]
      have h5 := mul_lt_mul_of_pos_left h4 hYpos
      rw [mul_inv_cancel₀ (ne_of_gt hYpos)] at h5
      linarith
    obtain ⟨hmA, hmB⟩ := hmeet H hHgrp hstep1
    -- full Kneser with the coset counts
    have hkf : ((A * H).card : ℝ) + ((B * H).card : ℝ)
        ≤ ((A * B).card : ℝ) + (H.card : ℝ) := by
      exact_mod_cast card_mul_le_card_mul_mulStab A B hAne hBne
    have hAH : α' * (Fintype.card G : ℝ) ≤ ((A * H).card : ℝ) := by
      have h1 : ((A * H).card : ℝ)
          = ((A.image (fun x => x • H)).card : ℝ) * (H.card : ℝ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (card_mul_eq_card_image_mul hHgrp A)
      rw [h1, ← hYH]
      have := mul_le_mul_of_nonneg_right hmA (le_of_lt hHpos)
      linarith [this]
    have hBH : α' * (Fintype.card G : ℝ) ≤ ((B * H).card : ℝ) := by
      have h1 : ((B * H).card : ℝ)
          = ((B.image (fun x => x • H)).card : ℝ) * (H.card : ℝ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (card_mul_eq_card_image_mul hHgrp B)
      rw [h1, ← hYH]
      have := mul_le_mul_of_nonneg_right hmB (le_of_lt hHpos)
      linarith [this]
    right
    have hYnat : 1 < indexF H := by
      have := indexF_pos hHgrp
      omega
    refine ⟨hYnat, ?_⟩
    have h2 : 2 * α' * (Fintype.card G : ℝ)
        ≤ ((A * B).card : ℝ) + (Fintype.card G : ℝ) / (indexF H : ℝ) := by
      rw [hHval] at hkf; linarith
    have h3 : (2 * α' - β) * (Fintype.card G : ℝ)
        < (Fintype.card G : ℝ) / (indexF H : ℝ) := by linarith
    have h3' : (2 * α' - β) * (Fintype.card G : ℝ)
        < (indexF H : ℝ)⁻¹ * (Fintype.card G : ℝ) := by
      rw [div_eq_mul_inv, mul_comm ((Fintype.card G : ℝ))] at h3
      linarith
    have h4 : (2 * α' - β) < (indexF H : ℝ)⁻¹ :=
      lt_of_mul_lt_mul_right h3' (le_of_lt hNpos)
    rw [lt_div_iff₀ hab']
    have h5 := mul_lt_mul_of_pos_left h4 hYpos
    rw [mul_inv_cancel₀ (ne_of_gt hYpos)] at h5
    linarith

end GaloisForLFunctions.HTGeometry.AddComb
