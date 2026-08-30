import GaloisForLFunctions.HTGeometry.JohnsonGraphConnected

/-!
# Transitivity on pairs of subsets with a fixed intersection size

Two ordered pairs of `m`-subsets meeting in the same number of points are carried to each other by a
permutation of the ambient set: the four blocks `S ∩ T`, `S \ T`, `T \ S` and the complement of
`S ∪ T` have matching sizes, and a permutation is glued from bijections of the blocks.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- A permutation matching two maps with equal fibre cardinalities. -/
noncomputable def permOfFiberCardEq {β : Type*} [DecidableEq β] (φ ψ : α → β)
    (h : ∀ b : β, Fintype.card {x : α // φ x = b} = Fintype.card {x : α // ψ x = b}) :
    Equiv.Perm α :=
  (Equiv.sigmaFiberEquiv φ).symm.trans
    ((Equiv.sigmaCongrRight fun b => Fintype.equivOfCardEq (h b)).trans (Equiv.sigmaFiberEquiv ψ))

omit [DecidableEq α] in
theorem permOfFiberCardEq_spec {β : Type*} [DecidableEq β] (φ ψ : α → β)
    (h : ∀ b : β, Fintype.card {x : α // φ x = b} = Fintype.card {x : α // ψ x = b}) (x : α) :
    ψ (permOfFiberCardEq φ ψ h x) = φ x := by
  show ψ ((Fintype.equivOfCardEq (h (φ x))) ⟨x, rfl⟩ : {y : α // ψ y = φ x}).1 = φ x
  exact ((Fintype.equivOfCardEq (h (φ x))) ⟨x, rfl⟩).2

/-- The four-block index of an ordered pair of subsets. -/
def blockIndex (S T : Finset α) (x : α) : Fin 4 :=
  if x ∈ S then (if x ∈ T then 0 else 1) else (if x ∈ T then 2 else 3)

theorem card_fiber_blockIndex (S T : Finset α) (b : Fin 4) :
    Fintype.card {x : α // blockIndex S T x = b}
      = (Finset.univ.filter fun x => blockIndex S T x = b).card := by
  rw [Fintype.card_subtype]

theorem filter_blockIndex_zero (S T : Finset α) :
    (Finset.univ.filter fun x => blockIndex S T x = 0) = S ∩ T := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter, blockIndex]
  by_cases hS : x ∈ S <;> by_cases hT : x ∈ T <;> simp [hS, hT]

theorem filter_blockIndex_one (S T : Finset α) :
    (Finset.univ.filter fun x => blockIndex S T x = 1) = S \ T := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, blockIndex]
  by_cases hS : x ∈ S <;> by_cases hT : x ∈ T <;> simp [hS, hT]

theorem filter_blockIndex_two (S T : Finset α) :
    (Finset.univ.filter fun x => blockIndex S T x = 2) = T \ S := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, blockIndex]
  by_cases hS : x ∈ S <;> by_cases hT : x ∈ T <;> simp [hS, hT]

theorem filter_blockIndex_three (S T : Finset α) :
    (Finset.univ.filter fun x => blockIndex S T x = 3) = Finset.univ \ (S ∪ T) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, Finset.mem_union,
    blockIndex]
  by_cases hS : x ∈ S <;> by_cases hT : x ∈ T <;> simp [hS, hT]

omit [Fintype α] in
theorem card_union_of_card_inter {m j : ℕ} {S T : Finset α} (hS : S.card = m) (hT : T.card = m)
    (hint : (S ∩ T).card = j) : (S ∪ T).card = m + m - j := by
  have h := Finset.card_union_add_card_inter S T
  rw [hint, hS, hT] at h
  omega


omit [Fintype α] in
theorem mem_left_iff_blockIndex {S T : Finset α} (x : α) :
    x ∈ S ↔ (blockIndex S T x = 0 ∨ blockIndex S T x = 1) := by
  unfold blockIndex
  by_cases hS : x ∈ S <;> by_cases hT : x ∈ T <;> simp [hS, hT]

omit [Fintype α] in
theorem mem_right_iff_blockIndex {S T : Finset α} (x : α) :
    x ∈ T ↔ (blockIndex S T x = 0 ∨ blockIndex S T x = 2) := by
  unfold blockIndex
  by_cases hS : x ∈ S <;> by_cases hT : x ∈ T <;> simp [hS, hT]

/-- **Transitivity on ordered pairs of subsets with a fixed intersection size.** -/
theorem exists_perm_image_pair {m j : ℕ} {S T S' T' : Finset α}
    (hS : S.card = m) (hT : T.card = m) (hint : (S ∩ T).card = j)
    (hS' : S'.card = m) (hT' : T'.card = m) (hint' : (S' ∩ T').card = j) :
    ∃ σ : Equiv.Perm α, S.image σ = S' ∧ T.image σ = T' := by
  classical
  have hfib : ∀ b : Fin 4, Fintype.card {x : α // blockIndex S T x = b}
      = Fintype.card {x : α // blockIndex S' T' x = b} := by
    intro b
    rw [card_fiber_blockIndex, card_fiber_blockIndex]
    fin_cases b
    · show (Finset.univ.filter fun x => blockIndex S T x = (0 : Fin 4)).card
        = (Finset.univ.filter fun x => blockIndex S' T' x = (0 : Fin 4)).card
      rw [filter_blockIndex_zero, filter_blockIndex_zero, hint, hint']
    · show (Finset.univ.filter fun x => blockIndex S T x = (1 : Fin 4)).card
        = (Finset.univ.filter fun x => blockIndex S' T' x = (1 : Fin 4)).card
      rw [filter_blockIndex_one, filter_blockIndex_one, Finset.card_sdiff, Finset.card_sdiff,
        Finset.inter_comm T S, Finset.inter_comm T' S', hint, hint', hS, hS']
    · show (Finset.univ.filter fun x => blockIndex S T x = (2 : Fin 4)).card
        = (Finset.univ.filter fun x => blockIndex S' T' x = (2 : Fin 4)).card
      rw [filter_blockIndex_two, filter_blockIndex_two, Finset.card_sdiff, Finset.card_sdiff,
        hint, hint', hT, hT']
    · show (Finset.univ.filter fun x => blockIndex S T x = (3 : Fin 4)).card
        = (Finset.univ.filter fun x => blockIndex S' T' x = (3 : Fin 4)).card
      rw [filter_blockIndex_three, filter_blockIndex_three, Finset.card_sdiff, Finset.card_sdiff,
        Finset.inter_eq_left.2 (Finset.subset_univ _), Finset.inter_eq_left.2 (Finset.subset_univ _),
        card_union_of_card_inter hS hT hint, card_union_of_card_inter hS' hT' hint']
  refine ⟨permOfFiberCardEq (blockIndex S T) (blockIndex S' T') hfib, ?_, ?_⟩
  · set σ := permOfFiberCardEq (blockIndex S T) (blockIndex S' T') hfib with hσ
    have hspec : ∀ x, blockIndex S' T' (σ x) = blockIndex S T x :=
      permOfFiberCardEq_spec (blockIndex S T) (blockIndex S' T') hfib
    have himg : ∀ x, (σ x ∈ S' ↔ x ∈ S) := by
      intro x
      rw [mem_left_iff_blockIndex (S := S') (T := T'), hspec x, ← mem_left_iff_blockIndex]
    ext y
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (himg x).2 hx
    · intro hy
      exact ⟨σ.symm y, (himg (σ.symm y)).1 (by rwa [Equiv.apply_symm_apply]), by simp⟩
  · set σ := permOfFiberCardEq (blockIndex S T) (blockIndex S' T') hfib with hσ
    have hspec : ∀ x, blockIndex S' T' (σ x) = blockIndex S T x :=
      permOfFiberCardEq_spec (blockIndex S T) (blockIndex S' T') hfib
    have himg : ∀ x, (σ x ∈ T' ↔ x ∈ T) := by
      intro x
      rw [mem_right_iff_blockIndex (S := S') (T := T'), hspec x, ← mem_right_iff_blockIndex]
    ext y
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (himg x).2 hx
    · intro hy
      exact ⟨σ.symm y, (himg (σ.symm y)).1 (by rwa [Equiv.apply_symm_apply]), by simp⟩


/-- The permutation of `m`-subsets induced by a permutation of the ambient set. -/
def cardImagePerm (m : ℕ) (σ : Equiv.Perm α) : Equiv.Perm {s : Finset α // s.card = m} where
  toFun s := ⟨s.1.image σ, by rw [Finset.card_image_of_injective _ σ.injective, s.2]⟩
  invFun s := ⟨s.1.image σ.symm, by rw [Finset.card_image_of_injective _ σ.symm.injective, s.2]⟩
  left_inv s := by
    refine Subtype.ext ?_
    simp [Finset.image_image]
  right_inv s := by
    refine Subtype.ext ?_
    simp [Finset.image_image]

omit [Fintype α] in
theorem cardImagePerm_swap (m : ℕ) (σ : Equiv.Perm α)
    (S T : {s : Finset α // s.card = m}) :
    Equiv.swap (cardImagePerm m σ S) (cardImagePerm m σ T)
      = cardImagePerm m σ * Equiv.swap S T * (cardImagePerm m σ)⁻¹ :=
  Equiv.swap_apply_apply _ _ _

/-- **A group of permutations of `m`-subsets containing the induced action of the ambient
symmetric group and one fixed-intersection transposition is everything.**  This closes the
balanced case, where the induced action alone is imprimitive. -/
theorem eq_top_of_rootAction_of_swap {m j : ℕ} (hj : j < m) (hbig : 2 * m ≤ Fintype.card α)
    (hne : j ≠ 0 ∨ 2 * m ≠ Fintype.card α)
    {G : Subgroup (Equiv.Perm {s : Finset α // s.card = m})}
    (hroot : ∀ σ : Equiv.Perm α, cardImagePerm m σ ∈ G)
    {S₀ T₀ : {s : Finset α // s.card = m}} (hj₀ : (S₀.1 ∩ T₀.1).card = j)
    (hsw : Equiv.swap S₀ T₀ ∈ G) : G = ⊤ := by
  refine eq_top_of_johnsonSwaps hj hbig hne fun S T hST => ?_
  obtain ⟨σ, hσS, hσT⟩ := exists_perm_image_pair S₀.2 T₀.2 hj₀ S.2 T.2 hST
  have h1 : cardImagePerm m σ S₀ = S := Subtype.ext hσS
  have h2 : cardImagePerm m σ T₀ = T := Subtype.ext hσT
  rw [← h1, ← h2, cardImagePerm_swap]
  exact G.mul_mem (G.mul_mem (hroot σ) hsw) (G.inv_mem (hroot σ))

end GaloisForLFunctions.HTGeometry
