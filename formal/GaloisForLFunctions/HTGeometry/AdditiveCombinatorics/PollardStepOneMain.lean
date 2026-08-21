import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardStabiliserBound

/-!
# STEP 1 of Grynkiewicz's proof

`pollard_step1`: if `A' ⊆ A`, `B' ⊆ B` satisfy `A' ·_t B' = A' · B' = A ·_t B` and the defect
`#(A \ A') + #(B \ B')` is at most `t − 1`, then either the stabiliser alternative
`PollardStruct` holds or `repSum A B t ≥ t#A + t#B − t²`.

The witnesses are the *saturations* `satur A A' B' = A' ∪ (A ∩ A'·H)` and its mirror image, which
have the same product set (`satur_mul_satur`), no larger defect (`defect_satur_le`), and are
saturated (`satur_saturated`).  The two branches are `pollard_step1_largeProduct` and
`pollard_step1_smallDoubling`.
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [DecidableEq G] [Fintype G]

theorem repSet_mono {A A' B B' : Finset G} (hA : A' ⊆ A) (hB : B' ⊆ B) (i : ℕ) :
    repSet A' B' i ⊆ repSet A B i := by
  intro g hg
  rw [mem_repSet] at hg ⊢
  exact le_trans hg (rep_mono hA hB g)

/-- **STEP 1, large-product branch.** -/
theorem pollard_step1_largeProduct (A B A' B' : Finset G) (t : ℕ)
    (hA' : A' ⊆ A) (hB' : B' ⊆ B)
    (hl : defect A A' B B' + 1 ≤ t)
    (heq2 : A' * B' = repSet A B t)
    (hlarge : A'.card + B'.card ≤ (A' * B').card + 1) :
    t * A.card + t * B.card ≤ repSum A B t + t ^ 2 := by
  have h1 : t * (repSet A B t).card ≤ repSum A B t := mul_card_repSet_le_repSum A B t
  rw [← heq2] at h1
  have hcardA := Finset.card_sdiff_add_card_eq_card hA'
  have hcardB := Finset.card_sdiff_add_card_eq_card hB'
  have h2 : t * (A'.card + B'.card) ≤ t * ((A' * B').card + 1) := Nat.mul_le_mul_left t hlarge
  have h3 : t * ((A' * B').card + 1) = t * (A' * B').card + t := by ring
  have h4 : t * A.card + t * B.card
      = t * (A'.card + B'.card) + t * defect A A' B B' := by
    rw [← hcardA, ← hcardB]
    simp only [defect]
    ring
  have h5 : t * (defect A A' B B' + 1) ≤ t * t := Nat.mul_le_mul_left t hl
  have h6 : t * (defect A A' B B' + 1) = t * defect A A' B B' + t := by ring
  have h7 : t * t = t ^ 2 := by ring
  omega

/-! ### Saturation -/

/-- The saturation of `A'` inside `A` relative to the stabiliser of `A' · B'`. -/
def satur (A A' B' : Finset G) : Finset G := A' ∪ (A ∩ (A' * mulStab (A' * B')))

theorem subset_satur (A A' B' : Finset G) : A' ⊆ satur A A' B' :=
  Finset.subset_union_left

theorem satur_subset {A A' B' : Finset G} (hA' : A' ⊆ A) : satur A A' B' ⊆ A := by
  exact Finset.union_subset hA' Finset.inter_subset_left

theorem satur_subset_mul (A A' B' : Finset G) :
    satur A A' B' ⊆ A' * mulStab (A' * B') := by
  refine Finset.union_subset ?_ Finset.inter_subset_right
  exact (isSubgroupFinset_mulStab (A' * B')).subset_mul A'

/-- Saturating both factors does not change the product set. -/
theorem satur_mul_satur (A A' B B' : Finset G) :
    satur A A' B' * satur B B' A' = A' * B' := by
  classical
  set H := mulStab (A' * B') with hHdef
  have hHgrp : IsSubgroupFinset H := isSubgroupFinset_mulStab (A' * B')
  have hBA : B' * A' = A' * B' := mul_comm B' A'
  have hsatB : satur B B' A' ⊆ B' * H := by
    have := satur_subset_mul B B' A'
    rw [hBA] at this
    exact this
  refine Subset.antisymm ?_ ?_
  · calc satur A A' B' * satur B B' A' ⊆ (A' * H) * (B' * H) :=
          mul_subset_mul (satur_subset_mul A A' B') hsatB
      _ = (A' * B') * (H * H) := mul_mul_mul_comm A' H B' H
      _ = (A' * B') * H := by rw [hHgrp.mul_self]
      _ = A' * B' := by rw [hHdef, mul_mulStab]
  · exact mul_subset_mul (subset_satur A A' B') (subset_satur B B' A')

theorem defect_satur_le (A A' B B' : Finset G) :
    defect A (satur A A' B') B (satur B B' A') ≤ defect A A' B B' := by
  rw [defect, defect]
  have h1 : (A \ satur A A' B').card ≤ (A \ A').card :=
    Finset.card_le_card (Finset.sdiff_subset_sdiff (Finset.Subset.refl A) (subset_satur A A' B'))
  have h2 : (B \ satur B B' A').card ≤ (B \ B').card :=
    Finset.card_le_card (Finset.sdiff_subset_sdiff (Finset.Subset.refl B) (subset_satur B B' A'))
  omega

/-- Saturation really is saturated. -/
theorem satur_saturated (A A' B B' : Finset G) :
    ∀ x ∈ A, x ∈ satur A A' B' * mulStab (satur A A' B' * satur B B' A') → x ∈ satur A A' B' := by
  classical
  intro x hx hmem
  rw [satur_mul_satur] at hmem
  set H := mulStab (A' * B') with hHdef
  have hHgrp : IsSubgroupFinset H := isSubgroupFinset_mulStab (A' * B')
  have hsub : satur A A' B' * H ⊆ A' * H := by
    calc satur A A' B' * H ⊆ (A' * H) * H := mul_subset_mul (satur_subset_mul A A' B') Subset.rfl
      _ = A' * (H * H) := mul_assoc A' H H
      _ = A' * H := by rw [hHgrp.mul_self]
  exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hx, hsub hmem⟩)


/-- **STEP 1 of Grynkiewicz's proof.**  If `A' · B'` is the set of `t`-representable products and
the defect is less than `t`, then either the full stabiliser bound holds (with saturated witnesses)
or `repSum ≥ t#A + t#B − t²`. -/
theorem pollard_step1 (A B A' B' : Finset G) (t : ℕ) (ht : 1 ≤ t)
    (hA' : A' ⊆ A) (hB' : B' ⊆ B) (hA'ne : A'.Nonempty) (hB'ne : B'.Nonempty)
    (hl : defect A A' B B' + 1 ≤ t)
    (heq1 : repSet A' B' t = A' * B') (heq2 : A' * B' = repSet A B t) :
    PollardStruct A B t ∨ (t * A.card + t * B.card ≤ repSum A B t + t ^ 2) := by
  classical
  set A'' := satur A A' B' with hA''def
  set B'' := satur B B' A' with hB''def
  have hprod : A'' * B'' = A' * B' := satur_mul_satur A A' B B'
  have hA''sub : A'' ⊆ A := satur_subset hA'
  have hB''sub : B'' ⊆ B := satur_subset hB'
  have hA''ne : A''.Nonempty := hA'ne.mono (subset_satur A A' B')
  have hB''ne : B''.Nonempty := hB'ne.mono (subset_satur B B' A')
  have hdef'' : defect A A'' B B'' + 1 ≤ t := by
    have hle := defect_satur_le A A' B B'
    rw [← hA''def, ← hB''def] at hle
    omega
  have heq2'' : A'' * B'' = repSet A B t := by rw [hprod, heq2]
  have heq1'' : repSet A'' B'' t = A'' * B'' := by
    refine Subset.antisymm (repSet_subset_mul A'' B'' ht) ?_
    rw [hprod, ← heq1]
    exact repSet_mono (subset_satur A A' B') (subset_satur B B' A') t
  have hsatA : ∀ x ∈ A, x ∈ A'' * mulStab (A'' * B'') → x ∈ A'' := satur_saturated A A' B B'
  have hsatB : ∀ y ∈ B, y ∈ B'' * mulStab (A'' * B'') → y ∈ B'' := by
    have h := satur_saturated B B' A A'
    intro y hy hmem
    apply h y hy
    have hcomm : satur B B' A' * satur A A' B' = A'' * B'' := by
      rw [hA''def, hB''def, mul_comm]
    rw [hcomm]
    exact hmem
  rcases le_or_gt (A''.card + B''.card) ((A'' * B'').card + 1) with hlarge | hsmall
  · exact Or.inr (pollard_step1_largeProduct A B A'' B'' t hA''sub hB''sub hdef'' heq2'' hlarge)
  · left
    refine ⟨A'', B'', hA''sub, hB''sub, hdef'', heq1'', heq2'', ?_⟩
    have hmain := pollard_step1_smallDoubling A B A'' B'' t hA''sub hB''sub hA''ne hB''ne
      hdef'' heq2'' (by omega) hsatA hsatB
    rw [← heq2'']
    exact hmain

end GaloisForLFunctions.HTGeometry.AddComb
