import GaloisForLFunctions.HTGeometry.LinearAlgebra.AlternatingSchur
import Mathlib.Data.Fintype.Option

/-!
# Binary completion along a prescribed matching

An alternating matrix on paired coordinates can be made nonsingular by
adding a standard alternating pair, or adding zero, independently along
each matched pair. The proof eliminates one pair at a time using Schur
complements; it works over arbitrary fields, including characteristic two.
-/

namespace GaloisForLFunctions.HTGeometry.LinearAlgebra

open Matrix
open scoped Classical

variable {F ι κ : Type*} [Field F]

/-- Independent alternating perturbations on the matched coordinate pairs. -/
def matchingPerturbation [DecidableEq ι] (ε : ι → F) : Matrix (Fin 2 × ι) (Fin 2 × ι) F :=
  blockDiagonal (fun i => alternatingPair (ε i))

theorem matchingPerturbation_mulVec [Fintype ι] [DecidableEq ι]
    (ε : ι → F) (v : Fin 2 × ι → F) (a : Fin 2) (i : ι) :
    (matchingPerturbation ε *ᵥ v) (a, i) =
      (alternatingPair (ε i) *ᵥ fun b => v (b, i)) a := by
  simp [matchingPerturbation, mulVec, dotProduct, Fintype.sum_prod_type,
    blockDiagonal_apply, ite_mul]

theorem isAlternatingMatrix_matchingPerturbation [Fintype ι] [DecidableEq ι] (ε : ι → F) :
    IsAlternatingMatrix (matchingPerturbation ε) := by
  intro v
  simp only [dotProduct, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  simp only [matchingPerturbation_mulVec]
  exact isAlternatingMatrix_pair (ε i) (fun a => v (a, i))

theorem matchingPerturbation_submatrix [DecidableEq ι] [DecidableEq κ]
    (ε : ι → F) (e : κ ≃ ι) :
    (matchingPerturbation ε).submatrix ((Equiv.refl (Fin 2)).prodCongr e)
      ((Equiv.refl (Fin 2)).prodCongr e) = matchingPerturbation (ε ∘ e) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp [matchingPerturbation, blockDiagonal_apply, Equiv.apply_eq_iff_eq]

/-- Separate the final matched pair from all the other pairs. -/
def optionPairEquiv (ι : Type*) : (Fin 2 × Option ι) ≃ ((Fin 2 × ι) ⊕ Fin 2) where
  toFun x := match x.2 with
    | some i => Sum.inl (x.1, i)
    | none => Sum.inr x.1
  invFun x := match x with
    | Sum.inl y => (y.1, some y.2)
    | Sum.inr a => (a, none)
  left_inv := by
    rintro ⟨a, i⟩
    cases i <;> rfl
  right_inv := by
    intro x
    cases x <;> rfl

private theorem matchingPerturbation_option_blocks [DecidableEq ι] (ε : ι → F) (t : F) :
    (matchingPerturbation (fun o : Option ι => o.elim t ε)).submatrix
      (optionPairEquiv ι).symm (optionPairEquiv ι).symm =
      fromBlocks (matchingPerturbation ε) 0 0 (alternatingPair t) := by
  ext i j
  rcases i with ⟨a, i⟩ | a <;> rcases j with ⟨b, j⟩ | b <;>
    simp [matchingPerturbation, blockDiagonal_apply, optionPairEquiv, fromBlocks]

/-- Every alternating matrix admits a nonsingular binary perturbation
along any fixed pairing of its coordinates. -/
theorem exists_binary_matching_completion [Fintype ι]
    (M : Matrix (Fin 2 × ι) (Fin 2 × ι) F) (hM : IsAlternatingMatrix M) :
    ∃ ε : ι → F, (∀ i, ε i = 0 ∨ ε i = 1) ∧
      (M + matchingPerturbation ε).det ≠ 0 := by
  classical
  suffices h : ∀ (α : Type*) [Fintype α] (N : Matrix (Fin 2 × α) (Fin 2 × α) F),
      IsAlternatingMatrix N → ∃ ε : α → F, (∀ i, ε i = 0 ∨ ε i = 1) ∧
        (N + matchingPerturbation ε).det ≠ 0 from h ι M hM
  intro α _
  apply Fintype.induction_empty_option
    (P := fun α _ => ∀ N : Matrix (Fin 2 × α) (Fin 2 × α) F,
      IsAlternatingMatrix N → ∃ ε : α → F, (∀ i, ε i = 0 ∨ ε i = 1) ∧
        (N + matchingPerturbation ε).det ≠ 0)
  · intro α β _ e ih N hN
    let e₂ : (Fin 2 × α) ≃ (Fin 2 × β) := (Equiv.refl (Fin 2)).prodCongr e
    obtain ⟨ε, hε, hdet⟩ := ih (N.submatrix e₂ e₂) (hN.submatrix_equiv e₂)
    refine ⟨ε ∘ e.symm, fun i => hε (e.symm i), ?_⟩
    have hpert : (matchingPerturbation (ε ∘ e.symm)).submatrix e₂ e₂ =
        matchingPerturbation ε := by
      rw [matchingPerturbation_submatrix]
      congr 1
      funext i
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
    intro hz
    apply hdet
    have heq := det_submatrix_equiv_self e₂ (N + matchingPerturbation (ε ∘ e.symm))
    rw [submatrix_add, hpert, hz] at heq
    exact heq
  · intro N _
    refine ⟨fun i => PEmpty.elim i, fun i => PEmpty.elim i, ?_⟩
    rw [det_isEmpty]
    exact one_ne_zero
  · intro α _ ih N hN
    let e := optionPairEquiv α
    let B := N.submatrix e.symm e.symm
    have hB : IsAlternatingMatrix B := hN.submatrix_equiv e.symm
    have hblocks : IsAlternatingMatrix
        (fromBlocks B.toBlocks₁₁ B.toBlocks₁₂ B.toBlocks₂₁ B.toBlocks₂₂) := by
      simpa only [fromBlocks_toBlocks] using hB
    obtain ⟨ε, hε, hdet⟩ := ih B.toBlocks₁₁ hblocks.fromBlocks_left
    have hdiag : IsAlternatingMatrix
        (fromBlocks (matchingPerturbation ε) (0 : Matrix (Fin 2 × α) (Fin 2) F) 0 0) :=
      isAlternatingMatrix_blockDiagonal (isAlternatingMatrix_matchingPerturbation ε)
        isAlternatingMatrix_zero
    have hcompleted : IsAlternatingMatrix (fromBlocks
        (B.toBlocks₁₁ + matchingPerturbation ε) B.toBlocks₁₂ B.toBlocks₂₁ B.toBlocks₂₂) := by
      simpa only [fromBlocks_add, add_zero] using hblocks.add hdiag
    obtain ⟨t, ht, htDet⟩ := exists_binary_pair_border hcompleted hdet
    refine ⟨fun o => o.elim t ε, ?_, ?_⟩
    · intro o
      cases o with
      | none => exact ht
      | some i => exact hε i
    · have hmatrix : (N + matchingPerturbation (fun o : Option α => o.elim t ε)).submatrix
          e.symm e.symm = fromBlocks (B.toBlocks₁₁ + matchingPerturbation ε)
            B.toBlocks₁₂ B.toBlocks₂₁ (B.toBlocks₂₂ + alternatingPair t) := by
        rw [submatrix_add, matchingPerturbation_option_blocks]
        change B + fromBlocks (matchingPerturbation ε) 0 0 (alternatingPair t) = _
        conv_lhs => arg 1; rw [← fromBlocks_toBlocks B]
        rw [fromBlocks_add, add_zero, add_zero]
      intro hz
      apply htDet
      rw [← hmatrix, det_submatrix_equiv_self, hz]

#print axioms exists_binary_matching_completion

end GaloisForLFunctions.HTGeometry.LinearAlgebra
