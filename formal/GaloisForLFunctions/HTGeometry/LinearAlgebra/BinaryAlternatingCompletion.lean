import GaloisForLFunctions.HTGeometry.LinearAlgebra.AlternatingSchur
import Mathlib.Data.Fintype.Option
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Binary completion along a prescribed matching

An alternating matrix on paired coordinates can be made nonsingular by
adding a standard alternating pair, or adding zero, independently along
each matched pair. The proof eliminates one pair at a time using Schur
complements; it works over arbitrary fields, including characteristic two.
-/

namespace GaloisForLFunctions.HTGeometry.LinearAlgebra

open Matrix

universe u v w

variable {F : Type v} {ι : Type u} {κ : Type w} [Field F]

/-- Independent alternating perturbations on the matched coordinate pairs. -/
noncomputable def matchingPerturbation (ε : ι → F) : Matrix (Fin 2 × ι) (Fin 2 × ι) F := by
  classical
  exact blockDiagonal (fun i => alternatingPair (ε i))

theorem matchingPerturbation_mulVec [Fintype ι]
    (ε : ι → F) (v : Fin 2 × ι → F) (a : Fin 2) (i : ι) :
    (matchingPerturbation ε *ᵥ v) (a, i) =
      (alternatingPair (ε i) *ᵥ fun b => v (b, i)) a := by
  classical
  simp [matchingPerturbation, mulVec, dotProduct, Fintype.sum_prod_type,
    blockDiagonal_apply, ite_mul]

theorem isAlternatingMatrix_matchingPerturbation [Fintype ι] (ε : ι → F) :
    IsAlternatingMatrix (matchingPerturbation ε) := by
  intro v
  simp only [dotProduct, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  simp only [matchingPerturbation_mulVec]
  exact isAlternatingMatrix_pair (ε i) (fun a => v (a, i))

theorem matchingPerturbation_submatrix
    (ε : ι → F) (e : κ ≃ ι) :
    (matchingPerturbation ε).submatrix ((Equiv.refl (Fin 2)).prodCongr e)
      ((Equiv.refl (Fin 2)).prodCongr e) = matchingPerturbation (ε ∘ e) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  by_cases hij : i = j
  · subst j
    simp [matchingPerturbation, blockDiagonal_apply]
  · have he : e i ≠ e j := fun h => hij (e.injective h)
    simp [matchingPerturbation, blockDiagonal_apply, hij, he]

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

private theorem matchingPerturbation_option_blocks (ε : ι → F) (t : F) :
    (matchingPerturbation (fun o : Option ι => o.elim t ε)).submatrix
      (optionPairEquiv ι).symm (optionPairEquiv ι).symm =
      fromBlocks (matchingPerturbation ε) 0 0 (alternatingPair t) := by
  ext i j
  rcases i with ⟨a, i⟩ | a <;> rcases j with ⟨b, j⟩ | b <;>
    simp [matchingPerturbation, blockDiagonal_apply, optionPairEquiv, fromBlocks]
  by_cases hij : i = j
  · subst j
    simp
  · have hsome : some i ≠ some j := fun h => hij (Option.some.inj h)
    simp [hij, hsome]

private theorem det_ne_zero_of_zero_kernel [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι F) (hker : ∀ v, M *ᵥ v = 0 → v = 0) : M.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hvne, hv⟩ := exists_mulVec_eq_zero_iff.mpr hdet
  exact hvne (hker v hv)

private theorem zero_kernel_of_det_ne_zero [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι F) (hdet : M.det ≠ 0) : ∀ v, M *ᵥ v = 0 → v = 0 := by
  intro v hv
  by_contra hne
  exact hdet (exists_mulVec_eq_zero_iff.mp ⟨v, hne, hv⟩)

private theorem exists_binary_matching_zero_kernel [Fintype ι]
    (M : Matrix (Fin 2 × ι) (Fin 2 × ι) F) (hM : IsAlternatingMatrix M) :
    ∃ ε : ι → F, (∀ i, ε i = 0 ∨ ε i = 1) ∧
      ∀ v, (M + matchingPerturbation ε) *ᵥ v = 0 → v = 0 := by
  classical
  suffices h : ∀ (α : Type u) [Fintype α] (N : Matrix (Fin 2 × α) (Fin 2 × α) F),
      IsAlternatingMatrix N → ∃ ε : α → F, (∀ i, ε i = 0 ∨ ε i = 1) ∧
        ∀ v, (N + matchingPerturbation ε) *ᵥ v = 0 → v = 0 from h ι M hM
  intro α _
  apply Fintype.induction_empty_option
    (P := fun α _ => ∀ N : Matrix (Fin 2 × α) (Fin 2 × α) F,
      IsAlternatingMatrix N → ∃ ε : α → F, (∀ i, ε i = 0 ∨ ε i = 1) ∧
        ∀ v, (N + matchingPerturbation ε) *ᵥ v = 0 → v = 0)
  · intro α β _ e ih N hN
    letI : Fintype α := Fintype.ofEquiv β e.symm
    let e₂ : (Fin 2 × α) ≃ (Fin 2 × β) := (Equiv.refl (Fin 2)).prodCongr e
    obtain ⟨ε, hε, hker⟩ := ih (N.submatrix e₂ e₂) (hN.submatrix_equiv e₂)
    have hdet := det_ne_zero_of_zero_kernel _ hker
    refine ⟨ε ∘ e.symm, fun i => hε (e.symm i), ?_⟩
    have hpert : (matchingPerturbation (ε ∘ e.symm)).submatrix e₂ e₂ =
        matchingPerturbation ε := by
      rw [matchingPerturbation_submatrix]
      congr 1
      funext i
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
    apply zero_kernel_of_det_ne_zero
    intro hz
    apply hdet
    have heq := det_submatrix_equiv_self e₂ (N + matchingPerturbation (ε ∘ e.symm))
    simp only [submatrix_add, Pi.add_apply, hpert, hz] at heq
    exact heq
  · intro N _
    refine ⟨fun i => PEmpty.elim i, fun i => PEmpty.elim i, ?_⟩
    intro v _
    funext i
    exact PEmpty.elim i.2
  · intro α _ ih N hN
    let e := optionPairEquiv α
    let B := N.submatrix e.symm e.symm
    have hB : IsAlternatingMatrix B := hN.submatrix_equiv e.symm
    have hblocks : IsAlternatingMatrix
        (fromBlocks B.toBlocks₁₁ B.toBlocks₁₂ B.toBlocks₂₁ B.toBlocks₂₂) := by
      simpa only [fromBlocks_toBlocks] using hB
    obtain ⟨ε, hε, hker⟩ := ih B.toBlocks₁₁ hblocks.fromBlocks_left
    have hdet := det_ne_zero_of_zero_kernel _ hker
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
        simp only [submatrix_add, Pi.add_apply]
        rw [matchingPerturbation_option_blocks]
        change B + fromBlocks (matchingPerturbation ε) 0 0 (alternatingPair t) = _
        conv_lhs => arg 1; rw [← fromBlocks_toBlocks B]
        rw [fromBlocks_add, add_zero, add_zero]
      apply zero_kernel_of_det_ne_zero
      intro hz
      apply htDet
      rw [← hmatrix, det_submatrix_equiv_self]
      exact hz

/-- Every alternating matrix admits a nonsingular binary perturbation
along any fixed pairing of its coordinates. -/
theorem exists_binary_matching_completion [Fintype ι] [DecidableEq ι]
    (M : Matrix (Fin 2 × ι) (Fin 2 × ι) F) (hM : IsAlternatingMatrix M) :
    ∃ ε : ι → F, (∀ i, ε i = 0 ∨ ε i = 1) ∧
      (M + matchingPerturbation ε).det ≠ 0 := by
  obtain ⟨ε, hε, hker⟩ := exists_binary_matching_zero_kernel M hM
  exact ⟨ε, hε, det_ne_zero_of_zero_kernel _ hker⟩

/-- Identify paired coordinates with two copies of their common index set. -/
def twoLayerEquiv (ι : Type*) : (Fin 2 × ι) ≃ (ι ⊕ ι) where
  toFun x := if x.1 = 0 then Sum.inl x.2 else Sum.inr x.2
  invFun x := match x with
    | Sum.inl i => (0, i)
    | Sum.inr i => (1, i)
  left_inv := by
    rintro ⟨⟨a, ha⟩, i⟩
    have h : a = 0 ∨ a = 1 := by omega
    rcases h with rfl | rfl <;> rfl
  right_inv := by
    intro x
    cases x <;> rfl

private theorem matchingPerturbation_twoLayer [DecidableEq ι] (ε : ι → F) :
    (matchingPerturbation ε).submatrix (twoLayerEquiv ι).symm (twoLayerEquiv ι).symm =
      fromBlocks 0 (diagonal ε) (-diagonal ε) 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> by_cases hij : i = j <;>
    simp [matchingPerturbation, blockDiagonal_apply, twoLayerEquiv, fromBlocks,
      alternatingPair, hij]

/-- In two-layer coordinates the completion changes only matched entries
in the off-diagonal blocks, by opposite binary amounts. -/
theorem exists_binary_offDiagonal_completion [Fintype ι] [DecidableEq ι]
    (M : Matrix (ι ⊕ ι) (ι ⊕ ι) F) (hM : IsAlternatingMatrix M) :
    ∃ ε : ι → F, (∀ i, ε i = 0 ∨ ε i = 1) ∧
      (M + fromBlocks 0 (diagonal ε) (-diagonal ε) 0).det ≠ 0 := by
  let e := twoLayerEquiv ι
  obtain ⟨ε, hε, hdet⟩ := exists_binary_matching_completion
    (M.submatrix e e) (hM.submatrix_equiv e)
  refine ⟨ε, hε, ?_⟩
  have hpert := matchingPerturbation_twoLayer ε
  have hmatrix : (M.submatrix e e + matchingPerturbation ε).submatrix e.symm e.symm =
      M + fromBlocks 0 (diagonal ε) (-diagonal ε) 0 := by
    simp only [submatrix_add, Pi.add_apply]
    congr 1
    ext i j
    simp [e]
  have htransport := det_submatrix_equiv_self e.symm (M.submatrix e e + matchingPerturbation ε)
  rw [hmatrix] at htransport
  exact fun hz => hdet (htransport.symm.trans hz)

#print axioms exists_binary_matching_completion
#print axioms exists_binary_offDiagonal_completion

end GaloisForLFunctions.HTGeometry.LinearAlgebra
