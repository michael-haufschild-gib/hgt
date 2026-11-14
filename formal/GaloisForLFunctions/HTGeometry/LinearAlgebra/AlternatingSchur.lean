import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Fintype.Prod

/-!
# Alternating Schur complements and binary two-coordinate perturbations

Eliminating an invertible principal block preserves alternation over every
field, including characteristic two. On the remaining two coordinates,
adding either zero or the standard alternating pair makes the block
invertible. These are the local steps of matching-wise matrix completion.
-/

namespace GaloisForLFunctions.HTGeometry.LinearAlgebra

open Matrix

variable {F ι κ : Type*} [Field F] [Fintype ι] [Fintype κ]

/-- The bilinear form represented by a matrix vanishes on the diagonal. -/
def IsAlternatingMatrix (M : Matrix ι ι F) : Prop := ∀ v, v ⬝ᵥ (M *ᵥ v) = 0

theorem IsAlternatingMatrix.add {M N : Matrix ι ι F}
    (hM : IsAlternatingMatrix M) (hN : IsAlternatingMatrix N) :
    IsAlternatingMatrix (M + N) := by
  intro v
  rw [add_mulVec, dotProduct_add, hM v, hN v, add_zero]

/-- Relabelling the same row and column indices preserves alternation. -/
theorem IsAlternatingMatrix.submatrix_equiv {M : Matrix ι ι F}
    (hM : IsAlternatingMatrix M) (e : κ ≃ ι) :
    IsAlternatingMatrix (M.submatrix e e) := by
  intro v
  rw [submatrix_mulVec_equiv]
  have hreindex := dotProduct_comp_equiv_symm v (M *ᵥ (v ∘ e.symm)) e.symm
  simpa only [Equiv.symm_symm, hM (v ∘ e.symm)] using hreindex

theorem quadratic_fromBlocks (A : Matrix ι ι F) (B : Matrix ι κ F)
    (C : Matrix κ ι F) (D : Matrix κ κ F) (v : ι ⊕ κ → F) :
    v ⬝ᵥ (fromBlocks A B C D *ᵥ v) =
      (v ∘ Sum.inl) ⬝ᵥ (A *ᵥ (v ∘ Sum.inl) + B *ᵥ (v ∘ Sum.inr)) +
      (v ∘ Sum.inr) ⬝ᵥ (C *ᵥ (v ∘ Sum.inl) + D *ᵥ (v ∘ Sum.inr)) := by
  rw [fromBlocks_mulVec]
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Function.comp_apply]

theorem IsAlternatingMatrix.fromBlocks_left {A : Matrix ι ι F} {B : Matrix ι κ F}
    {C : Matrix κ ι F} {D : Matrix κ κ F}
    (hM : IsAlternatingMatrix (fromBlocks A B C D)) : IsAlternatingMatrix A := by
  intro v
  have h := hM (Sum.elim v 0)
  rw [quadratic_fromBlocks] at h
  simpa only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, mulVec_zero,
    add_zero, zero_dotProduct, add_zero] using h

theorem isAlternatingMatrix_blockDiagonal {A : Matrix ι ι F} {D : Matrix κ κ F}
    (hA : IsAlternatingMatrix A) (hD : IsAlternatingMatrix D) :
    IsAlternatingMatrix (fromBlocks A 0 0 D) := by
  intro v
  rw [quadratic_fromBlocks, zero_mulVec, zero_mulVec, add_zero, zero_add,
    hA, hD, add_zero]

theorem isAlternatingMatrix_zero : IsAlternatingMatrix (0 : Matrix ι ι F) := by
  intro v
  rw [zero_mulVec, dotProduct_zero]

variable [DecidableEq ι]

/-- Completing the square in block form preserves an alternating form.
The substituted vector makes its first block vanish exactly. -/
theorem IsAlternatingMatrix.schur {A : Matrix ι ι F} {B : Matrix ι κ F}
    {C : Matrix κ ι F} {D : Matrix κ κ F} [Invertible A]
    (hM : IsAlternatingMatrix (fromBlocks A B C D)) :
    IsAlternatingMatrix (D - C * ⅟A * B) := by
  intro v
  let u := -(⅟A *ᵥ (B *ᵥ v))
  have htop : A *ᵥ u + B *ᵥ v = 0 := by
    dsimp only [u]
    rw [mulVec_neg, mulVec_mulVec, mul_invOf_self, one_mulVec, neg_add_cancel]
  have hbottom : C *ᵥ u + D *ᵥ v = (D - C * ⅟A * B) *ᵥ v := by
    dsimp only [u]
    rw [mulVec_neg, mulVec_mulVec, mulVec_mulVec, sub_mulVec]
    abel
  have h := hM (Sum.elim u v)
  rw [quadratic_fromBlocks] at h
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr] at h
  rw [htop, dotProduct_zero, zero_add, hbottom] at h
  exact h

/-- The standard alternating form on two coordinates, scaled by `t`. -/
def alternatingPair (t : F) : Matrix (Fin 2) (Fin 2) F := !![0, t; -t, 0]

theorem isAlternatingMatrix_pair (t : F) : IsAlternatingMatrix (alternatingPair t) := by
  intro v
  simp [alternatingPair, mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- An alternating two-coordinate block can always be made nonsingular
by adding either zero or one standard pair. -/
theorem exists_binary_alternatingPair {M : Matrix (Fin 2) (Fin 2) F}
    (hM : IsAlternatingMatrix M) :
    ∃ t : F, (t = 0 ∨ t = 1) ∧ (M + alternatingPair t).det ≠ 0 := by
  have h00 : M 0 0 = 0 := by
    simpa [mulVec, dotProduct, Fin.sum_univ_two] using hM ![1, 0]
  have h11 : M 1 1 = 0 := by
    simpa [mulVec, dotProduct, Fin.sum_univ_two] using hM ![0, 1]
  have hsum : M 0 1 + M 1 0 = 0 := by
    simpa [mulVec, dotProduct, Fin.sum_univ_two, h00, h11] using hM ![1, 1]
  have h10 : M 1 0 = -M 0 1 := eq_neg_of_add_eq_zero_right hsum
  by_cases h01 : M 0 1 = 0
  · refine ⟨1, Or.inr rfl, ?_⟩
    simp [det_fin_two, alternatingPair, h00, h11, h10, h01]
  · refine ⟨0, Or.inl rfl, ?_⟩
    simpa [det_fin_two, alternatingPair, h00, h11, h10] using mul_ne_zero h01 h01

/-- Once the principal block is invertible, one binary perturbation of
the last pair completes the entire alternating matrix. -/
theorem exists_binary_pair_border {A : Matrix ι ι F} {B : Matrix ι (Fin 2) F}
    {C : Matrix (Fin 2) ι F} {D : Matrix (Fin 2) (Fin 2) F}
    (hM : IsAlternatingMatrix (fromBlocks A B C D)) (hA : A.det ≠ 0) :
    ∃ t : F, (t = 0 ∨ t = 1) ∧ (fromBlocks A B C (D + alternatingPair t)).det ≠ 0 := by
  letI : Invertible A := Classical.choice ((nonempty_invertible_iff_isUnit A).mpr
    ((isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hA)))
  obtain ⟨t, ht, hdet⟩ := exists_binary_alternatingPair hM.schur
  refine ⟨t, ht, ?_⟩
  rw [det_fromBlocks₁₁]
  apply mul_ne_zero hA
  convert hdet using 2
  abel

#print axioms IsAlternatingMatrix.schur
#print axioms exists_binary_pair_border

end GaloisForLFunctions.HTGeometry.LinearAlgebra
