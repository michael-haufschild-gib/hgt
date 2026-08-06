import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Data.Matrix.Block

/-!
# Determinant and characteristic polynomial of a dependent block-diagonal matrix

Mathlib computes the determinant of `Matrix.blockDiagonal`, whose blocks all
share one index type.  A family of non-interacting subsystems has blocks of
different sizes, so its block-diagonal matrix is `Matrix.blockDiagonal'` over a
sigma type.  This file supplies the missing determinant law, by peeling off one
block at a time and using the two-block law `Matrix.det_fromBlocks_zero₁₂`, and
deduces that the characteristic polynomial of a dependent block-diagonal matrix
is the product of the characteristic polynomials of its blocks.
-/

open scoped Matrix BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Split a sigma type by whether the first component is a distinguished
value. -/
def sigmaSplitAt {C : Type*} [DecidableEq C] (c₀ : C) (I : C → Type*) :
    (Σ c, I c) ≃ I c₀ ⊕ (Σ c : {c : C // c ≠ c₀}, I c.1) where
  toFun x := if h : x.1 = c₀ then Sum.inl (h ▸ x.2) else Sum.inr ⟨⟨x.1, h⟩, x.2⟩
  invFun y :=
    match y with
    | Sum.inl a => ⟨c₀, a⟩
    | Sum.inr z => ⟨z.1.1, z.2⟩
  left_inv := by
    rintro ⟨c, a⟩
    by_cases h : c = c₀
    · subst h
      simp
    · simp [h]
  right_inv := by
    rintro (a | ⟨⟨c, hc⟩, a⟩)
    · simp
    · simp [hc]

@[simp] theorem sigmaSplitAt_symm_inl {C : Type*} [DecidableEq C] (c₀ : C)
    (I : C → Type*) (a : I c₀) :
    (sigmaSplitAt c₀ I).symm (Sum.inl a) = ⟨c₀, a⟩ := rfl

@[simp] theorem sigmaSplitAt_symm_inr {C : Type*} [DecidableEq C] (c₀ : C)
    (I : C → Type*) (z : Σ c : {c : C // c ≠ c₀}, I c.1) :
    (sigmaSplitAt c₀ I).symm (Sum.inr z) = ⟨z.1.1, z.2⟩ := rfl

variable {C : Type*} [Fintype C] [DecidableEq C]
    {I : C → Type*} [∀ c, Fintype (I c)] [∀ c, DecidableEq (I c)]
    {R : Type*} [CommRing R]

omit [Fintype C] [∀ c, Fintype (I c)] [∀ c, DecidableEq (I c)] in
/-- Peeling off one block from a dependent block-diagonal matrix. -/
theorem reindex_blockDiagonal'_sigmaSplitAt (c₀ : C)
    (M : ∀ c, Matrix (I c) (I c) R) :
    Matrix.reindex (sigmaSplitAt c₀ I) (sigmaSplitAt c₀ I)
        (Matrix.blockDiagonal' M) =
      Matrix.fromBlocks (M c₀) 0 0
        (Matrix.blockDiagonal' fun c : {c : C // c ≠ c₀} => M c.1) := by
  ext x y
  show Matrix.blockDiagonal' M ((sigmaSplitAt c₀ I).symm x)
    ((sigmaSplitAt c₀ I).symm y) = _
  cases x with
  | inl a =>
      cases y with
      | inl b =>
          rw [sigmaSplitAt_symm_inl, sigmaSplitAt_symm_inl,
            Matrix.blockDiagonal'_apply_eq]
          rfl
      | inr z =>
          rw [sigmaSplitAt_symm_inl, sigmaSplitAt_symm_inr,
            Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm z.1.2)]
          rfl
  | inr w =>
      cases y with
      | inl b =>
          rw [sigmaSplitAt_symm_inr, sigmaSplitAt_symm_inl,
            Matrix.blockDiagonal'_apply_ne _ _ _ w.1.2]
          rfl
      | inr z =>
          rw [sigmaSplitAt_symm_inr, sigmaSplitAt_symm_inr]
          obtain ⟨⟨c, hc⟩, a⟩ := w
          obtain ⟨⟨d, hd⟩, b⟩ := z
          by_cases hcd : c = d
          · subst hcd
            rw [Matrix.blockDiagonal'_apply_eq]
            exact (Matrix.blockDiagonal'_apply_eq
              (fun c : {c : C // c ≠ c₀} => M c.1) ⟨c, hc⟩ a b).symm
          · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hcd]
            exact (Matrix.blockDiagonal'_apply_ne
              (fun c : {c : C // c ≠ c₀} => M c.1) a b
              (fun h => hcd (congrArg Subtype.val h))).symm

/-- **Determinant of a dependent block-diagonal matrix.** -/
theorem det_blockDiagonal' (M : ∀ c, Matrix (I c) (I c) R) :
    (Matrix.blockDiagonal' M).det = ∏ c, (M c).det := by
  classical
  induction hn : Fintype.card C using Nat.strong_induction_on generalizing C with
  | _ n ih =>
    rcases isEmpty_or_nonempty C with hC | hC
    · haveI : IsEmpty (Σ c, I c) := ⟨fun x => hC.elim x.1⟩
      rw [Matrix.det_isEmpty, Finset.prod_of_isEmpty]
    · obtain ⟨c₀⟩ := hC
      haveI : Nonempty C := ⟨c₀⟩
      have hcard : Fintype.card {c : C // c ≠ c₀} < Fintype.card C := by
        rw [Fintype.card_subtype_compl (fun c : C => c = c₀),
          Fintype.card_subtype_eq]
        exact Nat.sub_lt Fintype.card_pos Nat.one_pos
      have hsub := ih (Fintype.card {c : C // c ≠ c₀}) (hn ▸ hcard)
        (fun c : {c : C // c ≠ c₀} => M c.1) rfl
      rw [← Matrix.det_submatrix_equiv_self (sigmaSplitAt c₀ I).symm
        (Matrix.blockDiagonal' M)]
      show (Matrix.reindex (sigmaSplitAt c₀ I) (sigmaSplitAt c₀ I)
        (Matrix.blockDiagonal' M)).det = _
      rw [reindex_blockDiagonal'_sigmaSplitAt, Matrix.det_fromBlocks_zero₁₂,
        hsub, ← Fintype.prod_eq_mul_prod_subtype_ne (fun c => (M c).det) c₀]

/-- The characteristic matrix of a dependent block-diagonal matrix is the
block-diagonal of the characteristic matrices. -/
theorem charmatrix_blockDiagonal' (M : ∀ c, Matrix (I c) (I c) R) :
    Matrix.charmatrix (Matrix.blockDiagonal' M) =
      Matrix.blockDiagonal' fun c => Matrix.charmatrix (M c) := by
  classical
  refine Matrix.ext fun x y => ?_
  obtain ⟨c, a⟩ := x
  obtain ⟨d, b⟩ := y
  rw [Matrix.charmatrix_apply]
  by_cases hcd : c = d
  · subst hcd
    rw [Matrix.blockDiagonal'_apply_eq (fun c => Matrix.charmatrix (M c)),
      Matrix.blockDiagonal'_apply_eq M, Matrix.charmatrix_apply]
    simp [Matrix.diagonal_apply, Sigma.mk.injEq]
  · rw [Matrix.blockDiagonal'_apply_ne
      (fun c => Matrix.charmatrix (M c)) a b hcd,
      Matrix.blockDiagonal'_apply_ne M a b hcd]
    simp [Sigma.mk.injEq, hcd]

/-- **Characteristic polynomial of a dependent block-diagonal matrix.** -/
theorem charpoly_blockDiagonal' (M : ∀ c, Matrix (I c) (I c) R) :
    (Matrix.blockDiagonal' M).charpoly = ∏ c, (M c).charpoly := by
  unfold Matrix.charpoly
  rw [charmatrix_blockDiagonal', det_blockDiagonal']

end

end GaloisForLFunctions.HTGeometry
