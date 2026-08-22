/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapDimensions
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Hasse detection for matrix rank

For finite square matrices, coefficientwise field extension is conjugate to extension of the
associated `mulVec` linear map.  The range dimension, hence the matrix rank, is therefore
unchanged.  Specializing to completed global fields gives local tests for prescribed rank.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

open scoped TensorProduct

/-- Coefficientwise scalar extension of a square matrix is conjugate to scalar extension of its
`mulVec` linear map through the canonical tensor/product equivalence. -/
theorem matrix_mulVecLin_map_conj_baseChange {K : Type u} {L : Type v} {n : Type w}
    [Field K] [Field L] [Algebra K L] [Fintype n] [DecidableEq n]
    (M : Matrix n n K) :
    (M.map (algebraMap K L)).mulVecLin =
      (TensorProduct.piScalarRight K L L n).toLinearMap.comp
        (((M.mulVecLin).baseChange L).comp
          (TensorProduct.piScalarRight K L L n).symm.toLinearMap) := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := (TensorProduct.piScalarRight K L L n).surjective z
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simpa only [map_add, Matrix.mulVec_add] using congrArg₂ (· + ·) hx hy
  | tmul a x =>
      ext i
      simp only [LinearMap.comp_apply, TensorProduct.piScalarRight_apply,
        TensorProduct.piScalarRightHom_tmul, Matrix.mulVecLin_apply]
      have hcoord : (fun j => x j • a) = a • ((algebraMap K L) ∘ x) := by
        ext j
        simp [Algebra.smul_def, mul_comm]
      rw [hcoord, Matrix.mulVec_smul]
      have hcoord' : (TensorProduct.piScalarRight K L L n).symm
          (a • ((algebraMap K L) ∘ x)) = a ⊗ₜ[K] x := by
        rw [show a • ((algebraMap K L) ∘ x) =
            TensorProduct.piScalarRight K L L n (a ⊗ₜ[K] x) by
          ext j
          simp [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
            Algebra.smul_def, mul_comm], LinearEquiv.symm_apply_apply]
      calc
        (a • (M.map (algebraMap K L)).mulVec ((algebraMap K L) ∘ x)) i =
            algebraMap K L (M.mulVec x i) * a := by
              simp only [Pi.smul_apply, Algebra.smul_def]
              change a * (M.map (algebraMap K L)).mulVec ((algebraMap K L) ∘ x) i =
                algebraMap K L (M.mulVec x i) * a
              rw [mul_comm a, ← RingHom.map_mulVec (algebraMap K L) M x i]
        _ = (M.mulVec x i) • a := by simp [Algebra.smul_def]
        _ = TensorProduct.piScalarRight K L L n (a ⊗ₜ[K] M.mulVec x) i := by
              simp [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
        _ = TensorProduct.piScalarRight K L L n
            ((M.mulVecLin).baseChange L (a ⊗ₜ[K] x)) i := by
              rw [LinearMap.baseChange_tmul, Matrix.mulVecLin_apply]
        _ = TensorProduct.piScalarRight K L L n
            ((M.mulVecLin).baseChange L
              ((TensorProduct.piScalarRight K L L n).symm
                (a • ((algebraMap K L) ∘ x)))) i := by
              exact congrArg
                (fun q => TensorProduct.piScalarRight K L L n ((M.mulVecLin).baseChange L q) i)
                hcoord'.symm

/-- Matrix rank is preserved by coefficientwise field scalar extension. -/
theorem matrix_rank_eq_rank_map {K : Type u} {L : Type v} {n : Type w}
    [Field K] [Field L] [Algebra K L] [Fintype n] [DecidableEq n]
    (M : Matrix n n K) : M.rank = (M.map (algebraMap K L)).rank := by
  let e : L ⊗[K] (n → K) ≃ₗ[L] n → L := TensorProduct.piScalarRight K L L n
  have hrange : LinearMap.range (M.map (algebraMap K L)).mulVecLin =
      (LinearMap.range ((M.mulVecLin).baseChange L)).map e.toLinearMap := by
    rw [matrix_mulVecLin_map_conj_baseChange]
    calc
      LinearMap.range (e.toLinearMap.comp
          (((M.mulVecLin).baseChange L).comp e.symm.toLinearMap)) =
          (LinearMap.range (((M.mulVecLin).baseChange L).comp e.symm.toLinearMap)).map
            e.toLinearMap := LinearMap.range_comp _ _
      _ = (LinearMap.range ((M.mulVecLin).baseChange L)).map e.toLinearMap := by
        rw [LinearMap.range_comp_of_range_eq_top]
        exact e.symm.range
  rw [Matrix.rank, Matrix.rank]
  calc
    Module.finrank K (LinearMap.range M.mulVecLin) =
        Module.finrank L (LinearMap.range ((M.mulVecLin).baseChange L)) :=
      (linearMap_range_finrank_baseChange (L := L) M.mulVecLin).symm
    _ = Module.finrank L ((LinearMap.range ((M.mulVecLin).baseChange L)).map e.toLinearMap) :=
      (e.finrank_map_eq _).symm
    _ = Module.finrank L (LinearMap.range (M.map (algebraMap K L)).mulVecLin) := by
      rw [hrange]

/-- A number-field matrix has the same rank after scalar extension to any completed place. -/
theorem numberFieldMatrix_rank_completion (K : Type u) [Field K] [NumberField K]
    (n : Type w) [Fintype n] [DecidableEq n] (M : Matrix n n K) (p : NumberFieldPlace K) :
    M.rank = (M.map (algebraMap K (completion K p))).rank :=
  matrix_rank_eq_rank_map (L := completion K p) M

/-- A number-field matrix has rank `r` exactly when all completed matrices have rank `r`. -/
theorem numberFieldMatrix_rank_eq_iff_forall_place (K : Type u) [Field K] [NumberField K]
    (n : Type w) [Fintype n] [DecidableEq n] (M : Matrix n n K) (r : ℕ) :
    M.rank = r ↔ ∀ p : NumberFieldPlace K,
      (M.map (algebraMap K (completion K p))).rank = r := by
  constructor
  · intro h p
    rw [← numberFieldMatrix_rank_completion K n M p, h]
  · intro h
    calc
      M.rank = (M.map (algebraMap K (completion K (witnessPlace K)))).rank :=
        numberFieldMatrix_rank_completion K n M (witnessPlace K)
      _ = r := h (witnessPlace K)

/-- An `F(t)`-matrix has the same rank after scalar extension to any finite or infinite
completion. -/
theorem rationalFunctionMatrix_rank_completion (F : Type u) [Field F] [Finite F]
    (n : Type w) [Fintype n] [DecidableEq n] (M : Matrix n n (RatFunc F))
    (p : RationalFunctionPlace F) :
    M.rank = (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).rank :=
  matrix_rank_eq_rank_map (L := rationalFunctionCompletion F p) M

/-- An `F(t)`-matrix has rank `r` exactly when every finite and infinite completed matrix has
rank `r`. -/
theorem rationalFunctionMatrix_rank_eq_iff_forall_place (F : Type u) [Field F] [Finite F]
    (n : Type w) [Fintype n] [DecidableEq n] (M : Matrix n n (RatFunc F)) (r : ℕ) :
    M.rank = r ↔ ∀ p : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).rank = r := by
  constructor
  · intro h p
    rw [← rationalFunctionMatrix_rank_completion F n M p, h]
  · intro h
    calc
      M.rank = (M.map (algebraMap (RatFunc F)
          (rationalFunctionCompletion F RationalFunctionPlace.infinite))).rank :=
        rationalFunctionMatrix_rank_completion F n M RationalFunctionPlace.infinite
      _ = r := h RationalFunctionPlace.infinite

/-- A prescribed number-field matrix rank is detected at one completed place. -/
theorem numberFieldMatrix_rank_eq_iff_exists_place (K : Type u) [Field K] [NumberField K]
    (n : Type w) [Fintype n] [DecidableEq n] (M : Matrix n n K) (r : ℕ) :
    M.rank = r ↔ ∃ p : NumberFieldPlace K,
      (M.map (algebraMap K (completion K p))).rank = r := by
  constructor
  · intro h
    exact ⟨witnessPlace K, (numberFieldMatrix_rank_completion K n M (witnessPlace K)).symm.trans h⟩
  · rintro ⟨p, hp⟩
    exact (numberFieldMatrix_rank_completion K n M p).trans hp

/-- A prescribed rational-function-field matrix rank is detected at one finite or infinite
completed place. -/
theorem rationalFunctionMatrix_rank_eq_iff_exists_place (F : Type u) [Field F] [Finite F]
    (n : Type w) [Fintype n] [DecidableEq n] (M : Matrix n n (RatFunc F)) (r : ℕ) :
    M.rank = r ↔ ∃ p : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).rank = r := by
  constructor
  · intro h
    exact ⟨.infinite,
      (rationalFunctionMatrix_rank_completion F n M .infinite).symm.trans h⟩
  · rintro ⟨p, hp⟩
    exact (rationalFunctionMatrix_rank_completion F n M p).trans hp

end GaloisForLFunctions.HTGeometry.ABHN
