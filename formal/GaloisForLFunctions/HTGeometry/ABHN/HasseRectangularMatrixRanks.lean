/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixRanks

/-!
# Hasse detection for rectangular matrix rank

Scalar extension preserves the rank of every finite matrix, not only endomorphism matrices.
Accordingly a prescribed rank of an arbitrary finite linear system can be detected at every, or at
one, completed place of a number field or rational function field.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w x

open scoped TensorProduct

/-- Coefficientwise scalar extension of an arbitrary finite matrix is conjugate to extension of
its `mulVec` linear map through canonical tensor/product equivalences. -/
theorem matrix_mulVecLin_map_conj_baseChange_rect {K : Type u} {L : Type v}
    {m : Type w} {n : Type x}
    [Field K] [Field L] [Algebra K L] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (M : Matrix m n K) :
    (M.map (algebraMap K L)).mulVecLin =
      (TensorProduct.piScalarRight K L L m).toLinearMap.comp
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
        _ = TensorProduct.piScalarRight K L L m (a ⊗ₜ[K] M.mulVec x) i := by
              simp [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
        _ = TensorProduct.piScalarRight K L L m
            ((M.mulVecLin).baseChange L (a ⊗ₜ[K] x)) i := by
              rw [LinearMap.baseChange_tmul, Matrix.mulVecLin_apply]
        _ = TensorProduct.piScalarRight K L L m
            ((M.mulVecLin).baseChange L
              ((TensorProduct.piScalarRight K L L n).symm
                (a • ((algebraMap K L) ∘ x)))) i := by
              exact congrArg
                (fun q => TensorProduct.piScalarRight K L L m ((M.mulVecLin).baseChange L q) i)
                hcoord'.symm

/-- Rank is preserved by coefficientwise extension of an arbitrary finite matrix. -/
theorem matrix_rank_eq_rank_map_rect {K : Type u} {L : Type v} {m : Type w} {n : Type x}
    [Field K] [Field L] [Algebra K L] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (M : Matrix m n K) : M.rank = (M.map (algebraMap K L)).rank := by
  let eDom : L ⊗[K] (n → K) ≃ₗ[L] n → L := TensorProduct.piScalarRight K L L n
  let eCod : L ⊗[K] (m → K) ≃ₗ[L] m → L := TensorProduct.piScalarRight K L L m
  have hrange : LinearMap.range (M.map (algebraMap K L)).mulVecLin =
      (LinearMap.range ((M.mulVecLin).baseChange L)).map eCod.toLinearMap := by
    rw [matrix_mulVecLin_map_conj_baseChange_rect]
    calc
      LinearMap.range (eCod.toLinearMap.comp
          (((M.mulVecLin).baseChange L).comp eDom.symm.toLinearMap)) =
          (LinearMap.range (((M.mulVecLin).baseChange L).comp eDom.symm.toLinearMap)).map
            eCod.toLinearMap := LinearMap.range_comp _ _
      _ = (LinearMap.range ((M.mulVecLin).baseChange L)).map eCod.toLinearMap := by
        rw [LinearMap.range_comp_of_range_eq_top]
        exact eDom.symm.range
  rw [Matrix.rank, Matrix.rank]
  calc
    Module.finrank K (LinearMap.range M.mulVecLin) =
        Module.finrank L (LinearMap.range ((M.mulVecLin).baseChange L)) :=
      (linearMap_range_finrank_baseChange (L := L) M.mulVecLin).symm
    _ = Module.finrank L ((LinearMap.range ((M.mulVecLin).baseChange L)).map eCod.toLinearMap) :=
      (eCod.finrank_map_eq _).symm
    _ = Module.finrank L (LinearMap.range (M.map (algebraMap K L)).mulVecLin) := by
      rw [hrange]

/-- A number-field rectangular matrix has the same rank after extension to any completion. -/
theorem numberFieldRectMatrix_rank_completion (K : Type u) [Field K] [NumberField K]
    (m : Type w) (n : Type x) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (M : Matrix m n K) (p : NumberFieldPlace K) :
    M.rank = (M.map (algebraMap K (completion K p))).rank :=
  matrix_rank_eq_rank_map_rect (L := completion K p) M

/-- A number-field rectangular matrix has rank `r` exactly when every completed matrix has rank
`r`. -/
theorem numberFieldRectMatrix_rank_eq_iff_forall_place (K : Type u) [Field K] [NumberField K]
    (m : Type w) (n : Type x) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (M : Matrix m n K) (r : ℕ) :
    M.rank = r ↔ ∀ p : NumberFieldPlace K,
      (M.map (algebraMap K (completion K p))).rank = r := by
  constructor
  · intro h p
    rw [← numberFieldRectMatrix_rank_completion K m n M p, h]
  · intro h
    calc
      M.rank = (M.map (algebraMap K (completion K (witnessPlace K)))).rank :=
        numberFieldRectMatrix_rank_completion K m n M (witnessPlace K)
      _ = r := h (witnessPlace K)

/-- A prescribed number-field rectangular matrix rank is certified at one completion. -/
theorem numberFieldRectMatrix_rank_eq_iff_exists_place (K : Type u) [Field K] [NumberField K]
    (m : Type w) (n : Type x) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (M : Matrix m n K) (r : ℕ) :
    M.rank = r ↔ ∃ p : NumberFieldPlace K,
      (M.map (algebraMap K (completion K p))).rank = r := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (numberFieldRectMatrix_rank_completion K m n M (witnessPlace K)).symm.trans h⟩
  · rintro ⟨p, hp⟩
    exact (numberFieldRectMatrix_rank_completion K m n M p).trans hp

/-- An `F(t)` rectangular matrix has the same rank after extension to every finite or infinite
completion. -/
theorem rationalFunctionRectMatrix_rank_completion (F : Type u) [Field F] [Finite F]
    (m : Type w) (n : Type x) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (M : Matrix m n (RatFunc F)) (p : RationalFunctionPlace F) :
    M.rank = (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).rank :=
  matrix_rank_eq_rank_map_rect (L := rationalFunctionCompletion F p) M

/-- An `F(t)` rectangular matrix has rank `r` exactly when every finite and infinite completed
matrix has rank `r`. -/
theorem rationalFunctionRectMatrix_rank_eq_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    (m : Type w) (n : Type x) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (M : Matrix m n (RatFunc F)) (r : ℕ) :
    M.rank = r ↔ ∀ p : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).rank = r := by
  constructor
  · intro h p
    rw [← rationalFunctionRectMatrix_rank_completion F m n M p, h]
  · intro h
    calc
      M.rank = (M.map (algebraMap (RatFunc F)
          (rationalFunctionCompletion F RationalFunctionPlace.infinite))).rank :=
        rationalFunctionRectMatrix_rank_completion F m n M RationalFunctionPlace.infinite
      _ = r := h RationalFunctionPlace.infinite

/-- A prescribed `F(t)` rectangular matrix rank is certified at one completion. -/
theorem rationalFunctionRectMatrix_rank_eq_iff_exists_place
    (F : Type u) [Field F] [Finite F]
    (m : Type w) (n : Type x) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (M : Matrix m n (RatFunc F)) (r : ℕ) :
    M.rank = r ↔ ∃ p : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).rank = r := by
  constructor
  · intro h
    exact ⟨.infinite,
      (rationalFunctionRectMatrix_rank_completion F m n M .infinite).symm.trans h⟩
  · rintro ⟨p, hp⟩
    exact (rationalFunctionRectMatrix_rank_completion F m n M p).trans hp

end GaloisForLFunctions.HTGeometry.ABHN
