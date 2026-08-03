import GaloisForLFunctions.RHTower.CyclicBarTensorOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm

/-!
# Projective continuity of cyclic-bar operators

For a normalized complex normed algebra, every cyclic-bar face, degeneracy, and cyclic rotation
is continuous for the projective tensor seminorm.  Face contractions have norm at most one by
submultiplicativity; degeneracies have norm at most one because the inserted unit has norm one;
rotation preserves the product bound exactly.

These maps are bundled as continuous linear maps and proved equal to the algebraic cyclic-bar
operators already used by `CyclicBarCyclicModule`.  Thus the analytic topology layer introduces
no replacement complex and no weakened structure maps.
-/

noncomputable section

open scoped BigOperators TensorProduct

namespace GaloisForLFunctions
namespace RHTower

section ProductBounds

variable {A : Type*} [NormedRing A]

/-- Product-norm contraction for a non-wrap cyclic face. -/
theorem cyclicBarFaceNonwrapTuple_norm_prod_le {n : ℕ} (i : Fin (n + 1))
    (x : Fin (n + 2) → A) :
    (∏ j, ‖cyclicBarFaceNonwrapTuple i x j‖) ≤ ∏ j, ‖x j‖ := by
  classical
  let y := Fin.removeNth i.succ x
  calc
    (∏ j, ‖cyclicBarFaceNonwrapTuple i x j‖) =
        ‖x i.castSucc * x i.succ‖ *
          ∏ j ∈ ({i}ᶜ : Finset (Fin (n + 1))), ‖y j‖ := by
            rw [Fintype.prod_eq_mul_prod_compl i]
            congr 1
            · simp [cyclicBarFaceNonwrapTuple]
            · apply Finset.prod_congr rfl
              intro j hj
              have hji : j ≠ i := by simpa using hj
              simp [cyclicBarFaceNonwrapTuple, y, hji]
    _ ≤ (‖x i.castSucc‖ * ‖x i.succ‖) *
          ∏ j ∈ ({i}ᶜ : Finset (Fin (n + 1))), ‖y j‖ := by
            gcongr
            exact norm_mul_le _ _
    _ = ‖x i.succ‖ * (‖y i‖ *
          ∏ j ∈ ({i}ᶜ : Finset (Fin (n + 1))), ‖y j‖) := by
            simp [y, Fin.removeNth]
            ring
    _ = ‖x i.succ‖ * ∏ j, ‖y j‖ := by
            rw [Fintype.prod_eq_mul_prod_compl i]
    _ = ∏ j, ‖x j‖ := by
            simpa [y, Fin.removeNth] using
              (Fin.mul_prod_removeNth i.succ (fun j => ‖x j‖))

/-- Product-norm contraction for the wrap cyclic face. -/
theorem cyclicBarFaceWrapTuple_norm_prod_le {n : ℕ} (x : Fin (n + 2) → A) :
    (∏ j, ‖cyclicBarFaceWrapTuple x j‖) ≤ ∏ j, ‖x j‖ := by
  classical
  let y := Fin.removeNth (Fin.last (n + 1)) x
  calc
    (∏ j, ‖cyclicBarFaceWrapTuple x j‖) =
        ‖x (Fin.last (n + 1)) * x 0‖ *
          ∏ j ∈ ({0}ᶜ : Finset (Fin (n + 1))), ‖y j‖ := by
            rw [Fintype.prod_eq_mul_prod_compl 0]
            congr 1
            apply Finset.prod_congr rfl
            intro j hj
            have hj0 : j ≠ 0 := by simpa using hj
            simp [cyclicBarFaceWrapTuple, y, hj0]
    _ ≤ (‖x (Fin.last (n + 1))‖ * ‖x 0‖) *
          ∏ j ∈ ({0}ᶜ : Finset (Fin (n + 1))), ‖y j‖ := by
            gcongr
            exact norm_mul_le _ _
    _ = ‖x (Fin.last (n + 1))‖ * (‖y 0‖ *
          ∏ j ∈ ({0}ᶜ : Finset (Fin (n + 1))), ‖y j‖) := by
            have hy0 : y 0 = x 0 := by
              simp [y, Fin.init]
            rw [hy0]
            ring
    _ = ‖x (Fin.last (n + 1))‖ * ∏ j, ‖y j‖ := by
            rw [Fintype.prod_eq_mul_prod_compl 0]
    _ = ∏ j, ‖x j‖ := by
            rw [← Fin.mul_prod_removeNth
              (Fin.last (n + 1)) (fun j => ‖x j‖)]
            congr 1

/-- Every cyclic face contracts the product norm of an elementary tensor. -/
theorem cyclicBarFaceTuple_norm_prod_le {n : ℕ} (i : Fin (n + 2))
    (x : Fin (n + 2) → A) :
    (∏ j, ‖cyclicBarFaceTuple i x j‖) ≤ ∏ j, ‖x j‖ := by
  induction i using Fin.lastCases with
  | last =>
      simpa [cyclicBarFaceTuple] using cyclicBarFaceWrapTuple_norm_prod_le x
  | cast i =>
      simpa [cyclicBarFaceTuple] using
        cyclicBarFaceNonwrapTuple_norm_prod_le i x

/-- Unit insertion preserves the product norm in a normalized normed ring. -/
theorem cyclicBarDegeneracyTuple_norm_prod {n : ℕ} [NormOneClass A]
    (i : Fin (n + 1)) (x : Fin (n + 1) → A) :
    (∏ j, ‖cyclicBarDegeneracyTuple i x j‖) = ∏ j, ‖x j‖ := by
  rw [show (fun j => ‖cyclicBarDegeneracyTuple i x j‖) =
      i.succ.insertNth ‖(1 : A)‖ (fun k => ‖x k‖) by
    funext j
    cases j using i.succ.succAboveCases with
    | x => simp [cyclicBarDegeneracyTuple]
    | p k => simp [cyclicBarDegeneracyTuple]]
  rw [Fin.prod_insertNth]
  simp

/-- Cyclic rotation preserves the product norm. -/
theorem cyclicBarRotateTuple_norm_prod {n : ℕ} (x : Fin (n + 1) → A) :
    (∏ j, ‖cyclicBarRotateTuple x j‖) = ∏ j, ‖x j‖ := by
  rw [← (finRotate (n + 1)).prod_comp Finset.univ _ (by simp)]
  simp [cyclicBarRotateTuple]

end ProductBounds

section ContinuousOperators

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

/-- Continuous multilinear contraction underlying a cyclic face. -/
def cyclicBarFaceContinuousMultilinear {n : ℕ} (i : Fin (n + 2)) :
    ContinuousMultilinearMap ℂ (fun _ : Fin (n + 2) => A)
      (CyclicBarTensor ℂ A n) := by
  let f : MultilinearMap ℂ (fun _ : Fin (n + 2) => A)
      (CyclicBarTensor ℂ A n) :=
    cyclicBarFaceMultilinear (R := ℂ) (A := A) i
  have h : ∀ x, ‖f x‖ ≤ 1 * ∏ j, ‖x j‖ := by
    intro x
    rw [one_mul]
    rw [show f x = PiTensorProduct.tprod ℂ (cyclicBarFaceTuple i x) from rfl]
    exact (PiTensorProduct.projectiveSeminorm_tprod_le (𝕜 := ℂ)
      (cyclicBarFaceTuple i x)).trans (cyclicBarFaceTuple_norm_prod_le i x)
  exact MultilinearMap.mkContinuous (𝕜 := ℂ)
    (E := fun _ : Fin (n + 2) => A) (G := CyclicBarTensor ℂ A n) f 1 h

/-- Projectively continuous cyclic face. -/
def cyclicBarFaceContinuousLinear {n : ℕ} (i : Fin (n + 2)) :
    CyclicBarTensor ℂ A (n + 1) →L[ℂ] CyclicBarTensor ℂ A n :=
  PiTensorProduct.liftEquiv ℂ (fun _ : Fin (n + 2) => A)
    (CyclicBarTensor ℂ A n) (cyclicBarFaceContinuousMultilinear i)

@[simp]
theorem cyclicBarFaceContinuousLinear_apply {n : ℕ} (i : Fin (n + 2))
    (x : CyclicBarTensor ℂ A (n + 1)) :
    cyclicBarFaceContinuousLinear i x =
      cyclicBarFace (R := ℂ) (A := A) i x := by
  change PiTensorProduct.lift
      (cyclicBarFaceMultilinear (R := ℂ) (A := A) i) x =
    PiTensorProduct.lift
      (cyclicBarFaceMultilinear (R := ℂ) (A := A) i) x
  rfl

/-- Continuous multilinear map underlying a cyclic degeneracy. -/
def cyclicBarDegeneracyContinuousMultilinear {n : ℕ} [NormOneClass A]
    (i : Fin (n + 1)) :
    ContinuousMultilinearMap ℂ (fun _ : Fin (n + 1) => A)
      (CyclicBarTensor ℂ A (n + 1)) := by
  let f : MultilinearMap ℂ (fun _ : Fin (n + 1) => A)
      (CyclicBarTensor ℂ A (n + 1)) :=
    cyclicBarDegeneracyMultilinear (R := ℂ) (A := A) i
  have h : ∀ x, ‖f x‖ ≤ 1 * ∏ j, ‖x j‖ := by
    intro x
    rw [one_mul]
    rw [show f x = PiTensorProduct.tprod ℂ
      (cyclicBarDegeneracyTuple i x) from rfl]
    exact (PiTensorProduct.projectiveSeminorm_tprod_le (𝕜 := ℂ)
      (cyclicBarDegeneracyTuple i x)).trans_eq
        (cyclicBarDegeneracyTuple_norm_prod i x)
  exact MultilinearMap.mkContinuous (𝕜 := ℂ)
    (E := fun _ : Fin (n + 1) => A)
    (G := CyclicBarTensor ℂ A (n + 1)) f 1 h

/-- Projectively continuous cyclic degeneracy. -/
def cyclicBarDegeneracyContinuousLinear {n : ℕ} [NormOneClass A]
    (i : Fin (n + 1)) :
    CyclicBarTensor ℂ A n →L[ℂ] CyclicBarTensor ℂ A (n + 1) :=
  PiTensorProduct.liftEquiv ℂ (fun _ : Fin (n + 1) => A)
    (CyclicBarTensor ℂ A (n + 1))
      (cyclicBarDegeneracyContinuousMultilinear i)

@[simp]
theorem cyclicBarDegeneracyContinuousLinear_apply {n : ℕ} (i : Fin (n + 1))
    [NormOneClass A] (x : CyclicBarTensor ℂ A n) :
    cyclicBarDegeneracyContinuousLinear i x =
      cyclicBarDegeneracy (R := ℂ) (A := A) i x := by
  change PiTensorProduct.lift
      (cyclicBarDegeneracyMultilinear (R := ℂ) (A := A) i) x =
    PiTensorProduct.lift
      (cyclicBarDegeneracyMultilinear (R := ℂ) (A := A) i) x
  rfl

/-- Continuous multilinear map underlying cyclic rotation. -/
def cyclicBarRotateContinuousMultilinear (n : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin (n + 1) => A)
      (CyclicBarTensor ℂ A n) := by
  let f : MultilinearMap ℂ (fun _ : Fin (n + 1) => A)
      (CyclicBarTensor ℂ A n) :=
    (PiTensorProduct.lift (R := ℂ)
      (s := fun _ : Fin (n + 1) => A)
      (E := CyclicBarTensor ℂ A n)).symm
        (cyclicBarRotate (R := ℂ) (A := A) n).toLinearMap
  have h : ∀ x, ‖f x‖ ≤ 1 * ∏ j, ‖x j‖ := by
    intro x
    rw [one_mul]
    rw [show f x = cyclicBarRotate (R := ℂ) (A := A) n
      (PiTensorProduct.tprod ℂ x) from rfl]
    rw [cyclicBarRotate_tprod]
    exact (PiTensorProduct.projectiveSeminorm_tprod_le (𝕜 := ℂ)
      (cyclicBarRotateTuple x)).trans_eq (cyclicBarRotateTuple_norm_prod x)
  exact MultilinearMap.mkContinuous (𝕜 := ℂ)
    (E := fun _ : Fin (n + 1) => A) (G := CyclicBarTensor ℂ A n) f 1 h

/-- Projectively continuous cyclic rotation. -/
def cyclicBarRotateContinuousLinear (n : ℕ) :
    CyclicBarTensor ℂ A n →L[ℂ] CyclicBarTensor ℂ A n :=
  PiTensorProduct.liftEquiv ℂ (fun _ : Fin (n + 1) => A)
    (CyclicBarTensor ℂ A n) (cyclicBarRotateContinuousMultilinear (A := A) n)

@[simp]
theorem cyclicBarRotateContinuousLinear_apply (n : ℕ)
    (x : CyclicBarTensor ℂ A n) :
    cyclicBarRotateContinuousLinear n x =
      cyclicBarRotate (R := ℂ) (A := A) n x := by
  change PiTensorProduct.lift
      ((PiTensorProduct.lift (R := ℂ)
        (s := fun _ : Fin (n + 1) => A)
        (E := CyclicBarTensor ℂ A n)).symm
          (cyclicBarRotate (R := ℂ) (A := A) n).toLinearMap) x = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem continuous_cyclicBarFace {n : ℕ} (i : Fin (n + 2)) :
    Continuous (cyclicBarFace (R := ℂ) (A := A) i) := by
  have hfun :
      (cyclicBarFace (R := ℂ) (A := A) i :
        CyclicBarTensor ℂ A (n + 1) → CyclicBarTensor ℂ A n) =
        cyclicBarFaceContinuousLinear (A := A) i := by
    funext x
    exact (cyclicBarFaceContinuousLinear_apply i x).symm
  rw [hfun]
  exact (cyclicBarFaceContinuousLinear (A := A) i).continuous

theorem continuous_cyclicBarDegeneracy {n : ℕ} [NormOneClass A]
    (i : Fin (n + 1)) :
    Continuous (cyclicBarDegeneracy (R := ℂ) (A := A) i) := by
  have hfun :
      (cyclicBarDegeneracy (R := ℂ) (A := A) i :
        CyclicBarTensor ℂ A n → CyclicBarTensor ℂ A (n + 1)) =
        cyclicBarDegeneracyContinuousLinear (A := A) i := by
    funext x
    exact (cyclicBarDegeneracyContinuousLinear_apply i x).symm
  rw [hfun]
  exact (cyclicBarDegeneracyContinuousLinear (A := A) i).continuous

theorem continuous_cyclicBarRotate (n : ℕ) :
    Continuous (cyclicBarRotate (R := ℂ) (A := A) n) := by
  have hfun :
      (cyclicBarRotate (R := ℂ) (A := A) n :
        CyclicBarTensor ℂ A n → CyclicBarTensor ℂ A n) =
        cyclicBarRotateContinuousLinear (A := A) n := by
    funext x
    exact (cyclicBarRotateContinuousLinear_apply n x).symm
  rw [hfun]
  exact (cyclicBarRotateContinuousLinear (A := A) n).continuous

end ContinuousOperators

end RHTower
end GaloisForLFunctions
