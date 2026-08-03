import GaloisForLFunctions.RHTower.PresentedSimplicialObject
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.PiTensorProduct.Basic

/-!
# Tensor operators for the noncommutative cyclic bar construction

This file constructs the face contractions, unit-inserting degeneracies, and cyclic rotation on
the genuine tensor powers of a possibly noncommutative unital algebra.  The construction uses
the universal property of `PiTensorProduct`; no free-word or degree-zero replacement occurs.
-/

noncomputable section

open CategoryTheory
open Function
open scoped TensorProduct

universe u v

namespace GaloisForLFunctions
namespace RHTower

variable {R : Type u} {A : Type v}

/-- Degree `n` of the cyclic bar construction of `A`. -/
abbrev CyclicBarTensor (R : Type u) (A : Type v) [CommRing R] [Ring A] [Algebra R A]
    (n : ℕ) :=
  PiTensorProduct R (fun _ : Fin (n + 1) ↦ A)

section Tuples

variable [Ring A]

/-- Non-wrap face: multiply entries `i` and `i+1`, then remove the latter entry. -/
def cyclicBarFaceNonwrapTuple {n : ℕ} (i : Fin (n + 1))
    (x : Fin (n + 2) → A) : Fin (n + 1) → A :=
  Function.update (Fin.removeNth i.succ x) i (x i.castSucc * x i.succ)

@[simp]
theorem cyclicBar_succ_succAbove_self {n : ℕ} (i : Fin (n + 1)) :
    i.succ.succAbove i = i.castSucc :=
  Fin.succAbove_of_castSucc_lt _ _ Fin.castSucc_lt_succ

theorem cyclicBarFaceNonwrapTuple_update_second {n : ℕ} (i : Fin (n + 1))
    (x : Fin (n + 2) → A) (a : A) :
    cyclicBarFaceNonwrapTuple i (Function.update x i.succ a) =
      Function.update (cyclicBarFaceNonwrapTuple i x) i (x i.castSucc * a) := by
  funext k
  by_cases h : k = i
  · subst k
    simp [cyclicBarFaceNonwrapTuple,
      Function.update_of_ne (Fin.ne_of_lt Fin.castSucc_lt_succ)]
  · simp [cyclicBarFaceNonwrapTuple, Fin.removeNth, Function.update_of_ne h]

theorem cyclicBarFaceNonwrapTuple_update_first {n : ℕ} (i : Fin (n + 1))
    (x : Fin (n + 2) → A) (a : A) :
    cyclicBarFaceNonwrapTuple i (Function.update x i.castSucc a) =
      Function.update (cyclicBarFaceNonwrapTuple i x) i (a * x i.succ) := by
  funext k
  by_cases h : k = i
  · subst k
    simp [cyclicBarFaceNonwrapTuple,
      Function.update_of_ne (Fin.ne_of_gt Fin.castSucc_lt_succ)]
  · have hne : i.succ.succAbove k ≠ i.castSucc := by
      rw [← cyclicBar_succ_succAbove_self i]
      exact Fin.succAbove_right_injective.ne h
    simp [cyclicBarFaceNonwrapTuple, Fin.removeNth, Function.update_of_ne h, hne]

theorem cyclicBarFaceNonwrapTuple_update_other {n : ℕ} (i q : Fin (n + 1))
    (hiq : q ≠ i) (x : Fin (n + 2) → A) (a : A) :
    cyclicBarFaceNonwrapTuple i (Function.update x (i.succ.succAbove q) a) =
      Function.update (cyclicBarFaceNonwrapTuple i x) q a := by
  funext k
  by_cases hki : k = i
  · subst k
    have hfirst : i.succ.succAbove q ≠ i.castSucc := by
      rw [← cyclicBar_succ_succAbove_self i]
      exact Fin.succAbove_right_injective.ne hiq
    simp only [cyclicBarFaceNonwrapTuple, Function.update_self]
    rw [Function.update_of_ne hfirst.symm,
      Function.update_of_ne (Fin.succAbove_ne i.succ q).symm,
      Function.update_of_ne hiq.symm, Function.update_self]
  · by_cases hkq : k = q
    · subst k
      simp [cyclicBarFaceNonwrapTuple, Fin.removeNth, hiq, Function.update_of_ne]
    · simp [cyclicBarFaceNonwrapTuple, Fin.removeNth, hki, hkq,
        Function.update_of_ne]

/-- Wrap face: multiply the last entry by the first and place the product first. -/
def cyclicBarFaceWrapTuple {n : ℕ} (x : Fin (n + 2) → A) : Fin (n + 1) → A :=
  Function.update (Fin.removeNth (Fin.last (n + 1)) x) 0
    (x (Fin.last (n + 1)) * x 0)

theorem cyclicBarFaceWrapTuple_update_last {n : ℕ} (x : Fin (n + 2) → A) (a : A) :
    cyclicBarFaceWrapTuple (Function.update x (Fin.last (n + 1)) a) =
      Function.update (cyclicBarFaceWrapTuple x) 0 (a * x 0) := by
  funext k
  by_cases hk : k = 0
  · subst k
    simp [cyclicBarFaceWrapTuple]
  · simp [cyclicBarFaceWrapTuple, Fin.removeNth, Fin.init,
      Function.update_of_ne hk]

theorem cyclicBarFaceWrapTuple_update_zero {n : ℕ} (x : Fin (n + 2) → A) (a : A) :
    cyclicBarFaceWrapTuple (Function.update x (0 : Fin (n + 1)).castSucc a) =
      Function.update (cyclicBarFaceWrapTuple x) 0 (x (Fin.last (n + 1)) * a) := by
  funext k
  by_cases hk : k = 0
  · subst k
    simp [cyclicBarFaceWrapTuple]
  · simp only [cyclicBarFaceWrapTuple, Fin.removeNth_last, Function.update_of_ne hk]
    change Fin.init (Function.update x 0 a) k = Fin.init x k
    change Function.update x 0 a k.castSucc = x k.castSucc
    rw [Function.update_of_ne]
    intro h
    apply hk
    apply Fin.castSucc_injective
    simpa using h

theorem cyclicBarFaceWrapTuple_update_other {n : ℕ} (q : Fin (n + 1)) (hq : q ≠ 0)
    (x : Fin (n + 2) → A) (a : A) :
    cyclicBarFaceWrapTuple (Function.update x q.castSucc a) =
      Function.update (cyclicBarFaceWrapTuple x) q a := by
  funext k
  by_cases hk0 : k = 0
  · subst k
    have hlast : Fin.last (n + 1) ≠ q.castSucc :=
      Fin.ne_of_gt (Fin.castSucc_lt_last q)
    have hzero : (0 : Fin (n + 2)) ≠ q.castSucc := by
      intro h
      apply hq
      apply Fin.castSucc_injective
      simpa using h.symm
    simp only [cyclicBarFaceWrapTuple, Function.update_self]
    rw [Function.update_of_ne hlast, Function.update_of_ne hzero,
      Function.update_of_ne hq.symm, Function.update_self]
  · by_cases hkq : k = q
    · subst k
      simp [cyclicBarFaceWrapTuple, hq]
    · simp [cyclicBarFaceWrapTuple, Fin.removeNth, hk0, hkq, hq,
        Function.update_of_ne]

/-- All cyclic-bar faces, including the wrap face in the final index. -/
def cyclicBarFaceTuple {n : ℕ} (i : Fin (n + 2))
    (x : Fin (n + 2) → A) : Fin (n + 1) → A :=
  Fin.lastCases (cyclicBarFaceWrapTuple x)
    (fun j ↦ cyclicBarFaceNonwrapTuple j x) i

/-- Insert the algebra unit immediately after entry `i`. -/
def cyclicBarDegeneracyTuple {n : ℕ} (i : Fin (n + 1))
    (x : Fin (n + 1) → A) : Fin (n + 2) → A :=
  Fin.insertNth i.succ 1 x

theorem cyclicBarDegeneracyTuple_update {n : ℕ} (i k : Fin (n + 1))
    (x : Fin (n + 1) → A) (a : A) :
    cyclicBarDegeneracyTuple i (Function.update x k a) =
      Function.update (cyclicBarDegeneracyTuple i x) (i.succ.succAbove k) a := by
  simpa only [cyclicBarDegeneracyTuple] using
    (@Fin.insertNth_update (n + 1) (fun _ : Fin (n + 2) ↦ A)
      i.succ 1 k a x)

/-- Right cyclic rotation `(a₀,…,aₙ) ↦ (aₙ,a₀,…,aₙ₋₁)`. -/
def cyclicBarRotateTuple {n : ℕ} (x : Fin (n + 1) → A) : Fin (n + 1) → A :=
  fun i ↦ x ((finRotate (n + 1)).symm i)

end Tuples

section LinearOperators

variable [CommRing R] [Ring A] [Algebra R A]

/-- Multilinear contraction defining one cyclic-bar face. -/
def cyclicBarFaceMultilinear {n : ℕ} (i : Fin (n + 2)) :
    MultilinearMap R (fun _ : Fin (n + 2) ↦ A) (CyclicBarTensor R A n) :=
  MultilinearMap.mk' (fun x ↦ PiTensorProduct.tprod R (cyclicBarFaceTuple i x))
    (by
      intro x k a b
      induction i using Fin.lastCases with
      | last =>
          simp only [cyclicBarFaceTuple, Fin.lastCases_last]
          cases k using Fin.lastCases with
          | last =>
              rw [cyclicBarFaceWrapTuple_update_last,
                cyclicBarFaceWrapTuple_update_last,
                cyclicBarFaceWrapTuple_update_last, add_mul]
              exact (PiTensorProduct.tprod R).map_update_add _ _ _ _
          | cast k =>
              cases k using Fin.cases with
              | zero =>
                  rw [cyclicBarFaceWrapTuple_update_zero,
                    cyclicBarFaceWrapTuple_update_zero,
                    cyclicBarFaceWrapTuple_update_zero, mul_add]
                  exact (PiTensorProduct.tprod R).map_update_add _ _ _ _
              | succ k =>
                  rw [cyclicBarFaceWrapTuple_update_other k.succ (Fin.succ_ne_zero k),
                    cyclicBarFaceWrapTuple_update_other k.succ (Fin.succ_ne_zero k),
                    cyclicBarFaceWrapTuple_update_other k.succ (Fin.succ_ne_zero k)]
                  exact (PiTensorProduct.tprod R).map_update_add _ _ _ _
      | cast i =>
          simp only [cyclicBarFaceTuple, Fin.lastCases_castSucc]
          cases k using i.succ.succAboveCases with
          | x =>
              rw [cyclicBarFaceNonwrapTuple_update_second,
                cyclicBarFaceNonwrapTuple_update_second,
                cyclicBarFaceNonwrapTuple_update_second, mul_add]
              exact (PiTensorProduct.tprod R).map_update_add _ _ _ _
          | p q =>
              by_cases hq : q = i
              · subst q
                simp only [cyclicBar_succ_succAbove_self]
                rw [cyclicBarFaceNonwrapTuple_update_first,
                  cyclicBarFaceNonwrapTuple_update_first,
                  cyclicBarFaceNonwrapTuple_update_first, add_mul]
                exact (PiTensorProduct.tprod R).map_update_add _ _ _ _
              · rw [cyclicBarFaceNonwrapTuple_update_other i q hq,
                  cyclicBarFaceNonwrapTuple_update_other i q hq,
                  cyclicBarFaceNonwrapTuple_update_other i q hq]
                exact (PiTensorProduct.tprod R).map_update_add _ _ _ _)
    (by
      intro x k r a
      induction i using Fin.lastCases with
      | last =>
          simp only [cyclicBarFaceTuple, Fin.lastCases_last]
          cases k using Fin.lastCases with
          | last =>
              rw [cyclicBarFaceWrapTuple_update_last,
                cyclicBarFaceWrapTuple_update_last, smul_mul_assoc]
              exact (PiTensorProduct.tprod R).map_update_smul _ _ _ _
          | cast k =>
              cases k using Fin.cases with
              | zero =>
                  rw [cyclicBarFaceWrapTuple_update_zero,
                    cyclicBarFaceWrapTuple_update_zero, mul_smul_comm]
                  exact (PiTensorProduct.tprod R).map_update_smul _ _ _ _
              | succ k =>
                  rw [cyclicBarFaceWrapTuple_update_other k.succ (Fin.succ_ne_zero k),
                    cyclicBarFaceWrapTuple_update_other k.succ (Fin.succ_ne_zero k)]
                  exact (PiTensorProduct.tprod R).map_update_smul _ _ _ _
      | cast i =>
          simp only [cyclicBarFaceTuple, Fin.lastCases_castSucc]
          cases k using i.succ.succAboveCases with
          | x =>
              rw [cyclicBarFaceNonwrapTuple_update_second,
                cyclicBarFaceNonwrapTuple_update_second, mul_smul_comm]
              exact (PiTensorProduct.tprod R).map_update_smul _ _ _ _
          | p q =>
              by_cases hq : q = i
              · subst q
                simp only [cyclicBar_succ_succAbove_self]
                rw [cyclicBarFaceNonwrapTuple_update_first,
                  cyclicBarFaceNonwrapTuple_update_first, smul_mul_assoc]
                exact (PiTensorProduct.tprod R).map_update_smul _ _ _ _
              · rw [cyclicBarFaceNonwrapTuple_update_other i q hq,
                  cyclicBarFaceNonwrapTuple_update_other i q hq]
                exact (PiTensorProduct.tprod R).map_update_smul _ _ _ _)

/-- Linear face contraction on tensor powers. -/
def cyclicBarFace {n : ℕ} (i : Fin (n + 2)) :
    CyclicBarTensor R A (n + 1) →ₗ[R] CyclicBarTensor R A n :=
  PiTensorProduct.lift (cyclicBarFaceMultilinear i)

@[simp]
theorem cyclicBarFace_tprod {n : ℕ} (i : Fin (n + 2)) (x : Fin (n + 2) → A) :
    cyclicBarFace (R := R) i (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R (cyclicBarFaceTuple i x) :=
  PiTensorProduct.lift.tprod _

/-- Multilinear unit insertion defining a degeneracy. -/
def cyclicBarDegeneracyMultilinear {n : ℕ} (i : Fin (n + 1)) :
    MultilinearMap R (fun _ : Fin (n + 1) ↦ A) (CyclicBarTensor R A (n + 1)) :=
  MultilinearMap.mk' (fun x ↦ PiTensorProduct.tprod R (cyclicBarDegeneracyTuple i x))
    (by
      intro x k a b
      rw [cyclicBarDegeneracyTuple_update, cyclicBarDegeneracyTuple_update,
        cyclicBarDegeneracyTuple_update]
      exact (PiTensorProduct.tprod R).map_update_add _ _ _ _)
    (by
      intro x k r a
      rw [cyclicBarDegeneracyTuple_update, cyclicBarDegeneracyTuple_update]
      exact (PiTensorProduct.tprod R).map_update_smul _ _ _ _)

/-- Linear degeneracy on tensor powers. -/
def cyclicBarDegeneracy {n : ℕ} (i : Fin (n + 1)) :
    CyclicBarTensor R A n →ₗ[R] CyclicBarTensor R A (n + 1) :=
  PiTensorProduct.lift (cyclicBarDegeneracyMultilinear i)

@[simp]
theorem cyclicBarDegeneracy_tprod {n : ℕ} (i : Fin (n + 1))
    (x : Fin (n + 1) → A) :
    cyclicBarDegeneracy (R := R) i (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R (cyclicBarDegeneracyTuple i x) :=
  PiTensorProduct.lift.tprod _

/-- Linear cyclic rotation on tensor powers. -/
def cyclicBarRotate (n : ℕ) :
    CyclicBarTensor R A n ≃ₗ[R] CyclicBarTensor R A n :=
  PiTensorProduct.reindex R (fun _ : Fin (n + 1) ↦ A) (finRotate (n + 1))

@[simp]
theorem cyclicBarRotate_tprod (n : ℕ) (x : Fin (n + 1) → A) :
    cyclicBarRotate (R := R) (A := A) n (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R (cyclicBarRotateTuple x) := by
  rw [cyclicBarRotate, PiTensorProduct.reindex_tprod]
  rfl

end LinearOperators

end RHTower
end GaloisForLFunctions
