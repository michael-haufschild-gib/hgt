/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicAlgebra
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Weighted companion matrices for cyclic algebras

The weighted cycle matrix advances each standard basis vector of `R^(n+1)` by one position and
sends the final basis vector to the first, weighted by `a`. It is the matrix component of the
faithful companion representation required for arbitrary-degree cyclic Galois normal forms.
The Galois-diagonal coefficient action and the resulting faithfulness theorem remain separate.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

variable {R : Type*} [CommSemiring R]

/-- The weighted cyclic companion matrix with final-to-first weight `a`. -/
noncomputable def cyclicCompanionMatrix (n : ℕ) (a : R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun i j => Fin.lastCases (if i = 0 then a else 0)
    (fun j' => if i = j'.succ then 1 else 0) j

/-- The companion matrix advances every non-final standard basis vector. -/
theorem cyclicCompanionMatrix_mulVec_single_castSucc (n : ℕ) (a x : R) (j : Fin n) :
    Matrix.mulVec (cyclicCompanionMatrix n a) (Pi.single j.castSucc x) = Pi.single j.succ x := by
  classical
  funext i
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single j.castSucc]
  · simp [cyclicCompanionMatrix, Fin.lastCases_castSucc]
    rw [Pi.single_apply]
  · intro k _ hkj
    simp [hkj]
  · simp

/-- The companion matrix sends the final standard basis vector to the first, weighted by `a`. -/
theorem cyclicCompanionMatrix_mulVec_single_last (n : ℕ) (a x : R) :
    Matrix.mulVec (cyclicCompanionMatrix n a) (Pi.single (Fin.last n) x) =
      Pi.single 0 (a * x) := by
  classical
  funext i
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (Fin.last n)]
  · simp [cyclicCompanionMatrix, Fin.lastCases_last]
    rw [Pi.single_apply]
  · intro k _ hkj
    simp [hkj]
  · simp

/-- Matrix multiplication by the weighted companion matrix is the explicit cyclic shift of a
coordinate vector, with the final coordinate moved to the first position and multiplied by `a`. -/
theorem cyclicCompanionMatrix_mulVec (n : ℕ) (a : R) (v : Fin (n + 1) → R) :
    Matrix.mulVec (cyclicCompanionMatrix n a) v =
      Fin.cons (a * v (Fin.last n)) (fun j => v j.castSucc) := by
  classical
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Matrix.mulVec, dotProduct]
    rw [Fin.sum_univ_castSucc]
    have hzero (j : Fin n) : (0 : Fin (n + 1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
    simp [cyclicCompanionMatrix, Fin.lastCases_castSucc, Fin.lastCases_last, hzero]
  · simp only [Matrix.mulVec, dotProduct]
    rw [Fin.sum_univ_castSucc]
    rw [Finset.sum_eq_single j]
    · simp [cyclicCompanionMatrix, Fin.lastCases_castSucc, Fin.lastCases_last]
    · intro k _ hkj
      simp [cyclicCompanionMatrix, Fin.lastCases_castSucc, hkj.symm]
    · simp

end GaloisForLFunctions.HTGeometry.ABHN
