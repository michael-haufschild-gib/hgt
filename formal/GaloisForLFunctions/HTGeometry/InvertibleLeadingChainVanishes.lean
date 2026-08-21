import GaloisForLFunctions.HTGeometry.ShiftedTopMatrix
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# An invertible operator matrix whose leading chain dies

The exact-degree branch of the phase dichotomy applies when the accumulated leading matrices of a
twisted chain never vanish.  It is natural to hope that invertibility over the operator ring already
forces that — for `2 × 2` matrices it very nearly does.  It does not.

The companion matrix of `t³ + ∂·t + 1` is invertible over `K[∂;δ]`, with an explicit inverse, and
its leading matrix at degree one has a single nonzero entry lying in the last column, so its square
is zero: the accumulated leading chain dies at the second step.  Its Newton polygon has vertices
`(0,0)`, `(1,−1)`, `(3,0)`, so the root valuations are `1` and `−1/2` twice — a genuinely
non-integral slope, which no integer shear can see.

So the restart step of the phase analysis is unavoidable, and the vanishing of the accumulated
leading chain is compatible with invertibility.

* `partialElt`, `degree_partialElt`, `coeff_partialElt`;
* `companionMatrix`, `companionInverse`, `companionMatrix_mul_inverse`,
  `companionInverse_mul_matrix`;
* `matDeg_companionMatrix`, `topCoeffMatrix_companionMatrix`;
* `topCoeffMatrix_companionMatrix_sq` — **the accumulated leading chain dies at the second step**;
* `chainProdK_companion_eq_zero`.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]

/-- The operator `∂` itself. -/
def partialElt : DiffOp K := mono 1 1

@[simp] theorem coeff_partialElt_one : coeff (partialElt : DiffOp K) 1 = 1 := coeff_mono_self 1 1

theorem coeff_partialElt_of_ne {m : ℕ} (h : m ≠ 1) : coeff (partialElt : DiffOp K) m = 0 :=
  coeff_mono_of_ne 1 (fun hc => h hc.symm)

theorem degree_partialElt : degree (partialElt : DiffOp K) = 1 := by
  refine le_antisymm (degree_mono_le 1 1) ?_
  exact le_degree (by rw [coeff_partialElt_one]; exact one_ne_zero)

/-- The companion matrix of `t³ + ∂·t + 1`. -/
def companionMatrix : Matrix (Fin 3) (Fin 3) (DiffOp K) :=
  !![0, 0, -1; 1, 0, -partialElt; 0, 1, 0]

/-- Its inverse. -/
def companionInverse : Matrix (Fin 3) (Fin 3) (DiffOp K) :=
  !![-partialElt, 1, 0; 0, 0, 1; -1, 0, 0]

theorem companionMatrix_mul_inverse :
    (companionMatrix : Matrix (Fin 3) (Fin 3) (DiffOp K)) * companionInverse = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [companionMatrix, companionInverse, Matrix.mul_apply, Fin.sum_univ_three]

theorem companionInverse_mul_matrix :
    (companionInverse : Matrix (Fin 3) (Fin 3) (DiffOp K)) * companionMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [companionMatrix, companionInverse, Matrix.mul_apply, Fin.sum_univ_three]

theorem matDeg_companionMatrix :
    matDeg (companionMatrix : Matrix (Fin 3) (Fin 3) (DiffOp K)) = 1 := by
  refine le_antisymm (matDeg_le fun i j => ?_) ?_
  · fin_cases i <;> fin_cases j <;>
      simp [companionMatrix, degree_zero, degree_one, degree_neg, degree_partialElt]
  · have h : degree ((companionMatrix : Matrix (Fin 3) (Fin 3) (DiffOp K)) 1 2) = 1 := by
      show degree (-(partialElt : DiffOp K)) = 1
      rw [degree_neg, degree_partialElt]
    rw [← h]
    exact degree_le_matDeg _ 1 2

theorem topCoeffMatrix_companionMatrix :
    topCoeffMatrix (companionMatrix : Matrix (Fin 3) (Fin 3) (DiffOp K)) 1
      = !![0, 0, 0; 0, 0, -1; 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [companionMatrix, topCoeffMatrix, one_def, coeff_mono_of_ne]

/-- **The accumulated leading chain dies at the second step**, although the matrix is invertible
over the operator ring. -/
theorem topCoeffMatrix_companionMatrix_sq :
    topCoeffMatrix (companionMatrix : Matrix (Fin 3) (Fin 3) (DiffOp K)) 1
        * topCoeffMatrix (companionMatrix : Matrix (Fin 3) (Fin 3) (DiffOp K)) 1 = 0 := by
  rw [topCoeffMatrix_companionMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem chainProdK_companion_eq_zero :
    chainProdK (fun _ : ℕ =>
      topCoeffMatrix (companionMatrix : Matrix (Fin 3) (Fin 3) (DiffOp K)) 1) 2 = 0 := by
  rw [chainProdK, chainProdK, chainProdK, one_mul, topCoeffMatrix_companionMatrix_sq]

end

end DiffOp

end GaloisForLFunctions.HTGeometry
