import GaloisForLFunctions.HTGeometry.BorelWeil.LUDecomposition

/-!
# The highest weight of the Borel–Weil module

The minor product `bwPoly m` is an eigenvector for left translation by the diagonal torus, with
eigenvalue the character `weightOfMult m`.  Together with the uniqueness of the lower unitriangular
invariant line, this identifies `weightOfMult m` as the **highest weight** of the Borel–Weil
module.

## Main results

* `prod_charFactor` — the double-product identity behind the weight computation.
* `substLeft_diagonal_bwPoly` — the torus eigenvalue of the minor product.
-/

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k]

theorem prod_charFactor (m : Fin N → ℕ) (b : Fin N → k) :
    ∏ j : Fin N, (∏ i : Fin N, (if (i : ℕ) < (j : ℕ) + 1 then b i else 1)) ^ (m j)
      = ∏ i : Fin N, (b i) ^ (weightOfMult m i) := by
  classical
  have hstep : ∀ j : Fin N, (∏ i : Fin N, (if (i : ℕ) < (j : ℕ) + 1 then b i else 1))
      = ∏ i : Fin N, (if i ≤ j then b i else 1) := by
    intro j
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases h : i ≤ j
    · rw [if_pos (Nat.lt_succ_of_le (Fin.le_def.mp h)), if_pos h]
    · rw [if_neg fun hcon => h (Fin.le_def.mpr (Nat.lt_succ_iff.mp hcon)), if_neg h]
  rw [Finset.prod_congr rfl fun j (_ : j ∈ Finset.univ) => congrArg (· ^ m j) (hstep j)]
  rw [Finset.prod_congr rfl fun j (_ : j ∈ Finset.univ) =>
    (Finset.prod_pow Finset.univ (m j) (fun i : Fin N => (if i ≤ j then b i else 1))).symm]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hpt : ∀ j : Fin N, (if i ≤ j then b i else 1) ^ (m j)
      = if i ≤ j then (b i) ^ (m j) else 1 := by
    intro j
    by_cases h : i ≤ j
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, one_pow]
  rw [Finset.prod_congr rfl fun j (_ : j ∈ Finset.univ) => hpt j, ← Finset.prod_filter,
    Finset.prod_pow_eq_pow_sum, weightOfMult]

theorem blockTriangular_diagonal' (t : Fin N → k) :
    (Matrix.diagonal t).BlockTriangular id := by
  intro i j h
  exact Matrix.diagonal_apply_ne _ (ne_of_gt h)

theorem leadingMinorMat_diagonal_mul (j : ℕ) (t : Fin N → k) (g : Matrix (Fin N) (Fin N) k) :
    leadingMinorMat j (Matrix.diagonal t * g)
      = (∏ i : Fin N, (if (i : ℕ) < j then t i else 1)) * leadingMinorMat j g := by
  have hlow : ∀ i i' : Fin N, i < i' → Matrix.diagonal t i i' = 0 :=
    fun i i' h => Matrix.diagonal_apply_ne _ (ne_of_lt h)
  rw [leadingMinorMat, truncate_mul_left j hlow g, Matrix.det_mul,
    det_truncate_of_blockTriangular (blockTriangular_diagonal' t), leadingMinorMat]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by
    by_cases h : (i : ℕ) < j
    · rw [if_pos h, if_pos h, Matrix.diagonal_apply_eq]
    · rw [if_neg h, if_neg h]

theorem bwVectorMat_diagonal_mul (m : Fin N → ℕ) (t : Fin N → k)
    (g : Matrix (Fin N) (Fin N) k) :
    bwVectorMat m (Matrix.diagonal t * g)
      = (∏ i : Fin N, (t i) ^ (weightOfMult m i)) * bwVectorMat m g := by
  classical
  rw [bwVectorMat, bwVectorMat]
  have hstep : ∀ j : Fin N, (leadingMinorMat ((j : ℕ) + 1) (Matrix.diagonal t * g)) ^ (m j)
      = (∏ i : Fin N, (if (i : ℕ) < (j : ℕ) + 1 then t i else 1)) ^ (m j)
        * (leadingMinorMat ((j : ℕ) + 1) g) ^ (m j) := by
    intro j
    rw [leadingMinorMat_diagonal_mul, mul_pow]
  rw [Finset.prod_congr rfl fun j (_ : j ∈ Finset.univ) => hstep j, Finset.prod_mul_distrib,
    prod_charFactor]

/-- **The torus eigenvalue of the highest weight vector.** -/
theorem substLeft_diagonal_bwPoly [Infinite k] (m : Fin N → ℕ) (t : Fin N → k) :
    substLeft (Matrix.diagonal t) (bwPoly m k)
      = (∏ i : Fin N, (t i) ^ (weightOfMult m i)) • bwPoly m k := by
  refine matEval_injective fun g => ?_
  rw [matEval_substLeft, matEval_smul, matEval_bwPoly, matEval_bwPoly,
    bwVectorMat_diagonal_mul]

end GaloisForLFunctions.HTGeometry.BorelWeil
