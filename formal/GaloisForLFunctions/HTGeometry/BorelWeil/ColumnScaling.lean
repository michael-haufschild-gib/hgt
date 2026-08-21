import GaloisForLFunctions.HTGeometry.BorelWeil.DetTwist

/-!
# Scaling one column of the generic matrix

To extend a section from `SL(N,k)` to a polynomial section on all matrices one divides a single
column by the determinant.  This file sets up that operation algebraically: `colScaleMat j₀ t` is
the diagonal matrix scaling the `j₀`-th column by `t`, and `scaleCol j₀` is the corresponding
substitution of a formal parameter into the polynomial ring, so that the coefficient of `Tʳ` in
`scaleCol j₀ p` is the part of `p` of degree `r` in the `j₀`-th column.

## Main definitions

* `GaloisForLFunctions.HTGeometry.BorelWeil.colScaleMat`
* `GaloisForLFunctions.HTGeometry.BorelWeil.scaleCol`

## Main results

* `matEval_mul_colScaleMat` — evaluating after scaling a column is evaluating the formal scaling.
* `sum_scaleCol_coeff` — the parts of `p` sum back to `p`.
-/

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k]

/-- Evaluation at a matrix, as a ring homomorphism. -/
noncomputable def matEvalHom (g : Matrix (Fin N) (Fin N) k) :
    MvPolynomial (Fin N × Fin N) k →+* k :=
  MvPolynomial.eval (fun ij : Fin N × Fin N => g ij.1 ij.2)

theorem matEvalHom_apply (g : Matrix (Fin N) (Fin N) k) (p : MvPolynomial (Fin N × Fin N) k) :
    matEvalHom g p = matEval g p := rfl

/-- The diagonal matrix that scales the `j₀`-th column by `t`. -/
def colScaleMat (j₀ : Fin N) (t : k) : Matrix (Fin N) (Fin N) k :=
  Matrix.diagonal (fun i => if i = j₀ then t else 1)

@[simp] theorem det_colScaleMat (j₀ : Fin N) (t : k) : (colScaleMat j₀ t).det = t := by
  classical
  rw [colScaleMat, Matrix.det_diagonal, Finset.prod_ite_eq' Finset.univ j₀ (fun _ => t)]
  simp

theorem colScaleMat_blockTriangular (j₀ : Fin N) (t : k) :
    (colScaleMat j₀ t).BlockTriangular id := by
  intro i j h
  exact Matrix.diagonal_apply_ne _ (ne_of_gt h)

theorem colScaleMat_apply_diag (j₀ : Fin N) (t : k) (i : Fin N) :
    colScaleMat j₀ t i i = if i = j₀ then t else 1 := by
  rw [colScaleMat, Matrix.diagonal_apply_eq]

theorem mul_colScaleMat_apply (j₀ : Fin N) (t : k) (g : Matrix (Fin N) (Fin N) k) (i j : Fin N) :
    (g * colScaleMat j₀ t) i j = g i j * (if j = j₀ then t else 1) := by
  rw [colScaleMat, Matrix.mul_diagonal]

/-- Formal scaling of the `j₀`-th column by the polynomial parameter. -/
noncomputable def scaleCol (j₀ : Fin N) :
    MvPolynomial (Fin N × Fin N) k →ₐ[k] Polynomial (MvPolynomial (Fin N × Fin N) k) :=
  MvPolynomial.aeval fun ij : Fin N × Fin N =>
    if ij.2 = j₀ then Polynomial.X * Polynomial.C (MvPolynomial.X ij)
    else Polynomial.C (MvPolynomial.X ij)

/-- Evaluating after scaling a column is the formal scaling evaluated at the scalar. -/
theorem matEval_mul_colScaleMat (j₀ : Fin N) (g : Matrix (Fin N) (Fin N) k) (t : k)
    (p : MvPolynomial (Fin N × Fin N) k) :
    matEval (g * colScaleMat j₀ t) p
      = Polynomial.eval₂ (matEvalHom g) t (scaleCol j₀ p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [scaleCol, MvPolynomial.aeval_C]
    simp [matEval, matEvalHom]
  | add p q hp hq =>
    rw [map_add, Polynomial.eval₂_add, matEval_add, hp, hq]
  | mul_X p ij hp =>
    rw [map_mul, Polynomial.eval₂_mul, matEval_mul, hp]
    congr 1
    rw [scaleCol, MvPolynomial.aeval_X]
    by_cases h : ij.2 = j₀
    · rw [if_pos h, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C]
      rw [matEval_X, mul_colScaleMat_apply, if_pos h, matEvalHom, MvPolynomial.eval_X, mul_comm]
    · rw [if_neg h, Polynomial.eval₂_C]
      rw [matEval_X, mul_colScaleMat_apply, if_neg h, matEvalHom, MvPolynomial.eval_X, mul_one]

theorem eval_one_scaleCol (j₀ : Fin N) (p : MvPolynomial (Fin N × Fin N) k) :
    Polynomial.eval (1 : MvPolynomial (Fin N × Fin N) k) (scaleCol j₀ p) = p := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [scaleCol, MvPolynomial.aeval_C]; simp
  | add p q hp hq => rw [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p ij hp =>
    rw [map_mul, Polynomial.eval_mul, hp]
    congr 1
    rw [scaleCol, MvPolynomial.aeval_X]
    by_cases h : ij.2 = j₀
    · rw [if_pos h]; simp
    · rw [if_neg h]; simp

/-- The parts of `p` in the `j₀`-th column degree sum back to `p`. -/
theorem sum_scaleCol_coeff (j₀ : Fin N) (p : MvPolynomial (Fin N × Fin N) k) :
    ∑ r ∈ Finset.range ((scaleCol j₀ p).natDegree + 1), (scaleCol j₀ p).coeff r = p := by
  calc ∑ r ∈ Finset.range ((scaleCol j₀ p).natDegree + 1), (scaleCol j₀ p).coeff r
      = ∑ r ∈ Finset.range ((scaleCol j₀ p).natDegree + 1), (scaleCol j₀ p).coeff r * 1 ^ r :=
        Finset.sum_congr rfl fun r _ => by rw [one_pow, mul_one]
    _ = Polynomial.eval (1 : MvPolynomial (Fin N × Fin N) k) (scaleCol j₀ p) :=
        (Polynomial.eval_eq_sum_range _).symm
    _ = p := eval_one_scaleCol j₀ p

end GaloisForLFunctions.HTGeometry.BorelWeil
