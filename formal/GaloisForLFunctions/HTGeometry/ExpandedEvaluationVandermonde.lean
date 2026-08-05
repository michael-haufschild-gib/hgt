import GaloisForLFunctions.HTGeometry.EvaluationRankDefectTopology
import Mathlib.LinearAlgebra.Vandermonde

/-!
# The expanded evaluation matrix of a single monomial is a row-scaled Vandermonde

The translation-rank genericity laws consume a full-rank hypothesis on the expanded differential
evaluation matrix: injectivity of its `mulVec`.  Nothing produced it, and for a general exponent
family it is a confluent-Vandermonde nondegeneracy that the corpus does not yet have.

For a **single** exponent the matrix factors completely.  Its `(b, d)` entry is the `d`-th power of
the row node at `b` times the value of one fixed monomial at `b`, so the matrix is the Vandermonde
matrix of the nodes scaled row by row.  Its determinant is therefore the product of the monomial
values times the Vandermonde product, and it is invertible exactly when the nodes are pairwise
distinct and no monomial value vanishes.

This is the base case of the missing full-rank statement; the open case is two or more exponents,
where the columns interleave and the determinant is no longer a product.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

/-- The monomial value carried by one row of the expanded evaluation matrix. -/
noncomputable def expandedMonomialValue {row : Type*} {n : ℕ}
    (e : Fin n →₀ ℕ) (y : row × Fin n → ℂ) (b : row) : ℂ :=
  MvPolynomial.eval (fun k => y (b, k)) (MvPolynomial.monomial e 1)

/-- The single-exponent expanded evaluation matrix, as a square matrix on the row nodes. -/
noncomputable def singleExponentEvaluationMatrix {q n : ℕ} (z : Fin (q + 1) → ℂ)
    (e : Fin n →₀ ℕ) (y : Fin (q + 1) × Fin n → ℂ) :
    Matrix (Fin (q + 1)) (Fin (q + 1)) ℂ :=
  Matrix.of fun b d => z b ^ (d : ℕ) * expandedMonomialValue e y b

/-- **The single-exponent matrix is the Vandermonde matrix scaled row by row.** -/
theorem singleExponentEvaluationMatrix_eq {q n : ℕ} (z : Fin (q + 1) → ℂ)
    (e : Fin n →₀ ℕ) (y : Fin (q + 1) × Fin n → ℂ) :
    singleExponentEvaluationMatrix z e y =
      Matrix.diagonal (expandedMonomialValue e y) * Matrix.vandermonde z := by
  ext b d
  rw [Matrix.diagonal_mul, Matrix.vandermonde_apply, singleExponentEvaluationMatrix]
  simp only [Matrix.of_apply]
  ring

/-- **Its determinant is the product of the monomial values times the Vandermonde product.** -/
theorem det_singleExponentEvaluationMatrix {q n : ℕ} (z : Fin (q + 1) → ℂ)
    (e : Fin n →₀ ℕ) (y : Fin (q + 1) × Fin n → ℂ) :
    (singleExponentEvaluationMatrix z e y).det =
      (∏ b, expandedMonomialValue e y b) * (Matrix.vandermonde z).det := by
  rw [singleExponentEvaluationMatrix_eq, Matrix.det_mul, Matrix.det_diagonal]

/-- **Distinct nodes and nonvanishing monomial values make it invertible.** -/
theorem isUnit_singleExponentEvaluationMatrix {q n : ℕ} {z : Fin (q + 1) → ℂ}
    (hz : Function.Injective z) {e : Fin n →₀ ℕ} {y : Fin (q + 1) × Fin n → ℂ}
    (hy : ∀ b, expandedMonomialValue e y b ≠ 0) :
    IsUnit (singleExponentEvaluationMatrix z e y) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, det_singleExponentEvaluationMatrix]
  refine mul_ne_zero ?_ (Matrix.det_vandermonde_ne_zero_iff.mpr hz)
  exact Finset.prod_ne_zero_iff.mpr fun b _ => hy b

/-- The expanded evaluation matrix at a single exponent has exactly the entries of the square
model. -/
theorem expandedDifferentialEvaluationMatrix_unit_apply {q n : ℕ} (z : Fin (q + 1) → ℂ)
    (exponent : Unit → (Fin n →₀ ℕ)) (y : Fin (q + 1) × Fin n → ℂ)
    (b : Fin (q + 1)) (d : Fin (q + 1)) :
    expandedDifferentialEvaluationMatrix q n z exponent y b ((), d) =
      singleExponentEvaluationMatrix z (exponent ()) y b d := rfl

/-- **Full rank of the single-exponent expanded evaluation matrix.**  With distinct row nodes and
nonvanishing monomial values, its `mulVec` is injective. -/
theorem mulVec_injective_expandedDifferentialEvaluationMatrix_unit {q n : ℕ}
    {z : Fin (q + 1) → ℂ} (hz : Function.Injective z)
    {exponent : Unit → (Fin n →₀ ℕ)} {y : Fin (q + 1) × Fin n → ℂ}
    (hy : ∀ b, expandedMonomialValue (exponent ()) y b ≠ 0) :
    Function.Injective
      (expandedDifferentialEvaluationMatrix q n z exponent y).mulVec := by
  classical
  have hsquare := Matrix.mulVec_injective_of_isUnit (isUnit_singleExponentEvaluationMatrix hz hy)
  intro u v huv
  have hcol : ∀ w : Unit × Fin (q + 1) → ℂ,
      (expandedDifferentialEvaluationMatrix q n z exponent y).mulVec w =
        (singleExponentEvaluationMatrix z (exponent ()) y).mulVec (fun d => w ((), d)) := by
    intro w
    funext b
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Finset.univ_unique,
      Finset.sum_singleton]
    rfl
  rw [hcol u, hcol v] at huv
  have hres := hsquare huv
  funext c
  obtain ⟨a, d⟩ := c
  cases a
  exact congrFun hres d

end GaloisForLFunctions.HTGeometry
