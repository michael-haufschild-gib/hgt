import GaloisForLFunctions.HTGeometry.ComplexUnipotentInverseBound

/-!
# Hermitian Siegel sets in complex Jacobi coordinates

Positive-definite Hermitian matrices admit upper-unipotent Jacobi coordinates with a genuinely
real positive diagonal.  This module packages those coordinates and the diagonal-ratio iteration
needed by complex reduction theory.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped ComplexOrder

variable {n : ℕ}

/-- Complex upper-unipotent Jacobi data with its positive diagonal stored over `ℝ`. -/
structure ComplexJacobiData (n : ℕ) where
  U : Matrix (Fin n) (Fin n) ℂ
  d : Fin n → ℝ
  pos : ∀ i, 0 < d i
  upper : ∀ i j, j < i → U i j = 0
  unit : ∀ i, U i i = 1

/-- Hermitian form attached to complex Jacobi data. -/
def ComplexJacobiData.form (J : ComplexJacobiData n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.conjTranspose J.U * Matrix.diagonal (fun i => (J.d i : ℂ)) * J.U

/-- Every positive-definite Hermitian form has complex Jacobi data with a real positive diagonal. -/
theorem exists_complexJacobiData {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    ∃ J : ComplexJacobiData n, J.form = A := by
  obtain ⟨U, e, hepos, hupper, hunit, hform⟩ := exists_complex_jacobi_decomposition hA
  let d : Fin n → ℝ := fun i => (e i).re
  have hde : ∀ i, (d i : ℂ) = e i := by
    intro i
    apply Complex.ext
    · rfl
    · simpa [d] using (Complex.lt_def.1 (hepos i)).2
  refine ⟨⟨U, d, ?_, hupper, hunit⟩, ?_⟩
  · intro i
    exact (Complex.lt_def.1 (hepos i)).1
  · change U.conjTranspose * Matrix.diagonal (fun i => (d i : ℂ)) * U = A
    rw [hform]
    rw [show (fun i => (d i : ℂ)) = e from funext hde]

/-- Complex Siegel bounds: controlled adjacent diagonal growth and bounded upper factor. -/
def ComplexJacobiData.IsSiegel (J : ComplexJacobiData n) (t u : ℝ) : Prop :=
  (∀ i j : Fin n, (i : ℕ) + 1 = (j : ℕ) → J.d i ≤ t * J.d j) ∧
    (∀ i j, ‖J.U i j‖ ≤ u)

/-- An upper-unipotent complex Jacobi factor has determinant one. -/
theorem ComplexJacobiData.det_eq_one (J : ComplexJacobiData n) : J.U.det = 1 :=
  complex_det_eq_one_of_unipotent J.upper J.unit

/-- The inverse of an upper-unipotent complex Jacobi factor is upper triangular. -/
theorem ComplexJacobiData.inv_upper (J : ComplexJacobiData n) :
    ∀ i j : Fin n, j < i → J.U⁻¹ i j = 0 := by
  haveI : Invertible J.U := Matrix.invertibleOfIsUnitDet _
    (by rw [J.det_eq_one]; exact isUnit_one)
  have hbt : J.U.BlockTriangular id := fun i j hij => J.upper i j hij
  exact fun i j hij => Matrix.blockTriangular_inv_of_blockTriangular hbt hij

/-- Iterate the adjacent complex Siegel diagonal bound along an exact chain. -/
theorem ComplexJacobiData.d_le_pow (J : ComplexJacobiData n) {t u : ℝ}
    (ht : 1 ≤ t) (hS : J.IsSiegel t u) :
    ∀ k : ℕ, ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + k → J.d i ≤ t ^ k * J.d j := by
  intro k
  induction k with
  | zero =>
      intro i j hij
      have : i = j := Fin.ext (by omega)
      rw [this, pow_zero, one_mul]
  | succ k ih =>
      intro i j hij
      have hlt : (i : ℕ) + 1 < n := by
        have := j.isLt
        omega
      set i' : Fin n := ⟨(i : ℕ) + 1, hlt⟩ with hi'
      have hstep : J.d i ≤ t * J.d i' := hS.1 i i' rfl
      have hrec : J.d i' ≤ t ^ k * J.d j := ih i' j (by simp only [hi']; omega)
      have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
      calc
        J.d i ≤ t * J.d i' := hstep
        _ ≤ t * (t ^ k * J.d j) := mul_le_mul_of_nonneg_left hrec ht0
        _ = t ^ (k + 1) * J.d j := by ring

/-- A single dimension power bounds every ordered pair of complex Jacobi diagonals. -/
theorem ComplexJacobiData.d_le_pow_n (J : ComplexJacobiData n) {t u : ℝ}
    (ht : 1 ≤ t) (hS : J.IsSiegel t u)
    {i j : Fin n} (hij : (i : ℕ) ≤ (j : ℕ)) :
    J.d i ≤ t ^ n * J.d j := by
  have h0 := J.d_le_pow ht hS ((j : ℕ) - (i : ℕ)) i j (by omega)
  refine h0.trans (mul_le_mul_of_nonneg_right ?_ (J.pos j).le)
  refine pow_le_pow_right₀ ht ?_
  have := j.isLt
  omega

end GaloisForLFunctions.HTGeometry
