import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic

/-!
# Orthogonal gauge classification from a purity Gram law

Equality of the Euclidean purity kernels of two full square frames is equivalent to an
orthogonal change of frame.  This is the finite-dimensional algebraic classifier used by the
simplex Bernstein purity theorem.
-/

namespace HTGeometry

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A real square matrix is orthogonal when its columns have identity Gram matrix. -/
def IsOrthogonalGauge (O : Matrix n n ℝ) : Prop :=
  O.transpose * O = 1

/-- Multiplying a frame on the left by an orthogonal gauge preserves its column Gram matrix. -/
theorem transpose_mul_self_eq_of_orthogonal_mul
    {A B O : Matrix n n ℝ} (hO : IsOrthogonalGauge O) (hA : A = O * B) :
    A.transpose * A = B.transpose * B := by
  rw [hA, Matrix.transpose_mul]
  calc
    B.transpose * O.transpose * (O * B) =
        B.transpose * ((O.transpose * O) * B) := by
      simp only [Matrix.mul_assoc]
    _ = B.transpose * B := by rw [hO, Matrix.one_mul]

/-- **Purity orthogonal-gauge classification.**  Two full real square frames have the same
column Gram matrix exactly when one is a unique orthogonal left gauge of the other. -/
theorem gram_eq_iff_existsUnique_orthogonalGauge_mul
    (A B : Matrix n n ℝ) (hB : IsUnit B.det) :
    A.transpose * A = B.transpose * B ↔
      ∃! O : Matrix n n ℝ, IsOrthogonalGauge O ∧ A = O * B := by
  constructor
  · intro hGram
    let O : Matrix n n ℝ := A * B⁻¹
    have hBt : IsUnit B.transpose.det := by
      simpa using hB
    have hOrth : IsOrthogonalGauge O := by
      rw [IsOrthogonalGauge]
      dsimp only [O]
      rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
      calc
        B.transpose⁻¹ * A.transpose * (A * B⁻¹) =
            B.transpose⁻¹ * (A.transpose * A) * B⁻¹ := by
              simp only [Matrix.mul_assoc]
        _ = B.transpose⁻¹ * (B.transpose * B) * B⁻¹ := by rw [hGram]
        _ = (B.transpose⁻¹ * B.transpose) * (B * B⁻¹) := by
              simp only [Matrix.mul_assoc]
        _ = 1 := by
              rw [Matrix.nonsing_inv_mul _ hBt, Matrix.mul_nonsing_inv _ hB]
              simp
    have hMul : A = O * B := by
      dsimp only [O]
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hB, Matrix.mul_one]
    refine ⟨O, ⟨hOrth, hMul⟩, ?_⟩
    intro P hP
    calc
      P = P * 1 := by simp
      _ = P * (B * B⁻¹) := by rw [Matrix.mul_nonsing_inv _ hB]
      _ = (P * B) * B⁻¹ := by rw [Matrix.mul_assoc]
      _ = A * B⁻¹ := by rw [← hP.2]
      _ = O := rfl
  · rintro ⟨O, ⟨hO, hA⟩, _huniq⟩
    exact transpose_mul_self_eq_of_orthogonal_mul hO hA

/-- The unique orthogonal gauge supplied by equal Gram matrices is explicitly `A * B⁻¹`. -/
theorem orthogonalGauge_eq_mul_nonsing_inv
    {A B O : Matrix n n ℝ} (hB : IsUnit B.det)
    (_hO : IsOrthogonalGauge O) (hA : A = O * B) :
    O = A * B⁻¹ := by
  calc
    O = O * 1 := by simp
    _ = O * (B * B⁻¹) := by rw [Matrix.mul_nonsing_inv _ hB]
    _ = (O * B) * B⁻¹ := by rw [Matrix.mul_assoc]
    _ = A * B⁻¹ := by rw [← hA]

end

end HTGeometry
