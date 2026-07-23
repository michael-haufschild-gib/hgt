import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Finite full-matrix cyclic-reader rigidity

Every real linear cyclic reader on a finite full matrix algebra is a scalar multiple of ordinary
trace.  No positivity, continuity, normalization, or nondegeneracy is required.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

/-- A linear reader is cyclic when it cannot distinguish `A B` from `B A`. -/
def MatrixCyclicReader
    {n : Type*} [Fintype n]
    (Φ : Matrix n n ℝ →ₗ[ℝ] ℝ) : Prop :=
  ∀ A B, Φ (A * B) = Φ (B * A)

/-- **Finite full-matrix cyclic-reader rigidity.**  Cyclicity forces scalar ordinary trace. -/
theorem matrixCyclicReader_eq_smul_trace
    {n : Type*} [Fintype n] [DecidableEq n]
    (Φ : Matrix n n ℝ →ₗ[ℝ] ℝ) (hΦ : MatrixCyclicReader Φ) (i0 : n) :
    Φ = Φ (Matrix.single i0 i0 1) • Matrix.traceLinearMap n ℝ ℝ := by
  apply (Matrix.stdBasis ℝ n n).ext
  rintro ⟨i, j⟩
  rw [Matrix.stdBasis_eq_single]
  by_cases hij : i = j
  · subst j
    have hdiag := hΦ (Matrix.single i i0 1) (Matrix.single i0 i 1)
    rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same] at hdiag
    simp only [one_mul] at hdiag
    simp [Matrix.traceLinearMap_apply, Matrix.trace, hdiag]
  · have hoff := hΦ (Matrix.single i i 1) (Matrix.single i j 1)
    have hzero :
        Matrix.single i j (1 : ℝ) * Matrix.single i i 1 = 0 := by
      exact Matrix.single_mul_single_of_ne 1 i j i (Ne.symm hij) 1
    rw [Matrix.single_mul_single_same, one_mul, hzero, map_zero] at hoff
    simp [Matrix.traceLinearMap_apply, Matrix.trace, hij, hoff]

theorem matrixCyclicReader_apply_eq_corner_mul_trace
    {n : Type*} [Fintype n] [DecidableEq n]
    (Φ : Matrix n n ℝ →ₗ[ℝ] ℝ) (hΦ : MatrixCyclicReader Φ)
    (i0 : n) (A : Matrix n n ℝ) :
    Φ A = Φ (Matrix.single i0 i0 1) * Matrix.trace A := by
  rw [matrixCyclicReader_eq_smul_trace Φ hΦ i0]
  simp [Matrix.traceLinearMap_apply]

end GaloisForLFunctions.HTGeometry
