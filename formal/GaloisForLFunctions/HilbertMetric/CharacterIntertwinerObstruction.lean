import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Character obstruction to invertible intertwiners

This file isolates the source-independent linear-algebra obstruction used by the exceptional
history-interface programme. An invertible intertwiner conjugates the two action matrices, so their
characters agree. Consequently one group element with different traces rules out every invertible
linear interface.
-/

open Matrix

namespace GaloisForLFunctions.HilbertMetric

variable {K ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι]

/-- Action matrices joined by an invertible intertwiner have equal traces. -/
theorem trace_eq_of_invertible_intertwiner
    (A B : Matrix ι ι K) (P : (Matrix ι ι K)ˣ)
    (hP : A * (P : Matrix ι ι K) = (P : Matrix ι ι K) * B) :
    Matrix.trace A = Matrix.trace B := by
  have hconj : (↑P⁻¹ : Matrix ι ι K) * A * (P : Matrix ι ι K) = B := by
    calc
      (↑P⁻¹ : Matrix ι ι K) * A * (P : Matrix ι ι K) =
          (↑P⁻¹ : Matrix ι ι K) * (A * (P : Matrix ι ι K)) := by
            rw [Matrix.mul_assoc]
      _ = (↑P⁻¹ : Matrix ι ι K) * ((P : Matrix ι ι K) * B) := by rw [hP]
      _ = ((↑P⁻¹ : Matrix ι ι K) * (P : Matrix ι ι K)) * B := by
            rw [Matrix.mul_assoc]
      _ = B := by simp
  calc
    Matrix.trace A =
        Matrix.trace ((↑P⁻¹ : Matrix ι ι K) * A * (P : Matrix ι ι K)) :=
      (Matrix.trace_units_conj' P A).symm
    _ = Matrix.trace B := by rw [hconj]

/-- A character mismatch at one element rules out an invertible linear intertwiner. -/
theorem no_invertible_intertwiner_of_trace_ne
    (A B : Matrix ι ι K) (htrace : Matrix.trace A ≠ Matrix.trace B) :
    ¬ ∃ P : (Matrix ι ι K)ˣ,
      A * (P : Matrix ι ι K) = (P : Matrix ι ι K) * B := by
  rintro ⟨P, hP⟩
  exact htrace (trace_eq_of_invertible_intertwiner A B P hP)

end GaloisForLFunctions.HilbertMetric
