import GaloisForLFunctions.HTGeometry.DifferentialJacobiFormula
import GaloisForLFunctions.HTGeometry.MatrixWignerSmithDifferentialMatroid

/-!
# The central clock of the Wigner--Smith connection

Jacobi's formula identifies the trace of the algebraic Wigner--Smith matrix with the logarithmic
derivative of the determinant of the scattering matrix:

```
tr Q = -i · (det S)′ / det S.
```

The trace is therefore the determinant clock alone; the traceless part carries the relative-channel
information, and it is invariant under scalar dressing.  Together these separate the central sector
from the projective sector.
-/

open scoped Differential
open Matrix

namespace GaloisForLFunctions.HTGeometry

universe u

/-- The entrywise derivative used by the Wigner--Smith connection is the entrywise derivative of
`DifferentialJacobiFormula`. -/
theorem matrixDifferential_eq_matrixDeriv {E : Type u} [Field E] [Differential E] {n : ℕ}
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E) :
    matrixDifferential S = matrixDeriv S := rfl

/-- **The central clock.**  The trace of the Wigner--Smith matrix is `-i` times the logarithmic
derivative of the determinant of the scattering matrix. -/
theorem trace_matrixWignerSmith {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential E] {n : ℕ} (ι : F) (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (hS : IsUnit S.det) :
    Matrix.trace (matrixWignerSmith ι S) =
      -algebraMap F E ι * ((S.det)′ / S.det) := by
  rw [matrixWignerSmith, Matrix.trace_smul, matrixDifferential_eq_matrixDeriv,
    trace_inv_mul_matrixDeriv S hS, smul_eq_mul]

/-- The trace vanishes exactly when the determinant is a differential constant: a scattering matrix
with constant determinant has no central clock. -/
theorem trace_matrixWignerSmith_eq_zero_iff {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential E] {n : ℕ} (ι : F) (hι : algebraMap F E ι ≠ 0)
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (hS : IsUnit S.det) :
    Matrix.trace (matrixWignerSmith ι S) = 0 ↔ (S.det)′ = 0 := by
  have hdet : S.det ≠ 0 := hS.ne_zero
  rw [trace_matrixWignerSmith ι S hS]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd (neg_eq_zero.mp h1) hι
    · exact (div_eq_zero_iff.mp h1).resolve_right hdet
  · intro h
    rw [h, zero_div, mul_zero]

end GaloisForLFunctions.HTGeometry
