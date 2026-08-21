import GaloisForLFunctions.HTGeometry.IdentityTangentSubmodule

/-!
# The tangent space of `SL₂` is traceless

Linearising `det = 1` at the identity gives the trace: over the dual numbers

`det(1 + εX) = (1 + εX₀₀)(1 + εX₁₁) − εX₀₁·εX₁₀ = 1 + ε(X₀₀ + X₁₁)`,

since `ε² = 0`.  So a family of differential polynomials containing the determinant equation forces
every tangent direction at the identity to be traceless — the hypothesis `htr` of Cassidy's
classification, with no nondegeneracy needed.

* `detPoly` — the determinant equation as a differential polynomial;
* `evalOver_detPoly`;
* `trace_eq_zero_of_mem_zeroSet`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable {C : Type*} [CommRing C] [Differential C]

/-- The determinant equation `x₀₀x₁₁ − x₀₁x₁₀ = 1`, as a differential polynomial. -/
def detPoly : DifferentialPolynomial (Fin 2 × Fin 2) C :=
  MvPolynomial.X (((0, 0) : Fin 2 × Fin 2), 0) * MvPolynomial.X (((1, 1) : Fin 2 × Fin 2), 0)
    - MvPolynomial.X (((0, 1) : Fin 2 × Fin 2), 0) * MvPolynomial.X (((1, 0) : Fin 2 × Fin 2), 0)
    - 1

omit [Differential C] in
theorem evalOver_detPoly {A : Type*} [CommRing A] [Algebra C A] [Differential A]
    (x : (Fin 2 × Fin 2) → A) :
    differentialPolynomialEvalOver (K := C) x (detPoly (C := C))
      = x (0, 0) * x (1, 1) - x (0, 1) * x (1, 0) - 1 := by
  rw [detPoly, map_sub, map_sub, map_mul, map_mul, map_one,
    differentialPolynomialEvalOver_X, differentialPolynomialEvalOver_X,
    differentialPolynomialEvalOver_X, differentialPolynomialEvalOver_X]
  simp only [differentialJet_zero]

/-- **A tangent direction at the identity of the determinant equation is traceless.** -/
theorem trace_eq_zero_of_mem_zeroSet {S : Set (DifferentialPolynomial (Fin 2 × Fin 2) C)}
    (hdet : detPoly (C := C) ∈ S) {X : Matrix (Fin 2) (Fin 2) C}
    (hX : dualMatrix 1 X ∈ matrixZeroSet (C := C) (A := DualNumber C) S) :
    X 0 0 + X 1 1 = 0 := by
  have h := hX _ hdet
  rw [evalOver_detPoly] at h
  have hval : (dualMatrix (1 : Matrix (Fin 2) (Fin 2) C) X (0, 0).1 (0, 0).2)
        * dualMatrix 1 X (1, 1).1 (1, 1).2
      - dualMatrix 1 X (0, 1).1 (0, 1).2 * dualMatrix 1 X (1, 0).1 (1, 0).2 - 1
      = dualMk (0 : C) (X 0 0 + X 1 1) := by
    simp only [dualMatrix_apply]
    have h00 : (1 : Matrix (Fin 2) (Fin 2) C) 0 0 = 1 := by simp
    have h11 : (1 : Matrix (Fin 2) (Fin 2) C) 1 1 = 1 := by simp
    have h01 : (1 : Matrix (Fin 2) (Fin 2) C) 0 1 = 0 := by simp
    have h10 : (1 : Matrix (Fin 2) (Fin 2) C) 1 0 = 0 := by simp
    rw [h00, h11, h01, h10]
    apply TrivSqZeroExt.ext
    · simp [dualMk, TrivSqZeroExt.fst_mul, smul_eq_mul]
    · simp [dualMk, TrivSqZeroExt.snd_mul, smul_eq_mul]
      ring
  rw [hval] at h
  have := congrArg TrivSqZeroExt.snd h
  simpa [dualMk] using this

end

end GaloisForLFunctions.HTGeometry
