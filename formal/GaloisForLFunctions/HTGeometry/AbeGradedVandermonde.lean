import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Graded Vandermonde blocks for Abe damping

Distinct damping speeds turn the successive jets of one local exponential
coordinate into a Vandermonde matrix.  This is the finite algebraic core of
the graded-determinant route: its leading parameter coefficient is nonzero,
so only a normalized determinant limit is needed from the Poincaré tail.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The jet matrix of exponential damping columns with speeds `c` at parameter `B`.
Row `i` is the speed `c i`; column `j` is the jet order `j`. -/
def abeGradedVandermonde {n : ℕ} (c : Fin n → ℂ) (B : ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.vandermonde fun i ↦ c i * B

@[simp]
theorem abeGradedVandermonde_apply {n : ℕ} (c : Fin n → ℂ) (B : ℂ)
    (i j : Fin n) :
    abeGradedVandermonde c B i j = (c i * B) ^ (j : ℕ) :=
  rfl

/-- Nonzero parameter scaling preserves distinct damping speeds. -/
theorem Function.Injective.complex_mul_right {n : ℕ} {c : Fin n → ℂ} {B : ℂ}
    (hc : Function.Injective c) (hB : B ≠ 0) :
    Function.Injective fun i ↦ c i * B := by
  intro i j hij
  apply hc
  exact mul_right_cancel₀ hB hij

/-- **Graded damping Vandermonde.**  Distinct nonzero-speed columns have an invertible
finite jet matrix at every nonzero damping parameter. -/
theorem abeGradedVandermonde_det_ne_zero {n : ℕ} (c : Fin n → ℂ) (B : ℂ)
    (hc : Function.Injective c) (hB : B ≠ 0) :
    (abeGradedVandermonde c B).det ≠ 0 := by
  exact Matrix.det_vandermonde_ne_zero_iff.mpr (Function.Injective.complex_mul_right hc hB)

end GaloisForLFunctions.HTGeometry
