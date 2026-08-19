import GaloisForLFunctions.HTGeometry.DifferentialJacobiFormula

/-!
# The matrix logarithmic derivative

Kolchin's logarithmic derivative `ℓδ g = g′ · g⁻¹` is the basic tool of differential algebraic group
theory: it is a crossed homomorphism,

`ℓδ (g h) = ℓδ g + g (ℓδ h) g⁻¹`,

it vanishes exactly on the matrices with constant entries, and it inverts to
`ℓδ (g⁻¹) = - g⁻¹ (ℓδ g) g`.  The entrywise derivative itself is already in the tree; what is added
here is the Leibniz rule in the general index type, the derivative of an inverse, and the
logarithmic derivative with its group law.
-/

open scoped Differential
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R : Type*} [CommRing R] [Differential R]

theorem matrixDeriv_add {m n : Type*} (M N : Matrix m n R) :
    matrixDeriv (M + N) = matrixDeriv M + matrixDeriv N := by
  ext i j
  simp [matrixDeriv, Matrix.add_apply]

@[simp] theorem matrixDeriv_zero {m n : Type*} : matrixDeriv (0 : Matrix m n R) = 0 := by
  ext i j
  simp [matrixDeriv]

@[simp] theorem matrixDeriv_one {n : Type*} [DecidableEq n] :
    matrixDeriv (1 : Matrix n n R) = 0 := by
  ext i j
  simp only [matrixDeriv, Matrix.one_apply, Matrix.zero_apply]
  split
  · simp
  · simp

/-- **The matrix Leibniz rule**, for an arbitrary finite index type. -/
theorem matrixDeriv_mul {n : Type*} [Fintype n] (M N : Matrix n n R) :
    matrixDeriv (M * N) = matrixDeriv M * N + M * matrixDeriv N := by
  ext i j
  rw [matrixDeriv_apply, Matrix.mul_apply, map_sum, Matrix.add_apply, Matrix.mul_apply,
    Matrix.mul_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Derivation.leibniz, matrixDeriv_apply, matrixDeriv_apply]
  simp only [smul_eq_mul]
  ring

/-- The derivative of an inverse. -/
theorem matrixDeriv_invOf {n : Type*} [Fintype n] [DecidableEq n] (g : Matrix n n R)
    [Invertible g] : matrixDeriv (⅟g) = -(⅟g * matrixDeriv g * ⅟g) := by
  have h : matrixDeriv g * ⅟g + g * matrixDeriv (⅟g) = 0 := by
    rw [← matrixDeriv_mul, mul_invOf_self, matrixDeriv_one]
  have h2 : g * matrixDeriv (⅟g) = -(matrixDeriv g * ⅟g) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h
  calc matrixDeriv (⅟g) = ⅟g * (g * matrixDeriv (⅟g)) := by
        rw [← mul_assoc, invOf_mul_self, one_mul]
    _ = ⅟g * -(matrixDeriv g * ⅟g) := by rw [h2]
    _ = -(⅟g * matrixDeriv g * ⅟g) := by rw [mul_neg, mul_assoc]

/-- **Kolchin's logarithmic derivative** of an invertible matrix. -/
def logDerivMatrix {n : Type*} [Fintype n] [DecidableEq n] (g : Matrix n n R) [Invertible g] :
    Matrix n n R := matrixDeriv g * ⅟g

theorem matrixDeriv_eq_logDerivMatrix_mul {n : Type*} [Fintype n] [DecidableEq n]
    (g : Matrix n n R) [Invertible g] : matrixDeriv g = logDerivMatrix g * g := by
  simp only [logDerivMatrix]
  rw [mul_assoc, invOf_mul_self, mul_one]

theorem logDerivMatrix_one {n : Type*} [Fintype n] [DecidableEq n]
    [Invertible (1 : Matrix n n R)] : logDerivMatrix (1 : Matrix n n R) = 0 := by
  simp only [logDerivMatrix, matrixDeriv_one, zero_mul]

/-- **The crossed-homomorphism law.** -/
theorem logDerivMatrix_mul {n : Type*} [Fintype n] [DecidableEq n] (g h : Matrix n n R)
    [Invertible g] [Invertible h] [Invertible (g * h)] :
    logDerivMatrix (g * h) = logDerivMatrix g + g * logDerivMatrix h * ⅟g := by
  simp only [logDerivMatrix]
  rw [matrixDeriv_mul, invOf_mul, add_mul]
  congr 1
  · rw [mul_assoc, ← mul_assoc h, mul_invOf_self, one_mul]
  · rw [mul_assoc, mul_assoc, mul_assoc]

/-- The logarithmic derivative of an inverse. -/
theorem logDerivMatrix_invOf {n : Type*} [Fintype n] [DecidableEq n] (g : Matrix n n R)
    [Invertible g] : logDerivMatrix (⅟g) = -(⅟g * logDerivMatrix g * g) := by
  have h1 : logDerivMatrix (⅟g) = -(⅟g * matrixDeriv g) := by
    simp only [logDerivMatrix, matrixDeriv_invOf, invOf_invOf, neg_mul]
    rw [mul_assoc, mul_assoc, invOf_mul_self, mul_one]
  have h2 : -(⅟g * logDerivMatrix g * g) = -(⅟g * matrixDeriv g) := by
    simp only [logDerivMatrix]
    rw [mul_assoc, mul_assoc, invOf_mul_self, mul_one]
  rw [h1, h2]

/-- The logarithmic derivative vanishes exactly on constant matrices. -/
theorem logDerivMatrix_eq_zero_iff {n : Type*} [Fintype n] [DecidableEq n] (g : Matrix n n R)
    [Invertible g] : logDerivMatrix g = 0 ↔ matrixDeriv g = 0 := by
  constructor
  · intro h
    rw [matrixDeriv_eq_logDerivMatrix_mul g, h, zero_mul]
  · intro h
    simp only [logDerivMatrix, h, zero_mul]

end

end GaloisForLFunctions.HTGeometry
