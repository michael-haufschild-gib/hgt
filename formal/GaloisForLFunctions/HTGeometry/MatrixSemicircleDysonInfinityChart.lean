import GaloisForLFunctions.HTGeometry.MatrixSemicircleDysonPolynomial
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# The nonsingular chart of the matrix-semicircle Dyson system at infinity

After `H = zG` and `u = z⁻²`, Speicher's equation becomes
`H = I + u η(H)H`. This file defines its polynomial system exactly. Its fiber over `u = 0`
is the single point `H = I`, and the square Jacobian in all matrix-entry coordinates is the
identity there. The rescaled and original Dyson systems are proved equivalent for `z ≠ 0`.
-/

open scoped BigOperators Matrix
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K]

/-- Entry `(i,j)` of the rescaled Dyson equation `H - I - u η(H)H = 0`. -/
def matrixDysonInfinityPolynomial (A : K → Matrix I I ℂ) (i j : I) :
    MvPolynomial (MatrixDysonVariable I) ℂ :=
  matrixDysonEntry i j - MvPolynomial.C (if i = j then 1 else 0) -
    matrixDysonZ I * matrixDysonQuadraticPolynomial A i j

/-- Evaluation point for the infinity coordinate `u` and rescaled transform `H`. -/
def matrixDysonInfinityPoint (u : ℂ) (H : Matrix I I ℂ) : MatrixDysonVariable I → ℂ :=
  matrixDysonPoint u H

/-- Literal evaluation of the rescaled polynomial system. -/
theorem eval_matrixDysonInfinityPolynomial (A : K → Matrix I I ℂ) (u : ℂ)
    (H : Matrix I I ℂ) (i j : I) :
    MvPolynomial.eval (matrixDysonInfinityPoint u H)
        (matrixDysonInfinityPolynomial A i j) =
      (H - 1 - u • (matrixSemicircleCovariance A H * H)) i j := by
  simp only [matrixDysonInfinityPolynomial, map_sub, map_mul, MvPolynomial.eval_C,
    eval_matrixDysonEntry, eval_matrixDysonZ, matrixDysonInfinityPoint,
    Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
    eval_matrixDysonQuadraticPolynomial]

/-- Simultaneous vanishing is exactly the rescaled matrix Dyson equation. -/
theorem matrixDysonInfinityPolynomial_vanishes_iff (A : K → Matrix I I ℂ) (u : ℂ)
    (H : Matrix I I ℂ) :
    (∀ i j, MvPolynomial.eval (matrixDysonInfinityPoint u H)
        (matrixDysonInfinityPolynomial A i j) = 0) ↔
      H = 1 + u • (matrixSemicircleCovariance A H * H) := by
  constructor
  · intro h
    ext i j
    have hij := h i j
    simp only [eval_matrixDysonInfinityPolynomial, Matrix.sub_apply, Matrix.add_apply] at hij ⊢
    linear_combination hij
  · intro h i j
    have hij := congr_fun (congr_fun h i) j
    simp only [eval_matrixDysonInfinityPolynomial, Matrix.sub_apply, Matrix.add_apply] at hij ⊢
    linear_combination hij

/-- The fiber at infinity consists of exactly the identity matrix. -/
theorem matrixDysonInfinityPolynomial_vanishes_zero_iff
    (A : K → Matrix I I ℂ) (H : Matrix I I ℂ) :
    (∀ i j, MvPolynomial.eval (matrixDysonInfinityPoint 0 H)
        (matrixDysonInfinityPolynomial A i j) = 0) ↔ H = 1 := by
  rw [matrixDysonInfinityPolynomial_vanishes_iff]
  simp

/-- For `z ≠ 0`, the infinity chart with `u=z⁻²`, `H=zG` is exactly the original Dyson system. -/
theorem matrixDysonInfinityPolynomial_rescaled_vanishes_iff
    (A : K → Matrix I I ℂ) (z : ℂ) (hz : z ≠ 0) (G : Matrix I I ℂ) :
    (∀ i j, MvPolynomial.eval
        (matrixDysonInfinityPoint (z⁻¹ ^ (2 : ℕ)) (z • G))
        (matrixDysonInfinityPolynomial A i j) = 0) ↔
      ∀ i j, MvPolynomial.eval (matrixDysonPoint z G)
        (matrixDysonPolynomial A i j) = 0 := by
  rw [matrixDysonInfinityPolynomial_vanishes_iff,
    matrixDysonPolynomial_vanishes_iff, matrixSemicircleCovariance_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hzscale : z⁻¹ ^ (2 : ℕ) * (z * z) = 1 := by field_simp
  rw [hzscale, one_smul]

/-- Formal entry Jacobian of the infinity system at its distinguished fiber point. -/
def matrixDysonInfinityJacobian (A : K → Matrix I I ℂ) :
    Matrix (I × I) (I × I) ℂ :=
  fun ij ab => MvPolynomial.eval (matrixDysonInfinityPoint 0 (1 : Matrix I I ℂ))
    (MvPolynomial.pderiv (some ab) (matrixDysonInfinityPolynomial A ij.1 ij.2))

theorem eval_pderiv_matrixDysonInfinityPolynomial_zero_one
    (A : K → Matrix I I ℂ) (i j a b : I) :
    MvPolynomial.eval (matrixDysonInfinityPoint 0 (1 : Matrix I I ℂ))
        (MvPolynomial.pderiv (some (a, b)) (matrixDysonInfinityPolynomial A i j)) =
      if i = a ∧ j = b then 1 else 0 := by
  simp [matrixDysonInfinityPolynomial, matrixDysonInfinityPoint, matrixDysonEntry,
    matrixDysonZ, matrixDysonPoint, Pi.single_apply]
  split_ifs <;> simp_all

/-- The entry Jacobian at infinity is exactly the identity. -/
theorem matrixDysonInfinityJacobian_eq_one (A : K → Matrix I I ℂ) :
    matrixDysonInfinityJacobian A = 1 := by
  ext ij ab
  rw [matrixDysonInfinityJacobian,
    eval_pderiv_matrixDysonInfinityPolynomial_zero_one]
  simp [Matrix.one_apply, Prod.ext_iff]

/-- In particular, the infinity-chart Jacobian determinant is the unit. -/
theorem matrixDysonInfinityJacobian_det (A : K → Matrix I I ℂ) :
    (matrixDysonInfinityJacobian A).det = 1 := by
  rw [matrixDysonInfinityJacobian_eq_one, Matrix.det_one]

/-- The rescaled system is polynomial of total degree at most three. -/
theorem matrixDysonInfinityPolynomial_totalDegree_le_three
    (A : K → Matrix I I ℂ) (i j : I) :
    (matrixDysonInfinityPolynomial A i j).totalDegree ≤ 3 := by
  have hzq :
      (matrixDysonZ I * matrixDysonQuadraticPolynomial A i j).totalDegree ≤ 3 := by
    calc
      (matrixDysonZ I * matrixDysonQuadraticPolynomial A i j).totalDegree ≤
          (matrixDysonZ I).totalDegree +
            (matrixDysonQuadraticPolynomial A i j).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 1 + 2 := Nat.add_le_add (by simp [matrixDysonZ])
        (matrixDysonQuadraticPolynomial_totalDegree_le_two A i j)
      _ = 3 := by norm_num
  unfold matrixDysonInfinityPolynomial
  refine (MvPolynomial.totalDegree_sub _ _).trans ?_
  apply max_le
  · refine (MvPolynomial.totalDegree_sub _ _).trans ?_
    exact max_le (by simp [matrixDysonEntry]) (by split <;> simp)
  · exact hzq

end

end GaloisForLFunctions.HTGeometry
