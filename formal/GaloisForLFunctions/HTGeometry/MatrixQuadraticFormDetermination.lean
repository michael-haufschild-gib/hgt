import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Complex matrix determination by quadratic forms

The diagonal values of a complex sesquilinear form determine every mixed value by the four-point
complex polarization identity.  Consequently a finite complex matrix is determined by
`xᴴ M x`, and a matrix whose every quadratic value is purely imaginary is skew-Hermitian.
-/

open scoped Matrix ComplexConjugate
open Matrix

namespace GaloisForLFunctions.HTGeometry

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Equality of all complex quadratic values determines a finite complex matrix. -/
theorem matrix_eq_of_quadraticForm_eq
    (M N : Matrix I I ℂ)
    (h : ∀ x : I → ℂ, star x ⬝ᵥ M.mulVec x = star x ⬝ᵥ N.mulVec x) :
    M = N := by
  have hpolar (P : Matrix I I ℂ) (x y : I → ℂ) :
      (4 : ℂ) * (star x ⬝ᵥ P.mulVec y) =
        (star (x + y) ⬝ᵥ P.mulVec (x + y) -
          star (x - y) ⬝ᵥ P.mulVec (x - y)) -
        Complex.I * (star (x + Complex.I • y) ⬝ᵥ P.mulVec (x + Complex.I • y) -
          star (x - Complex.I • y) ⬝ᵥ P.mulVec (x - Complex.I • y)) := by
    let B : (I → ℂ) → (I → ℂ) → ℂ := fun u v => star u ⬝ᵥ P.mulVec v
    have hadd_left (u v w : I → ℂ) : B (u + v) w = B u w + B v w := by
      simp [B, dotProduct, Pi.star_apply, map_add, add_mul, Finset.sum_add_distrib]
    have hsub_left (u v w : I → ℂ) : B (u - v) w = B u w - B v w := by
      simp [B, dotProduct, Pi.star_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
    have hadd_right (u v w : I → ℂ) : B u (v + w) = B u v + B u w := by
      simp [B, Matrix.mulVec_add, dotProduct_add]
    have hsub_right (u v w : I → ℂ) : B u (v - w) = B u v - B u w := by
      simp [B, Matrix.mulVec_sub, dotProduct_sub]
    have hI_left (u v : I → ℂ) : B (Complex.I • u) v = -Complex.I * B u v := by
      simp [B, dotProduct, Pi.star_apply, Finset.mul_sum, mul_assoc]
    have hI_right (u v : I → ℂ) : B u (Complex.I • v) = Complex.I * B u v := by
      simp [B, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
    change (4 : ℂ) * B x y =
      (B (x + y) (x + y) - B (x - y) (x - y)) -
        Complex.I * (B (x + Complex.I • y) (x + Complex.I • y) -
          B (x - Complex.I • y) (x - Complex.I • y))
    simp only [hadd_left, hsub_left, hadd_right, hsub_right, hI_left, hI_right]
    ring_nf
    rw [pow_two, Complex.I_mul_I]
    ring
  have hbilinear : ∀ x y : I → ℂ,
      star x ⬝ᵥ M.mulVec y = star x ⬝ᵥ N.mulVec y := by
    intro x y
    have hM := hpolar M x y
    have hN := hpolar N x y
    rw [h (x + y), h (x - y), h (x + Complex.I • y),
      h (x - Complex.I • y)] at hM
    rw [← hN] at hM
    exact mul_left_cancel₀ (by norm_num : (4 : ℂ) ≠ 0) hM
  ext i j
  have hij := hbilinear (Pi.single i 1) (Pi.single j 1)
  simpa [dotProduct, Matrix.mulVec, Pi.single_apply] using hij

omit [DecidableEq I] in
/-- Taking the adjoint conjugates every diagonal sesquilinear quadratic value. -/
theorem matrixQuadraticForm_conjTranspose
    (M : Matrix I I ℂ) (x : I → ℂ) :
    star x ⬝ᵥ Mᴴ.mulVec x = star (star x ⬝ᵥ M.mulVec x) := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def, map_sum, map_mul,
    Matrix.conjTranspose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp
  ring

/-- Purely imaginary diagonal quadratic values characterize skew-Hermitian matrices. -/
theorem conjTranspose_eq_neg_of_quadraticForm_re_eq_zero
    (M : Matrix I I ℂ)
    (h : ∀ x : I → ℂ, (star x ⬝ᵥ M.mulVec x).re = 0) :
    Mᴴ = -M := by
  apply matrix_eq_of_quadraticForm_eq
  intro x
  rw [matrixQuadraticForm_conjTranspose]
  simp only [Matrix.neg_mulVec, dotProduct_neg]
  apply Complex.ext
  · simpa [h x]
  · simp

end GaloisForLFunctions.HTGeometry
