import GaloisForLFunctions.HTGeometry.HermitianInertia

/-!
# Real-axis kernel positivity does not select form positivity

An exact three-dimensional Hermitian counterexample: the inverse form has a
strictly positive scalar kernel on every real moment-curve point while the
form itself has two negative squares.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix Complex
open scoped ComplexOrder Matrix

noncomputable section

abbrev RealAxisKernelIndex := Fin 3

/-- The inverse-form matrix whose scalar real-axis kernel is visible. -/
def realAxisKernelG : Matrix RealAxisKernelIndex RealAxisKernelIndex ℂ :=
  !![1, 0, 2;
     0, -3, 0;
     2, 0, 1]

/-- The real symmetric form `H = G⁻¹`. -/
def realAxisKernelH : Matrix RealAxisKernelIndex RealAxisKernelIndex ℂ :=
  !![-(1 / 3 : ℂ), 0, 2 / 3;
     0, -(1 / 3 : ℂ), 0;
     2 / 3, 0, -(1 / 3 : ℂ)]

/-- The real moment-curve vector `(1, t, t²)`. -/
def realAxisKernelEval (t : ℝ) : RealAxisKernelIndex → ℂ :=
  fun j => ((t ^ (j : ℕ) : ℝ) : ℂ)

/-- Scalar reproducing-kernel shadow of `H` along the real moment curve. -/
def realAxisKernel (t : ℝ) : ℝ :=
  (star (realAxisKernelEval t) ⬝ᵥ realAxisKernelH⁻¹ *ᵥ realAxisKernelEval t).re

/-- An off-curve polynomial direction. -/
def realAxisKernelHiddenNegativeVector : RealAxisKernelIndex → ℂ := ![0, 1, 0]

/-- Real quadratic form of the displayed Hermitian matrix. -/
def realAxisKernelQuadratic (x : RealAxisKernelIndex → ℂ) : ℝ :=
  (star x ⬝ᵥ realAxisKernelH *ᵥ x).re

theorem realAxisKernelH_mul_G : realAxisKernelH * realAxisKernelG = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realAxisKernelH, realAxisKernelG, Matrix.mul_apply, Fin.sum_univ_succ]

theorem realAxisKernelG_mul_H : realAxisKernelG * realAxisKernelH = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realAxisKernelH, realAxisKernelG, Matrix.mul_apply, Fin.sum_univ_succ]

theorem realAxisKernelH_isUnit : IsUnit realAxisKernelH :=
  IsUnit.of_mul_eq_one realAxisKernelG realAxisKernelH_mul_G

theorem realAxisKernelG_isUnit : IsUnit realAxisKernelG :=
  IsUnit.of_mul_eq_one realAxisKernelH realAxisKernelG_mul_H

theorem realAxisKernelH_inv_eq_G : realAxisKernelH⁻¹ = realAxisKernelG := by
  letI : Invertible realAxisKernelH := realAxisKernelH_isUnit.invertible
  apply (Matrix.mul_right_inj_of_invertible realAxisKernelH).mp
  rw [Matrix.mul_inv_of_invertible, realAxisKernelH_mul_G]

theorem realAxisKernelG_isHermitian : realAxisKernelG.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realAxisKernelG, Matrix.conjTranspose_apply]

theorem realAxisKernelH_isHermitian : realAxisKernelH.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realAxisKernelH, Matrix.conjTranspose_apply]

/-- Every entry of `H` is real, so its Hermitian symmetry is ordinary real symmetry. -/
theorem realAxisKernelH_entries_real (i j : RealAxisKernelIndex) :
    (realAxisKernelH i j).im = 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [realAxisKernelH]

/-- A change of coordinates which diagonalizes the real symmetric form by congruence. -/
def realAxisKernelChange : Matrix RealAxisKernelIndex RealAxisKernelIndex ℂ :=
  !![1, 0, 1;
     0, 1, 0;
     1, 0, -1]

def realAxisKernelChangeInv : Matrix RealAxisKernelIndex RealAxisKernelIndex ℂ :=
  !![1 / 2, 0, 1 / 2;
     0, 1, 0;
     1 / 2, 0, -(1 / 2 : ℂ)]

theorem realAxisKernelChange_mul_inv :
    realAxisKernelChange * realAxisKernelChangeInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realAxisKernelChange, realAxisKernelChangeInv, Matrix.mul_apply,
      Fin.sum_univ_succ]

theorem realAxisKernelChange_isUnit : IsUnit realAxisKernelChange :=
  IsUnit.of_mul_eq_one realAxisKernelChangeInv realAxisKernelChange_mul_inv

def realAxisKernelDiagonalValues : RealAxisKernelIndex → ℝ :=
  ![2 / 3, -(1 / 3), -2]

def realAxisKernelDiagonal : Matrix RealAxisKernelIndex RealAxisKernelIndex ℂ :=
  Matrix.diagonal fun i => (realAxisKernelDiagonalValues i : ℂ)

theorem realAxisKernelH_congruent_diagonal :
    realAxisKernelChangeᴴ * realAxisKernelH * realAxisKernelChange = realAxisKernelDiagonal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realAxisKernelChange, realAxisKernelH, realAxisKernelDiagonal,
      realAxisKernelDiagonalValues, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ]

theorem realAxisKernelDiagonal_negIndex : hermNegIndex realAxisKernelDiagonal = 2 := by
  change hermNegIndex (Matrix.diagonal fun i => (realAxisKernelDiagonalValues i : ℂ)) = 2
  rw [negIndex_diagonal]
  have hset : ({i | realAxisKernelDiagonalValues i < 0} : Finset RealAxisKernelIndex) =
      ({(1 : RealAxisKernelIndex), 2} : Finset RealAxisKernelIndex) := by
    ext i
    fin_cases i
    · norm_num [realAxisKernelDiagonalValues]
      decide
    · norm_num [realAxisKernelDiagonalValues]
    · norm_num [realAxisKernelDiagonalValues]
      decide
  rw [hset]
  decide

/-- `H` has precisely two negative squares. -/
theorem realAxisKernelH_negIndex : hermNegIndex realAxisKernelH = 2 := by
  calc
    hermNegIndex realAxisKernelH =
        hermNegIndex (realAxisKernelChangeᴴ * realAxisKernelH * realAxisKernelChange) :=
      (negIndex_conjugate realAxisKernelH realAxisKernelChange_isUnit).symm
    _ = hermNegIndex realAxisKernelDiagonal := by rw [realAxisKernelH_congruent_diagonal]
    _ = 2 := realAxisKernelDiagonal_negIndex

/-- Exact complex scalar evaluation before taking its real part. -/
theorem realAxisKernel_complex_eq_polynomial (t : ℝ) :
    star (realAxisKernelEval t) ⬝ᵥ realAxisKernelG *ᵥ realAxisKernelEval t =
      ((1 + t ^ 2 + t ^ 4 : ℝ) : ℂ) := by
  norm_num [realAxisKernelEval, realAxisKernelG, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, Complex.star_def]
  ring

/-- The scalar shadow is exactly `1 + t² + t⁴`. -/
theorem realAxisKernel_eq_polynomial (t : ℝ) :
    realAxisKernel t = 1 + t ^ 2 + t ^ 4 := by
  unfold realAxisKernel
  rw [realAxisKernelH_inv_eq_G, realAxisKernel_complex_eq_polynomial]
  simp only [Complex.ofReal_re]

theorem realAxisKernel_pos (t : ℝ) : 0 < realAxisKernel t := by
  rw [realAxisKernel_eq_polynomial]
  nlinarith [sq_nonneg t, sq_nonneg (t ^ 2)]

/-- The off-curve direction `y` is strictly negative for `H`. -/
theorem realAxisKernel_hidden_negative_quadratic :
    realAxisKernelQuadratic realAxisKernelHiddenNegativeVector = -(1 / 3 : ℝ) := by
  norm_num [realAxisKernelQuadratic, realAxisKernelHiddenNegativeVector,
    realAxisKernelH, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Complex.star_def]

/-- Complete exact counterexample: real-axis scalar-kernel positivity does not force form positivity. -/
theorem realAxisKernelPositivityNonselectorCertificate :
    realAxisKernelH.IsHermitian ∧
      (∀ i j, (realAxisKernelH i j).im = 0) ∧
        IsUnit realAxisKernelH ∧
          realAxisKernelH⁻¹ = realAxisKernelG ∧
            hermNegIndex realAxisKernelH = 2 ∧
              (∀ t : ℝ, realAxisKernel t = 1 + t ^ 2 + t ^ 4) ∧
                (∀ t : ℝ, 0 < realAxisKernel t) ∧
                  realAxisKernelQuadratic realAxisKernelHiddenNegativeVector = -(1 / 3 : ℝ) := by
  exact ⟨realAxisKernelH_isHermitian, realAxisKernelH_entries_real, realAxisKernelH_isUnit,
    realAxisKernelH_inv_eq_G, realAxisKernelH_negIndex, realAxisKernel_eq_polynomial,
    realAxisKernel_pos, realAxisKernel_hidden_negative_quadratic⟩

end

end GaloisForLFunctions.HTGeometry
