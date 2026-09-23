import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# Higgs-spinor outer squares are Lorentz-null

A complex doublet has four real coordinates. Its Hermitian outer square is a positive
semidefinite `2 × 2` matrix, hence a standard Hermitian representative of a causal
four-vector. This file proves the exact kinematic bridge:

* the Hermitian determinant is the quadratic form of signature `(1, 3)`;
* every complex-doublet outer square lies on its null cone;
* the outer square is invariant under a common unit complex phase.

The last statement makes the transition necessarily singular: the outer square cannot be an
invertible four-real-dimensional coordinate change. Nothing here identifies weak isospin with
Lorentz spin, constructs a tetrad, or derives gravitational dynamics.
-/

open Matrix
open scoped ComplexOrder Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Hermitian `2 × 2` representative of the real coordinates `(t, x, y, z)`. -/
def lorentzHermitianMatrix (t x y z : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((t + z : ℝ) : ℂ), (x : ℂ) + (y : ℂ) * Complex.I;
     (x : ℂ) - (y : ℂ) * Complex.I, ((t - z : ℝ) : ℂ)]

/-- The coordinate representative is Hermitian. -/
theorem lorentzHermitianMatrix_isHermitian (t x y z : ℝ) :
    (lorentzHermitianMatrix t x y z).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [lorentzHermitianMatrix]
  ring

/-- Its determinant is exactly the Lorentz quadratic form of signature `(1, 3)`. -/
theorem lorentzHermitianMatrix_det (t x y z : ℝ) :
    (lorentzHermitianMatrix t x y z).det =
      ((t ^ (2 : ℕ) - x ^ (2 : ℕ) - y ^ (2 : ℕ) - z ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two]
  push_cast
  simp [lorentzHermitianMatrix]
  calc
    (↑t + ↑z) * (↑t - ↑z) -
          (↑x + ↑y * Complex.I) * (↑x - ↑y * Complex.I) =
        ↑t ^ (2 : ℕ) - ↑x ^ (2 : ℕ) + ↑y ^ (2 : ℕ) * Complex.I ^ (2 : ℕ) - ↑z ^ (2 : ℕ) := by ring
    _ = ↑t ^ (2 : ℕ) - ↑x ^ (2 : ℕ) - ↑y ^ (2 : ℕ) - ↑z ^ (2 : ℕ) := by
      rw [Complex.I_sq]
      ring

/-- Hermitian outer square of a complex doublet. -/
def higgsSpinorEventMatrix (H : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.vecMulVec H (star H)

/-- Scalar coordinate extracted from a complex doublet. -/
def higgsSpinorTime (H : Fin 2 → ℂ) : ℝ :=
  (Complex.normSq (H 0) + Complex.normSq (H 1)) / 2

/-- First traceless Hermitian coordinate extracted from a complex doublet. -/
def higgsSpinorX (H : Fin 2 → ℂ) : ℝ :=
  (H 0 * (starRingEnd ℂ) (H 1)).re

/-- Second traceless Hermitian coordinate extracted from a complex doublet. -/
def higgsSpinorY (H : Fin 2 → ℂ) : ℝ :=
  (H 0 * (starRingEnd ℂ) (H 1)).im

/-- Third traceless Hermitian coordinate extracted from a complex doublet. -/
def higgsSpinorZ (H : Fin 2 → ℂ) : ℝ :=
  (Complex.normSq (H 0) - Complex.normSq (H 1)) / 2

/-- The scalar coordinate of every complex doublet is nonnegative. -/
theorem higgsSpinorTime_nonneg (H : Fin 2 → ℂ) :
    0 ≤ higgsSpinorTime H := by
  exact div_nonneg
    (add_nonneg (Complex.normSq_nonneg (H 0)) (Complex.normSq_nonneg (H 1)))
    (by norm_num)

/-- A complex-doublet outer square is positive semidefinite. -/
theorem higgsSpinorEventMatrix_posSemidef (H : Fin 2 → ℂ) :
    (higgsSpinorEventMatrix H).PosSemidef := by
  exact Matrix.posSemidef_vecMulVec_self_star H

/-- A complex-doublet outer square is Hermitian. -/
theorem higgsSpinorEventMatrix_isHermitian (H : Fin 2 → ℂ) :
    (higgsSpinorEventMatrix H).IsHermitian :=
  (higgsSpinorEventMatrix_posSemidef H).isHermitian

/-- A two-component outer square has zero determinant. -/
theorem higgsSpinorEventMatrix_det (H : Fin 2 → ℂ) :
    (higgsSpinorEventMatrix H).det = 0 := by
  exact Matrix.det_vecMulVec H (star H)

/-- Exact light-cone identity for the four real coordinates of a complex doublet. -/
theorem higgsSpinor_null (H : Fin 2 → ℂ) :
    higgsSpinorTime H ^ (2 : ℕ) =
      higgsSpinorX H ^ (2 : ℕ) + higgsSpinorY H ^ (2 : ℕ) + higgsSpinorZ H ^ (2 : ℕ) := by
  simp only [higgsSpinorTime, higgsSpinorX, higgsSpinorY, higgsSpinorZ,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-- Equivalent vanishing of the Lorentz quadratic form. -/
theorem higgsSpinor_lorentzQuadratic_eq_zero (H : Fin 2 → ℂ) :
    higgsSpinorTime H ^ (2 : ℕ) - higgsSpinorX H ^ (2 : ℕ) -
        higgsSpinorY H ^ (2 : ℕ) - higgsSpinorZ H ^ (2 : ℕ) = 0 := by
  rw [higgsSpinor_null]
  ring

/-- The outer square is exactly the Lorentz-Hermitian matrix of the extracted coordinates. -/
theorem higgsSpinorEventMatrix_eq_lorentzHermitianMatrix (H : Fin 2 → ℂ) :
    higgsSpinorEventMatrix H =
      lorentzHermitianMatrix
        (higgsSpinorTime H) (higgsSpinorX H) (higgsSpinorY H) (higgsSpinorZ H) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [higgsSpinorEventMatrix, lorentzHermitianMatrix, higgsSpinorTime, higgsSpinorX,
      higgsSpinorY, higgsSpinorZ, Matrix.vecMulVec_apply, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im]
  all_goals apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- A common unit complex phase is erased by the Hermitian outer square. -/
theorem higgsSpinorEventMatrix_phase_invariant
    (u : ℂ) (H : Fin 2 → ℂ) (hu : u * star u = 1) :
    higgsSpinorEventMatrix (u • H) = higgsSpinorEventMatrix H := by
  ext i j
  simp only [higgsSpinorEventMatrix, Matrix.vecMulVec_apply, Pi.star_apply,
    Pi.smul_apply, smul_eq_mul, star_mul]
  calc
    u * H i * (star (H j) * star u) =
        (u * star u) * (H i * star (H j)) := by ring
    _ = H i * star (H j) := by rw [hu, one_mul]

end GaloisForLFunctions.HTGeometry
