import GaloisForLFunctions.HTGeometry.HiggsSpinorNullCone
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The colour Gram matrix is a Minkowski-future vector

For a complex `3 × 2` matrix `X`, the Hermitian Gram matrix `Xᴴ X` forgets the left
three-dimensional frame.  This file proves the exact algebraic content of the resulting
four-real-dimensional object:

* the Gram matrix is positive semidefinite, Hermitian, and has the same rank as `X`;
* left unitary transformations are invisible and right transformations act covariantly;
* its Pauli coordinates lie in the closed Minkowski future cone;
* Lorentz mass-squared is exactly the sum of the squared norms of the three `2 × 2` minors;
* the causal boundary is therefore exactly the common zero locus of those minors;
* an event supported on one colour row is Lorentz-null.

The mathematics is the finite `3 × 2` Cauchy--Binet identity and the standard Hermitian model of
the Lorentz cone.  Nothing here asserts that a physical event uses this quotient, identifies weak
isospin with spatial rotations, constructs a spacetime incidence relation, or derives dynamics.
-/

open Matrix
open scoped ComplexOrder Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- A finite event with three left channels and two right channels. -/
abbrev ColorEventMatrix := Matrix (Fin 3) (Fin 2) ℂ

/-- The `2 × 2` Hermitian matrix left after forgetting the event's left frame. -/
def colorGramMatrix (X : ColorEventMatrix) : Matrix (Fin 2) (Fin 2) ℂ :=
  Xᴴ * X

/-- Squared norm of one of the two columns. -/
def colorColumnNormSq (X : ColorEventMatrix) (j : Fin 2) : ℝ :=
  Complex.normSq (X 0 j) + Complex.normSq (X 1 j) + Complex.normSq (X 2 j)

/-- Hermitian pairing between the two columns. -/
def colorColumnPairing (X : ColorEventMatrix) : ℂ :=
  star (X 0 0) * X 0 1 + star (X 1 0) * X 1 1 + star (X 2 0) * X 2 1

/-- Time coordinate of the colour Gram matrix. -/
def colorGramTime (X : ColorEventMatrix) : ℝ :=
  (colorColumnNormSq X 0 + colorColumnNormSq X 1) / 2

/-- First traceless Hermitian coordinate of the colour Gram matrix. -/
def colorGramX (X : ColorEventMatrix) : ℝ :=
  (colorColumnPairing X).re

/-- Second traceless Hermitian coordinate of the colour Gram matrix. -/
def colorGramY (X : ColorEventMatrix) : ℝ :=
  (colorColumnPairing X).im

/-- Third traceless Hermitian coordinate of the colour Gram matrix. -/
def colorGramZ (X : ColorEventMatrix) : ℝ :=
  (colorColumnNormSq X 0 - colorColumnNormSq X 1) / 2

/-- Minor on colour rows zero and one. -/
def colorMinor01 (X : ColorEventMatrix) : ℂ :=
  X 0 0 * X 1 1 - X 1 0 * X 0 1

/-- Minor on colour rows zero and two. -/
def colorMinor02 (X : ColorEventMatrix) : ℂ :=
  X 0 0 * X 2 1 - X 2 0 * X 0 1

/-- Minor on colour rows one and two. -/
def colorMinor12 (X : ColorEventMatrix) : ℂ :=
  X 1 0 * X 2 1 - X 2 0 * X 1 1

/-- Sum of squared norms of all maximal minors. -/
def colorMinorEnergy (X : ColorEventMatrix) : ℝ :=
  Complex.normSq (colorMinor01 X) +
    Complex.normSq (colorMinor02 X) +
    Complex.normSq (colorMinor12 X)

/-- Lorentz quadratic form of the four Gram coordinates. -/
def colorGramLorentzMassSq (X : ColorEventMatrix) : ℝ :=
  colorGramTime X ^ (2 : ℕ) - colorGramX X ^ (2 : ℕ) -
    colorGramY X ^ (2 : ℕ) - colorGramZ X ^ (2 : ℕ)

/-- The first diagonal Gram entry is the squared norm of the first column. -/
theorem colorGramMatrix_apply_zero_zero (X : ColorEventMatrix) :
    colorGramMatrix X 0 0 = colorColumnNormSq X 0 := by
  simp [colorGramMatrix, colorColumnNormSq, Matrix.mul_apply,
    Fin.sum_univ_succ, Complex.normSq_eq_conj_mul_self]
  ring

/-- The off-diagonal Gram entry is the Hermitian column pairing. -/
theorem colorGramMatrix_apply_zero_one (X : ColorEventMatrix) :
    colorGramMatrix X 0 1 = colorColumnPairing X := by
  simp [colorGramMatrix, colorColumnPairing, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

/-- The second diagonal Gram entry is the squared norm of the second column. -/
theorem colorGramMatrix_apply_one_one (X : ColorEventMatrix) :
    colorGramMatrix X 1 1 = colorColumnNormSq X 1 := by
  simp [colorGramMatrix, colorColumnNormSq, Matrix.mul_apply,
    Fin.sum_univ_succ, Complex.normSq_eq_conj_mul_self]
  ring

/-- The colour Gram matrix is exactly the Lorentz-Hermitian matrix of its four coordinates. -/
theorem colorGramMatrix_eq_lorentzHermitianMatrix (X : ColorEventMatrix) :
    colorGramMatrix X =
      lorentzHermitianMatrix
        (colorGramTime X) (colorGramX X) (colorGramY X) (colorGramZ X) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals apply Complex.ext <;>
    simp [colorGramMatrix, lorentzHermitianMatrix, colorGramTime, colorGramX,
      colorGramY, colorGramZ, colorColumnNormSq, colorColumnPairing,
      Matrix.mul_apply, Fin.sum_univ_succ, Complex.normSq_eq_conj_mul_self,
      Complex.mul_re, Complex.mul_im] <;> ring

/-- `3 × 2` Cauchy--Binet in Lorentz form: mass-squared is the sum of the three squared minors. -/
theorem colorGramLorentzMassSq_eq_minorEnergy (X : ColorEventMatrix) :
    colorGramLorentzMassSq X = colorMinorEnergy X := by
  simp [colorGramLorentzMassSq, colorGramTime, colorGramX, colorGramY, colorGramZ,
    colorColumnNormSq, colorColumnPairing, colorMinorEnergy, colorMinor01, colorMinor02,
    colorMinor12, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-- Every colour Gram matrix is positive semidefinite. -/
theorem colorGramMatrix_posSemidef (X : ColorEventMatrix) :
    (colorGramMatrix X).PosSemidef := by
  exact Matrix.posSemidef_conjTranspose_mul_self X

/-- Every colour Gram matrix is Hermitian. -/
theorem colorGramMatrix_isHermitian (X : ColorEventMatrix) :
    (colorGramMatrix X).IsHermitian :=
  (colorGramMatrix_posSemidef X).isHermitian

/-- Passing to the Gram matrix preserves the complex rank of the event. -/
theorem colorGramMatrix_rank (X : ColorEventMatrix) :
    (colorGramMatrix X).rank = X.rank := by
  exact Matrix.rank_conjTranspose_mul_self X

/-- A left isometry is invisible to the colour Gram matrix. -/
theorem colorGramMatrix_left_invariant
    (U : Matrix (Fin 3) (Fin 3) ℂ) (X : ColorEventMatrix)
    (hU : Uᴴ * U = 1) :
    colorGramMatrix (U * X) = colorGramMatrix X := by
  simp only [colorGramMatrix, Matrix.conjTranspose_mul]
  rw [Matrix.mul_assoc Xᴴ Uᴴ (U * X), ← Matrix.mul_assoc Uᴴ U X, hU]
  simp

/-- A right frame change acts on the colour Gram matrix by conjugation. -/
theorem colorGramMatrix_right_covariant
    (X : ColorEventMatrix) (V : Matrix (Fin 2) (Fin 2) ℂ) :
    colorGramMatrix (X * Vᴴ) = V * colorGramMatrix X * Vᴴ := by
  simp [colorGramMatrix, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Combined left invisibility and right covariance. -/
theorem colorGramMatrix_left_right_covariant
    (U : Matrix (Fin 3) (Fin 3) ℂ) (X : ColorEventMatrix)
    (V : Matrix (Fin 2) (Fin 2) ℂ) (hU : Uᴴ * U = 1) :
    colorGramMatrix (U * X * Vᴴ) = V * colorGramMatrix X * Vᴴ := by
  calc
    colorGramMatrix (U * X * Vᴴ) =
        V * colorGramMatrix (U * X) * Vᴴ :=
      colorGramMatrix_right_covariant (U * X) V
    _ = V * colorGramMatrix X * Vᴴ := by
      rw [colorGramMatrix_left_invariant U X hU]

/-- The Gram determinant is the Lorentz quadratic form of the four coordinates. -/
theorem colorGramMatrix_det (X : ColorEventMatrix) :
    (colorGramMatrix X).det = (colorGramLorentzMassSq X : ℂ) := by
  rw [colorGramMatrix_eq_lorentzHermitianMatrix, lorentzHermitianMatrix_det]
  rfl

/-- The Gram determinant is the real nonnegative minor energy. -/
theorem colorGramMatrix_det_eq_minorEnergy (X : ColorEventMatrix) :
    (colorGramMatrix X).det = (colorMinorEnergy X : ℂ) := by
  rw [colorGramMatrix_det, colorGramLorentzMassSq_eq_minorEnergy]

/-- The Gram time coordinate always points to the closed future. -/
theorem colorGramTime_nonneg (X : ColorEventMatrix) :
    0 ≤ colorGramTime X := by
  have h0 : 0 ≤ colorColumnNormSq X 0 := by
    exact add_nonneg
      (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
      (Complex.normSq_nonneg _)
  have h1 : 0 ≤ colorColumnNormSq X 1 := by
    exact add_nonneg
      (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
      (Complex.normSq_nonneg _)
  exact div_nonneg (add_nonneg h0 h1) (by norm_num)

/-- Every colour Gram coordinate is Lorentz-causal. -/
theorem colorGramLorentzMassSq_nonneg (X : ColorEventMatrix) :
    0 ≤ colorGramLorentzMassSq X := by
  rw [colorGramLorentzMassSq_eq_minorEnergy]
  exact add_nonneg
    (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
    (Complex.normSq_nonneg _)

/-- The event lies on the Lorentz boundary exactly when all maximal minors vanish. -/
theorem colorGramLorentzMassSq_eq_zero_iff (X : ColorEventMatrix) :
    colorGramLorentzMassSq X = 0 ↔
      colorMinor01 X = 0 ∧ colorMinor02 X = 0 ∧ colorMinor12 X = 0 := by
  rw [colorGramLorentzMassSq_eq_minorEnergy]
  unfold colorMinorEnergy
  constructor
  · intro h
    have h01 : Complex.normSq (colorMinor01 X) = 0 := by
      nlinarith [Complex.normSq_nonneg (colorMinor01 X),
        Complex.normSq_nonneg (colorMinor02 X), Complex.normSq_nonneg (colorMinor12 X)]
    have h02 : Complex.normSq (colorMinor02 X) = 0 := by
      nlinarith [Complex.normSq_nonneg (colorMinor01 X),
        Complex.normSq_nonneg (colorMinor02 X), Complex.normSq_nonneg (colorMinor12 X)]
    have h12 : Complex.normSq (colorMinor12 X) = 0 := by
      nlinarith [Complex.normSq_nonneg (colorMinor01 X),
        Complex.normSq_nonneg (colorMinor02 X), Complex.normSq_nonneg (colorMinor12 X)]
    exact ⟨Complex.normSq_eq_zero.mp h01, Complex.normSq_eq_zero.mp h02,
      Complex.normSq_eq_zero.mp h12⟩
  · rintro ⟨h01, h02, h12⟩
    simp [h01, h02, h12]

/-- Strictly timelike Gram coordinates are exactly the events with a nonzero maximal minor. -/
theorem colorGramLorentzMassSq_pos_iff (X : ColorEventMatrix) :
    0 < colorGramLorentzMassSq X ↔
      colorMinor01 X ≠ 0 ∨ colorMinor02 X ≠ 0 ∨ colorMinor12 X ≠ 0 := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have hz := (colorGramLorentzMassSq_eq_zero_iff X).mpr hn
    linarith
  · intro h
    have hne : colorGramLorentzMassSq X ≠ 0 := by
      intro hz
      have hm := (colorGramLorentzMassSq_eq_zero_iff X).mp hz
      rcases h with h01 | h02 | h12
      · exact h01 hm.1
      · exact h02 hm.2.1
      · exact h12 hm.2.2
    exact lt_of_le_of_ne (colorGramLorentzMassSq_nonneg X) (Ne.symm hne)

/-- Event supported on one left row. -/
def singleColorEvent (H : Fin 2 → ℂ) : ColorEventMatrix :=
  fun i j => if i = 0 then H j else 0

/-- Every event supported on one left row maps to the Lorentz-null boundary. -/
theorem singleColorEvent_lorentz_null (H : Fin 2 → ℂ) :
    colorGramLorentzMassSq (singleColorEvent H) = 0 := by
  rw [colorGramLorentzMassSq_eq_zero_iff]
  simp [singleColorEvent, colorMinor01, colorMinor02, colorMinor12]

end GaloisForLFunctions.HTGeometry
