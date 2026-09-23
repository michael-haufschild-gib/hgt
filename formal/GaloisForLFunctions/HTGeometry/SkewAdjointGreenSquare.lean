import GaloisForLFunctions.HTGeometry.MatrixTracePowerMoment

/-!
# The positive Green square of a skew-adjoint constraint

If `C` is a finite skew-adjoint constraint and `G` is a left inverse of `C`, then adjunction makes
`-Gᴴ` a right inverse.  The mixed inverse identity forces `G` itself to be skew-adjoint.  Its
Green square

`Gᴴ G = -G²`

is positive semidefinite, and its shifted trace powers form a reflection-positive Hankel moment
sequence.  This is the finite algebra behind inverse-square spectral nodes produced by a static
centered constraint; it assumes no analytic moment comparison.
-/

open scoped BigOperators ComplexOrder

namespace HTGeometry

open Matrix

noncomputable section

/-- The positive Green square attached to an indexed matrix. -/
def matrixGreenSquare {n : Type*} [Fintype n]
    (G : Matrix n n ℂ) : Matrix n n ℂ :=
  Gᴴ * G

/-- Every finite Green square is positive semidefinite. -/
theorem matrixGreenSquare_posSemidef
    {n : Type*} [Fintype n]
    (G : Matrix n n ℂ) :
    (matrixGreenSquare G).PosSemidef := by
  classical
  exact posSemidef_conjTranspose_mul_self G

/-- A skew-adjoint Green operator identifies its positive square with the negative ordinary
square. -/
theorem matrixGreenSquare_eq_neg_sq_of_skew
    {n : Type*} [Fintype n] [DecidableEq n]
    {G : Matrix n n ℂ} (hG : Gᴴ = -G) :
    matrixGreenSquare G = -(G ^ (2 : ℕ)) := by
  rw [matrixGreenSquare, hG, pow_two]
  simp

/-- A left inverse of a skew-adjoint square matrix is automatically skew-adjoint.  The adjoint
equation supplies the opposite-sided inverse, so no second inverse hypothesis is needed. -/
theorem leftInverse_conjTranspose_eq_neg_of_skew
    {n : Type*} [Fintype n] [DecidableEq n]
    {C G : Matrix n n ℂ} (hC : Cᴴ = -C)
    (hGC : G * C = 1) :
    Gᴴ = -G := by
  have hstar := congrArg Matrix.conjTranspose hGC
  have hright : C * (-Gᴴ) = 1 := by
    rw [Matrix.conjTranspose_mul, hC, Matrix.conjTranspose_one] at hstar
    simpa only [neg_mul, mul_neg, neg_neg] using hstar
  calc
    Gᴴ = 1 * Gᴴ := by rw [one_mul]
    _ = (G * C) * Gᴴ := by rw [hGC]
    _ = G * (C * Gᴴ) := by rw [mul_assoc]
    _ = G * (-1) := by
      have hCGstar : C * Gᴴ = -1 := by
        have := congrArg Neg.neg hright
        simpa [mul_neg] using this
      rw [hCGstar]
    _ = -G := by rw [mul_neg, mul_one]

/-- The Green square of a left inverse of a skew-adjoint constraint is exactly its negative
inverse square. -/
theorem inverse_matrixGreenSquare_eq_neg_sq
    {n : Type*} [Fintype n] [DecidableEq n]
    {C G : Matrix n n ℂ} (hC : Cᴴ = -C)
    (hGC : G * C = 1) :
    matrixGreenSquare G = -(G ^ (2 : ℕ)) :=
  matrixGreenSquare_eq_neg_sq_of_skew
    (leftInverse_conjTranspose_eq_neg_of_skew hC hGC)

/-- The trace-power moments of every finite Green square are nonnegative on polynomial squares. -/
theorem matrixGreenTracePowerMoment_nonnegative
    {n : Type*} [Fintype n] [DecidableEq n]
    (G : Matrix n n ℂ) (p : Polynomial ℝ) :
    0 ≤ momentFunctional (matrixTracePowerMoment (matrixGreenSquare G)) (p ^ (2 : ℕ)) :=
  matrixTracePowerMoment_nonnegative (matrixGreenSquare_posSemidef G) p

end

end HTGeometry
