import GaloisForLFunctions.HTGeometry.HiggsSpinorNullCone

/-!
# The exceptional cubic contains an exact Lorentz slice

Inside the standard complex corner `H₃(ℂ)` of the Albert algebra `H₃(𝕆)`, fix the primitive
idempotent `diag(1, 0, 0)` and use the complementary `H₂(ℂ)` block as four real coordinates.
This file proves symbolically that the cubic determinant on this block is exactly a scalar times
the Lorentz quadratic form:

`det (diag(s, X(t,x,y,z))) = s (t² - x² - y² - z²)`.

At `s = 1`, the exceptional cubic therefore restricts exactly to the Lorentz norm. This is a
dependency-closed algebraic statement. It does not formalize octonionic multiplication, identify
the block with physical spacetime, select Lorentzian reality dynamically, or derive gravity.
-/

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/--
Block-diagonal `H₃(ℂ)` representative consisting of a scalar primitive-idempotent direction and
the standard Lorentz-Hermitian `H₂(ℂ)` block.
-/
def exceptionalComplexCornerMatrix (s t x y z : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(s : ℂ), 0, 0;
     0, ((t + z : ℝ) : ℂ), (x : ℂ) + (y : ℂ) * Complex.I;
     0, (x : ℂ) - (y : ℂ) * Complex.I, ((t - z : ℝ) : ℂ)]

/-- The complex-corner representative is Hermitian. -/
theorem exceptionalComplexCornerMatrix_isHermitian (s t x y z : ℝ) :
    (exceptionalComplexCornerMatrix s t x y z).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [exceptionalComplexCornerMatrix]
  ring

/--
Exact cubic-to-Lorentz factorization in the complex corner of the exceptional Jordan algebra.
-/
theorem exceptionalComplexCornerMatrix_det (s t x y z : ℝ) :
    (exceptionalComplexCornerMatrix s t x y z).det =
      ((s * (t ^ (2 : ℕ) - x ^ (2 : ℕ) - y ^ (2 : ℕ) - z ^ (2 : ℕ)) : ℝ) : ℂ) := by
  rw [Matrix.det_fin_three]
  push_cast
  simp [exceptionalComplexCornerMatrix]
  calc
    ↑s * (↑t + ↑z) * (↑t - ↑z) -
          ↑s * (↑x + ↑y * Complex.I) * (↑x - ↑y * Complex.I) =
        ↑s * (↑t ^ (2 : ℕ) - ↑x ^ (2 : ℕ) + ↑y ^ (2 : ℕ) * Complex.I ^ (2 : ℕ) - ↑z ^ (2 : ℕ)) := by ring
    _ = ↑s * (↑t ^ (2 : ℕ) - ↑x ^ (2 : ℕ) - ↑y ^ (2 : ℕ) - ↑z ^ (2 : ℕ)) := by
      rw [Complex.I_sq]
      ring

/--
On the affine slice through the primitive idempotent, the cubic determinant is exactly the
Lorentz quadratic form.
-/
theorem exceptionalPrimitiveIdempotentSlice_det (t x y z : ℝ) :
    (exceptionalComplexCornerMatrix 1 t x y z).det =
      ((t ^ (2 : ℕ) - x ^ (2 : ℕ) - y ^ (2 : ℕ) - z ^ (2 : ℕ) : ℝ) : ℂ) := by
  simpa using exceptionalComplexCornerMatrix_det 1 t x y z

/--
The lower `H₂(ℂ)` block of the exceptional complex corner is precisely the previously formalized
Lorentz-Hermitian coordinate matrix.
-/
theorem exceptionalComplexCorner_lowerBlock (s t x y z : ℝ) (i j : Fin 2) :
    exceptionalComplexCornerMatrix s t x y z i.succ j.succ =
      lorentzHermitianMatrix t x y z i j := by
  fin_cases i <;> fin_cases j <;>
    simp [exceptionalComplexCornerMatrix, lorentzHermitianMatrix]

end GaloisForLFunctions.HTGeometry
