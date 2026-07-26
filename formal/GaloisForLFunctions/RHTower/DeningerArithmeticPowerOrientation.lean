import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Orientation coherence for Deninger's arithmetic power correspondences

For the composable complete-intersection presentations

`x^n - y = 0`, `y^m - z = 0`,

the relative cotangent differential has matrix

`[[a, 0], [-1, b]]`,

where `a = n*x^(n-1)` and `b = m*y^(m-1)`.  This module proves the
orientation-preserving elementary reduction to `diag(1, a*b)`.  The identity block is
contractible; after substituting `y = x^n`, the residual entry is the derivative of
`x^(n*m) - z`.

This is the determinant-orientation coherence needed by the Milnor--Witt/Gysin part of the
source arithmetic cohomology construction.  It does not assert coherence of chosen paths in the
full algebraic K-theory framing space.
-/

namespace RHTower

noncomputable section

variable {R : Type*} [CommRing R]

/-- Cotangent matrix of the iterated monic power-map presentation. -/
def deningerPowerIteratedCotangentMatrix (a b : R) :
    Matrix (Fin 2) (Fin 2) R :=
  !![a, 0; -1, b]

/-- Orientation-preserving row change splitting the iterated presentation. -/
def deningerPowerOrientationLeft (a : R) :
    Matrix (Fin 2) (Fin 2) R :=
  !![0, -1; 1, a]

/-- Orientation-preserving column change splitting the iterated presentation. -/
def deningerPowerOrientationRight (b : R) :
    Matrix (Fin 2) (Fin 2) R :=
  !![1, b; 0, 1]

/-- Split cotangent differential: one contractible block and the composite derivative. -/
def deningerPowerSplitCotangentMatrix (a b : R) :
    Matrix (Fin 2) (Fin 2) R :=
  !![1, 0; 0, a * b]

/-- The row change has determinant one, so it preserves the determinant orientation. -/
theorem det_deningerPowerOrientationLeft (a : R) :
    (deningerPowerOrientationLeft a).det = 1 := by
  simp [deningerPowerOrientationLeft, Matrix.det_fin_two_of]

/-- The column change has determinant one, so it preserves the determinant orientation. -/
theorem det_deningerPowerOrientationRight (b : R) :
    (deningerPowerOrientationRight b).det = 1 := by
  simp [deningerPowerOrientationRight, Matrix.det_fin_two_of]

/--
Explicit orientation-preserving cancellation of the intermediate power-map coordinate.
-/
theorem deningerPowerIteratedCotangentMatrix_reduction (a b : R) :
    deningerPowerOrientationLeft a *
          deningerPowerIteratedCotangentMatrix a b *
        deningerPowerOrientationRight b =
      deningerPowerSplitCotangentMatrix a b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [deningerPowerOrientationLeft,
      deningerPowerIteratedCotangentMatrix,
      deningerPowerOrientationRight,
      deningerPowerSplitCotangentMatrix,
      Matrix.mul_apply]

end

end RHTower
