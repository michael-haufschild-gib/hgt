import GaloisForLFunctions.HTGeometry.Polynomial.ChebyshevDifferential
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.ChebyshevWindows

/-!
# Differential energy of monotone Chebyshev windows

The unit-capacity windows satisfy both an exact first-derivative energy
identity and the shifted Chebyshev differential equation on the whole line.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor

/-- The value and weighted derivative of a shifted window have constant total energy. -/
theorem shiftedChebyshev_differential_energy (n : ℕ) :
    X * (1 - X) * (shiftedChebyshev n).derivative ^ 2 +
      (n : ℝ[X]) ^ 2 * shiftedChebyshev n ^ 2 = (n : ℝ[X]) ^ 2 := by
  have h := chebyshev_affine_differential_energy (n : ℤ) (2 : ℝ) (-1)
  simp only [C_ofNat, C_neg, C_1, ← sub_eq_add_neg, Int.cast_natCast] at h
  simp only [shiftedChebyshev, C_ofNat, C_1]
  apply mul_left_cancel₀ (show (4 : ℝ[X]) ≠ 0 by norm_num)
  linear_combination -h

/-- The shifted spectral equation is valid at both endpoints as a polynomial identity. -/
theorem shiftedChebyshev_differential_equation (n : ℕ) :
    2 * X * (1 - X) * (shiftedChebyshev n).derivative.derivative +
      (1 - 2 * X) * (shiftedChebyshev n).derivative +
      2 * (n : ℝ[X]) ^ 2 * shiftedChebyshev n = 0 := by
  have h := chebyshev_affine_differential_equation (n : ℤ) (2 : ℝ) (-1)
  simp only [C_ofNat, C_neg, C_1, ← sub_eq_add_neg, Int.cast_natCast] at h
  simp only [shiftedChebyshev, C_ofNat, C_1]
  apply mul_left_cancel₀ (show (2 : ℝ[X]) ≠ 0 by norm_num)
  linear_combination -h

end GaloisForLFunctions.HTGeometry.ChronologicalTensor
