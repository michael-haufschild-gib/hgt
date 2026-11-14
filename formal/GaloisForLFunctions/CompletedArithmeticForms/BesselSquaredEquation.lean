import GaloisForLFunctions.KodairaParshinAbc.Periods.DifferentialSymmetricSquare
import GaloisForLFunctions.HTGeometry.VortexClassicalSeries

/-!
# Symmetric squares of the reciprocal-Gamma Bessel series

The formal Bessel equation survives every complex order, including resonant
orders. Its symmetric square therefore gives a third-order equation for
the square of the actual Bessel coefficient series at every radial scale.
-/

noncomputable section

namespace GaloisForLFunctions.CompletedArithmeticForms

open PowerSeries HTGeometry KodairaParshinAbc.Periods

/-- All complex orders satisfy the integral symmetric-square Bessel equation. -/
theorem besselSquared_differential_equation (a : ℝ) (z : ℂ) :
    symmetricSquareD (derivative ℂ) PowerSeries.X (C (z + 1)) (-C ((a : ℂ) ^ 2))
      (vortexBesselSeries a z ^ 2) = 0 := by
  have h : secondOrderD (derivative ℂ) PowerSeries.X (C (z + 1)) (-C ((a : ℂ) ^ 2))
      (vortexBesselSeries a z) = 0 := by
    simpa only [secondOrderD, neg_mul, sub_eq_add_neg] using vortexBessel_differential_equation a z
  rw [symmetricSquareD_square, h, map_zero, mul_zero, mul_zero, add_zero]

end GaloisForLFunctions.CompletedArithmeticForms
