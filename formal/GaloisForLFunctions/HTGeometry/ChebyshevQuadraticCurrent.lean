import GaloisForLFunctions.HTGeometry.LogarithmicDerivativeFixedField

/-!
# The transported quadratic current of the two-cusp-two-cone signature

The `(2, 2, ∞)` branch of the orbifold classification is the Chebyshev branch: the coordinate
downstairs is `y = w + w⁻¹`, the maps are Chebyshev polynomials, and the transported object is a
quadratic differential with simple poles at the two order-two points `y = ±2` and a double pole at
the cusp.

The identity behind that statement is elementary and exact:

`(w′/w)² = y′² / (y² - 4)`.

The left side is the square of the Maurer–Cartan current upstairs, invariant under the deck
involution `w ↦ w⁻¹`; the right side is its expression in the invariant coordinate, whose
denominator `y² - 4` vanishes exactly at the two cone points.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

variable {E : Type*} [Field E] [CharZero E] [Differential E]

/-- The derivative of the Chebyshev coordinate. -/
theorem deriv_add_inv {w : E} (hw : w ≠ 0) :
    (w + w⁻¹)′ = w′ * (w ^ 2 - 1) / w ^ 2 := by
  have hinv : (w⁻¹)′ = -w⁻¹ ^ 2 * w′ := by
    simpa [smul_eq_mul] using Differential.deriv.leibniz_inv w
  rw [map_add, hinv]
  field_simp
  ring

/-- The Chebyshev coordinate squared, minus four. -/
theorem add_inv_sq_sub_four {w : E} (hw : w ≠ 0) :
    (w + w⁻¹) ^ 2 - 4 = (w ^ 2 - 1) ^ 2 / w ^ 2 := by
  field_simp
  ring

/-- **The quadratic current of the `(2,2,∞)` signature.**  The square of the logarithmic derivative
upstairs is the quadratic differential `y′²/(y² - 4)` in the Chebyshev coordinate. -/
theorem logDeriv_sq_eq_chebyshev_current {w : E} (hw : w ≠ 0) (hw1 : w ^ 2 - 1 ≠ 0) :
    (w′ / w) ^ 2 = ((w + w⁻¹)′) ^ 2 / ((w + w⁻¹) ^ 2 - 4) := by
  rw [deriv_add_inv hw, add_inv_sq_sub_four hw]
  have hw2 : (w : E) ^ 2 ≠ 0 := pow_ne_zero _ hw
  field_simp
  ring

/-- The deck involution negates the logarithmic derivative, hence fixes its square. -/
theorem logDeriv_inv {w : E} (hw : w ≠ 0) :
    (w⁻¹)′ / w⁻¹ = -(w′ / w) := by
  have hinv : (w⁻¹)′ = -w⁻¹ ^ 2 * w′ := by
    simpa [smul_eq_mul] using Differential.deriv.leibniz_inv w
  rw [hinv]
  field_simp

/-- The Chebyshev coordinate is invariant under the deck involution. -/
theorem add_inv_involutive {w : E} (hw : w ≠ 0) :
    w⁻¹ + (w⁻¹)⁻¹ = w + w⁻¹ := by
  rw [inv_inv]
  ring

end

end GaloisForLFunctions.HTGeometry
