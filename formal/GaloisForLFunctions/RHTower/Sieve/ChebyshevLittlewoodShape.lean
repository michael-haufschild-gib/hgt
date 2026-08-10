import GaloisForLFunctions.RHTower.Sieve.ChebyshevLittlewoodContour
import GaloisForLFunctions.RHTower.Sieve.ChebyshevKappaOneShape

/-!
# Shape of the rectangle of width `A/log T`

The three quantities the collapse steps consume — the width of the rectangle, its positivity, and
the reciprocal distance of the left edge from the abscissa — at the left abscissa `1 - A/log T`.

Where the exponent-one rectangle has width `(1 + 1/40000)/log T` and reciprocal distance
`40000 log T`, this one has width `(1 + A)/log T` and reciprocal distance `log T / A`: the deeper
the shift, the wider the rectangle and the *smaller* the pole coefficient.  That is the trade the
final balance optimises, and it is only available because `A` is free.
-/

namespace RHTower.Sieve

open ArithmeticFunction GaloisForLFunctions.HTGeometry

/-- The width of the rectangle. -/
theorem chebRightTwo_sub_chebLeftLw (A T : ℝ) :
    chebRightTwo T - chebLeftLw A T = (1 + A) / Real.log T := by
  rw [chebRightTwo, chebLeftLw]
  ring

/-- The width, in the inequality form the collapse consumes. -/
theorem chebRightTwo_sub_chebLeftLw_le (A T : ℝ) :
    chebRightTwo T - chebLeftLw A T ≤ (1 + A) / Real.log T :=
  le_of_eq (chebRightTwo_sub_chebLeftLw A T)

/-- The rectangle has positive width. -/
theorem chebRightTwo_sub_chebLeftLw_pos {A T : ℝ} (hA : 0 < A) (hT : 8 ≤ Real.log T) :
    0 < chebRightTwo T - chebLeftLw A T := by
  rw [chebRightTwo_sub_chebLeftLw]
  have hL : (0 : ℝ) < Real.log T := by linarith
  positivity

/-- **The reciprocal of the left edge's distance from the abscissa.**  It is `log T / A`, so a
deeper shift makes the pole term smaller. -/
theorem one_sub_chebLeftLw_inv (A T : ℝ) :
    (1 - chebLeftLw A T)⁻¹ = Real.log T / A := by
  rw [chebLeftLw, show (1 : ℝ) - (1 - A / Real.log T) = A / Real.log T by ring, inv_div]

end RHTower.Sieve
