import GaloisForLFunctions.RHTower.Sieve.ChebyshevLlPowers

/-!
# Shape of the rectangle of width `c·log log T/log T`

The width of the rectangle and the reciprocal distance of its left edge from the abscissa.  Both
are the fixed-depth quantities at the depth `A = c·log log T`: width `(1 + A)/log T` and pole
coefficient `log T/A`.  Since `A` grows with `T`, the pole coefficient grows strictly more slowly
than `log T` — which is what the deeper contour buys.
-/

namespace RHTower.Sieve

/-- The width of the rectangle. -/
theorem chebRightTwo_sub_chebLeftLl (c T : ℝ) :
    chebRightTwo T - chebLeftLl c T = (1 + c * Real.log (Real.log T)) / Real.log T := by
  rw [chebRightTwo, chebLeftLl]
  ring

/-- The width, in the inequality form the collapse consumes. -/
theorem chebRightTwo_sub_chebLeftLl_le (c T : ℝ) :
    chebRightTwo T - chebLeftLl c T ≤ (1 + c * Real.log (Real.log T)) / Real.log T :=
  le_of_eq (chebRightTwo_sub_chebLeftLl c T)

/-- The rectangle has positive width. -/
theorem chebRightTwo_sub_chebLeftLl_pos {c T : ℝ} (hc : 0 < c) (hT : 8 ≤ Real.log T) :
    0 < chebRightTwo T - chebLeftLl c T := by
  rw [chebRightTwo_sub_chebLeftLl]
  have hL : (0 : ℝ) < Real.log T := by linarith
  have hLL : (0 : ℝ) < Real.log (Real.log T) := logLog_pos_of_eight hT
  positivity

/-- **The reciprocal of the left edge's distance from the abscissa.** -/
theorem one_sub_chebLeftLl_inv (c T : ℝ) :
    (1 - chebLeftLl c T)⁻¹ = Real.log T / (c * Real.log (Real.log T)) := by
  rw [chebLeftLl,
    show (1 : ℝ) - (1 - c * Real.log (Real.log T) / Real.log T)
      = c * Real.log (Real.log T) / Real.log T by ring, inv_div]

end RHTower.Sieve
