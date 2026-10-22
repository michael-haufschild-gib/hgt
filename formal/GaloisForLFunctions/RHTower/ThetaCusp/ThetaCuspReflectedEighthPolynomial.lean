import Mathlib.Data.Real.Basic

/-!
# Native reflected eighth polynomial

Lightweight algebraic home for the rank-three reflected-Hankel polynomial.  Keeping this
definition independent of the analytic theta stack makes exact invariant calculations cheap to
check.
-/

namespace RHTower

noncomputable section

/-- Native rank-three reflected eighth polynomial in four signed even log jets. -/
def thetaCuspReflectedEighthPolynomial (A B C D : ℝ) : ℝ :=
  768 * A ^ (6 : ℕ) - 1344 * A ^ (4 : ℕ) * B + 304 * A ^ (2 : ℕ) * B ^ (2 : ℕ) -
    68 * B ^ (3 : ℕ) + 128 * A ^ (3 : ℕ) * C - 4 * A ^ (2 : ℕ) * D + B * D - C ^ (2 : ℕ)

end

end RHTower
