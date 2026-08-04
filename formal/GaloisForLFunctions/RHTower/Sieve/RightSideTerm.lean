import GaloisForLFunctions.RHTower.Sieve.LeftEdgeTerm
import GaloisForLFunctions.RHTower.Sieve.GrowthSubstitution

/-!
# The right-hand terms at the balanced parameter

The truncation error and the horizontal edges share a shape: a coefficient times `y^{d(K)}` divided
by a power of the truncation height.  At the balanced parameter the numerator grows like
`exp(c₀ t)` and the height is at least `exp(t)/4`, so each term is the trivial size `y` times
`exp(-(1-c₀)t)` — a genuine decay, because `c₀ ≤ 1/2`.

One decay order suffices: taking `j = 0` in the contour bound already gives the exponent `1 - c₀`,
and higher `j` only improves it.
-/

namespace RHTower.Sieve

open Real

/-- **A right-hand term collapses to the trivial size times a decay.** -/
theorem rightSide_term_le {x y A : ℝ} (hx2 : 2 ≤ (Real.log x) ^ ((1 : ℝ) / 10))
    (hx1 : 1 ≤ Real.log x) (hy0 : 0 < y) (hy1 : 0 ≤ Real.log y)
    (hxy : Real.log y ≤ 2 * Real.log x) (hA : 0 ≤ A) :
    A * y ^ rightAbscissa (contourParam x) / truncHeight (contourParam x)
      ≤ 4 * A * y * Real.exp (-((1 - zeroFreeConst) * (Real.log x) ^ ((1 : ℝ) / 10))) := by
  set t : ℝ := (Real.log x) ^ ((1 : ℝ) / 10) with htdef
  have hexp0 : (0 : ℝ) < Real.exp t := Real.exp_pos t
  have hT : Real.exp t / 4 ≤ truncHeight (contourParam x) := exp_div_four_le_truncHeight hx2
  have hTpos : (0 : ℝ) < truncHeight (contourParam x) := lt_of_lt_of_le (by positivity) hT
  have hpow : y ^ rightAbscissa (contourParam x) ≤ y * Real.exp (zeroFreeConst * t) :=
    rpow_rightAbscissa_le hx1 hy0 hy1 hxy
  have hnum : A * y ^ rightAbscissa (contourParam x) ≤ A * (y * Real.exp (zeroFreeConst * t)) :=
    mul_le_mul_of_nonneg_left hpow hA
  have hnum0 : (0 : ℝ) ≤ A * (y * Real.exp (zeroFreeConst * t)) := by positivity
  have hstep : A * y ^ rightAbscissa (contourParam x) / truncHeight (contourParam x)
      ≤ A * (y * Real.exp (zeroFreeConst * t)) / (Real.exp t / 4) := by
    gcongr
  refine le_trans hstep (le_of_eq ?_)
  field_simp
  rw [mul_assoc, ← Real.exp_add,
    show t + -(t * (1 - zeroFreeConst)) = zeroFreeConst * t by ring]

end RHTower.Sieve
