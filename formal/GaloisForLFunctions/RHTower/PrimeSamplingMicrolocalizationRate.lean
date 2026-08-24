import GaloisForLFunctions.RHTower.PrimeHigherMertensRate
import GaloisForLFunctions.RHTower.PrimeSamplingMicrolocalization

/-!
# Exponential-rate logarithmic prime-window microlocalization

The qualitative `o(1)` window law is insufficient when an adapted Fock radius shrinks
polynomially.  This module exposes the stronger de la Vallée Poussin remainder already proved by
`PrimeHigherMertensRate` in logarithmic coordinates.  It gives an exact main-term/remainder split
for every window and a square-root-exponential bound on each endpoint remainder.
-/

open Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- Second-order prime Mertens remainder at logarithmic coordinate `y`. -/
def primeLogSquareRemainder (y : ℝ) : ℝ :=
  primeLogPowSum 2 (Real.exp y) - y ^ 2 / 2 - mertensLogPowConstantFull 1

/-- Exact decomposition of a logarithmic prime window into `2 x r` and its two endpoint
remainders. -/
theorem primeLogWindowMass_eq_main_add_remainders (x r : ℝ) :
    primeLogWindowMass x r =
      2 * x * r + primeLogSquareRemainder (x + r) -
        primeLogSquareRemainder (x - r) := by
  rw [primeLogWindowMass, primeLogSquareRemainder, primeLogSquareRemainder]
  ring

/-- The second-order remainder in logarithmic coordinates has unconditional
`y * exp (-c * sqrt y)` decay. -/
theorem exists_primeLogSquareRemainder_bound :
    ∃ B c Y : ℝ, 0 < c ∧ 0 ≤ B ∧ 1 ≤ Y ∧ ∀ y : ℝ, Y ≤ y →
      |primeLogSquareRemainder y| ≤
        B * y * Real.exp (-c * Real.sqrt y) := by
  obtain ⟨B, c, X, hc, hB, hX, hbound⟩ := exists_primeLogPowSum_sub_bound 1
  let Y : ℝ := max 1 (Real.log X)
  refine ⟨B, c, Y, hc, hB, le_max_left _ _, ?_⟩
  intro y hy
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hlog : Real.log X ≤ y := le_trans (le_max_right _ _) hy
  have hXe : X ≤ Real.exp y := by
    rw [← Real.exp_log hXpos]
    exact Real.exp_le_exp.mpr hlog
  have h := hbound (Real.exp y) hXe
  norm_num at h
  simpa [primeLogSquareRemainder, Real.log_exp] using h

end

end RHTower
