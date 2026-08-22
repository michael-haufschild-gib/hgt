import GaloisForLFunctions.HTGeometry.SquaredVariableSubstitution
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# The square-root exponential moment sequence

`∫_0^∞ a^n e^{-√a} da = 2 (2n+1)!`.  The substitution `a = t²` turns the half-line integral into a
Gamma integral of odd order, so the odd factorials appear on the nose.  This is the base measure of
the shifted factorial moment problem: the density `e^{-√a}/2` represents `(2n+1)!`.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

theorem integral_pow_mul_exp_neg_sqrt (n : ℕ) :
    ∫ a in Set.Ioi (0:ℝ), a ^ n * Real.exp (-Real.sqrt a)
      = 2 * (Nat.factorial (2 * n + 1) : ℝ) := by
  rw [integral_Ioi_comp_sq (fun a => a ^ n * Real.exp (-Real.sqrt a))]
  have hpoint : ∀ t ∈ Set.Ioi (0:ℝ),
      (2 * t) * (((t : ℝ) ^ 2) ^ n * Real.exp (-Real.sqrt (t ^ 2)))
        = 2 * (Real.exp (-t) * t ^ (2 * n + 1)) := by
    intro t ht
    have ht' : (0:ℝ) < t := ht
    rw [Real.sqrt_sq ht'.le, ← pow_mul]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint, MeasureTheory.integral_const_mul]
  congr 1
  have hgam : Real.Gamma ((2 * n + 2 : ℕ) : ℝ) = (Nat.factorial (2 * n + 1) : ℝ) := by
    have h := Real.Gamma_nat_eq_factorial (2 * n + 1)
    rw [show (((2 * n + 2 : ℕ)) : ℝ) = ((2 * n + 1 : ℕ) : ℝ) + 1 by push_cast; ring]
    exact h
  rw [← hgam, Real.Gamma_eq_integral (by positivity)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht' : (0:ℝ) < t := ht
  congr 1
  rw [show ((2 * n + 2 : ℕ) : ℝ) - 1 = ((2 * n + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast]

end GaloisForLFunctions.HTGeometry

end
