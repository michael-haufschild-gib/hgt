import GaloisForLFunctions.RHTower.LegStripThreshold
import GaloisForLFunctions.HTGeometry.HilbertMatrixShiftIntertwining

/-!
# The two moment representations of the Hilbert–Hankel kernel

The entries of the Hilbert matrix are simultaneously the moments of Lebesgue measure on the unit
interval and the Laplace transform values of the exponential:

```text
1/(m+n+1) = ∫₀¹ t^{m+n} dt = ∫₀^∞ e^{-(m+n+1)x} dx.
```

The first reading is the interval cell, the second is the Hardy ladder; the equality of the two is
the coordinate identification the source-normal bridge rests on.  Both are unconditional, and the
kernel of the previous module is the complex cast of either.
-/

open MeasureTheory intervalIntegral Set

namespace GaloisForLFunctions

noncomputable section

/-- **The interval-cell reading.**  The Hilbert entries are the moments of Lebesgue measure on the
unit interval. -/
theorem hilbertMoment_eq_integral_pow (k : ℕ) :
    (∫ t in (0:ℝ)..1, t ^ k) = 1 / ((k : ℝ) + 1) := by
  rw [integral_pow]
  norm_num

/-- **The Hardy-ladder reading.**  The same entries are the Laplace values of the exponential. -/
theorem hilbertMoment_eq_integral_exp (k : ℕ) :
    (∫ x in Ioi (0:ℝ), Real.exp (-(((k : ℝ) + 1) * x))) = 1 / ((k : ℝ) + 1) := by
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [RHTower.integral_exp_neg_mul_Ioi hpos, one_div]

/-- The two readings agree: this is the coordinate identification of the bridge. -/
theorem integral_pow_eq_integral_exp (k : ℕ) :
    (∫ t in (0:ℝ)..1, t ^ k) = ∫ x in Ioi (0:ℝ), Real.exp (-(((k : ℝ) + 1) * x)) := by
  rw [hilbertMoment_eq_integral_pow, hilbertMoment_eq_integral_exp]

/-- The Hilbert–Hankel kernel is the complex cast of the moment. -/
theorem hilbertKernel_eq_ofReal (m n : ℕ) :
    hilbertKernel m n = ((1 / ((m + n : ℕ) + 1 : ℝ) : ℝ) : ℂ) := by
  rw [hilbertKernel, one_div]
  push_cast
  ring

/-! ## Positivity from the moment reading -/

/-- **The Hilbert matrix is positive semidefinite.**  Its quadratic form is the integral over the
unit interval of the square of the generating polynomial, by the interval-cell reading of the
entries. -/
theorem hilbertQuadraticForm_nonneg (a : ℕ →₀ ℝ) :
    0 ≤ ∑ m ∈ a.support, ∑ n ∈ a.support,
      a m * a n * (1 / (((m + n : ℕ) : ℝ) + 1)) := by
  have hexp : ∀ t : ℝ, (∑ m ∈ a.support, a m * t ^ m) ^ 2
      = ∑ m ∈ a.support, ∑ n ∈ a.support, a m * a n * t ^ (m + n) := by
    intro t
    rw [pow_two, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
    rw [pow_add]
    ring
  have hint : (∫ t in (0:ℝ)..1, (∑ m ∈ a.support, a m * t ^ m) ^ 2)
      = ∑ m ∈ a.support, ∑ n ∈ a.support,
        a m * a n * (1 / (((m + n : ℕ) : ℝ) + 1)) := by
    rw [intervalIntegral.integral_congr (g := fun t => ∑ m ∈ a.support, ∑ n ∈ a.support,
      a m * a n * t ^ (m + n)) (fun t _ => hexp t)]
    rw [intervalIntegral.integral_finsetSum fun m _ =>
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [intervalIntegral.integral_finsetSum fun n _ =>
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [intervalIntegral.integral_const_mul, hilbertMoment_eq_integral_pow]
  rw [← hint]
  exact intervalIntegral.integral_nonneg (by norm_num) fun t _ => sq_nonneg _

end

end GaloisForLFunctions
