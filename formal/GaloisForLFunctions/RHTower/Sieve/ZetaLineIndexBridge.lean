import GaloisForLFunctions.RHTower.Sieve.ZetaPartialSumTruncation
import GaloisForLFunctions.RHTower.Sieve.DirichletLittleOh

/-!
# Reconciling the truncation with the derivative-test range

The truncation writes its head as `∑_{k ∈ Icc 1 N} ((k : ℝ) : ℂ) ^ (-(1 + it))` while the derivative
test bounds `∑_{n ∈ Ico 1 M} (n : ℂ) ^ (-1 - it)`.  The two agree once `M = N + 1`: the ranges are
the same finite set and the summands are equal after clearing the cast and rearranging the exponent.

The truncation point of the chain is `M = 2 ^ (topExponent t + 1)`, which exceeds `(t/8π)^(3 : ℕ)`, so the
tail terms of the truncation are negligible against the head.
-/

namespace RHTower.Sieve

open Finset

/-- The two ways of writing the partial sum agree. -/
theorem sum_Icc_cpow_eq_sum_Ico (t : ℝ) (M : ℕ) :
    ∑ k ∈ Finset.Icc 1 M, ((k : ℝ) : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))
      = ∑ n ∈ Finset.Ico (1 : ℕ) (M + 1), (n : ℂ) ^ (-1 - Complex.I * (t : ℂ)) := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hbase : ((k : ℝ) : ℂ) = (k : ℂ) := by push_cast; ring
  have hexp : (-(1 + Complex.I * (t : ℂ))) = -1 - Complex.I * (t : ℂ) := by ring
  rw [hbase, hexp]

/-- The truncation point of the chain exceeds `(t / 8π)^(3 : ℕ)`. -/
theorem cube_le_two_pow_topExponent {t : ℝ} (ht : 8 * Real.pi ≤ t) :
    (t / (8 * Real.pi)) ^ (3 : ℕ) ≤ ((2 ^ (topExponent t + 1) : ℕ) : ℝ) := by
  have hπ := Real.pi_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h8π : (0 : ℝ) < 8 * Real.pi := by positivity
  have hq : (0 : ℝ) < t / (8 * Real.pi) := by
    have : (0 : ℝ) < t := lt_of_lt_of_le h8π ht
    positivity
  have hfloor := Nat.lt_floor_add_one (3 * Real.log (t / (8 * Real.pi)) / Real.log 2)
  rw [← topExponent] at hfloor
  have hkey : 3 * Real.log (t / (8 * Real.pi))
      ≤ (((topExponent t : ℕ) : ℝ) + 1) * Real.log 2 := by
    have hstep := mul_le_mul_of_nonneg_right hfloor.le hlog2.le
    rw [div_mul_cancel₀ _ hlog2.ne'] at hstep
    linarith
  have hcube : (t / (8 * Real.pi)) ^ (3 : ℕ)
      = Real.exp (3 * Real.log (t / (8 * Real.pi))) := by
    rw [← Real.rpow_natCast (t / (8 * Real.pi)) 3, Real.rpow_def_of_pos hq]
    push_cast
    ring_nf
  have htwo : ((2 ^ (topExponent t + 1) : ℕ) : ℝ)
      = Real.exp ((((topExponent t : ℕ) : ℝ) + 1) * Real.log 2) := by
    push_cast
    rw [← Real.rpow_natCast (2 : ℝ) (topExponent t + 1), Real.rpow_def_of_pos (by norm_num)]
    push_cast
    ring_nf
  rw [hcube, htwo]
  exact Real.exp_le_exp.mpr hkey

end RHTower.Sieve
