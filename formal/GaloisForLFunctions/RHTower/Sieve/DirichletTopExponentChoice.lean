import GaloisForLFunctions.RHTower.Sieve.DirichletSplitPointChoice

/-!
# Choosing the top of the range

The lower bound on `t` in the exponent form reads `8π · 2^(R/3) ≤ t`, so the largest admissible `R`
is the floor of `3 log (t / 8π) / log 2`.  That choice both satisfies the bound and grows like
`3 log t / log 2`, which is the number of dyadic blocks the tail sum has to cover.

Together with the split point this fixes the two exponents of the estimate in terms of `t` and the
order `K`, leaving only `ε` free.
-/

namespace RHTower.Sieve

open Finset

/-- The largest exponent whose block still sits below `t`. -/
noncomputable def topExponent (t : ℝ) : ℕ :=
  ⌊3 * Real.log (t / (8 * Real.pi)) / Real.log 2⌋₊

theorem topExponent_arg_nonneg {t : ℝ} (ht : 8 * Real.pi ≤ t) :
    0 ≤ 3 * Real.log (t / (8 * Real.pi)) / Real.log 2 := by
  have hπ := Real.pi_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h8π : (0 : ℝ) < 8 * Real.pi := by positivity
  have hone : (1 : ℝ) ≤ t / (8 * Real.pi) := by
    rw [le_div_iff₀ h8π]
    linarith
  have hlognn : 0 ≤ Real.log (t / (8 * Real.pi)) := Real.log_nonneg hone
  positivity

/-- **The chosen top exponent is at most the balance point.** -/
theorem topExponent_le {t : ℝ} (ht : 8 * Real.pi ≤ t) :
    ((topExponent t : ℕ) : ℝ) ≤ 3 * Real.log (t / (8 * Real.pi)) / Real.log 2 :=
  Nat.floor_le (topExponent_arg_nonneg ht)

/-- **The chosen top exponent satisfies the lower bound on `t`.** -/
theorem topExponent_bound {t : ℝ} (ht : 8 * Real.pi ≤ t) :
    8 * Real.pi * (2 : ℝ) ^ (((topExponent t : ℕ) : ℝ) / 3) ≤ t := by
  have hπ := Real.pi_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h8π : (0 : ℝ) < 8 * Real.pi := by positivity
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le h8π ht
  have hle := topExponent_le ht
  have hkey : (((topExponent t : ℕ) : ℝ) / 3) * Real.log 2
      ≤ Real.log (t / (8 * Real.pi)) := by
    have h := mul_le_mul_of_nonneg_right hle hlog2.le
    rw [div_mul_cancel₀ _ hlog2.ne'] at h
    linarith
  have hrpow : (2 : ℝ) ^ (((topExponent t : ℕ) : ℝ) / 3)
      = Real.exp ((((topExponent t : ℕ) : ℝ) / 3) * Real.log 2) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    ring_nf
  rw [hrpow]
  have hexp : Real.exp ((((topExponent t : ℕ) : ℝ) / 3) * Real.log 2) ≤ t / (8 * Real.pi) := by
    have := Real.exp_le_exp.mpr hkey
    rwa [Real.exp_log (by positivity)] at this
  rw [← le_div_iff₀' h8π]
  exact hexp

end RHTower.Sieve
