import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiFactorialChebyshevEndpoint

/-!
# Deterministic endpoint bound for the critical CCM--FU factorial primitive

The factorial boundary in the critical Chebyshev--factorial prefix is not an
uncontrolled arithmetic term.  A two-sided integral Stirling comparison gives
it logarithmic size, without a prime-distribution premise.  This leaves any
power-scale obstruction in the profile-weighted CCM--FU charge necessarily in
the Chebyshev remainder, not in factorial normalization.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

private theorem ccmFUSuzuki_log_factorial_eq_sum (N : ℕ) :
    Real.log (N.factorial : ℝ) = ∑ k ∈ Finset.Icc 1 N, Real.log k := by
  induction N with
  | zero => simp
  | succ N ih =>
    calc
      Real.log ((N + 1).factorial : ℝ) =
          Real.log (N.factorial : ℝ) + Real.log ((N + 1 : ℕ) : ℝ) := by
            rw [Nat.factorial_succ, Nat.cast_mul,
              Real.log_mul (by positivity) (by positivity)]
            ring
      _ = (∑ k ∈ Finset.Icc 1 N, Real.log k) + Real.log ((N + 1 : ℕ) : ℝ) := by
            rw [ih]
      _ = ∑ k ∈ Finset.Icc 1 (N + 1), Real.log k := by
            rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]

/-- The deterministic factorial endpoint in the literal critical CCM--FU
prefix is at most logarithmic.  Its proof uses only finite Stirling comparison;
no prime-distribution or RH input is used. -/
theorem ccmFUSuzukiCriticalFactorialEndpointDefect_abs_le_log (N : ℕ) :
    |ccmFUSuzukiCriticalFactorialEndpointDefect N| ≤
      Real.log ((N + 3 : ℕ) : ℝ) + 1 + Real.log 2 := by
  have hN : 1 ≤ N + 2 := by omega
  have hupper := sum_log_le_stirling (N + 2) hN
  have hlower := stirling_le_sum_log (N + 2) hN
  rw [← ccmFUSuzuki_log_factorial_eq_sum] at hupper hlower
  have hlog : 0 ≤ Real.log ((N + 3 : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ N + 3 by omega)
  have hratio : Real.log (((N + 3 : ℕ) : ℝ) / ((N + 2 : ℕ) : ℝ)) ≤
      1 / ((N + 2 : ℕ) : ℝ) := by
    have hpos : 0 < ((N + 3 : ℕ) : ℝ) / ((N + 2 : ℕ) : ℝ) := by positivity
    have h := Real.log_le_sub_one_of_pos hpos
    have hrewrite :
        ((N + 3 : ℕ) : ℝ) / ((N + 2 : ℕ) : ℝ) - 1 =
          1 / ((N + 2 : ℕ) : ℝ) := by
      push_cast
      field_simp
      ring
    rwa [hrewrite] at h
  have hlogdiff : Real.log ((N + 3 : ℕ) : ℝ) -
      Real.log ((N + 2 : ℕ) : ℝ) ≤ 1 / ((N + 2 : ℕ) : ℝ) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    exact hratio
  unfold ccmFUSuzukiCriticalFactorialEndpointDefect
  rw [abs_le]
  constructor
  · have hden : 0 < ((N + 2 : ℕ) : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hlogdiff (Nat.cast_nonneg (N + 2))
    have hprod : ((N + 2 : ℕ) : ℝ) *
        (Real.log ((N + 3 : ℕ) : ℝ) - Real.log ((N + 2 : ℕ) : ℝ)) ≤ 1 := by
      rw [mul_div_cancel₀ _ hden.ne'] at hmul
      exact hmul
    have hendpoint : 1 + Real.log 2 - Real.log ((N + 3 : ℕ) : ℝ) ≤
        ((N + 3 : ℕ) : ℝ) - ((N + 3 : ℕ) : ℝ) *
          Real.log ((N + 3 : ℕ) : ℝ) +
          Real.log ((N + 2).factorial : ℝ) + Real.log 2 := by
      push_cast at hlower hprod ⊢
      nlinarith
    have htwo : 0 ≤ 2 * (1 + Real.log 2) := by
      have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      positivity
    linarith
  · have hupper' : Real.log ((N + 2).factorial : ℝ) ≤
        ((N + 3 : ℕ) : ℝ) * Real.log ((N + 3 : ℕ) : ℝ) -
          ((N + 3 : ℕ) : ℝ) + 1 := by
      convert hupper using 1 <;> (push_cast; ring)
    nlinarith

end

end RHTower
