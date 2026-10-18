import GaloisForLFunctions.RHTower.MertensThirdTheorem
import GaloisForLFunctions.RHTower.Sieve.MertensSecondExpRate

/-!
# A vanishing Euler-product budget for valuation defects

The higher-prime-power remainder has a favorable sign in the upper bound for
the inverse Euler product. Retaining that sign transfers the unconditional
exponential error in the reciprocal-prime sum to an arbitrarily small multiple
of `1 / log N` in the exponent of the product bound.
-/

open Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

theorem primeRecipSum_eq_mertensS (N : ℕ) : primeRecipSum N = Sieve.mertensS N := by
  have hset : (Finset.Icc 0 N).filter Nat.Prime = Nat.primesLE N := by
    ext p
    simp [Nat.mem_primesLE]
  rw [Sieve.mertensS, ← hset, Finset.sum_filter]
  simp [primeRecipSum, primeRecipWeight, one_div]

/-- The two source definitions of the reciprocal-prime constant agree. -/
theorem meisselMertensConst_eq_mertensSecondConstant :
    Sieve.meisselMertensConst = mertensSecondConstant := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto
      (fun N : ℕ => |Sieve.mertensS N - Sieve.logLog N - Sieve.meisselMertensConst|)
      atTop (𝓝 0) := by
    refine squeeze_zero' (g := fun N : ℕ =>
      (2 * Sieve.mertensFirstConst + 1 / 2) / Real.log N)
      (Eventually.of_forall fun _ => abs_nonneg _) ?_
      (tendsto_const_nhds.div_atTop hlog)
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact Sieve.abs_mertensS_sub_logLog_sub_const_le hN
  have hs : Tendsto (fun N : ℕ => primeRecipSum N - Real.log (Real.log N))
      atTop (𝓝 Sieve.meisselMertensConst) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [Real.norm_eq_abs, primeRecipSum_eq_mertensS, Sieve.logLog] using hlim
  exact tendsto_nhds_unique hs tendsto_primeRecipSum_sub_logLog

/-- A finite higher-prime-power defect is bounded by its full positive sum. -/
theorem neg_primeLogDefect_le_partial (N : ℕ) :
    -primeLogDefect 1 ≤ primeLogDefectPartial N := by
  have hnn (n : ℕ) : 0 ≤ -(if n.Prime then
      Real.log (1 - (n : ℝ)⁻¹) + (n : ℝ)⁻¹ else 0) := by
    by_cases hp : n.Prime
    · simp only [if_pos hp]
      have hn : (2 : ℝ) ≤ n := by exact_mod_cast hp.two_le
      have hinv : (n : ℝ)⁻¹ < 1 := by
        rw [inv_lt_one₀ (by linarith)]
        linarith
      linarith only [negLog_sub_self_nonneg hinv]
    · simp [hp]
  have h := summable_defectIndicator.neg.sum_le_tsum (Finset.Icc 0 N) (fun n _ => hnn n)
  rw [tsum_neg, tsum_defectIndicator, Finset.sum_neg_distrib] at h
  change -primeLogDefectPartial N ≤ -(-primeLogDefect 1) at h
  linarith only [h]

/-- The exponential prime-sum error remains negligible after multiplication by `log N`. -/
theorem tendsto_log_mul_prime_sum_exp_error {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => Real.log N * Real.exp (-c * Real.sqrt (Real.log N)))
      atTop (𝓝 0) := by
  have harg : Tendsto (fun N : ℕ => Real.sqrt (Real.log N)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 c hc).comp harg
  simpa only [Function.comp_def, Real.rpow_two,
    Real.sq_sqrt (Real.log_natCast_nonneg _)] using h

/-- The inverse prime product has an arbitrarily small `1/log N` exponent error,
unconditionally. The discarded higher-prime-power tail has the favorable sign. -/
theorem eventually_inv_mertens_le_exp_small {a : ℝ} (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop, (mertensPrimeProduct N)⁻¹ ≤
      Real.exp Real.eulerMascheroniConstant * Real.log N * Real.exp (a / Real.log N) := by
  obtain ⟨B, c, hc, _, hrate⟩ := Sieve.exists_mertensS_sub_logLog_sub_const_exp_rate
  have hlim : Tendsto (fun N : ℕ =>
      B * (Real.log N * Real.exp (-c * Real.sqrt (Real.log N)))) atTop (𝓝 0) := by
    simpa using (tendsto_log_mul_prime_sum_exp_error hc).const_mul B
  filter_upwards [hrate, (tendsto_order.mp hlim).2 a ha,
    eventually_ge_atTop 2] with N hN hsmall hN2
  have hlog : 0 < Real.log N :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsum : primeRecipSum N - Real.log (Real.log N) - mertensSecondConstant
      ≤ a / Real.log N := by
    rw [primeRecipSum_eq_mertensS, ← meisselMertensConst_eq_mertensSecondConstant,
      le_div_iff₀ hlog]
    have hbound := mul_le_mul_of_nonneg_right
      ((le_abs_self _).trans hN) hlog.le
    dsimp only [Sieve.logLog] at hbound
    nlinarith only [hbound, hsmall]
  have hproduct : -Real.log (mertensPrimeProduct N) ≤
      Real.eulerMascheroniConstant + Real.log (Real.log N) + a / Real.log N := by
    rw [log_mertensPrimeProduct]
    rw [mertensSecondConstant_eq] at hsum
    linarith only [hsum, neg_primeLogDefect_le_partial N]
  calc (mertensPrimeProduct N)⁻¹ = Real.exp (-Real.log (mertensPrimeProduct N)) := by
        rw [Real.exp_neg, Real.exp_log (mertensPrimeProduct_pos N)]
    _ ≤ Real.exp (Real.eulerMascheroniConstant + Real.log (Real.log N) +
        a / Real.log N) := Real.exp_le_exp.mpr hproduct
    _ = Real.exp Real.eulerMascheroniConstant * Real.log N *
        Real.exp (a / Real.log N) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log hlog]

end

end RHTower
