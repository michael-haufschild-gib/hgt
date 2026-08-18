import GaloisForLFunctions.RHTower.Sieve.HalaszMontgomeryDyadic

/-!
# The dyadic second-derivative envelope in closed form

The endpoint envelope of the second-derivative test on a dyadic block has the exponent-pair shape
`√T + N/√U`: the top endpoint contributes the square root of the frequency window, the bottom
endpoint the reciprocal square root of the resonance threshold.  Written this way the
Halász--Montgomery constant reads `N + N log K/δ + K(√T + N/√U)`, which is the shape a
large-values argument optimises.
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

theorem logDyadicLambda_eq (N : ℕ) (t : ℝ) :
    logDyadicLambda N t = t / (8 * Real.pi * (N : ℝ) ^ 2) := by
  rw [logDyadicLambda]
  simp only [Nat.factorial_one, Nat.cast_one, mul_one]
  ring

/-- **The envelope in closed form.**  `B(N,U,T) ≤ 214√T + 1536·N/√U`. -/
theorem logDyadicSecondEnvelope_le {N : ℕ} (hN : 1 ≤ N) {U T : ℝ} (hU : 0 < U) (hT : 0 ≤ T) :
    logDyadicSecondEnvelope N U T
      ≤ 214 * Real.sqrt T + 1536 * ((N : ℝ) / Real.sqrt U) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  have hU0 : (0 : ℝ) < Real.sqrt U := Real.sqrt_pos.2 hU
  have hsqTU : Real.sqrt U * Real.sqrt U = U := Real.mul_self_sqrt hU.le
  have hsqTT : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT
  have hlamT0 : (0 : ℝ) ≤ 16 * logDyadicLambda N T := by
    rw [logDyadicLambda_eq]
    positivity
  have hlamU : (0 : ℝ) < logDyadicLambda N U := logDyadicLambda_pos hN hU
  -- the increasing endpoint
  have hNterm : (N : ℝ) * ((16 : ℝ) * logDyadicLambda N T) ^ ((1 : ℝ) / 2)
      ≤ (5 / 6) * Real.sqrt T := by
    rw [← Real.sqrt_eq_rpow]
    refine le_of_pow_le_pow_left₀ (two_ne_zero) (by positivity) ?_
    have hsq : (Real.sqrt (16 * logDyadicLambda N T)) ^ 2 = 16 * logDyadicLambda N T :=
      Real.sq_sqrt hlamT0
    have hL : ((N : ℝ) * Real.sqrt (16 * logDyadicLambda N T)) ^ 2
        = (N : ℝ) ^ 2 * (16 * logDyadicLambda N T) := by
      rw [mul_pow, hsq]
    have hR : ((5 / 6 : ℝ) * Real.sqrt T) ^ 2 = (25 / 36) * T := by
      rw [mul_pow, Real.sq_sqrt hT]
      ring
    rw [hL, hR, logDyadicLambda_eq]
    have hval : (N : ℝ) ^ 2 * (16 * (T / (8 * Real.pi * (N : ℝ) ^ 2))) = 2 * T / Real.pi := by
      field_simp
      ring
    rw [hval, div_le_iff₀ hpi]
    nlinarith [hT, hpi3]
  -- the decreasing endpoint
  have hUterm : (logDyadicLambda N U) ^ (-((1 : ℝ) / 2))
      ≤ 6 * ((N : ℝ) / Real.sqrt U) := by
    rw [Real.rpow_neg hlamU.le, ← Real.sqrt_eq_rpow]
    have hsq : Real.sqrt (logDyadicLambda N U) * Real.sqrt (logDyadicLambda N U)
        = logDyadicLambda N U := Real.mul_self_sqrt hlamU.le
    have hs0 : (0 : ℝ) < Real.sqrt (logDyadicLambda N U) := Real.sqrt_pos.2 hlamU
    refine le_of_pow_le_pow_left₀ (two_ne_zero) (by positivity) ?_
    have hL : ((Real.sqrt (logDyadicLambda N U))⁻¹) ^ 2 = (logDyadicLambda N U)⁻¹ := by
      rw [inv_pow, sq, hsq]
    have hquot : ((N : ℝ) / Real.sqrt U) ^ 2 = (N : ℝ) ^ 2 / U := by
      rw [div_pow, Real.sq_sqrt hU.le]
    have hR : ((6 : ℝ) * ((N : ℝ) / Real.sqrt U)) ^ 2
        = (36 * (N : ℝ) ^ 2) / U := by
      rw [mul_pow, hquot]
      ring
    rw [hL, hR, logDyadicLambda_eq]
    have hval : (U / (8 * Real.pi * (N : ℝ) ^ 2))⁻¹ = (8 * Real.pi * (N : ℝ) ^ 2) / U := by
      rw [inv_div]
    rw [hval]
    refine div_le_div_of_nonneg_right ?_ hU.le
    nlinarith [hpi4, hN0]
  rw [logDyadicSecondEnvelope]
  have hfin : (256 : ℝ) * ((N : ℝ) * (16 * logDyadicLambda N T) ^ ((1 : ℝ) / 2)
        + (logDyadicLambda N U) ^ (-((1 : ℝ) / 2)))
      ≤ 256 * ((5 / 6) * Real.sqrt T + 6 * ((N : ℝ) / Real.sqrt U)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    linarith
  refine hfin.trans ?_
  have hsqT : (0 : ℝ) ≤ Real.sqrt T := Real.sqrt_nonneg T
  have hNU : (0 : ℝ) ≤ (N : ℝ) / Real.sqrt U := by positivity
  nlinarith [hsqT, hNU]

/-- **Lemma 2.6 (Halász--Montgomery) in the exposé's shape.**  For one-separated frequencies in a
window of diameter `T`, the mean square of a dyadic Dirichlet polynomial over `K` of them is at
most `(N + N log K/δ + K(√T + N/√U))·‖a‖²`, with explicit absolute constants. -/
theorem halaszMontgomery_dyadic_explicit {N K : ℕ} (hN : 1 ≤ N) (a : EuclideanSpace ℂ (Fin N))
    {lam : ℕ → ℝ} {delta U T : ℝ} (hdelta : 0 < delta) (hU : 0 < U) (hT : 0 ≤ T)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hdiam : ∀ r ∈ Finset.range K, ∀ s ∈ Finset.range K, |lam s - lam r| ≤ T)
    (hnear : 3 * U ≤ 4 * Real.pi * (N : ℝ))
    (hlamT : logDyadicLambda N T ≤ 1) :
    ∑ r ∈ Finset.range K, ‖⟪dyadicDirRow N (lam r), a⟫_ℂ‖ ^ 2
      ≤ ((N : ℝ) + (12 * Real.pi * (N : ℝ) / delta) * (1 + Real.log K)
          + (K : ℝ) * (1 + 214 * Real.sqrt T + 1536 * ((N : ℝ) / Real.sqrt U))) * ‖a‖ ^ 2 := by
  have hsqT : (0 : ℝ) ≤ Real.sqrt T := Real.sqrt_nonneg T
  have hNU : (0 : ℝ) ≤ (N : ℝ) / Real.sqrt U := by
    have : (0 : ℝ) < Real.sqrt U := Real.sqrt_pos.2 hU
    positivity
  have hB1 : (1 : ℝ) ≤ 1 + 214 * Real.sqrt T + 1536 * ((N : ℝ) / Real.sqrt U) := by
    nlinarith [hsqT, hNU]
  have hB : logDyadicSecondEnvelope N U T
      ≤ 1 + 214 * Real.sqrt T + 1536 * ((N : ℝ) / Real.sqrt U) := by
    have := logDyadicSecondEnvelope_le hN hU hT
    linarith
  exact halaszMontgomery_dyadic_log hN a hdelta hU hgap hdiam hnear hlamT hB hB1

end RHTower.Sieve
