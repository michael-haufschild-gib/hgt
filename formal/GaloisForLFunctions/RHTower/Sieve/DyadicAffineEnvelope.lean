import GaloisForLFunctions.RHTower.Sieve.DyadicSecondEnvelopeClosed

/-!
# The dyadic phase bound in affine form

To sum the two regimes of the logarithmic phase over the dyadic blocks of `[1, M]` one needs each
block's bound in the shape `a + b·N` with `a`, `b` independent of the block.  The second-derivative
regime already has it, and — this is the point — so does the *trivial* regime: the second-derivative
test is unavailable exactly when `t > 8πN²`, and then `N < √(t/(8π)) < √t/5`, which is already
inside the `214√t` of the affine bound.  So the three-way split of the classical argument collapses
to a two-way one, and the affine bound holds unconditionally.
-/

namespace RHTower.Sieve

/-- The affine form of the second-derivative envelope at a single frequency. -/
theorem logDyadicSecondBound_le_affine {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (ht : 0 < t) :
    logDyadicSecondBound N t ≤ 214 * Real.sqrt t + 1536 * ((N : ℝ) / Real.sqrt t) := by
  have hEq : logDyadicSecondBound N t = logDyadicSecondEnvelope N t t := rfl
  rw [hEq]
  exact logDyadicSecondEnvelope_le hN ht ht.le

/-- **The trivial bound is already affine when the second-derivative test is unavailable.**  If
`logDyadicLambda N t > 1` then `8πN² < t`, so `N < √t/5`. -/
theorem trivial_le_affine {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (ht : 0 < t)
    (hbig : 1 < logDyadicLambda N t) :
    (N : ℝ) ≤ 214 * Real.sqrt t + 1536 * ((N : ℝ) / Real.sqrt t) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hsq : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.2 ht
  have hsqsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  -- `logDyadicLambda N t = t / (8πN²)`
  have hlam : logDyadicLambda N t = t / (2 * Real.pi) / (2 * (N : ℝ)) ^ (2 : ℕ) := by
    rw [logDyadicLambda]
    norm_num
  rw [hlam] at hbig
  have hden : (0 : ℝ) < (2 * (N : ℝ)) ^ (2 : ℕ) := by positivity
  have h2pi : (0 : ℝ) < 2 * Real.pi := by linarith
  have hgt : (2 * (N : ℝ)) ^ (2 : ℕ) < t / (2 * Real.pi) := by
    rw [lt_div_iff₀ hden] at hbig
    linarith [hbig]
  have hkey : 8 * Real.pi * (N : ℝ) ^ (2 : ℕ) < t := by
    rw [lt_div_iff₀ h2pi] at hgt
    nlinarith [hgt]
  have hNsq : 25 * (N : ℝ) ^ (2 : ℕ) < t := by nlinarith [hkey, hpi, sq_nonneg ((N : ℝ))]
  have hNle : (N : ℝ) ≤ Real.sqrt t / 5 := by
    have h5 : (0 : ℝ) < 5 := by norm_num
    rw [le_div_iff₀ h5]
    nlinarith [hNsq, hsqsq, hsq, hN0]
  have hfrac : (0 : ℝ) ≤ 1536 * ((N : ℝ) / Real.sqrt t) := by positivity
  nlinarith [hNle, hsq, hfrac]

end RHTower.Sieve
