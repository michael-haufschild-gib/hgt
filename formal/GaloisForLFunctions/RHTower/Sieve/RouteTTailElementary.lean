import GaloisForLFunctions.RHTower.Sieve.RouteTTailSurrogate

/-!
# The tail regimes stripped to their essential shape

The three regimes of `Sieve/RouteTTailSurrogate` still carry the inner constants `3i`, `2i` and the
square root.  All three are removed here by elementary comparisons — `(3i)^{-a} ≤ i^{-a}`,
`log(2i) ≤ 2 log i`, `(3i)^v = 3^v i^v`, `log i ≤ 4 i^{1/4}` — leaving

```text
   contour     :  9C·i^{−m/6}·(HF + 2 log i)          ≤ ρ₀
   truncation  :  9C·3^v·i^v·(1 + (log i)² + HF)/|t|  ≤ ρ₀
   Chebyshev   :  24·i^{−1/4}                          ≤ ρ₀ ,
```

which is the form the schedule is substituted into.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- `log i ≤ 4·i^{1/4}`. -/
theorem log_le_four_mul_rpow_quarter {i : ℝ} (hi : 1 ≤ i) :
    Real.log i ≤ 4 * i ^ ((1 : ℝ) / 4) := by
  have hi0 : (0 : ℝ) < i := by linarith
  have hq : (0 : ℝ) < i ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hi0 _
  have h := Real.log_le_sub_one_of_pos hq
  rw [Real.log_rpow hi0] at h
  linarith

/-- **The Chebyshev regime.** -/
theorem cheb_regime_le {i : ℝ} (hi : 1 ≤ i) :
    6 * Real.log i / Real.sqrt i ≤ 24 * i ^ (-((1 : ℝ) / 4)) := by
  have hi0 : (0 : ℝ) < i := by linarith
  have hsq : Real.sqrt i = i ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow i
  have hlog := log_le_four_mul_rpow_quarter hi
  have hsqrtpos : (0 : ℝ) < i ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hi0 _
  rw [hsq, div_le_iff₀ hsqrtpos]
  have hval : 24 * i ^ (-((1 : ℝ) / 4)) * i ^ ((1 : ℝ) / 2) = 24 * i ^ ((1 : ℝ) / 4) := by
    rw [mul_assoc, ← Real.rpow_add hi0]
    norm_num
  rw [hval]
  linarith

/-- **The contour regime.** -/
theorem contour_regime_le {C HF m i : ℝ} (hC : 0 ≤ C) (hi : 2 ≤ i) (hm : 0 ≤ m) (hHF : 0 ≤ HF) :
    9 * C * ((3 * i) ^ (-(m / 6)) * (HF + Real.log (2 * i)))
      ≤ 9 * C * (i ^ (-(m / 6)) * (HF + 2 * Real.log i)) := by
  have hi0 : (0 : ℝ) < i := by linarith
  have hi1 : (1 : ℝ) ≤ i := by linarith
  have hlogi : (0 : ℝ) ≤ Real.log i := Real.log_nonneg hi1
  have hlog2 : Real.log 2 ≤ Real.log i := Real.log_le_log (by norm_num) hi
  have hlog2i : Real.log (2 * i) ≤ 2 * Real.log i := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hi0)]
    linarith
  have h3i : (3 * i) ^ (-(m / 6)) ≤ i ^ (-(m / 6)) := by
    rw [Real.mul_rpow (by norm_num) hi0.le]
    have h3 : (3 : ℝ) ^ (-(m / 6)) ≤ 1 := by
      refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hip : (0 : ℝ) < i ^ (-(m / 6)) := Real.rpow_pos_of_pos hi0 _
    nlinarith [h3, hip]
  have hfac : HF + Real.log (2 * i) ≤ HF + 2 * Real.log i := by linarith
  have h3i0 : (0 : ℝ) ≤ (3 * i) ^ (-(m / 6)) := Real.rpow_nonneg (by linarith) _
  have hfac0 : (0 : ℝ) ≤ HF + Real.log (2 * i) := by
    have : (0 : ℝ) ≤ Real.log (2 * i) := Real.log_nonneg (by linarith)
    linarith
  have hmul := mul_le_mul h3i hfac hfac0 (Real.rpow_nonneg hi0.le _)
  nlinarith [hmul, hC]

/-- **The truncation regime.** -/
theorem trunc_regime_le {C HF v i tt : ℝ} (hC : 0 ≤ C) (hi : 1 ≤ i) (hHF : 0 ≤ HF)
    (ht : 1 ≤ tt) :
    9 * C * ((3 * i) ^ v * (1 + (Real.log i) ^ 2 + HF)) / (1 + tt)
      ≤ 9 * C * ((3 : ℝ) ^ v * i ^ v * (1 + (Real.log i) ^ 2 + HF)) / tt := by
  have hi0 : (0 : ℝ) < i := by linarith
  have ht0 : (0 : ℝ) < tt := by linarith
  have hsplit : (3 * i) ^ v = (3 : ℝ) ^ v * i ^ v := Real.mul_rpow (by norm_num) hi0.le
  rw [hsplit]
  have hnum0 : (0 : ℝ) ≤ 9 * C * ((3 : ℝ) ^ v * i ^ v * (1 + (Real.log i) ^ 2 + HF)) := by
    have h1 : (0 : ℝ) ≤ (3 : ℝ) ^ v := Real.rpow_nonneg (by norm_num) _
    have h2 : (0 : ℝ) ≤ i ^ v := Real.rpow_nonneg hi0.le _
    have h3 : (0 : ℝ) ≤ 1 + (Real.log i) ^ 2 + HF := by positivity
    positivity
  exact div_le_div_of_nonneg_left hnum0 ht0 (by linarith)

/-- **The tail cosine sum through the elementary regimes.** -/
theorem exists_abs_sum_cos_div_primesRange_le_elementary :
    ∃ A delta C : ℝ, 0 < delta ∧ 0 < C ∧
      ∀ (y z : ℕ) (t ρ₀ : ℝ), 2 ≤ y → y ≤ z → 0 ≤ ρ₀ →
        16 * Real.pi / 3 ≤ |t| →
        14 * Real.exp 9 ≤ ρ₀ * (y : ℝ) →
        (∀ i : ℕ, y ≤ i → i ≤ z →
          9 * C * ((i : ℝ) ^ (-(min delta (routeTWidthLowSurrogate A (-t)) / 6))
            * (routeTHeightFactorUpper A (-t) + 2 * Real.log (i : ℝ))) ≤ ρ₀) →
        (∀ i : ℕ, y ≤ i → i ≤ z →
          9 * C * ((3 : ℝ) ^ (2 * (1 / (routeTWidthUpperConst
                * (Real.log |t| / Real.log 2) ^ ((9 : ℝ) / 10))) / 3)
              * (i : ℝ) ^ (2 * (1 / (routeTWidthUpperConst
                * (Real.log |t| / Real.log 2) ^ ((9 : ℝ) / 10))) / 3)
              * (1 + (Real.log (i : ℝ)) ^ 2 + routeTHeightFactorUpper A (-t))) / |t| ≤ ρ₀) →
        (∀ i : ℕ, y ≤ i → i ≤ z → 24 * (i : ℝ) ^ (-((1 : ℝ) / 4)) ≤ ρ₀) →
        |∑ p ∈ primesRange y z, Real.cos (t * Real.log (p : ℝ)) / (p : ℝ)|
          ≤ 9 * ρ₀ * (2 + Real.log (z : ℝ)) := by
  obtain ⟨A, delta, C, hdelta, hC, hbound⟩ := exists_abs_sum_cos_div_primesRange_le_surrogate
  refine ⟨A, delta, C, hdelta, hC, ?_⟩
  intro y z t ρ₀ hy hyz hρ₀ hτ he9 h1 h2 h3
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have ht1 : (1 : ℝ) ≤ |t| := by linarith
  have hτ1 : (1 : ℝ) ≤ |(-t : ℝ)| := by rw [abs_neg]; exact ht1
  have hHF0 : (0 : ℝ) ≤ routeTHeightFactorUpper A (-t) := by
    have := routeTTwistHeightFactor_nonneg A (-t)
    have hup := routeTTwistHeightFactor_le_surrogate (A := A) (τ := -t) (by rw [abs_neg]; exact hτ)
    linarith
  have hmin0 : (0 : ℝ) ≤ min delta (routeTWidthLowSurrogate A (-t)) := by
    refine le_min hdelta.le ?_
    rw [routeTWidthLowSurrogate]
    have := routeTWidthReciprocalSurrogate_pos A (-t)
    positivity
  refine hbound y z t ρ₀ (by omega) hyz hρ₀ hτ he9 ?_ ?_ ?_
  · intro i hyi hiz
    have hi2 : (2 : ℝ) ≤ (i : ℝ) := by exact_mod_cast le_trans hy hyi
    exact le_trans (contour_regime_le hC.le hi2 hmin0 hHF0) (h1 i hyi hiz)
  · intro i hyi hiz
    have hi1 : (1 : ℝ) ≤ (i : ℝ) := by
      have : 1 ≤ i := le_trans (by omega) hyi
      exact_mod_cast this
    exact le_trans (trunc_regime_le hC.le hi1 hHF0 ht1) (h2 i hyi hiz)
  · intro i hyi hiz
    have hi1 : (1 : ℝ) ≤ (i : ℝ) := by
      have : 1 ≤ i := le_trans (by omega) hyi
      exact_mod_cast this
    exact le_trans (cheb_regime_le hi1) (h3 i hyi hiz)

end

end RHTower.Sieve
