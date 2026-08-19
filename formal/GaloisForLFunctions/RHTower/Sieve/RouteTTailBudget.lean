import GaloisForLFunctions.RHTower.Sieve.RouteTSurrogateSize

/-!
# The tail regimes in `log i` and `log|t|` alone

Substituting the budgets of `Sieve/RouteTSurrogateSize` into the three regimes of
`Sieve/RouteTTailElementary` removes the last nested surrogate.  With

```text
   G  := routeTReciprocalBudget A t ,      v := routeTTruncExponent t ,
```

the Granville–Soundararajan tail is bounded as soon as, at every block top `i` of the range,

```text
   contour     :  9C·i^{−min(delta, 1/G)/6}·(1 + (4+log|t|)G + 2 log i)  ≤ ρ₀ ,
   truncation  :  9C·3^v·i^v·(2 + (log i)² + (4+log|t|)G)/|t|            ≤ ρ₀ ,
   Chebyshev   :  24·i^{−1/4}                                            ≤ ρ₀ .
```

Every quantity here is an explicit elementary function of `i` and `|t|`.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The Perron truncation exponent. -/
def routeTTruncExponent (t : ℝ) : ℝ :=
  2 * (1 / (routeTWidthUpperConst * (Real.log |t| / Real.log 2) ^ ((9 : ℝ) / 10))) / 3

/-- **The tail cosine sum through the budgets.** -/
theorem exists_abs_sum_cos_div_primesRange_le_budget :
    ∃ A delta C : ℝ, 0 < delta ∧ 0 < C ∧
      ∀ (y z : ℕ) (t ρ₀ : ℝ), 2 ≤ y → y ≤ z → 0 ≤ ρ₀ →
        16 * Real.pi / 3 ≤ |t| →
        14 * Real.exp 9 ≤ ρ₀ * (y : ℝ) →
        (∀ i : ℕ, y ≤ i → i ≤ z →
          9 * C * ((i : ℝ) ^ (-(min delta (1 / routeTReciprocalBudget A t) / 6))
            * (1 + (4 + Real.log |t|) * routeTReciprocalBudget A t
                + 2 * Real.log (i : ℝ))) ≤ ρ₀) →
        (∀ i : ℕ, y ≤ i → i ≤ z →
          9 * C * ((3 : ℝ) ^ routeTTruncExponent t * (i : ℝ) ^ routeTTruncExponent t
              * (2 + (Real.log (i : ℝ)) ^ 2
                  + (4 + Real.log |t|) * routeTReciprocalBudget A t)) / |t| ≤ ρ₀) →
        (∀ i : ℕ, y ≤ i → i ≤ z → 24 * (i : ℝ) ^ (-((1 : ℝ) / 4)) ≤ ρ₀) →
        |∑ p ∈ primesRange y z, Real.cos (t * Real.log (p : ℝ)) / (p : ℝ)|
          ≤ 9 * ρ₀ * (2 + Real.log (z : ℝ)) := by
  obtain ⟨A, delta, C, hdelta, hC, hbound⟩ := exists_abs_sum_cos_div_primesRange_le_elementary
  refine ⟨A, delta, C, hdelta, hC, ?_⟩
  intro y z t ρ₀ hy hyz hρ₀ hτ he9 h1 h2 h3
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have ht1 : (1 : ℝ) ≤ |t| := by linarith
  have hwid := routeTWidthLowSurrogate_ge (A := A) ht1
  have hHF := routeTHeightFactorUpper_le (A := A) ht1
  refine hbound y z t ρ₀ hy hyz hρ₀ hτ he9 ?_ ?_ h3
  · intro i hyi hiz
    refine le_trans ?_ (h1 i hyi hiz)
    have hi1 : (1 : ℝ) ≤ (i : ℝ) := by
      have : 1 ≤ i := le_trans (by omega) hyi
      exact_mod_cast this
    have hmin : min delta (1 / routeTReciprocalBudget A t)
        ≤ min delta (routeTWidthLowSurrogate A (-t)) :=
      le_min (min_le_left _ _) (le_trans (min_le_right _ _) hwid)
    have hexp : (i : ℝ) ^ (-(min delta (routeTWidthLowSurrogate A (-t)) / 6))
        ≤ (i : ℝ) ^ (-(min delta (1 / routeTReciprocalBudget A t) / 6)) :=
      Real.rpow_le_rpow_of_exponent_le hi1 (by linarith)
    have hlogi : (0 : ℝ) ≤ Real.log (i : ℝ) := Real.log_nonneg hi1
    have hHF0 : (0 : ℝ) ≤ routeTHeightFactorUpper A (-t) := by
      have hnn := routeTTwistHeightFactor_nonneg A (-t)
      have hup := routeTTwistHeightFactor_le_surrogate (A := A) (τ := -t)
        (by rw [abs_neg]; exact hτ)
      linarith
    have hfac : routeTHeightFactorUpper A (-t) + 2 * Real.log (i : ℝ)
        ≤ 1 + (4 + Real.log |t|) * routeTReciprocalBudget A t + 2 * Real.log (i : ℝ) := by
      linarith
    have hfac0 : (0 : ℝ) ≤ routeTHeightFactorUpper A (-t) + 2 * Real.log (i : ℝ) := by linarith
    have hmul := mul_le_mul hexp hfac hfac0 (Real.rpow_nonneg (by linarith) _)
    nlinarith [hmul, hC.le]
  · intro i hyi hiz
    refine le_trans ?_ (h2 i hyi hiz)
    have hi1 : (1 : ℝ) ≤ (i : ℝ) := by
      have : 1 ≤ i := le_trans (by omega) hyi
      exact_mod_cast this
    have ht0 : (0 : ℝ) < |t| := by linarith
    have hHF0 : (0 : ℝ) ≤ routeTHeightFactorUpper A (-t) := by
      have hnn := routeTTwistHeightFactor_nonneg A (-t)
      have hup := routeTTwistHeightFactor_le_surrogate (A := A) (τ := -t)
        (by rw [abs_neg]; exact hτ)
      linarith
    have hfac : 1 + (Real.log (i : ℝ)) ^ 2 + routeTHeightFactorUpper A (-t)
        ≤ 2 + (Real.log (i : ℝ)) ^ 2 + (4 + Real.log |t|) * routeTReciprocalBudget A t := by
      linarith
    have hpow0 : (0 : ℝ) ≤ (3 : ℝ) ^ routeTTruncExponent t * (i : ℝ) ^ routeTTruncExponent t := by
      have h1' : (0 : ℝ) ≤ (3 : ℝ) ^ routeTTruncExponent t := Real.rpow_nonneg (by norm_num) _
      have h2' : (0 : ℝ) ≤ (i : ℝ) ^ routeTTruncExponent t := Real.rpow_nonneg (by linarith) _
      positivity
    have hmul := mul_le_mul_of_nonneg_left hfac hpow0
    have hCmul := mul_le_mul_of_nonneg_left hmul (by positivity : (0:ℝ) ≤ 9 * C)
    have hstep : 9 * C * ((3 : ℝ) ^ routeTTruncExponent t * (i : ℝ) ^ routeTTruncExponent t
          * (1 + (Real.log (i : ℝ)) ^ 2 + routeTHeightFactorUpper A (-t)))
        ≤ 9 * C * ((3 : ℝ) ^ routeTTruncExponent t * (i : ℝ) ^ routeTTruncExponent t
          * (2 + (Real.log (i : ℝ)) ^ 2
              + (4 + Real.log |t|) * routeTReciprocalBudget A t)) := by
      nlinarith [hCmul]
    exact div_le_div_of_nonneg_right hstep ht0.le

end

end RHTower.Sieve
