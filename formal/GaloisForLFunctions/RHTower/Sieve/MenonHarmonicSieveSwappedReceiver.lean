import GaloisForLFunctions.RHTower.Sieve.DyadicPrimeMeanSquare
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicRamareBlockSwapped

/-!
# The swapped receiver with the two-dimensional sieve's prime mean square

`MenonHarmonicRamareBlockSwapped` pays the prime factor by reciprocal Halasz--Montgomery, whose
`hmMassRecip` carries the mean-value theorem's `N·∑|a_n|²` term — lossy by `N/W` once the prime
scale exceeds the frequency radius, which is exactly the regime where the swapped ordering is used.

The corpus already owns the sharp alternative for a dyadic prime block:
`Sieve/DyadicPrimeMeanSquare.integral_normSq_dyadicPrimePoly_le`, the two-dimensional sieve bound

```text
∫_{-W}^{W}|∑_{R<p≤2R}p^{-1+2πiw}|² dw
   ≤ (5/(4δR²))( π(2R)−π(R) + 2( 8e·K·R/E² + K·(Selberg remainder) ) ) ,
```

whose diagonal is the truthful `≍ W/(R log R)` and whose off-diagonal is `≍ (log R)^{-2}` — one
logarithm past the mean-value theorem.  This file feeds it through the swapped ordering, with the
cofactor paid by its own harmonic supremum.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- Product integral from a bounded second factor and a mean square for the first: the generic
form of the swapped ordering. -/
theorem setIntegral_normSq_product_le_meanSquareSup
    {F G : ℝ → ℂ} (hF : Continuous F) (hG : Continuous G) {W U I : ℝ}
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    (hbound : ∀ w ∈ E, ‖G w‖ ≤ U)
    (hI : (∫ w in E, ‖F w‖ ^ (2 : ℕ)) ≤ I) :
    (∫ w in E, ‖F w * G w‖ ^ (2 : ℕ)) ≤ U ^ (2 : ℕ) * I := by
  have hrw : (∫ w in E, ‖F w * G w‖ ^ (2 : ℕ))
      = ∫ w in E, ‖G w‖ ^ (2 : ℕ) * ‖F w‖ ^ (2 : ℕ) := by
    refine MeasureTheory.setIntegral_congr_fun hEm fun w _ => ?_
    rw [norm_mul, mul_pow, mul_comm]
  rw [hrw]
  refine le_trans (setIntegral_normSq_mul_le_of_bound hG hF hEm hEs hbound) ?_
  exact mul_le_mul_of_nonneg_left hI (by positivity)

/-- **The dyadic prime block against a harmonic cofactor, received by the two-dimensional
sieve.**  The prime factor is paid by its sharp sieve mean square and the cofactor by its own
harmonic supremum; no Halasz--Montgomery kernel and no mean-value diagonal enters. -/
theorem integral_Icc_normSq_dyadicPrimePoly_mul_harmonicCofactor_le
    (P D : Finset ℕ) {R h K k P₁ : ℕ} {δ W z : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hWδ : 2 * Real.pi * δ * W ≤ 1)
    (hK : 6 * (R : ℝ) * δ ≤ (K : ℝ)) (hhR : h ≤ R) (hR1 : 1 ≤ R)
    (hP₁ : 2 ≤ P₁) (hP₁h : P₁ ≤ h) (hh1 : 1 ≤ h) (hz : 1 ≤ z)
    (hlev : ((h : ℝ)) ^ (2 * k) ≤ z)
    (hk : Real.exp 1 * (∑ p ∈ rangePrimes P₁ h, 2 / ((p : ℝ) - 2)) + Real.log 2 ≤ (k : ℝ)) :
    (∫ w in Set.Icc (-W) W,
        ‖logPoly (fun n => ((1 : ℂ) / (n : ℂ))) (bigPrimeSet R (2 * R)) w
          * logPoly (harmonicRamareCofactorCoeff P) D w‖ ^ (2 : ℕ))
      ≤ harmonicPrimeMass D ^ (2 : ℕ) *
          ((5 / (4 * δ)) * (1 / (R : ℝ) ^ (2 : ℕ))
            * (((bigPrimeSet R (2 * R)).card : ℝ)
              + 2 * (2 * Real.exp 1 * (K : ℝ) * (2 * (R : ℝ))
                      / (Real.exp (mertensS h - mertensS P₁)) ^ (2 : ℕ)
                    + (K : ℝ) * ∑ e ∈ (rangePrimorial P₁ h).divisors,
                        (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0)))) := by
  have hsieve := integral_normSq_dyadicPrimePoly_le (R := R) (h := h) (K := K) (k := k)
    (P₁ := P₁) (δ := δ) (W := W) (z := z)
    hδ0 hδ1 hWδ hK hhR hR1 hP₁ hP₁h hh1 hz hlev hk
  exact setIntegral_normSq_product_le_meanSquareSup
    (continuous_logPoly _ _) (continuous_logPoly _ _) measurableSet_Icc (le_refl _)
    (fun w _ => norm_logPoly_harmonicRamareCofactorCoeff_le P D w) hsieve

end

end RHTower.Sieve
