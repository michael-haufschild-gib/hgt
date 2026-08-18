import GaloisForLFunctions.RHTower.Sieve.PrimePairNeighbour

/-!
# The mean square of a dyadic prime Dirichlet polynomial

Feeding the shifted prime-pair sieve into the almost-diagonal mean value theorem gives the estimate
that the all-interval `E₃` argument consumes for its two large prime variables:

```text
∫_{-W}^{W} |∑_{R < p ≤ 2R} p^{-1+2πiw}|² dw
    ≤ (5/(4δR²)) ( π(2R) − π(R) + 2 ( 8e·K·R/E² + K·(sieve remainder) ) ) ,
```

valid whenever `2πδW ≤ 1`, `K ≥ 6Rδ` and the sieve parameters are admissible, with
`E = exp(mertensS h − mertensS P₁) ≍ log h/log P₁`.  The first term is the diagonal, of size
`≍ W/(R log R)`; the second is the off-diagonal, of size `≍ 1/(log h)²` — one logarithm better than
the mean value theorem alone, which is the whole point of the two-dimensional sieve.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **The neighbour mass of a dyadic prime block, bounded by the sieve.** -/
theorem sum_logNeighbourCount_sieve_le {R h K k P₁ : ℕ} {δ z : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hK : 6 * (R : ℝ) * δ ≤ (K : ℝ)) (hhR : h ≤ R)
    (hP₁ : 2 ≤ P₁) (hP₁h : P₁ ≤ h) (hh1 : 1 ≤ h) (hz : 1 ≤ z)
    (hlev : ((h : ℝ)) ^ (2 * k) ≤ z)
    (hk : Real.exp 1 * (∑ p ∈ rangePrimes P₁ h, 2 / ((p : ℝ) - 2)) + Real.log 2 ≤ (k : ℝ)) :
    ∑ n ∈ bigPrimeSet R (2 * R),
        (logNeighbourCount (bigPrimeSet R (2 * R)) δ n : ℝ)
      ≤ ((bigPrimeSet R (2 * R)).card : ℝ)
        + 2 * (2 * Real.exp 1 * (K : ℝ) * (2 * (R : ℝ))
                / (Real.exp (mertensS h - mertensS P₁)) ^ 2
              + (K : ℝ) * ∑ e ∈ (rangePrimorial P₁ h).divisors,
                  (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0)) := by
  classical
  have hY : (0 : ℝ) ≤ 2 * (R : ℝ) := by positivity
  have hfloor : ⌊(2 * (R : ℝ))⌋₊ = 2 * R := by
    rw [show (2 * (R : ℝ)) = ((2 * R : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
  have hpair := sum_card_primePair_le (2 * (R : ℝ)) hP₁ (h := h) K k hz hY hh1 hP₁h hlev hk
  rw [hfloor] at hpair
  refine le_trans (sum_logNeighbourCount_bigPrimeSet_le hδ0 hδ1 hK hhR) ?_
  linarith [hpair]

/-- **The mean square of a dyadic prime Dirichlet polynomial.** -/
theorem integral_normSq_dyadicPrimePoly_le {R h K k P₁ : ℕ} {δ W z : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hWδ : 2 * Real.pi * δ * W ≤ 1)
    (hK : 6 * (R : ℝ) * δ ≤ (K : ℝ)) (hhR : h ≤ R) (hR1 : 1 ≤ R)
    (hP₁ : 2 ≤ P₁) (hP₁h : P₁ ≤ h) (hh1 : 1 ≤ h) (hz : 1 ≤ z)
    (hlev : ((h : ℝ)) ^ (2 * k) ≤ z)
    (hk : Real.exp 1 * (∑ p ∈ rangePrimes P₁ h, 2 / ((p : ℝ) - 2)) + Real.log 2 ≤ (k : ℝ)) :
    (∫ w in Set.Icc (-W) W,
        ‖logPoly (fun n => ((1 : ℂ) / (n : ℂ))) (bigPrimeSet R (2 * R)) w‖ ^ 2)
      ≤ (5 / (4 * δ)) * (1 / (R : ℝ) ^ 2)
          * (((bigPrimeSet R (2 * R)).card : ℝ)
            + 2 * (2 * Real.exp 1 * (K : ℝ) * (2 * (R : ℝ))
                    / (Real.exp (mertensS h - mertensS P₁)) ^ 2
                  + (K : ℝ) * ∑ e ∈ (rangePrimorial P₁ h).divisors,
                      (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0))) := by
  classical
  set s : Finset ℕ := bigPrimeSet R (2 * R) with hs
  set a : ℕ → ℂ := fun n => ((1 : ℂ) / (n : ℂ)) with ha
  have hR0 : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR1
  have hcoef : ∀ n ∈ s, ‖a n‖ ^ 2 ≤ 1 / (R : ℝ) ^ 2 := by
    intro n hn
    rw [hs, bigPrimeSet, Finset.mem_filter, Finset.mem_Icc] at hn
    have hnR : (R : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : R ≤ n)
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hnorm : ‖a n‖ = 1 / (n : ℝ) := by
      rw [ha]
      simp only [norm_div, norm_one, Complex.norm_natCast]
    rw [hnorm, div_pow, one_pow]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith [hnR, hR0])
  have hbase := integral_Icc_normSq_logPoly_le_count a s hδ0 hWδ
  have hstep : ∑ n ∈ s, (logNeighbourCount s δ n : ℝ) * ‖a n‖ ^ 2
      ≤ (1 / (R : ℝ) ^ 2) * ∑ n ∈ s, (logNeighbourCount s δ n : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hc0 : (0 : ℝ) ≤ (logNeighbourCount s δ n : ℝ) := Nat.cast_nonneg _
    have := hcoef n hn
    nlinarith [hc0, this]
  have hsieve := sum_logNeighbourCount_sieve_le (R := R) (h := h) (K := K) (k := k) (P₁ := P₁)
    (δ := δ) (z := z) hδ0 hδ1 hK hhR hP₁ hP₁h hh1 hz hlev hk
  have hpos : (0 : ℝ) ≤ 5 / (4 * δ) := by positivity
  have hR2 : (0 : ℝ) ≤ 1 / (R : ℝ) ^ 2 := by positivity
  calc (∫ w in Set.Icc (-W) W, ‖logPoly a s w‖ ^ 2)
      ≤ (5 / (4 * δ)) * ∑ n ∈ s, (logNeighbourCount s δ n : ℝ) * ‖a n‖ ^ 2 := hbase
    _ ≤ (5 / (4 * δ)) * ((1 / (R : ℝ) ^ 2) * ∑ n ∈ s, (logNeighbourCount s δ n : ℝ)) :=
        mul_le_mul_of_nonneg_left hstep hpos
    _ ≤ (5 / (4 * δ)) * ((1 / (R : ℝ) ^ 2)
          * (((bigPrimeSet R (2 * R)).card : ℝ)
            + 2 * (2 * Real.exp 1 * (K : ℝ) * (2 * (R : ℝ))
                    / (Real.exp (mertensS h - mertensS P₁)) ^ 2
                  + (K : ℝ) * ∑ e ∈ (rangePrimorial P₁ h).divisors,
                      (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0)))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsieve hR2) hpos
    _ = (5 / (4 * δ)) * (1 / (R : ℝ) ^ 2)
          * (((bigPrimeSet R (2 * R)).card : ℝ)
            + 2 * (2 * Real.exp 1 * (K : ℝ) * (2 * (R : ℝ))
                    / (Real.exp (mertensS h - mertensS P₁)) ^ 2
                  + (K : ℝ) * ∑ e ∈ (rangePrimorial P₁ h).divisors,
                      (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0))) := by
        ring

end

end RHTower.Sieve
