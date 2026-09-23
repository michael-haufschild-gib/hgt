import GaloisForLFunctions.RHTower.Sieve.GhsScaleCount

/-!
# The admissible window for the height

At `K = ghsScaleCount N` the height inequality becomes a condition on `n` alone: since
`4^K ≤ ((log N)/(4 log 2))²`, it is implied by

```text
(5/4n)·(16/9)·((log N)/(4 log 2))²·(log N + log 4) ≤ 1750·ghsShapeConst ,
```

which asks `n ≳ (log N)³`.  Against it stands `n² ≤ ghsScale N 1`, which asks `n ≤ N^{1/4}`.  The
window `(log N)³ ≪ n ≪ N^{1/4}` is where the argument lives, and every remaining hypothesis is a
statement about `N` and a height inside it.
-/

noncomputable section

namespace RHTower.Sieve

open Complex MeasureTheory Set Finset

/-- **The height inequality at the maximal scale count.** -/
theorem ghs_height_of_scaleCount {N n : ℕ} (hN : 16 ≤ N) (hn : 1 ≤ n)
    (hheight : (5 / (4 * (n : ℝ)))
        * ((16 / 9) * (Real.log N / (4 * Real.log 2)) ^ (2 : ℕ) * (Real.log N + Real.log 4))
      ≤ 1750 * ghsShapeConst) :
    (5 / (4 * (n : ℝ)))
        * ((16 / 9) * 4 ^ (ghsScaleCount N) * (Real.log N + Real.log 4))
      ≤ 1750 * ghsShapeConst := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hNR : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by linarith)
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcoef : (0 : ℝ) ≤ 5 / (4 * (n : ℝ)) := by positivity
  have hsum : (0 : ℝ) ≤ Real.log N + Real.log 4 := by linarith
  have hstep : (16 / 9 : ℝ) * 4 ^ (ghsScaleCount N) * (Real.log N + Real.log 4)
      ≤ (16 / 9) * (Real.log N / (4 * Real.log 2)) ^ (2 : ℕ) * (Real.log N + Real.log 4) := by
    have hpow := four_pow_ghsScaleCount_le hN
    nlinarith [hpow, hsum]
  exact le_trans (mul_le_mul_of_nonneg_left hstep hcoef) hheight

/-- **The mean value at the maximal scale count.**  Every hypothesis is now a statement about `N`
and a height `n` inside the admissible window. -/
theorem norm_sum_Icc_le_ghs_window
    {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hcm : ∀ p q : ℕ, f (p * q) = f p * f q)
    (hf : ∀ i : ℕ, ‖f i‖ ≤ 1)
    {N n z : ℕ} {σ δ : ℝ} (hσ : 1 < σ) (hz : 1 ≤ z) (hδ : 0 ≤ δ)
    (hunif : ∀ y : ℝ, |y| ≤ (n : ℝ) →
      δ ≤ Real.sqrt (mulDistSqPair f (charFn y) (Nat.primesLE z)))
    (hne : Real.exp 4 ≤ (n : ℝ)) (hN : 16 ≤ N)
    (hPN : n ^ (2 : ℕ) ≤ N) (hNP : 2 ≤ N / n ^ (2 : ℕ))
    (hroot : n ^ (2 : ℕ) ≤ ghsScale N 1)
    (hheight : (5 / (4 * (n : ℝ)))
        * ((16 / 9) * (Real.log N / (4 * Real.log 2)) ^ (2 : ℕ) * (Real.log N + Real.log 4))
      ≤ 1750 * ghsShapeConst) :
    ‖∑ m ∈ Finset.Icc 1 N, f m‖
      ≤ (ghsRecursionError N
            + ((ghsScaleCount N + 2 : ℕ) : ℝ)
              * (ghsTotalError N n (ghsScaleCount N) σ + (1 / (2 * Real.pi))
                  * (dampedSize σ δ z N * ((N : ℝ) + 1 / 2) ^ σ
                      * ghsBlockConstOf σ ghsShapeConst))) / Real.log (N : ℝ) := by
  have hn : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    rw [hn0] at hne
    simp only [Nat.cast_zero] at hne
    linarith [Real.exp_pos (4 : ℝ)]
  exact norm_sum_Icc_le_ghs_total hf1 hmul hcm hf hσ hz hδ hunif hn hne (by omega) hPN hNP
    hroot (two_pow_ghsScaleCount_le hN) (ghs_height_of_scaleCount hN hn hheight)

end RHTower.Sieve

end
