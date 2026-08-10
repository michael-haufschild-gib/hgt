import GaloisForLFunctions.RHTower.Sieve.GhsFullAssembly

/-!
# The parameters, reduced to four scalar inequalities

Of the conditions `norm_sum_Icc_le_ghs_full` imposes, four are consequences of the others:

* `2 ≤ ⌊N/B_k⌋` follows from the threshold, since `⌊N/B_k⌋ ≥ ghsScale N (k+1) ≥ 2`;
* `n² ≤ A_k` for `k ≥ 1` follows from `n² ≤ ghsBlockRight N 0`, since the endpoints increase;
* `n² ≤ ghsBlockRight N 0` follows from `n² ≤ ghsScale N 1`, because
  `ghsScale N 1 ≤ ⌊N/ghsScale N 1⌋` — the square root scale is below its own complement;
* the threshold and the height inequality are monotone in the block index, so only the last block
  has to be checked.

What is left for the caller is: `e⁴ ≤ n`, `n² ≤ ghsScale N 1`, `2^K·4·log 2 ≤ log N`, and one height
inequality at `4^K`.
-/

noncomputable section

namespace RHTower.Sieve

open Complex MeasureTheory Set Finset

/-- **The square-root scale is below its own complement.** -/
theorem ghsScale_le_ghsBlockRight_zero {N : ℕ} (hN : 1 ≤ N) :
    ghsScale N 1 ≤ ghsBlockRight N 0 := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hs1 : 1 ≤ ghsScale N 1 := one_le_ghsScale hN
  have hfl : ((ghsScale N 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 ^ (1 : ℕ)) := by
    rw [ghsScale]
    exact Nat.floor_le (Real.rpow_nonneg hN0.le _)
  have hsq : ((ghsScale N 1 * ghsScale N 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
    have hroot : ((N : ℝ) ^ ((1 : ℝ) / 2 ^ (1 : ℕ))) * ((N : ℝ) ^ ((1 : ℝ) / 2 ^ (1 : ℕ)))
        = (N : ℝ) := by
      rw [← Real.rpow_add hN0]
      norm_num
    have h0 : (0 : ℝ) ≤ ((ghsScale N 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    push_cast
    nlinarith [hfl, hroot, h0]
  have hrw : ghsBlockRight N 0 = N / ghsScale N 1 := by norm_num [ghsBlockRight]
  rw [hrw, Nat.le_div_iff_mul_le (by omega)]
  exact_mod_cast hsq

/-- The complementary scale of every block is at least two. -/
theorem two_le_div_ghsBlockRight {N k : ℕ} (hN : 1 ≤ N)
    (hk : (2 : ℝ) ^ (k + 1) * Real.log 2 ≤ Real.log N) :
    2 ≤ N / ghsBlockRight N k := by
  have hs : 2 ≤ ghsScale N (k + 1) := ghsScale_pos hN hk
  exact le_trans hs (le_div_div (by omega) (ghsScale_le hN))

/-- **The mean value with the parameters reduced.** -/
theorem norm_sum_Icc_le_ghs_reduced
    {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hcm : ∀ p q : ℕ, f (p * q) = f p * f q)
    (hf : ∀ i : ℕ, ‖f i‖ ≤ 1)
    {N n z K : ℕ} {σ δ E : ℝ} (hσ : 1 < σ) (hz : 1 ≤ z) (hδ : 0 ≤ δ)
    (hunif : ∀ y : ℝ, |y| ≤ (n : ℝ) →
      δ ≤ Real.sqrt (mulDistSqPair f (charFn y) (Nat.primesLE z)))
    (hn : 1 ≤ n) (hne : Real.exp 4 ≤ (n : ℝ)) (hN : 2 ≤ N)
    (hPN : n ^ 2 ≤ N) (hNP : 2 ≤ N / n ^ 2)
    (hroot : n ^ 2 ≤ ghsScale N 1)
    (hK : (2 : ℝ) ^ K * (4 * Real.log 2) ≤ Real.log N)
    (hheightK : (5 / (4 * (n : ℝ))) * ((16 / 9) * 4 ^ K * (Real.log N + Real.log 4))
        ≤ 1750 * ghsShapeConst)
    (hE1 : ghsUniformError N n σ ≤ E)
    (hE2 : (N : ℝ) * (((Real.log ((n ^ 2 : ℕ) : ℝ) + Real.log 4)
              / Real.log ((N / n ^ 2 : ℕ) : ℝ)) * (Real.log N + Real.log 4)) ≤ E)
    (hE3 : (N : ℝ) * (((1 / Real.log 2)
              * (Real.log (N : ℝ) - Real.log ((ghsPart N n (K + 1) : ℕ) : ℝ)
                  + mertensBlockGapConst))
            * (Real.log ((N / ghsPart N n (K + 1) : ℕ) : ℝ) + Real.log 4)) ≤ E) :
    ‖∑ m ∈ Finset.Icc 1 N, f m‖
      ≤ (ghsRecursionError N
            + ((K + 2 : ℕ) : ℝ)
              * (E + (1 / (2 * Real.pi))
                  * (dampedSize σ δ z N * ((N : ℝ) + 1 / 2) ^ σ
                      * ghsBlockConstOf σ ghsShapeConst))) / Real.log (N : ℝ) := by
  have hN1 : 1 ≤ N := by omega
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hA0 : n ^ 2 ≤ ghsBlockRight N 0 :=
    le_trans hroot (ghsScale_le_ghsBlockRight_zero hN1)
  -- the threshold is monotone in the block index
  have hthr : ∀ k, k < K → (2 : ℝ) ^ (k + 1) * (4 * Real.log 2) ≤ Real.log N := by
    intro k hk
    have hmono : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ K :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith [hK, hmono, hlog2]
  have hthr' : ∀ k, k < K → (2 : ℝ) ^ (k + 1) * Real.log 2 ≤ Real.log N := by
    intro k hk
    have h := hthr k hk
    have hpow : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
    nlinarith [h, hlog2, hpow]
  refine norm_sum_Icc_le_ghs_full hf1 hmul hcm hf hσ hz hδ hunif hn hne hN hPN hNP hA0
    hthr (fun k hk => two_le_div_ghsBlockRight hN1 (hthr' k hk))
    (fun k hk1 _ => le_trans hA0 ?_) ?_ hE1 hE2 hE3
  · rw [ghsBlockRight_eq_left_succ]
    exact ghsBlockLeft_mono hN1 hk1
  · intro k hk
    have hmono : (4 : ℝ) ^ (k + 1) ≤ (4 : ℝ) ^ K :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hlogN : (0 : ℝ) < Real.log N := by
      have hpow : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
      nlinarith [hK, hlog2, hpow]
    have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hcoef : (0 : ℝ) ≤ 5 / (4 * (n : ℝ)) := by positivity
    have hstep : (16 / 9 : ℝ) * 4 ^ (k + 1) * (Real.log N + Real.log 4)
        ≤ (16 / 9) * 4 ^ K * (Real.log N + Real.log 4) := by
      have : (0 : ℝ) ≤ Real.log N + Real.log 4 := by linarith
      nlinarith [hmono, this]
    exact le_trans (mul_le_mul_of_nonneg_left hstep hcoef) hheightK

end RHTower.Sieve

end
