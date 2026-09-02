import GaloisForLFunctions.RHTower.Sieve.KloostermanProductFrequencySliceBound
import GaloisForLFunctions.RHTower.Sieve.KloostermanAnalyticFrontier

/-!
# Product-harmonic aggregation for the terminal Kloosterman quadratic

The shared-gcd-safe pair estimate is restored through every signed modulus weight and source
coefficient.  Because the pair bound is independent of physical interval length and source
indices, the full terminal quadratic is controlled by source \`ℓ¹\` mass squared times one explicit
modulus-pair budget.  This is an unconditional absolute-value baseline, not a spectral estimate.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

def kloostermanProductHarmonicPairBudget (q r : ℕ) : ℝ :=
  min
    ((Nat.totient (q + 1) : ℝ) *
      ((((q + 1) * (r + 1) : ℕ) : ℝ) *
        (1 + Real.log ((q + 1) * (r + 1)))))
    ((Nat.totient (r + 1) : ℝ) *
      ((((q + 1) * (r + 1) : ℕ) : ℝ) *
        (1 + Real.log ((q + 1) * (r + 1)))))

def kloostermanDistinctModulusProductHarmonicBudget (Q : Finset ℕ) (w : ℕ → ℂ) : ℝ :=
  ∑ q ∈ Q, ‖w q‖ * ∑ r ∈ Q.erase q, ‖w r‖ * kloostermanProductHarmonicPairBudget q r

theorem kloostermanProductHarmonicPairBudget_nonneg (q r : ℕ) : 0 ≤ kloostermanProductHarmonicPairBudget q r := by
  have hNnat : 1 ≤ (q + 1) * (r + 1) :=
    Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Nat.succ_ne_zero q) (Nat.succ_ne_zero r))
  have hN : (1 : ℝ) ≤ (((q + 1) * (r + 1) : ℕ) : ℝ) := by exact_mod_cast hNnat
  have hlog : 0 ≤ Real.log (((q + 1) * (r + 1) : ℕ) : ℝ) :=
    Real.log_nonneg hN
  have hfactor : 0 ≤ 1 + Real.log (((q + 1) * (r + 1) : ℕ) : ℝ) := by
    linarith
  have hfactor' : 0 ≤ 1 + Real.log (((q : ℝ) + 1) * ((r : ℝ) + 1)) := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hfactor
  unfold kloostermanProductHarmonicPairBudget
  apply le_min
  · exact mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) hfactor')
  · exact mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) hfactor')

theorem kloostermanDistinctModulusProductHarmonicBudget_nonneg (Q : Finset ℕ) (w : ℕ → ℂ) :
    0 ≤ kloostermanDistinctModulusProductHarmonicBudget Q w := by
  unfold kloostermanDistinctModulusProductHarmonicBudget
  apply Finset.sum_nonneg
  intro q hq
  apply mul_nonneg (norm_nonneg _)
  apply Finset.sum_nonneg
  intro r hr
  exact mul_nonneg (norm_nonneg _) (kloostermanProductHarmonicPairBudget_nonneg q r)

/-- Terminal distinct-modulus Gram entry bounded by the shared-gcd-safe modulus budget. -/
theorem norm_kloostermanDistinctModulusTerminalGram_le_productHarmonic
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ) (n k : ℕ) :
    ‖kloostermanDistinctModulusTerminalGram M Q w n k‖ ≤
      kloostermanDistinctModulusProductHarmonicBudget Q w := by
  calc
    ‖kloostermanDistinctModulusTerminalGram M Q w n k‖ ≤
        ∑ q ∈ Q, ‖star (w q) *
          ∑ r ∈ Q.erase q, w r *
            kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
              (Int.cast (n : ℤ)) (Int.cast (k : ℤ))‖ := by
      unfold kloostermanDistinctModulusTerminalGram
      exact norm_sum_le _ _
    _ = ∑ q ∈ Q, ‖w q‖ * ‖∑ r ∈ Q.erase q, w r *
          kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
            (Int.cast (n : ℤ)) (Int.cast (k : ℤ))‖ := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [norm_mul, norm_star]
    _ ≤ ∑ q ∈ Q, ‖w q‖ * ∑ r ∈ Q.erase q,
          ‖w r * kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
            (Int.cast (n : ℤ)) (Int.cast (k : ℤ))‖ := by
      apply Finset.sum_le_sum
      intro q hq
      gcongr
      exact norm_sum_le _ _
    _ = ∑ q ∈ Q, ‖w q‖ * ∑ r ∈ Q.erase q,
          ‖w r‖ * ‖kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
            (Int.cast (n : ℤ)) (Int.cast (k : ℤ))‖ := by
      apply Finset.sum_congr rfl
      intro q hq
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      rw [norm_mul]
    _ ≤ ∑ q ∈ Q, ‖w q‖ * ∑ r ∈ Q.erase q,
          ‖w r‖ * kloostermanProductHarmonicPairBudget q r := by
      apply Finset.sum_le_sum
      intro q hq
      gcongr with r hr
      have hrq : r ≠ q := (Finset.mem_erase.mp hr).1
      simpa [kloostermanProductHarmonicPairBudget, Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
        norm_kloostermanNaturalCrossIntervalTerminalBlock_le_productHarmonic
          M (q + 1) (r + 1) (Ne.symm (Nat.succ_ne_succ_iff.mpr hrq))
            (Int.cast (n : ℤ)) (Int.cast (k : ℤ))
    _ = kloostermanDistinctModulusProductHarmonicBudget Q w := rfl

/-- Existing stored distinct-modulus Gram inherits the product-harmonic budget. -/
theorem norm_kloostermanDistinctModulusGram_Icc_le_productHarmonic
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ) (n k : ℕ) :
    ‖kloostermanDistinctModulusGram Q w (Finset.Icc 1 M) n k‖ ≤
      kloostermanDistinctModulusProductHarmonicBudget Q w := by
  rw [kloostermanDistinctModulusGram_Icc_eq_terminalGram]
  exact norm_kloostermanDistinctModulusTerminalGram_le_productHarmonic M Q w n k

/-- Full source quadratic bounded by squared source ℓ¹ mass times the modulus budget. -/
theorem norm_kloostermanDistinctModulusTerminalGramQuadratic_le_productHarmonic
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    ‖kloostermanDistinctModulusTerminalGramQuadratic M Q w B b‖ ≤
      (∑ n ∈ B, ‖b n‖) ^ 2 * kloostermanDistinctModulusProductHarmonicBudget Q w := by
  calc
    ‖kloostermanDistinctModulusTerminalGramQuadratic M Q w B b‖ ≤
        ∑ n ∈ B, ‖star (b n) * ∑ k ∈ B, b k *
          kloostermanDistinctModulusTerminalGram M Q w n k‖ := by
      unfold kloostermanDistinctModulusTerminalGramQuadratic
      exact norm_sum_le _ _
    _ = ∑ n ∈ B, ‖b n‖ * ‖∑ k ∈ B, b k *
          kloostermanDistinctModulusTerminalGram M Q w n k‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_mul, norm_star]
    _ ≤ ∑ n ∈ B, ‖b n‖ * ∑ k ∈ B,
          ‖b k * kloostermanDistinctModulusTerminalGram M Q w n k‖ := by
      apply Finset.sum_le_sum
      intro n hn
      gcongr
      exact norm_sum_le _ _
    _ = ∑ n ∈ B, ‖b n‖ * ∑ k ∈ B,
          ‖b k‖ * ‖kloostermanDistinctModulusTerminalGram M Q w n k‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_mul]
    _ ≤ ∑ n ∈ B, ‖b n‖ * ∑ k ∈ B,
          ‖b k‖ * kloostermanDistinctModulusProductHarmonicBudget Q w := by
      apply Finset.sum_le_sum
      intro n hn
      gcongr with k hk
      exact norm_kloostermanDistinctModulusTerminalGram_le_productHarmonic M Q w n k
    _ = (∑ n ∈ B, ‖b n‖) ^ 2 * kloostermanDistinctModulusProductHarmonicBudget Q w := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      ring

/-- Erased source off-diagonal obeys the same squared-ℓ¹ product-harmonic budget. -/
theorem norm_kloostermanDistinctModulusTerminalGramOffDiagonal_le_productHarmonic
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    ‖kloostermanDistinctModulusTerminalGramOffDiagonal M Q w B b‖ ≤
      (∑ n ∈ B, ‖b n‖) ^ 2 * kloostermanDistinctModulusProductHarmonicBudget Q w := by
  calc
    ‖kloostermanDistinctModulusTerminalGramOffDiagonal M Q w B b‖ ≤
        ∑ n ∈ B, ‖star (b n) * ∑ k ∈ B.erase n, b k *
          kloostermanDistinctModulusTerminalGram M Q w n k‖ := by
      unfold kloostermanDistinctModulusTerminalGramOffDiagonal
      exact norm_sum_le _ _
    _ = ∑ n ∈ B, ‖b n‖ * ‖∑ k ∈ B.erase n, b k *
          kloostermanDistinctModulusTerminalGram M Q w n k‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_mul, norm_star]
    _ ≤ ∑ n ∈ B, ‖b n‖ * ∑ k ∈ B.erase n,
          ‖b k * kloostermanDistinctModulusTerminalGram M Q w n k‖ := by
      apply Finset.sum_le_sum
      intro n hn
      gcongr
      exact norm_sum_le _ _
    _ = ∑ n ∈ B, ‖b n‖ * ∑ k ∈ B.erase n,
          ‖b k‖ * ‖kloostermanDistinctModulusTerminalGram M Q w n k‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_mul]
    _ ≤ ∑ n ∈ B, ‖b n‖ * ∑ k ∈ B,
          ‖b k‖ * kloostermanDistinctModulusProductHarmonicBudget Q w := by
      apply Finset.sum_le_sum
      intro n hn
      gcongr
      calc
        (∑ k ∈ B.erase n,
            ‖b k‖ * ‖kloostermanDistinctModulusTerminalGram M Q w n k‖) ≤
            ∑ k ∈ B.erase n, ‖b k‖ * kloostermanDistinctModulusProductHarmonicBudget Q w := by
          gcongr with k hk
          exact norm_kloostermanDistinctModulusTerminalGram_le_productHarmonic M Q w n k
        _ ≤ ∑ k ∈ B, ‖b k‖ * kloostermanDistinctModulusProductHarmonicBudget Q w := by
          rw [← Finset.sum_erase_add _ _ hn]
          exact le_add_of_nonneg_right
            (mul_nonneg (norm_nonneg _) (kloostermanDistinctModulusProductHarmonicBudget_nonneg Q w))
    _ = (∑ n ∈ B, ‖b n‖) ^ 2 * kloostermanDistinctModulusProductHarmonicBudget Q w := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      ring

end

end RHTower.Sieve

