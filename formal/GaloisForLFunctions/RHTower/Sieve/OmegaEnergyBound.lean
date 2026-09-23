import GaloisForLFunctions.RHTower.Sieve.OmegaBudgetFromLadder
import GaloisForLFunctions.RHTower.Sieve.TuranKubiliusRange

/-!
# The coefficient energy of the weighted Möbius polynomial

Bounding `ω_P(n)` by the number of designated primes wastes a whole power of the logarithm.  The
Turán--Kubilius variance gives the correct size: on average `ω_P(n)` is the harmonic mass of the
designated range, so the coefficient energy is the length of the range times the square of that
mass.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The prime-reciprocal sum is nonnegative. -/
theorem mertensS_nonneg' (N : ℕ) : 0 ≤ mertensS N := by
  rw [mertensS]
  refine Finset.sum_nonneg fun p _ => ?_
  positivity

/-- **The coefficient energy of the weighted Möbius polynomial over a half-open range.** -/
theorem sum_normSq_omegaCoeff_Ioc_le {z₀ z : ℕ} (hz : z₀ ≤ z) (a b : ℕ) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ioc a b, ‖omegaCoeff (primesRange z₀ z) n‖ ^ (2 : ℕ)
      ≤ 8 * ((b : ℝ) - a) * mertensS z + 8 * ((Nat.primesLE z).card : ℝ)
          + 16 * ((Nat.primesLE z).card : ℝ) ^ (2 : ℕ)
        + 2 * (mertensS z - mertensS z₀) ^ (2 : ℕ) * ((b : ℝ) - a) := by
  classical
  set W : ℝ := mertensS z - mertensS z₀ with hW
  have hterm : ∀ n ∈ Finset.Ioc a b, ‖omegaCoeff (primesRange z₀ z) n‖ ^ (2 : ℕ)
      ≤ 2 * (((primeFactorsIn (primesRange z₀ z) n).card : ℝ) - W) ^ (2 : ℕ) + 2 * W ^ (2 : ℕ) := by
    intro n _
    have hnorm : ‖omegaCoeff (primesRange z₀ z) n‖
        = |((ArithmeticFunction.moebius n : ℤ) : ℝ)
            * ((primeFactorsIn (primesRange z₀ z) n).card : ℝ)| := by
      rw [omegaCoeff, Complex.norm_real, Real.norm_eq_abs]
    have hcard0 : (0 : ℝ) ≤ ((primeFactorsIn (primesRange z₀ z) n).card : ℝ) :=
      Nat.cast_nonneg _
    have h1 := abs_moebius_real_le_one n
    have h4 : (0 : ℝ) ≤ |((ArithmeticFunction.moebius n : ℤ) : ℝ)| := abs_nonneg _
    have hle : ‖omegaCoeff (primesRange z₀ z) n‖
        ≤ ((primeFactorsIn (primesRange z₀ z) n).card : ℝ) := by
      rw [hnorm, abs_mul, abs_of_nonneg hcard0]
      nlinarith [h1, h4, hcard0]
    have hsq : ‖omegaCoeff (primesRange z₀ z) n‖ ^ (2 : ℕ)
        ≤ ((primeFactorsIn (primesRange z₀ z) n).card : ℝ) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (norm_nonneg _) hle 2
    nlinarith [hsq, sq_nonneg (((primeFactorsIn (primesRange z₀ z) n).card : ℝ) - 2 * W)]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc]
  have hvar := sum_variance_primesRange_le hz a b hab
  have hcount : (((b - a : ℕ) : ℕ) : ℝ) ≤ (b : ℝ) - a := by
    have : ((b - a : ℕ) : ℝ) = (b : ℝ) - (a : ℝ) := by
      have : a ≤ b := hab
      push_cast [Nat.cast_sub this]
      ring
    linarith [this.le]
  have hW2 : (0 : ℝ) ≤ W ^ (2 : ℕ) := sq_nonneg W
  nlinarith [hvar, hcount, hW2]

/-- **The coefficient energy over a closed range.** -/
theorem sum_normSq_omegaCoeff_Icc_le {z₀ z : ℕ} (hz : z₀ ≤ z) {A B : ℕ} (hA : 1 ≤ A) :
    ∑ n ∈ Finset.Icc A B, ‖omegaCoeff (primesRange z₀ z) n‖ ^ (2 : ℕ)
      ≤ 8 * (B : ℝ) * mertensS z + 8 * ((Nat.primesLE z).card : ℝ)
          + 16 * ((Nat.primesLE z).card : ℝ) ^ (2 : ℕ)
        + 2 * (mertensS z - mertensS z₀) ^ (2 : ℕ) * (B : ℝ) := by
  classical
  by_cases hAB : A ≤ B
  · have hIcc : Finset.Icc A B = Finset.Ioc (A - 1) B := by
      ext n
      rw [Finset.mem_Icc, Finset.mem_Ioc]
      omega
    rw [hIcc]
    have hab : A - 1 ≤ B := by omega
    refine (sum_normSq_omegaCoeff_Ioc_le hz (A - 1) B hab).trans ?_
    have hstep : (B : ℝ) - ((A - 1 : ℕ) : ℝ) ≤ (B : ℝ) := by
      have : (0 : ℝ) ≤ ((A - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have hm : (0 : ℝ) ≤ mertensS z := mertensS_nonneg' z
    have hW2 : (0 : ℝ) ≤ (mertensS z - mertensS z₀) ^ (2 : ℕ) := sq_nonneg _
    nlinarith [hstep, hm, hW2]
  · have hempty : Finset.Icc A B = ∅ := by
      rw [Finset.Icc_eq_empty]
      omega
    rw [hempty, Finset.sum_empty]
    have hm : (0 : ℝ) ≤ mertensS z := mertensS_nonneg' z
    have hW2 : (0 : ℝ) ≤ (mertensS z - mertensS z₀) ^ (2 : ℕ) := sq_nonneg _
    have hB : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg _
    have hp : (0 : ℝ) ≤ ((Nat.primesLE z).card : ℝ) := Nat.cast_nonneg _
    positivity

end

end RHTower.Sieve
