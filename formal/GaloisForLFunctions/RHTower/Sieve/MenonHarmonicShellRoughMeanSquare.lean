import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicSparseSetMeanSquare
import GaloisForLFunctions.RHTower.Sieve.RoughCount

/-!
# The rough part of a shell, bounded by its sieve count

Under the smallest-prime-factor partition the ladder blocks above a cutoff `z` capture exactly the
integers of the shell with **no** prime factor at most `z`.  Brun's pure sieve counts those
(`Sieve/RoughCount.card_rough_Ioc_le`), and the sparse-set mean square of
`MenonHarmonicSparseSetMeanSquare` turns that count into a frequency bound.  The composite is a
`≍ 1/log z` bound for the whole rough part, with no factorisation estimate anywhere.
-/

namespace RHTower.Sieve

open Finset MeasureTheory
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- The integers of a shell with no prime factor at most `z`. -/
def menonShellRough (A B z : ℕ) : Finset ℕ :=
  {n ∈ Finset.Icc A B | ∀ p ∈ Nat.primesLE z, ¬ p ∣ n}

theorem menonShellRough_subset (A B z : ℕ) :
    menonShellRough A B z ⊆ Finset.Icc A B := Finset.filter_subset _ _

/-- **The rough part's mean square, from any count bound.** -/
theorem integral_Icc_normSq_menonShellRough_le_count
    {A B z : ℕ} (hA : 1 ≤ A) {T : ℝ} (hT : 0 ≤ T) {C : ℝ}
    (hC : ((menonShellRough A B z).card : ℝ) ≤ C) :
    (∫ w in Set.Icc (-T) T,
      ‖logPoly harmonicMoebiusC (menonShellRough A B z) w‖ ^ (2 : ℕ))
      ≤ (5 * Real.pi / 2) * (C / (A : ℝ) ^ (2 : ℕ)) * T
        + ((5 * Real.exp 1 / 2) * (C / (A : ℝ))
          + (5 / 4) * (C / (A : ℝ) ^ (2 : ℕ))) := by
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hA
  have hbase := integral_Icc_normSq_logPoly_harmonicMoebius_le_card
    (S := menonShellRough A B z) (A := A) (N := B) hA (menonShellRough_subset A B z) hT
  refine hbase.trans ?_
  have h1 : ((menonShellRough A B z).card : ℝ) / (A : ℝ) ^ (2 : ℕ) ≤ C / (A : ℝ) ^ (2 : ℕ) :=
    div_le_div_of_nonneg_right hC (by positivity)
  have h2 : ((menonShellRough A B z).card : ℝ) / (A : ℝ) ≤ C / (A : ℝ) :=
    div_le_div_of_nonneg_right hC hA0.le
  have hpi : (0 : ℝ) ≤ 5 * Real.pi / 2 := by positivity
  have he : (0 : ℝ) ≤ 5 * Real.exp 1 / 2 := by positivity
  have s1 : (5 * Real.pi / 2) * (((menonShellRough A B z).card : ℝ) / (A : ℝ) ^ (2 : ℕ)) * T
      ≤ (5 * Real.pi / 2) * (C / (A : ℝ) ^ (2 : ℕ)) * T :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hpi) hT
  have s2 : (5 * Real.exp 1 / 2) * (((menonShellRough A B z).card : ℝ) / (A : ℝ))
      ≤ (5 * Real.exp 1 / 2) * (C / (A : ℝ)) :=
    mul_le_mul_of_nonneg_left h2 he
  have s3 : (5 / 4 : ℝ) * (((menonShellRough A B z).card : ℝ) / (A : ℝ) ^ (2 : ℕ))
      ≤ (5 / 4 : ℝ) * (C / (A : ℝ) ^ (2 : ℕ)) :=
    mul_le_mul_of_nonneg_left h1 (by norm_num)
  linarith

/-- **The rough part's mean square, with Brun's pure sieve count inserted.**  The whole rough part
of the shell is `≍ 1/log z`, with no factorisation estimate. -/
theorem integral_Icc_normSq_menonShellRough_le_brun
    {A B z r : ℕ} (hA : 1 ≤ A) (hz : 2 ≤ z) (hAB : A - 1 ≤ B) (hr : Even r)
    {lam : ℝ} (hlam : 1 ≤ lam) {T : ℝ} (hT : 0 ≤ T) :
    (∫ w in Set.Icc (-T) T,
      ‖logPoly harmonicMoebiusC (menonShellRough A B z) w‖ ^ (2 : ℕ))
      ≤ (5 * Real.pi / 2) *
            (((((B : ℝ) - ((A - 1 : ℕ) : ℝ))
                  * (Real.exp mertensSecondLowerConst / Real.log z)
                + ((B : ℝ) - ((A - 1 : ℕ) : ℝ))
                    * (Real.exp (lam * mertensSecondUpperConst)
                        * (Real.log z) ^ lam / lam ^ r)
                + ((truncDivisors (primorial z) r).card : ℝ))) / (A : ℝ) ^ (2 : ℕ)) * T
        + ((5 * Real.exp 1 / 2) *
              (((((B : ℝ) - ((A - 1 : ℕ) : ℝ))
                    * (Real.exp mertensSecondLowerConst / Real.log z)
                  + ((B : ℝ) - ((A - 1 : ℕ) : ℝ))
                      * (Real.exp (lam * mertensSecondUpperConst)
                          * (Real.log z) ^ lam / lam ^ r)
                  + ((truncDivisors (primorial z) r).card : ℝ))) / (A : ℝ))
          + (5 / 4) *
              (((((B : ℝ) - ((A - 1 : ℕ) : ℝ))
                    * (Real.exp mertensSecondLowerConst / Real.log z)
                  + ((B : ℝ) - ((A - 1 : ℕ) : ℝ))
                      * (Real.exp (lam * mertensSecondUpperConst)
                          * (Real.log z) ^ lam / lam ^ r)
                  + ((truncDivisors (primorial z) r).card : ℝ))) / (A : ℝ) ^ (2 : ℕ))) := by
  classical
  have hIcc : Finset.Icc A B = Finset.Ioc (A - 1) B := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hcount : ((menonShellRough A B z).card : ℝ)
      ≤ ((B : ℝ) - ((A - 1 : ℕ) : ℝ))
            * (Real.exp mertensSecondLowerConst / Real.log z)
          + ((B : ℝ) - ((A - 1 : ℕ) : ℝ))
              * (Real.exp (lam * mertensSecondUpperConst)
                  * (Real.log z) ^ lam / lam ^ r)
          + ((truncDivisors (primorial z) r).card : ℝ) := by
    have hrw : menonShellRough A B z
        = {n ∈ Finset.Ioc (A - 1) B | ∀ p ∈ Nat.primesLE z, ¬ p ∣ n} := by
      rw [menonShellRough, hIcc]
    rw [hrw]
    exact card_rough_Ioc_le hz hAB hr hlam
  exact integral_Icc_normSq_menonShellRough_le_count hA hT hcount

end

end RHTower.Sieve
