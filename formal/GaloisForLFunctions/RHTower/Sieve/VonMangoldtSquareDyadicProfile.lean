/- Dyadic quadratic profile and increment-convolution error for the harmonic Mangoldt square. -/

import GaloisForLFunctions.RHTower.Sieve.QuadraticIncrementConvolution
import GaloisForLFunctions.RHTower.Sieve.VonMangoldtHarmonicSquareAsymptotic

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction BigOperators

namespace RHTower.Sieve

theorem monotone_vonMangoldtHarmonicSquareSum :
    Monotone vonMangoldtHarmonicSquareSum := by
  intro M N hMN
  rw [vonMangoldtHarmonicSquareSum, vonMangoldtHarmonicSquareSum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, hn.2.trans hMN⟩
  · intro n hn hnot
    positivity

/-- Harmonic von Mangoldt square mass sampled at exact dyadic cutoffs. -/
def vonMangoldtSquareDyadicProfile (M : ℕ) : ℝ :=
  vonMangoldtHarmonicSquareSum (2 ^ M)

@[simp] theorem vonMangoldtSquareDyadicProfile_zero :
    vonMangoldtSquareDyadicProfile 0 = 0 := by
  norm_num [vonMangoldtSquareDyadicProfile, vonMangoldtHarmonicSquareSum]

theorem monotone_vonMangoldtSquareDyadicProfile :
    Monotone vonMangoldtSquareDyadicProfile := by
  intro M N hMN
  apply monotone_vonMangoldtHarmonicSquareSum
  exact Nat.pow_le_pow_right (by norm_num : 0 < 2) hMN

/-- Quadratic coefficient of the dyadic cumulative profile. -/
def vonMangoldtSquareDyadicQuadraticCoeff : ℝ := Real.log 2 ^ (2 : ℕ) / 2

/-- Linear error coefficient inherited from the explicit harmonic square law. -/
def vonMangoldtSquareDyadicLinearError : ℝ := 39 * Real.log 2 + 25

theorem vonMangoldtSquareDyadicQuadraticCoeff_nonneg :
    0 ≤ vonMangoldtSquareDyadicQuadraticCoeff := by
  unfold vonMangoldtSquareDyadicQuadraticCoeff
  positivity

theorem vonMangoldtSquareDyadicLinearError_nonneg :
    0 ≤ vonMangoldtSquareDyadicLinearError := by
  unfold vonMangoldtSquareDyadicLinearError
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  positivity

/-- Uniform linear error around the exact dyadic quadratic profile. -/
theorem abs_vonMangoldtSquareDyadicProfile_sub_le (M : ℕ) :
    |vonMangoldtSquareDyadicProfile M -
        vonMangoldtSquareDyadicQuadraticCoeff * (M : ℝ) ^ (2 : ℕ)| ≤
      vonMangoldtSquareDyadicLinearError * ((M : ℝ) + 1) := by
  have hpow : 1 ≤ 2 ^ M := one_le_pow₀ (by norm_num : 1 ≤ 2)
  have h := abs_vonMangoldtHarmonicSquareSum_sub_le (2 ^ M) hpow
  have hlog : Real.log ((2 ^ M : ℕ) : ℝ) = (M : ℝ) * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  change |vonMangoldtSquareDyadicProfile M -
      Real.log ((2 ^ M : ℕ) : ℝ) ^ (2 : ℕ) / 2| ≤
    39 * Real.log ((2 ^ M : ℕ) : ℝ) + 25 at h
  rw [hlog] at h
  have hmain : ((M : ℝ) * Real.log 2) ^ (2 : ℕ) / 2 =
      vonMangoldtSquareDyadicQuadraticCoeff * (M : ℝ) ^ (2 : ℕ) := by
    rw [vonMangoldtSquareDyadicQuadraticCoeff]
    ring
  rw [hmain] at h
  refine h.trans ?_
  rw [vonMangoldtSquareDyadicLinearError]
  have hM0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith

/-- Exact cubic remainder for the dyadic quadratic increment convolution. -/
theorem abs_quadraticIncrementConvolution_vonMangoldtSquareDyadicProfile_sub_le
    (M : ℕ) :
    |quadraticIncrementConvolution vonMangoldtSquareDyadicProfile M -
        vonMangoldtSquareDyadicQuadraticCoeff ^ (2 : ℕ) *
          ((M : ℝ) * ((M : ℝ) + 1) *
            ((M : ℝ) ^ (2 : ℕ) + (M : ℝ) + 1) / 6)| ≤
      5 * vonMangoldtSquareDyadicLinearError *
        (vonMangoldtSquareDyadicQuadraticCoeff +
          vonMangoldtSquareDyadicLinearError) *
        ((M : ℝ) + 1) ^ (3 : ℕ) := by
  exact abs_quadraticIncrementConvolution_sub_le
    vonMangoldtSquareDyadicProfile_zero
    monotone_vonMangoldtSquareDyadicProfile
    vonMangoldtSquareDyadicQuadraticCoeff_nonneg
    vonMangoldtSquareDyadicLinearError_nonneg
    abs_vonMangoldtSquareDyadicProfile_sub_le M

end RHTower.Sieve
