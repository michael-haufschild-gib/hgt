import GaloisForLFunctions.ArithmeticCountingPositivity.RealMultiplicativeContractionsHavePositiveDivisorCounts
import GaloisForLFunctions.RenormalizedIntersectionTheory.ThePositiveDivisorMeanControlsTheSignedPrimitive

/-!
# Positive divisor means for rough prime flips

Removing small primes preserves complete multiplicativity and the bound by one.
The resulting divisor convolution remains nonnegative, and every rough signed
harmonic partial sum stays above minus one. The full von Mangoldt convolution
then bounds the signed mean by twice the positive mean with a universal logarithmic error.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

open GaloisForLFunctions.ArithmeticCountingPositivity
  GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

private theorem roughFlip_one (P : Set ℕ) (Q : ℕ) : roughGauge Q (primeSetFlip P) 1 = 1 := by
  simpa [roughGauge] using signGauge_map_one (primeSetFlip_isSignGauge P)

/-- Rough prime removal leaves a nonnegative divisor convolution. -/
theorem roughFlipDivisorCount_nonneg (P : Set ℕ) (Q n : ℕ) :
    0 ≤ signDivisorCount (roughGauge Q (primeSetFlip P)) n :=
  contractionDivisorCount_nonneg (roughFlip_one P Q)
    (roughGauge_mul (fun _ _ ha hb => (primeSetFlip_isSignGauge P).mul ha hb) Q)
    (abs_roughGauge_le (abs_primeSetFlip_le P) Q) n

/-- The lower bound is independent of the roughness cutoff and the flipped primes. -/
theorem neg_one_le_roughFlipHarmonicSum (P : Set ℕ) (Q N : ℕ) :
    -1 ≤ gaugeHarmonicSum (roughGauge Q (primeSetFlip P)) N :=
  neg_one_le_harmonicSum_of_real_multiplicative (roughFlip_one P Q)
    (roughGauge_mul (fun _ _ ha hb => (primeSetFlip_isSignGauge P).mul ha hb) Q)
    (abs_roughGauge_le (abs_primeSetFlip_le P) Q) N

private theorem abs_divisorMean_sub_logWeightSum_le {ω : ℕ → ℝ}
    (hbd : ∀ n, |ω n| ≤ 1) (N : ℕ) :
    |gaugeHarmonicSum (signDivisorCount ω) N - logWeightSum ω N| ≤
      gaugeHarmonicSum (fun _ => 1) N := by
  rw [gaugeHarmonicSum_signDivisorCount_eq, logWeightSum_eq, ← sum_sub_distrib]
  calc
    _ ≤ ∑ d ∈ Icc 1 N, |ω d / d * gaugeHarmonicSum (fun _ => 1) (N / d) -
        ω d / d * Real.log (N / d : ℕ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Icc 1 N, (1 : ℝ) / d := by
      apply sum_le_sum
      intro d hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
      rw [← mul_sub, abs_mul, abs_div, abs_of_pos hd0]
      calc
        _ ≤ (1 / (d : ℝ)) * 1 := mul_le_mul
          (div_le_div_of_nonneg_right (hbd d) hd0.le)
          (abs_harmonic_sub_log_le (N / d)) (abs_nonneg _) (by positivity)
        _ = _ := mul_one _
    _ = _ := rfl

private theorem full_vonMangoldt_convolution_eq (ω : ℕ → ℝ) (N : ℕ) :
    (∑ d ∈ Icc 1 N, Λ d / d * gaugeHarmonicSum ω (N / d)) =
      ∑ m ∈ Icc 1 N, ω m / m * gaugeHarmonicSum (fun d => Λ d) (N / m) := by
  let a : ℕ → ℝ := fun d => Λ d / d
  let b : ℕ → ℝ := fun m => ω m / m
  change (∑ d ∈ Icc 1 N, a d * ∑ k ∈ Icc 1 (N / d), b k) =
    ∑ d ∈ Icc 1 N, b d * ∑ k ∈ Icc 1 (N / d), a k
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, a d * b (n / d) := by
      simpa only [mul_sum] using (RHTower.Sieve.sum_divisors_swap N (fun d k => a d * b k)).symm
    _ = ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, b d * a (n / d) := by
      refine sum_congr rfl fun n _ => ?_
      rw [← Nat.sum_divisorsAntidiagonal (fun d k => a d * b k),
        Nat.sum_divisorsAntidiagonal' (fun d k => a d * b k)]
      exact sum_congr rfl fun d _ => mul_comm _ _
    _ = _ := by
      simpa only [mul_sum] using RHTower.Sieve.sum_divisors_swap N (fun d k => b d * a k)

private theorem abs_full_vonMangoldt_convolution_sub_le {ω : ℕ → ℝ}
    (hbd : ∀ n, |ω n| ≤ 1) (N : ℕ) :
    |(∑ d ∈ Icc 1 N, Λ d / d * gaugeHarmonicSum ω (N / d)) - logWeightSum ω N| ≤
      (Real.log 4 + 4) * gaugeHarmonicSum (fun _ => 1) N := by
  rw [full_vonMangoldt_convolution_eq, logWeightSum_eq, ← sum_sub_distrib]
  calc
    _ ≤ ∑ m ∈ Icc 1 N, |ω m / m * gaugeHarmonicSum (fun d => Λ d) (N / m) -
        ω m / m * Real.log (N / m : ℕ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Icc 1 N, (Real.log 4 + 4) * (1 / (m : ℝ)) := by
      apply sum_le_sum
      intro m hm
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.mp hm).1
      have hq : 1 ≤ N / m := (Nat.le_div_iff_mul_le (mem_Icc.mp hm).1).mpr
        (by simpa using (mem_Icc.mp hm).2)
      have hA : |gaugeHarmonicSum (fun d => Λ d) (N / m) - Real.log (N / m : ℕ)| ≤
          Real.log 4 + 4 := by
        simpa only [gaugeHarmonicSum] using RHTower.Mertens.mertens_first (N / m) hq
      rw [← mul_sub, abs_mul, abs_div, abs_of_pos hm0]
      exact (mul_le_mul (div_le_div_of_nonneg_right (hbd m) hm0.le)
        hA (abs_nonneg _) (by positivity)).trans_eq (mul_comm _ _)
    _ = _ := by rw [← mul_sum]; rfl

/-- The full von Mangoldt convolution gives a universal signed-to-positive comparison:
each twisted term is at most its untwisted counterpart plus twice its weight. -/
theorem harmonicSum_mul_log_le_two_divisorMean {ω : ℕ → ℝ} (h1 : ω 1 = 1)
    (hmul : ∀ m n, m ≠ 0 → n ≠ 0 → ω (m * n) = ω m * ω n)
    (hbd : ∀ n, |ω n| ≤ 1) {N : ℕ} (hN : 1 ≤ N) :
    gaugeHarmonicSum ω N * Real.log N ≤ 2 * gaugeHarmonicSum (signDivisorCount ω) N +
      (4 + 3 * (Real.log 4 + 4)) * (1 + Real.log N) := by
  let C := Real.log 4 + 4
  let H := gaugeHarmonicSum (fun _ => (1 : ℝ)) N
  let W := logWeightSum ω N
  let G := gaugeHarmonicSum (signDivisorCount ω) N
  let M := polarMoment ω N
  let B := gaugeHarmonicSum (fun d => Λ d) N
  let Q := ∑ d ∈ Icc 1 N, Λ d / d * gaugeHarmonicSum ω (N / d)
  have hC : 0 ≤ C := by
    have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    dsimp only [C]
    linarith only [h]
  have hconv : (∑ d ∈ Icc 1 N, Λ d * (ω d / d) * gaugeHarmonicSum ω (N / d)) ≤ Q + 2 * B := by
    change (∑ d ∈ Icc 1 N, Λ d * (ω d / d) * gaugeHarmonicSum ω (N / d)) ≤
      (∑ d ∈ Icc 1 N, Λ d / d * gaugeHarmonicSum ω (N / d)) +
        2 * (∑ d ∈ Icc 1 N, Λ d / d)
    rw [mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro d _
    have hω := abs_le.mp (hbd d)
    have hS := neg_one_le_harmonicSum_of_real_multiplicative h1 hmul hbd (N / d)
    have hproduct := mul_nonneg (show 0 ≤ 1 - ω d by linarith only [hω.2])
      (show 0 ≤ gaugeHarmonicSum ω (N / d) + 1 by linarith only [hS])
    have hscalar : ω d * gaugeHarmonicSum ω (N / d) ≤ gaugeHarmonicSum ω (N / d) + 2 := by
      nlinarith only [hproduct, hω.1]
    have hweight := div_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := d)) (Nat.cast_nonneg d)
    calc
      _ = (Λ d / d) * (ω d * gaugeHarmonicSum ω (N / d)) := by ring
      _ ≤ (Λ d / d) * (gaugeHarmonicSum ω (N / d) + 2) :=
        mul_le_mul_of_nonneg_left hscalar hweight
      _ = _ := by ring
  have hidentity := logMoment_eq_vonMangoldt ω hmul N
  rw [logMoment_eq] at hidentity
  have hrenewal : gaugeHarmonicSum ω N * Real.log N - M ≤ Q + 2 * B :=
    hidentity.trans_le hconv
  have hQ : |Q - W| ≤ C * H := abs_full_vonMangoldt_convolution_sub_le hbd N
  have hM : |M - W| ≤ 2 := abs_polarMoment_sub_logWeightSum_le hbd hN
  have hG : |G - W| ≤ H := abs_divisorMean_sub_logWeightSum_le hbd N
  have hB : |B - Real.log N| ≤ C := RHTower.Mertens.mertens_first N hN
  have hH : H ≤ 1 + Real.log N := by
    have h := (abs_le.mp (abs_harmonic_sub_log_le N)).2
    linarith only [h]
  have hweighted := mul_le_mul_of_nonneg_left hH (show 0 ≤ C + 2 by linarith only [hC])
  have hlog := Real.log_natCast_nonneg N
  have hClog := mul_nonneg hC hlog
  change gaugeHarmonicSum ω N * Real.log N ≤ 2 * G + (4 + 3 * C) * (1 + Real.log N)
  have hQu := (abs_le.mp hQ).2
  have hMu := (abs_le.mp hM).2
  have hGl := (abs_le.mp hG).1
  have hBu := (abs_le.mp hB).2
  nlinarith only [hrenewal, hQu, hMu, hGl, hBu, hweighted, hClog]

/-- Rough prime flips satisfy the same comparison with a cutoff-independent constant. -/
theorem roughFlipHarmonicSum_mul_log_le_two_divisorMean (P : Set ℕ) (Q : ℕ)
    {N : ℕ} (hN : 1 ≤ N) :
    gaugeHarmonicSum (roughGauge Q (primeSetFlip P)) N * Real.log N ≤
      2 * gaugeHarmonicSum (signDivisorCount (roughGauge Q (primeSetFlip P))) N +
        (4 + 3 * (Real.log 4 + 4)) * (1 + Real.log N) :=
  harmonicSum_mul_log_le_two_divisorMean (roughFlip_one P Q)
    (roughGauge_mul (fun _ _ ha hb => (primeSetFlip_isSignGauge P).mul ha hb) Q)
    (abs_roughGauge_le (abs_primeSetFlip_le P) Q) hN

/-- The absolute rough mean is controlled by its positive divisor mean, uniformly in
the prime pattern and roughness cutoff. -/
theorem abs_roughFlipHarmonicSum_le_divisorMean (P : Set ℕ) (Q : ℕ)
    {N : ℕ} (hN : 3 ≤ N) :
    |gaugeHarmonicSum (roughGauge Q (primeSetFlip P)) N| ≤
      2 * (gaugeHarmonicSum (signDivisorCount (roughGauge Q (primeSetFlip P))) N / Real.log N) +
        2 * (4 + 3 * (Real.log 4 + 4)) := by
  let G := gaugeHarmonicSum (signDivisorCount (roughGauge Q (primeSetFlip P))) N
  let S := gaugeHarmonicSum (roughGauge Q (primeSetFlip P)) N
  let K := 4 + 3 * (Real.log 4 + 4)
  have hK : 1 ≤ K := by
    have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    dsimp only [K]
    linarith only [h]
  have hG : 0 ≤ G := by
    change 0 ≤ ∑ n ∈ Icc 1 N, signDivisorCount (roughGauge Q (primeSetFlip P)) n / n
    exact sum_nonneg fun n _ => div_nonneg (roughFlipDivisorCount_nonneg P Q n) (Nat.cast_nonneg n)
  have hL1 := one_le_log_of_three_le hN
  have hL : 0 < Real.log N := zero_lt_one.trans_le hL1
  have hupper : S * Real.log N ≤ 2 * G + K * (1 + Real.log N) :=
    roughFlipHarmonicSum_mul_log_le_two_divisorMean P Q (by omega)
  have herror := mul_le_mul_of_nonneg_left
    (show 1 + Real.log N ≤ 2 * Real.log N by linarith only [hL1]) (zero_le_one.trans hK)
  have hscaled : S * Real.log N ≤ (2 * (G / Real.log N) + 2 * K) * Real.log N := by
    have heq : (2 * (G / Real.log N) + 2 * K) * Real.log N =
        2 * G + 2 * K * Real.log N := by field_simp [hL.ne']
    rw [heq]
    nlinarith only [hupper, herror]
  have hS : S ≤ 2 * (G / Real.log N) + 2 * K :=
    le_of_mul_le_mul_left (a := Real.log N) (by simpa only [mul_comm] using hscaled) hL
  have hright : 1 ≤ 2 * (G / Real.log N) + 2 * K := by
    have h := div_nonneg hG hL.le
    linarith only [h, hK]
  have hlower : -1 ≤ S := neg_one_le_roughFlipHarmonicSum P Q N
  change |S| ≤ 2 * (G / Real.log N) + 2 * K
  exact abs_le.mpr ⟨by linarith only [hlower, hright], hS⟩

end GaloisForLFunctions.RenormalizedIntersectionTheory

