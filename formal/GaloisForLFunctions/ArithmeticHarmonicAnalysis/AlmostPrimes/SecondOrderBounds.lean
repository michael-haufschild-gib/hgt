import GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlmostPrimes.ConvolutionBounds
import GaloisForLFunctions.HTGeometry.VonMangoldtSelfConvolution
import GaloisForLFunctions.RHTower.ShortWindowNoGo
import GaloisForLFunctions.RHTower.VonMangoldtMollifierPolynomialMeanSquare

/-!
# Smaller second-order almost-prime envelopes

The exact one-prime and two-prime coefficient formulas improve the
general logarithmic envelope. On prime powers the constant is `1/4`,
attained by prime squares; on all integers the constant is `1/2`.
-/

noncomputable section

open Finset ArithmeticFunction MeasureTheory RHTower
open scoped ArithmeticFunction
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlmostPrimes

/-- The prime-power envelope has constant `1/4`. -/
theorem selfConvolution_primePower_le_quarter {n : ℕ} (hn : IsPrimePow n) :
    (Λ * Λ) n ≤ Real.log n ^ 2 / 4 := by
  obtain ⟨p, a, hp, ha, hpa⟩ := (isPrimePow_nat_iff n).mp hn
  rw [← hpa, vonMangoldt_mul_self_prime_pow hp ha, Nat.cast_pow, Real.log_pow]
  have hquad : 4 * ((a : ℝ) - 1) ≤ (a : ℝ) ^ 2 := by
    nlinarith only [sq_nonneg ((a : ℝ) - 2)]
  have h := mul_le_mul_of_nonneg_right hquad (sq_nonneg (Real.log p))
  nlinarith only [h]

/-- Prime squares attain the prime-power envelope exactly. -/
theorem selfConvolution_primeSquare_eq_quarter (p : Nat.Primes) :
    (Λ * Λ) ((p : ℕ) ^ 2) = Real.log (((p : ℕ) ^ 2 : ℕ) : ℝ) ^ 2 / 4 := by
  rw [vonMangoldt_mul_self_prime_pow p.property (by omega), Nat.cast_pow, Real.log_pow]
  norm_num
  ring

/-- Two different prime factors give the universal constant `1/2`. -/
theorem selfConvolution_le_half (n : ℕ) : (Λ * Λ) n ≤ Real.log n ^ 2 / 2 := by
  classical
  by_cases hn0 : n = 0
  · subst n; simp
  by_cases hc0 : n.primeFactors.card = 0
  · have hn1 : n = 1 := by
      have h := Nat.primeFactors_eq_empty.mp (card_eq_zero.mp hc0)
      omega
    subst n; simp
  by_cases hc1 : n.primeFactors.card = 1
  · have h := selfConvolution_primePower_le_quarter
      (isPrimePow_iff_card_primeFactors_eq_one.mpr hc1)
    nlinarith only [h, sq_nonneg (Real.log n)]
  by_cases hc2 : n.primeFactors.card = 2
  · obtain ⟨p, q, hpq, hfac⟩ := card_eq_two.mp hc2
    have hp : p.Prime := Nat.prime_of_mem_primeFactors (by rw [hfac]; simp)
    have hq : q.Prime := Nat.prime_of_mem_primeFactors (by rw [hfac]; simp)
    have hpqdiv : p * q ∣ n := by
      simpa only [hfac, prod_pair hpq] using Nat.prod_primeFactors_dvd n
    have hprod : (p : ℝ) * q ≤ n := by
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpqdiv
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have hlog := Real.log_le_log (mul_pos hp0 hq0) hprod
    rw [Real.log_mul hp0.ne' hq0.ne'] at hlog
    have hsq := pow_le_pow_left₀
      (add_nonneg (Real.log_natCast_nonneg p) (Real.log_natCast_nonneg q)) hlog 2
    rw [vonMangoldt_mul_self_of_card_eq_two hc2, hfac, prod_pair hpq]
    nlinarith only [hsq, sq_nonneg (Real.log p - Real.log q)]
  · rw [vonMangoldt_mul_self_eq_zero_of_three_le (by omega : 3 ≤ n.primeFactors.card)]
    positivity

theorem selfConvolution_sq_le_quarter (n : ℕ) :
    ((Λ * Λ) n) ^ 2 ≤ Real.log n ^ 4 / 4 := by
  have h0 : 0 ≤ (Λ * Λ) n := by simpa only [pow_two] using convolution_nonneg 2 n
  have h := pow_le_pow_left₀ h0 (selfConvolution_le_half n) 2
  nlinarith only [h]

/-- The second-order harmonic energy improves the general envelope by a factor of four. -/
theorem selfConvolution_harmonic_energy_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Icc 1 N, ((Λ * Λ) n) ^ 2 / n ≤
      (Real.log N ^ 4 / 4) * (1 + Real.log N) := by
  calc ∑ n ∈ Icc 1 N, ((Λ * Λ) n) ^ 2 / n ≤
      ∑ n ∈ Icc 1 N, (Real.log N ^ 4 / 4) * (1 / n) := by
        apply sum_le_sum
        intro n hn
        obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
        have hlog := Real.log_le_log hn0 (show (n : ℝ) ≤ N by exact_mod_cast hnN)
        have hpow := pow_le_pow_left₀ (Real.log_natCast_nonneg n) hlog 4
        rw [div_eq_mul_inv, one_div]
        exact mul_le_mul_of_nonneg_right
          ((selfConvolution_sq_le_quarter n).trans (by linarith only [hpow]))
          (inv_nonneg.mpr hn0.le)
    _ = (Real.log N ^ 4 / 4) * ∑ n ∈ Icc 1 N, (1 : ℝ) / n := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (RHTower.harmonic_Icc_le_one_add_log N hN)
      (by positivity)

/-- The improved second-order energy feeds directly into the critical-line mean-value bound. -/
theorem selfConvolution_critical_meanSquare_le (N : ℕ) (hN : 1 ≤ N)
    {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    (∫ τ in T₁..T₂,
      ‖edPoly (fun n => (((Λ * Λ) n : ℝ) : ℂ)) (Icc 1 N) (displacedLinePt 0 τ)‖ ^ 2) ≤
      (T₂ - T₁ + 8 * N * (1 + Real.log N)) *
        ((Real.log N ^ 4 / 4) * (1 + Real.log N)) := by
  have h := integral_normSq_edPoly_displaced_le 0 (fun n => (((Λ * Λ) n : ℝ) : ℂ)) N T₁ T₂
  simp only [mul_zero, zero_sub, Real.rpow_neg_one, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, ← div_eq_mul_inv] at h
  refine h.trans (mul_le_mul_of_nonneg_left (selfConvolution_harmonic_energy_le N hN) ?_)
  exact add_nonneg (sub_nonneg.mpr hT)
    (mul_nonneg (by positivity) (add_nonneg zero_le_one (Real.log_natCast_nonneg N)))

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlmostPrimes
