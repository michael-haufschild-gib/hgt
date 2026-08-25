import GaloisForLFunctions.RHTower.Sieve.VonMangoldtSelfConvCrossHarmonicBound
import GaloisForLFunctions.RHTower.ShortWindowNoGo

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction

namespace RHTower.Sieve

/-- Universal logarithmic envelope for the von Mangoldt self-convolution. -/
theorem vonMangoldtSelfConv_le_two_mul_log_sq
    (n : ℕ) (hn : 1 ≤ n) :
    (Λ * Λ) n ≤ 2 * Real.log n ^ 2 := by
  classical
  by_cases hcard0 : n.primeFactors.card = 0
  · have hempty : n.primeFactors = ∅ := Finset.card_eq_zero.mp hcard0
    have hn01 := Nat.primeFactors_eq_empty.mp hempty
    have hn1 : n = 1 := by omega
    subst hn1
    norm_num
  by_cases hcard1 : n.primeFactors.card = 1
  · have hpp : IsPrimePow n := isPrimePow_iff_card_primeFactors_eq_one.mpr hcard1
    have hle := vonMangoldtSelfConv_le_log_sq_of_isPrimePow hpp
    nlinarith [sq_nonneg (Real.log (n : ℝ))]
  by_cases hcard2 : n.primeFactors.card = 2
  · obtain ⟨p, q, hpq, hfac⟩ := Finset.card_eq_two.mp hcard2
    have hpmem : p ∈ n.primeFactors := by rw [hfac]; simp
    have hqmem : q ∈ n.primeFactors := by rw [hfac]; simp
    have hpdata := Nat.mem_primeFactors.mp hpmem
    have hqdata := Nat.mem_primeFactors.mp hqmem
    have hpN : p ≤ n := Nat.le_of_dvd (by omega) hpdata.2.1
    have hqN : q ≤ n := Nat.le_of_dvd (by omega) hqdata.2.1
    have hlogN0 : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hn)
    have hlogp0 : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hpdata.1.one_lt.le)
    have hlogq0 : 0 ≤ Real.log (q : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hqdata.1.one_lt.le)
    have hlogpN : Real.log (p : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by exact_mod_cast hpdata.1.pos) (by exact_mod_cast hpN)
    have hlogqN : Real.log (q : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by exact_mod_cast hqdata.1.pos) (by exact_mod_cast hqN)
    rw [GaloisForLFunctions.HTGeometry.vonMangoldt_mul_self_of_card_eq_two hcard2,
      hfac, Finset.prod_pair hpq]
    nlinarith [mul_le_mul hlogpN hlogqN hlogq0 hlogN0]
  · have hcard3 : 3 ≤ n.primeFactors.card := by omega
    rw [GaloisForLFunctions.HTGeometry.vonMangoldt_mul_self_eq_zero_of_three_le hcard3]
    positivity

theorem vonMangoldtSelfConv_sq_le_four_mul_log_four
    (n : ℕ) (hn : 1 ≤ n) :
    ((Λ * Λ) n) ^ 2 ≤ 4 * Real.log n ^ 4 := by
  have hnonneg := vonMangoldtSelfConv_nonneg n
  have hupper := vonMangoldtSelfConv_le_two_mul_log_sq n hn
  nlinarith [sq_nonneg (2 * Real.log (n : ℝ) ^ 2 - (Λ * Λ) n)]

/-- Coarse finite envelope for the remaining differentiated Barban--Vehov moment. -/
theorem vonMangoldtSelfConvHarmonicSquareSum_le
    (N : ℕ) (hN : 1 ≤ N) :
    vonMangoldtSelfConvHarmonicSquareSum N ≤
      4 * Real.log N ^ 4 * (1 + Real.log N) := by
  rw [vonMangoldtSelfConvHarmonicSquareSum]
  calc
    ∑ k ∈ Finset.Icc 2 N, ((Λ * Λ) k) ^ 2 / (k : ℝ) ≤
        ∑ k ∈ Finset.Icc 2 N, 4 * Real.log N ^ 4 / (k : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
      have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
      have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hlogk0 : 0 ≤ Real.log (k : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
      have hlogkN : Real.log (k : ℝ) ≤ Real.log (N : ℝ) :=
        Real.log_le_log hkR (by exact_mod_cast hkN)
      apply div_le_div_of_nonneg_right _ hkR.le
      calc
        ((Λ * Λ) k) ^ 2 ≤ 4 * Real.log k ^ 4 :=
          vonMangoldtSelfConv_sq_le_four_mul_log_four k (by omega)
        _ ≤ 4 * Real.log N ^ 4 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogk0 hlogkN 4) (by norm_num)
    _ = 4 * Real.log N ^ 4 * ∑ k ∈ Finset.Icc 2 N, (1 : ℝ) / k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ 4 * Real.log N ^ 4 * (1 + Real.log N) := by
      have hsum : ∑ k ∈ Finset.Icc 2 N, (1 : ℝ) / k ≤
          1 + Real.log N := by
        calc
          ∑ k ∈ Finset.Icc 2 N, (1 : ℝ) / k ≤
              ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / k := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro k hk
              have hk2 := (Finset.mem_Icc.mp hk).1
              exact Finset.mem_Icc.mpr
                ⟨by omega, (Finset.mem_Icc.mp hk).2⟩
            · intro k hk hnot
              positivity
          _ ≤ 1 + Real.log N := RHTower.harmonic_Icc_le_one_add_log N hN
      exact mul_le_mul_of_nonneg_left hsum (by positivity)

end RHTower.Sieve
