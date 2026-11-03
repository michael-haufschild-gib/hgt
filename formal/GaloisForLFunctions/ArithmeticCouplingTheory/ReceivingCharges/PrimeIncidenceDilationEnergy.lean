import GaloisForLFunctions.ArithmeticCouplingTheory.TheMertensPolarization
import GaloisForLFunctions.RHTower.Sieve.MoebiusScaledReindex

/-!
# Exact finite-horizon energy of prime-incidence packets

The dilation energy is diagonal in prime-incidence coordinates. Its weight at
prime `p` is `log p / p` times the harmonic mass through `⌊N/p⌋`. The identity
retains the horizon boundary and is unchanged by harmonic pole centering.
-/

noncomputable section

open Finset ArithmeticFunction

namespace GaloisForLFunctions.ArithmeticCouplingTheory

private theorem sum_divisible {d : ℕ} (hd : 0 < d) (N : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, if d ∣ n then f n else 0) =
      ∑ n ∈ Icc 1 (N / d), f (d * n) := by
  rw [← sum_filter]
  exact RHTower.Sieve.sum_filter_dvd_eq_sum_scaled hd f

/-- Subtracting a constant changes no dilation jump. -/
theorem jumpEnergy_sub_const (N : ℕ) (F : ℕ → ℝ) (a : ℝ) :
    jumpEnergy N (fun n => F n - a) = jumpEnergy N F := by
  unfold jumpEnergy
  apply sum_congr rfl
  intro kn _
  congr 2
  ring

private theorem indicator_dilation_square (d k n : ℕ) :
    ((if d ∣ k * n then (1 : ℝ) else 0) - (if d ∣ n then 1 else 0)) ^ 2 =
      (if d ∣ k * n then (1 : ℝ) else 0) - (if d ∣ n then 1 else 0) := by
  by_cases hn : d ∣ n
  · have hkn : d ∣ k * n := dvd_mul_of_dvd_right hn k
    simp only [if_pos hn, if_pos hkn, sub_self, zero_pow two_ne_zero]
  · simp only [if_neg hn, sub_zero]
    split_ifs <;> norm_num

private theorem sum_mertens_quotient_div (N : ℕ) :
    (∑ n ∈ Icc 1 N, mertensSum (N / n) / n) =
      ∑ n ∈ Icc 1 N, Real.log n / n := by
  have hs := sum_dilation_source_eq N (fun n => 1 / (n : ℝ))
  have ht := sum_dilation_target_eq N (fun _ => (1 : ℝ))
  simpa only [one_mul, one_div_mul_eq_div] using hs.symm.trans ht

/-- An integer divisibility comb has exact energy `log d · H⌊N/d⌋ / d`. -/
theorem jumpEnergy_divisibilityIndicator {d : ℕ} (hd : 0 < d) (N : ℕ) :
    jumpEnergy N (fun n => if d ∣ n then (1 : ℝ) else 0) =
      Real.log d / d * ∑ n ∈ Icc 1 (N / d), 1 / (n : ℝ) := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have he : jumpEnergy N (fun n => if d ∣ n then (1 : ℝ) else 0) =
      (∑ n ∈ Icc 1 N, (if d ∣ n then (1 : ℝ) else 0) * Real.log n / n) -
        ∑ n ∈ Icc 1 N, (if d ∣ n then (1 : ℝ) else 0) / n * mertensSum (N / n) := by
    rw [jumpEnergy]
    simp only [indicator_dilation_square, sub_div, mul_sub, sum_sub_distrib]
    rw [sum_dilation_target_eq N (fun n => if d ∣ n then (1 : ℝ) else 0),
      sum_dilation_source_eq N (fun n => (if d ∣ n then (1 : ℝ) else 0) / n)]
  rw [he]
  simp only [ite_mul, ite_div, one_mul, zero_mul, zero_div, one_div_mul_eq_div]
  rw [sum_divisible hd, sum_divisible hd]
  have hfirst : (∑ n ∈ Icc 1 (N / d), Real.log (d * n : ℕ) / (d * n : ℕ)) =
      Real.log d / d * (∑ n ∈ Icc 1 (N / d), 1 / (n : ℝ)) +
        (1 / (d : ℝ)) * ∑ n ∈ Icc 1 (N / d), Real.log n / n := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (mem_Icc.mp hn).1
    rw [Nat.cast_mul, Real.log_mul hdR hnR]
    ring
  have hsecond : (∑ n ∈ Icc 1 (N / d), mertensSum (N / (d * n)) / (d * n : ℕ)) =
      (1 / (d : ℝ)) * ∑ n ∈ Icc 1 (N / d), Real.log n / n := by
    rw [← sum_mertens_quotient_div, mul_sum]
    apply sum_congr rfl
    intro n _
    rw [← Nat.div_div_eq_div_mul, Nat.cast_mul]
    ring
  rw [hfirst, hsecond]
  ring

/-- Mangoldt weights linearize squared prime-incidence jumps. -/
theorem vonMangoldt_incidence_jump_square {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (b : ℕ → ℝ) (k n : ℕ) :
    Λ k * (incidencePacket P b (k * n) - incidencePacket P b n) ^ 2 =
      Λ k * (incidencePacket P (fun p => b p ^ 2) (k * n) -
        incidencePacket P (fun p => b p ^ 2) n) := by
  by_cases hk : Λ k = 0
  · simp only [hk, zero_mul]
  · rw [incidencePacket_dilation_jump hP b (vonMangoldt_ne_zero_iff.mp hk),
      incidencePacket_dilation_jump hP (fun p => b p ^ 2) (vonMangoldt_ne_zero_iff.mp hk)]
    split_ifs <;> simp only [zero_pow two_ne_zero]

/-- Distinct prime coordinates are exactly orthogonal for finite-horizon dilation energy. -/
theorem jumpEnergy_incidencePacket_diagonal {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (b : ℕ → ℝ) (N : ℕ) :
    jumpEnergy N (incidencePacket P b) =
      ∑ p ∈ P, b p ^ 2 * (Real.log p / p * ∑ n ∈ Icc 1 (N / p), 1 / (n : ℝ)) := by
  have hterm (k n : ℕ) :
      Λ k / k * ((incidencePacket P b (k * n) - incidencePacket P b n) ^ 2 / n) =
        ∑ p ∈ P, b p ^ 2 * (Λ k / k *
          (((if p ∣ k * n then (1 : ℝ) else 0) - (if p ∣ n then 1 else 0)) ^ 2 / n)) := by
    calc
      _ = (Λ k * (incidencePacket P b (k * n) - incidencePacket P b n) ^ 2) /
          ((k : ℝ) * n) := by ring
      _ = (Λ k * (incidencePacket P (fun p => b p ^ 2) (k * n) -
          incidencePacket P (fun p => b p ^ 2) n)) / ((k : ℝ) * n) := by
        rw [vonMangoldt_incidence_jump_square hP]
      _ = _ := by
        simp only [incidencePacket, ← sum_sub_distrib, mul_sum,
          indicator_dilation_square]
        rw [div_eq_mul_inv, sum_mul]
        apply sum_congr rfl
        intro p _
        ring
  rw [jumpEnergy]
  simp only [hterm]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  rw [← mul_sum]
  congr 1
  exact jumpEnergy_divisibilityIndicator (hP p hp).pos N

#print axioms jumpEnergy_divisibilityIndicator
#print axioms jumpEnergy_incidencePacket_diagonal

end GaloisForLFunctions.ArithmeticCouplingTheory
