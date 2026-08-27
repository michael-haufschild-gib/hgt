import GaloisForLFunctions.RHTower.Sieve.PrimePairDivisorWeightedMean

/-!
# Divisor-weighted one-prime means

Endpoint errors in Matomäki--Teräväinen's Lemma 2.3 contain one prime constrained to a short
interval and an unrestricted divisor-bounded convolution coefficient.  Multiplication by that
prime costs at most a factor two in the divisor function.  Reindexing its multiples therefore
retains the reciprocal-prime saving under every fixed divisor power.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Exact floor-scale divisor-moment bound along multiples of one prescribed prime. -/
theorem sum_card_divisors_pow_prime_dvd_le_floorPolylog
    (K Y : ℕ) {p : ℕ} (hp : p.Prime) :
    ∑ n ∈ Finset.Icc 1 Y,
        (if p ∣ n then ((n.divisors.card : ℝ) ^ K) else 0) ≤
      (2 : ℝ) ^ K * ((Y / p : ℕ) : ℝ) *
        (1 + Real.log ((Y / p : ℕ) : ℝ)) ^ (2 ^ K - 1) := by
  rw [← Finset.sum_filter]
  rw [sum_Icc_dvd_reindex p Y hp.pos]
  let N := Y / p
  rcases Nat.eq_zero_or_pos N with hN | hN
  · simp [N, hN]
  · have hmoment := sum_card_divisors_pow_le_polylog K N hN
    calc
      ∑ k ∈ Finset.Icc 1 N, (((p * k).divisors.card : ℝ) ^ K) ≤
          ∑ k ∈ Finset.Icc 1 N, (2 : ℝ) ^ K * ((k.divisors.card : ℝ) ^ K) := by
        apply Finset.sum_le_sum
        intro k hkMem
        have hk : 0 < k := by
          rw [Finset.mem_Icc] at hkMem
          omega
        have hcardN := card_divisors_mul_prime_le_two hp hk
        have hcardR : (((p * k).divisors.card : ℕ) : ℝ) ≤
            (2 : ℝ) * ((k.divisors.card : ℕ) : ℝ) := by
          exact_mod_cast hcardN
        have hpow := pow_le_pow_left₀
          (by positivity : (0 : ℝ) ≤ ((p * k).divisors.card : ℝ)) hcardR K
        simpa [mul_pow] using hpow
      _ = (2 : ℝ) ^ K * ∑ k ∈ Finset.Icc 1 N, ((k.divisors.card : ℝ) ^ K) := by
        rw [Finset.mul_sum]
      _ ≤ (2 : ℝ) ^ K *
          ((N : ℝ) * (1 + Real.log (N : ℝ)) ^ (2 ^ K - 1)) := by
        exact mul_le_mul_of_nonneg_left hmoment (by positivity)
      _ = (2 : ℝ) ^ K * ((Y / p : ℕ) : ℝ) *
          (1 + Real.log ((Y / p : ℕ) : ℝ)) ^ (2 ^ K - 1) := by
        simp only [N]
        ring

/-- Common-scale divisor-moment bound with the reciprocal-prime factor exposed. -/
theorem sum_card_divisors_pow_prime_dvd_le_polylog
    (K Y : ℕ) (hY : 1 ≤ Y) {p : ℕ} (hp : p.Prime) :
    ∑ n ∈ Finset.Icc 1 Y,
        (if p ∣ n then ((n.divisors.card : ℝ) ^ K) else 0) ≤
      (2 : ℝ) ^ K * ((Y : ℝ) / (p : ℝ)) *
        (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1) := by
  have hbase := sum_card_divisors_pow_prime_dvd_le_floorPolylog K Y hp
  let N := Y / p
  rcases Nat.eq_zero_or_pos N with hN | hN
  · have hzero : ∀ n ∈ Finset.Icc 1 Y, ¬p ∣ n := by
      intro n hn hdvd
      have hnpos : 0 < n := by
        rw [Finset.mem_Icc] at hn
        omega
      have hle : p ≤ Y := (Nat.le_of_dvd hnpos hdvd).trans (Finset.mem_Icc.mp hn).2
      have hdiv : 1 ≤ Y / p := (Nat.one_le_div_iff hp.pos).mpr hle
      have : 1 ≤ N := by simpa only [N] using hdiv
      omega
    have hlhs : ∑ n ∈ Finset.Icc 1 Y,
        (if p ∣ n then ((n.divisors.card : ℝ) ^ K) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      simp [hzero n hn]
    rw [hlhs]
    positivity
  · have hNY : N ≤ Y := Nat.div_le_self Y p
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hlog : Real.log (N : ℝ) ≤ Real.log (Y : ℝ) :=
      Real.log_le_log hNR (by exact_mod_cast hNY)
    have hpow : (1 + Real.log (N : ℝ)) ^ (2 ^ K - 1) ≤
        (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1) := by
      apply pow_le_pow_left₀
      · have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
        linarith
      · linarith
    have hdiv : (N : ℝ) ≤ (Y : ℝ) / (p : ℝ) := Nat.cast_div_le
    have hpoly0 : 0 ≤ (1 + Real.log (N : ℝ)) ^ (2 ^ K - 1) := by positivity
    have hpolyY0 : 0 ≤ (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1) := by
      have : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by exact_mod_cast hY)
      positivity
    calc
      ∑ n ∈ Finset.Icc 1 Y,
          (if p ∣ n then ((n.divisors.card : ℝ) ^ K) else 0) ≤
        (2 : ℝ) ^ K * (N : ℝ) *
          (1 + Real.log (N : ℝ)) ^ (2 ^ K - 1) := by
            simpa only [N] using hbase
      _ ≤ (2 : ℝ) ^ K * ((Y : ℝ) / (p : ℝ)) *
          (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1) := by
        gcongr

/-- Number of prescribed primes dividing `n`, with ordered membership retained. -/
def primeDivisorCount (S : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ p ∈ S, if p ∣ n then 1 else 0

/-- Divisor-weighted count of prescribed primes dividing `n`. -/
def weightedPrimeDivisorCount (K : ℕ) (S : Finset ℕ) (n : ℕ) : ℝ :=
  (n.divisors.card : ℝ) ^ K * primeDivisorCount S n

/-- Weighted family mean bounded by reciprocal mass and a fixed divisor polylogarithm. -/
theorem sum_weightedPrimeDivisorCount_le
    (K Y : ℕ) (hY : 1 ≤ Y) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) :
    ∑ n ∈ Finset.Icc 1 Y, weightedPrimeDivisorCount K S n ≤
      (2 : ℝ) ^ K * (Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1) *
        ∑ p ∈ S, 1 / (p : ℝ) := by
  let C : ℝ := (2 : ℝ) ^ K * (Y : ℝ) *
    (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1)
  calc
    ∑ n ∈ Finset.Icc 1 Y, weightedPrimeDivisorCount K S n =
        ∑ p ∈ S, ∑ n ∈ Finset.Icc 1 Y,
          (if p ∣ n then ((n.divisors.card : ℝ) ^ K) else 0) := by
      unfold weightedPrimeDivisorCount primeDivisorCount
      simp_rw [Finset.mul_sum, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_comm]
    _ ≤ ∑ p ∈ S, C * (1 / (p : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      have h := sum_card_divisors_pow_prime_dvd_le_polylog K Y hY (hS p hp)
      dsimp [C]
      convert h using 1 <;> try rfl
      simp only [div_eq_mul_inv]
      ring
    _ = (2 : ℝ) ^ K * (Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1) *
        ∑ p ∈ S, 1 / (p : ℝ) := by
      dsimp [C]
      rw [Finset.mul_sum]

end

end RHTower.Sieve
