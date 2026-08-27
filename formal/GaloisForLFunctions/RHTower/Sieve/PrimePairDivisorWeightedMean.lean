import GaloisForLFunctions.RHTower.Sieve.MaynardFixedDivisorMoment
import GaloisForLFunctions.RHTower.PrimeSquareMobiusDensityFracture
import GaloisForLFunctions.RHTower.Sieve.PrimePairDivisorMean

/-!
# Divisor-weighted prime-pair means

Matomäki--Teräväinen's `c₃,n` estimate weights same-block prime collisions by a fixed power of the
divisor function.  Multiplication by two primes increases the number of divisors by at most four.
Reindexing multiples of their product therefore preserves the pair-reciprocal saving, at the cost
of `4 ^ K` times the standard divisor-moment polylogarithm.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Multiplication by one prime at most doubles the number of divisors. -/
theorem card_divisors_mul_prime_le_two {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    (p * k).divisors.card ≤ 2 * k.divisors.card := by
  classical
  let s : Finset (Fin 2 × ℕ) := Finset.univ.product k.divisors
  let f : Fin 2 × ℕ → ℕ := fun x => if x.1 = 0 then x.2 else p * x.2
  have hsurj : Set.SurjOn f (s : Set (Fin 2 × ℕ)) ((p * k).divisors : Set ℕ) := by
    intro d hd
    have hdk : d ∣ p * k := (Nat.mem_divisors.mp hd).1
    by_cases hpd : p ∣ d
    · obtain ⟨e, rfl⟩ := hpd
      have he : e ∣ k := (Nat.mul_dvd_mul_iff_left hp.pos).mp hdk
      refine ⟨(1, e), ?_, ?_⟩
      · simp [s, Nat.mem_divisors, he, hk.ne']
      · simp [f]
    · have hcop : d.Coprime p := (hp.coprime_iff_not_dvd.mpr hpd).symm
      have he : d ∣ k := hcop.dvd_of_dvd_mul_left hdk
      refine ⟨(0, d), ?_, ?_⟩
      · simp [s, Nat.mem_divisors, he, hk.ne']
      · simp [f]
  have hcard := Finset.card_le_card_of_surjOn f hsurj
  simpa [s] using hcard

/-- Multiplication by two primes at most quadruples the number of divisors. -/
theorem card_divisors_mul_two_primes_le_four {p q k : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hk : 0 < k) :
    (p * q * k).divisors.card ≤ 4 * k.divisors.card := by
  have hpBound := card_divisors_mul_prime_le_two hp (Nat.mul_pos hq.pos hk)
  have hqBound := card_divisors_mul_prime_le_two hq hk
  have h := hpBound.trans (Nat.mul_le_mul_left 2 hqBound)
  calc
    (p * q * k).divisors.card ≤ 2 * (2 * k.divisors.card) := by
      simpa only [mul_assoc] using h
    _ = 4 * k.divisors.card := by ring

/-- Exact floor-scale divisor-moment bound along multiples of a prescribed prime pair. -/
theorem sum_card_divisors_pow_pair_dvd_le_floorPolylog
    (K Y : ℕ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    ∑ n ∈ Finset.Icc 1 Y,
        (if p * q ∣ n then ((n.divisors.card : ℝ) ^ K) else 0) ≤
      (4 : ℝ) ^ K * ((Y / (p * q) : ℕ) : ℝ) *
        (1 + Real.log ((Y / (p * q) : ℕ) : ℝ)) ^ (2 ^ K - 1) := by
  have hd : 0 < p * q := Nat.mul_pos hp.pos hq.pos
  rw [← Finset.sum_filter]
  rw [sum_Icc_dvd_reindex (p * q) Y hd]
  let N := Y / (p * q)
  rcases Nat.eq_zero_or_pos N with hN | hN
  · simp [N, hN]
  · have hmoment := sum_card_divisors_pow_le_polylog K N hN
    calc
      ∑ k ∈ Finset.Icc 1 N, ((((p * q) * k).divisors.card : ℝ) ^ K) ≤
          ∑ k ∈ Finset.Icc 1 N, (4 : ℝ) ^ K * ((k.divisors.card : ℝ) ^ K) := by
        apply Finset.sum_le_sum
        intro k hkMem
        have hk : 0 < k := by
          rw [Finset.mem_Icc] at hkMem
          omega
        have hcardN := card_divisors_mul_two_primes_le_four hp hq hk
        have hcardR : (((p * q * k).divisors.card : ℕ) : ℝ) ≤
            (4 : ℝ) * ((k.divisors.card : ℕ) : ℝ) := by
          exact_mod_cast hcardN
        have hpow := pow_le_pow_left₀
          (by positivity : (0 : ℝ) ≤ ((p * q * k).divisors.card : ℝ)) hcardR K
        simpa [mul_pow] using hpow
      _ = (4 : ℝ) ^ K * ∑ k ∈ Finset.Icc 1 N, ((k.divisors.card : ℝ) ^ K) := by
        rw [Finset.mul_sum]
      _ ≤ (4 : ℝ) ^ K *
          ((N : ℝ) * (1 + Real.log (N : ℝ)) ^ (2 ^ K - 1)) := by
        exact mul_le_mul_of_nonneg_left hmoment (by positivity)
      _ = (4 : ℝ) ^ K * ((Y / (p * q) : ℕ) : ℝ) *
          (1 + Real.log ((Y / (p * q) : ℕ) : ℝ)) ^ (2 ^ K - 1) := by
        simp only [N]
        ring

/-- Common-scale divisor-moment bound with the prime-pair reciprocal factor exposed. -/
theorem sum_card_divisors_pow_pair_dvd_le_polylog
    (K Y : ℕ) (hY : 1 ≤ Y) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    ∑ n ∈ Finset.Icc 1 Y,
        (if p * q ∣ n then ((n.divisors.card : ℝ) ^ K) else 0) ≤
      (4 : ℝ) ^ K * ((Y : ℝ) / ((p : ℝ) * (q : ℝ))) *
        (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1) := by
  have hbase := sum_card_divisors_pow_pair_dvd_le_floorPolylog K Y hp hq
  let N := Y / (p * q)
  rcases Nat.eq_zero_or_pos N with hN | hN
  · have hzero : ∀ n ∈ Finset.Icc 1 Y, ¬p * q ∣ n := by
      intro n hn hdvd
      have hnpos : 0 < n := by
        rw [Finset.mem_Icc] at hn
        omega
      have hle : p * q ≤ Y := (Nat.le_of_dvd hnpos hdvd).trans (Finset.mem_Icc.mp hn).2
      have hdiv : 1 ≤ Y / (p * q) :=
        (Nat.one_le_div_iff (Nat.mul_pos hp.pos hq.pos)).mpr hle
      have : 1 ≤ N := by simpa only [N] using hdiv
      omega
    have hlhs : ∑ n ∈ Finset.Icc 1 Y,
        (if p * q ∣ n then ((n.divisors.card : ℝ) ^ K) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      simp [hzero n hn]
    rw [hlhs]
    positivity
  · have hNY : N ≤ Y := Nat.div_le_self Y (p * q)
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hlog : Real.log (N : ℝ) ≤ Real.log (Y : ℝ) :=
      Real.log_le_log hNR (by exact_mod_cast hNY)
    have hpow : (1 + Real.log (N : ℝ)) ^ (2 ^ K - 1) ≤
        (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1) := by
      apply pow_le_pow_left₀
      · have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
        linarith
      · linarith
    have hdiv : (N : ℝ) ≤ (Y : ℝ) / ((p : ℝ) * (q : ℝ)) := by
      have hcast : ((Y / (p * q) : ℕ) : ℝ) ≤ (Y : ℝ) / ((p * q : ℕ) : ℝ) :=
        Nat.cast_div_le
      push_cast at hcast
      exact hcast
    have hpoly0 : 0 ≤ (1 + Real.log (N : ℝ)) ^ (2 ^ K - 1) := by positivity
    have hpolyY0 : 0 ≤ (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1) := by
      have : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by exact_mod_cast hY)
      positivity
    calc
      ∑ n ∈ Finset.Icc 1 Y,
          (if p * q ∣ n then ((n.divisors.card : ℝ) ^ K) else 0) ≤
        (4 : ℝ) ^ K * (N : ℝ) *
          (1 + Real.log (N : ℝ)) ^ (2 ^ K - 1) := by
            simpa only [N] using hbase
      _ ≤ (4 : ℝ) ^ K * ((Y : ℝ) / ((p : ℝ) * (q : ℝ))) *
          (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1) := by
        gcongr

/-- Divisor-weighted count of prescribed ordered prime pairs dividing `n`. -/
def weightedPrimePairDivisorCount
    (K : ℕ) (S : Finset ℕ) (T : ℕ → Finset ℕ) (n : ℕ) : ℝ :=
  (n.divisors.card : ℝ) ^ K * primePairDivisorCount S T n

/-- Weighted family mean bounded by pair reciprocal mass and a fixed divisor polylogarithm. -/
theorem sum_weightedPrimePairDivisorCount_le
    (K Y : ℕ) (hY : 1 ≤ Y) (S : Finset ℕ) (T : ℕ → Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hT : ∀ p ∈ S, ∀ q ∈ T p, q.Prime) :
    ∑ n ∈ Finset.Icc 1 Y, weightedPrimePairDivisorCount K S T n ≤
      (4 : ℝ) ^ K * (Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1) *
        ∑ p ∈ S, (1 / (p : ℝ)) * ∑ q ∈ T p, 1 / (q : ℝ) := by
  let C : ℝ := (4 : ℝ) ^ K * (Y : ℝ) *
    (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1)
  calc
    ∑ n ∈ Finset.Icc 1 Y, weightedPrimePairDivisorCount K S T n =
        ∑ p ∈ S, ∑ q ∈ T p, ∑ n ∈ Finset.Icc 1 Y,
          (if p * q ∣ n then ((n.divisors.card : ℝ) ^ K) else 0) := by
      unfold weightedPrimePairDivisorCount primePairDivisorCount
      simp_rw [Finset.mul_sum, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_comm]
    _ ≤ ∑ p ∈ S, ∑ q ∈ T p, C * (1 / (p : ℝ)) * (1 / (q : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      have h := sum_card_divisors_pow_pair_dvd_le_polylog
        K Y hY (hS p hp) (hT p hp q hq)
      dsimp [C]
      convert h using 1 <;> try rfl
      simp only [div_eq_mul_inv]
      rw [mul_inv]
      ring
    _ = (4 : ℝ) ^ K * (Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1) *
        ∑ p ∈ S, (1 / (p : ℝ)) * ∑ q ∈ T p, 1 / (q : ℝ) := by
      dsimp [C]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [← mul_assoc, Finset.mul_sum]

/-- Uniform fibre mass factors out of the weighted pair estimate. -/
theorem sum_weightedPrimePairDivisorCount_le_of_fibreMass
    (K Y : ℕ) (hY : 1 ≤ Y) (S : Finset ℕ) (T : ℕ → Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hT : ∀ p ∈ S, ∀ q ∈ T p, q.Prime)
    {η : ℝ} (hmass : ∀ p ∈ S, ∑ q ∈ T p, 1 / (q : ℝ) ≤ η) :
    ∑ n ∈ Finset.Icc 1 Y, weightedPrimePairDivisorCount K S T n ≤
      (4 : ℝ) ^ K * (Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1) *
        η * ∑ p ∈ S, 1 / (p : ℝ) := by
  have hbase := sum_weightedPrimePairDivisorCount_le K Y hY S T hS hT
  have hC : 0 ≤ (4 : ℝ) ^ K * (Y : ℝ) *
      (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1) := by
    have hlog : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by exact_mod_cast hY)
    positivity
  calc
    ∑ n ∈ Finset.Icc 1 Y, weightedPrimePairDivisorCount K S T n ≤
        (4 : ℝ) ^ K * (Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1) *
          ∑ p ∈ S, (1 / (p : ℝ)) * ∑ q ∈ T p, 1 / (q : ℝ) := hbase
    _ ≤ (4 : ℝ) ^ K * (Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1) *
          ∑ p ∈ S, (1 / (p : ℝ)) * η := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (hmass p hp)
        (one_div_nonneg.mpr (by exact_mod_cast (hS p hp).pos.le))
    _ = (4 : ℝ) ^ K * (Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1) *
        η * ∑ p ∈ S, 1 / (p : ℝ) := by
      rw [← Finset.sum_mul]
      ring

end

end RHTower.Sieve
