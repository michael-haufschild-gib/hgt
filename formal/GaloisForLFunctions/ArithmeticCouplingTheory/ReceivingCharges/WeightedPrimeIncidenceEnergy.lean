import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.PrimeIncidenceDilationEnergy

/-!
# Prime-incidence energy in an invariant conductor fibre

A weight unchanged by multiplication by `p` passes through every `p`-tower
edge. Reindexing its source and target drifts leaves exactly the cofactor
harmonic mass, with the same factor `log p / p` as the unweighted identity.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped Classical

namespace GaloisForLFunctions.ArithmeticCouplingTheory

private def dilationDrift (N : ℕ) (h : ℕ → ℝ) : ℝ :=
  ∑ kn ∈ dilationPairs N, Λ kn.1 / kn.1 * ((h (kn.1 * kn.2) - h kn.2) / kn.2)

private theorem dilationDrift_eq (N : ℕ) (h : ℕ → ℝ) :
    dilationDrift N h =
      ∑ n ∈ Icc 1 N, h n / (n : ℝ) * (Real.log n - mertensSum (N / n)) := by
  simp only [dilationDrift, sub_div, mul_sub, sum_sub_distrib]
  rw [sum_dilation_target_eq N h, sum_dilation_source_eq N (fun n => h n / n)]
  simp only [← sum_sub_distrib]
  exact sum_congr rfl fun _ _ => by ring

private theorem sum_divisible {p : ℕ} (hp : 0 < p) (N : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, if p ∣ n then f n else 0) =
      ∑ n ∈ Icc 1 (N / p), f (p * n) := by
  rw [← sum_filter]
  exact RHTower.Sieve.sum_filter_dvd_eq_sum_scaled hp f

/-- Invariance under a prime extends to every power of that prime. -/
theorem invariant_on_prime_tower {p k : ℕ} (hp : p.Prime) (hk : IsPrimePow k)
    (hpk : p ∣ k) (h : ℕ → ℝ) (hinv : ∀ n, h (p * n) = h n) (n : ℕ) :
    h (k * n) = h n := by
  have hq : k.minFac.Prime := Nat.minFac_prime hk.ne_one
  have hkpow := hk.minFac_pow_factorization_eq
  have hpq : p = k.minFac := by
    rw [← hkpow] at hpk
    exact (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hpk)
  rw [← hpq] at hkpow
  rw [← hkpow]
  have hpow (a : ℕ) : h (p ^ a * n) = h n := by
    induction a with
    | zero => simp only [pow_zero, one_mul]
    | succ a ih =>
      rw [pow_succ, show (p ^ a * p) * n = p * (p ^ a * n) by ac_rfl, hinv, ih]
  exact hpow _

private theorem weighted_indicator_edge {p : ℕ} (hp : p.Prime)
    (h : ℕ → ℝ) (hinv : ∀ n, h (p * n) = h n) (k n : ℕ) :
    Λ k * h n *
      ((if p ∣ k * n then (1 : ℝ) else 0) - (if p ∣ n then 1 else 0)) ^ 2 =
    Λ k * ((h (k * n) * (if p ∣ k * n then 1 else 0) -
      h n * (if p ∣ n then 1 else 0)) -
        (if p ∣ n then 1 else 0) * (h (k * n) - h n)) := by
  by_cases hΛ : Λ k = 0
  · simp only [hΛ, zero_mul]
  by_cases hn : p ∣ n
  · have hkn := dvd_mul_of_dvd_right hn k
    simp only [if_pos hn, if_pos hkn]
    ring
  by_cases hkn : p ∣ k * n
  · have hpk := (hp.dvd_mul.mp hkn).resolve_right hn
    rw [invariant_on_prime_tower hp (vonMangoldt_ne_zero_iff.mp hΛ) hpk h hinv n]
    simp only [if_neg hn, if_pos hkn]
    ring
  · simp only [if_neg hn, if_neg hkn]
    ring

private theorem indicator_source_drift {p : ℕ} (hp : 0 < p) (N : ℕ)
    (h : ℕ → ℝ) (hinv : ∀ n, h (p * n) = h n) :
    (∑ kn ∈ dilationPairs N, Λ kn.1 / kn.1 *
      ((if p ∣ kn.2 then (1 : ℝ) else 0) * (h (kn.1 * kn.2) - h kn.2) / kn.2)) =
      (1 / (p : ℝ)) * dilationDrift (N / p) h := by
  rw [sum_dilationPairs_eq N (fun k n => Λ k / k *
    ((if p ∣ n then (1 : ℝ) else 0) * (h (k * n) - h n) / n))]
  have hrow (n : ℕ) :
      (∑ k ∈ Icc 1 (N / n), Λ k / k *
        ((if p ∣ n then (1 : ℝ) else 0) * (h (k * n) - h n) / n)) =
      if p ∣ n then
        (∑ k ∈ Icc 1 (N / n), Λ k / k * (h (k * n) - h n)) / n else 0 := by
    by_cases hn : p ∣ n
    · simp only [if_pos hn, one_mul, div_eq_mul_inv, mul_assoc, sum_mul]
    · simp only [if_neg hn, zero_mul, zero_div, mul_zero, sum_const_zero]
  simp only [hrow]
  rw [sum_divisible hp, dilationDrift,
    sum_dilationPairs_eq (N / p) (fun k n => Λ k / k * ((h (k * n) - h n) / n)), mul_sum]
  apply sum_congr rfl
  intro n _
  rw [← Nat.div_div_eq_div_mul, Nat.cast_mul, hinv]
  simp only [div_eq_mul_inv, mul_inv_rev, sum_mul, mul_sum]
  apply sum_congr rfl
  intro k _
  rw [show k * (p * n) = p * (k * n) by ac_rfl, hinv]
  ring

private theorem indicator_target_drift {p : ℕ} (hp : 0 < p) (N : ℕ)
    (h : ℕ → ℝ) (hinv : ∀ n, h (p * n) = h n) :
    dilationDrift N (fun n => h n * (if p ∣ n then 1 else 0)) =
      Real.log p / p * (∑ n ∈ Icc 1 (N / p), h n / (n : ℝ)) +
        (1 / (p : ℝ)) * dilationDrift (N / p) h := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [dilationDrift_eq]
  have hrow (n : ℕ) :
      (h n * (if p ∣ n then (1 : ℝ) else 0)) / n *
        (Real.log n - mertensSum (N / n)) =
      if p ∣ n then h n / n * (Real.log n - mertensSum (N / n)) else 0 := by
    split_ifs <;> ring
  simp only [hrow]
  rw [sum_divisible hp, dilationDrift_eq, mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (mem_Icc.mp hn).1
  rw [hinv, Nat.cast_mul, Real.log_mul hpR hnR, ← Nat.div_div_eq_div_mul]
  ring

/-- An invariant conductor weight retains its exact harmonic cofactor on every prime edge. -/
theorem weighted_primeIncidence_energy {p : ℕ} (hp : p.Prime) (N : ℕ)
    (h : ℕ → ℝ) (hinv : ∀ n, h (p * n) = h n) :
    (∑ kn ∈ dilationPairs N, Λ kn.1 / kn.1 *
      (h kn.2 * ((if p ∣ kn.1 * kn.2 then (1 : ℝ) else 0) -
        (if p ∣ kn.2 then 1 else 0)) ^ 2 / kn.2)) =
      Real.log p / p * (∑ n ∈ Icc 1 (N / p), h n / (n : ℝ)) := by
  have hedge (k n : ℕ) :
      Λ k / k * (h n * ((if p ∣ k * n then (1 : ℝ) else 0) -
        (if p ∣ n then 1 else 0)) ^ 2 / n) =
      Λ k / k * ((h (k * n) * (if p ∣ k * n then 1 else 0) -
        h n * (if p ∣ n then 1 else 0)) / n) -
      Λ k / k * ((if p ∣ n then 1 else 0) * (h (k * n) - h n) / n) := by
    have he := weighted_indicator_edge hp h hinv k n
    calc
      _ = (Λ k * h n * ((if p ∣ k * n then (1 : ℝ) else 0) -
        (if p ∣ n then 1 else 0)) ^ 2) / ((k : ℝ) * n) := by ring
      _ = _ := by rw [he]; ring
  simp only [hedge, sum_sub_distrib]
  change dilationDrift N (fun n => h n * (if p ∣ n then 1 else 0)) - _ = _
  rw [indicator_target_drift hp.pos N h hinv, indicator_source_drift hp.pos N h hinv]
  ring

private theorem weighted_indicator_square (p k n : ℕ) :
    ((if p ∣ k * n then (1 : ℝ) else 0) - (if p ∣ n then 1 else 0)) ^ 2 =
      (if p ∣ k * n then (1 : ℝ) else 0) - (if p ∣ n then 1 else 0) := by
  by_cases hn : p ∣ n
  · have hkn := dvd_mul_of_dvd_right hn k
    simp only [if_pos hn, if_pos hkn, sub_self, zero_pow two_ne_zero]
  · simp only [if_neg hn, sub_zero]
    split_ifs <;> norm_num

/-- The weighted finite prime-incidence pairing remains diagonal on every invariant fibre. -/
theorem weighted_primeIncidence_packet_pairing {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (b d h : ℕ → ℝ)
    (hinv : ∀ p ∈ P, ∀ n, h (p * n) = h n) (N : ℕ) :
    (∑ kn ∈ dilationPairs N, Λ kn.1 / kn.1 *
      (h kn.2 * ((incidencePacket P b (kn.1 * kn.2) - incidencePacket P b kn.2) *
        (incidencePacket P d (kn.1 * kn.2) - incidencePacket P d kn.2)) / kn.2)) =
      ∑ p ∈ P, b p * d p *
        (Real.log p / p * ∑ n ∈ Icc 1 (N / p), h n / (n : ℝ)) := by
  have hlinear (k n : ℕ) :
      Λ k * (incidencePacket P b (k * n) - incidencePacket P b n) *
        (incidencePacket P d (k * n) - incidencePacket P d n) =
      Λ k * (incidencePacket P (fun p => b p * d p) (k * n) -
        incidencePacket P (fun p => b p * d p) n) := by
    by_cases hΛ : Λ k = 0
    · simp only [hΛ, zero_mul]
    · rw [incidencePacket_dilation_jump hP b (vonMangoldt_ne_zero_iff.mp hΛ),
        incidencePacket_dilation_jump hP d (vonMangoldt_ne_zero_iff.mp hΛ),
        incidencePacket_dilation_jump hP (fun p => b p * d p) (vonMangoldt_ne_zero_iff.mp hΛ)]
      split_ifs <;> ring
  have hterm (k n : ℕ) :
      Λ k / k * (h n * ((incidencePacket P b (k * n) - incidencePacket P b n) *
        (incidencePacket P d (k * n) - incidencePacket P d n)) / n) =
      ∑ p ∈ P, b p * d p * (Λ k / k *
        (h n * ((if p ∣ k * n then (1 : ℝ) else 0) - (if p ∣ n then 1 else 0)) ^ 2 / n)) := by
    calc
      _ = (h n / ((k : ℝ) * n)) *
          (Λ k * (incidencePacket P b (k * n) - incidencePacket P b n) *
            (incidencePacket P d (k * n) - incidencePacket P d n)) := by ring
      _ = (h n / ((k : ℝ) * n)) *
          (Λ k * (incidencePacket P (fun p => b p * d p) (k * n) -
            incidencePacket P (fun p => b p * d p) n)) := by rw [hlinear]
      _ = _ := by
        simp only [incidencePacket, ← sum_sub_distrib, mul_sum, weighted_indicator_square]
        exact sum_congr rfl fun p _ => by ring
  simp only [hterm]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  rw [← mul_sum, weighted_primeIncidence_energy (hP p hp) N h (hinv p hp)]

#print axioms weighted_primeIncidence_energy
#print axioms weighted_primeIncidence_packet_pairing

end GaloisForLFunctions.ArithmeticCouplingTheory
