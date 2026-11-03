import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.FiniteHorizonPrimeCharge
import GaloisForLFunctions.RHTower.Sieve.PrimeDivisorWeightedMean

/-!
# Ordinary and harmonic moments of coherent prime incidence

Distinct prime incidences meet on multiples of their product. Separating the
diagonal gives a second moment bounded by squared reciprocal mass plus
reciprocal mass, uniformly in the conductor cutoff and the horizon.
-/

noncomputable section

open Finset
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open SelectiveMultiscaleArithmeticPositivity
open _root_.RHTower.Sieve

private theorem prime_count_square_le {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    primeDivisorCount P n ^ 2 ≤
      primePairDivisorCount P (fun _ => P) n + primeDivisorCount P n := by
  have hpair (p : ℕ) (hp : p ∈ P) (q : ℕ) (hq : q ∈ P) :
      (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then 1 else 0) ≤
        (if p * q ∣ n then 1 else 0) +
          if p = q then (if p ∣ n then 1 else 0) else 0 := by
    by_cases hpq : p = q
    · subst q
      split_ifs <;> norm_num
    · simp only [if_neg hpq, add_zero]
      by_cases hpn : p ∣ n
      · by_cases hqn : q ∣ n
        · have hpqn := ((Nat.coprime_primes (hP p hp) (hP q hq)).2 hpq).
            mul_dvd_of_dvd_of_dvd hpn hqn
          simp only [if_pos hpn, if_pos hqn, if_pos hpqn, one_mul, le_refl]
        · simp only [if_pos hpn, if_neg hqn, mul_zero]
          split_ifs <;> norm_num
      · simp only [if_neg hpn, zero_mul]
        split_ifs <;> norm_num
  calc
    primeDivisorCount P n ^ 2 = ∑ p ∈ P, ∑ q ∈ P,
        (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then 1 else 0) := by
      rw [primeDivisorCount, sq, sum_mul]
      simp only [mul_sum]
    _ ≤ ∑ p ∈ P, ∑ q ∈ P,
        ((if p * q ∣ n then (1 : ℝ) else 0) +
          if p = q then (if p ∣ n then 1 else 0) else 0) :=
      sum_le_sum fun p hp => sum_le_sum fun q hq => hpair p hp q hq
    _ = _ := by
      simp only [sum_add_distrib, sum_ite_eq, ite_true]
      rw [primePairDivisorCount, primeDivisorCount]
      congr 1
      exact sum_congr rfl fun p hp => if_pos hp

private theorem count_moment_le {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (N : ℕ) (ν : ℕ → ℝ) (A : ℝ)
    (hν : ∀ n ∈ Icc 1 N, 0 ≤ ν n)
    (hd : ∀ d : ℕ, 0 < d →
      (∑ n ∈ Icc 1 N, if d ∣ n then ν n else 0) ≤ A / d) :
    (∑ n ∈ Icc 1 N, ν n * primeDivisorCount P n ^ 2) ≤
      A * ((∑ p ∈ P, 1 / (p : ℝ)) ^ 2 + ∑ p ∈ P, 1 / (p : ℝ)) := by
  have hpair : (∑ n ∈ Icc 1 N, ν n * primePairDivisorCount P (fun _ => P) n) =
      ∑ p ∈ P, ∑ q ∈ P, ∑ n ∈ Icc 1 N, if p * q ∣ n then ν n else 0 := by
    simp only [primePairDivisorCount, mul_sum, mul_ite, mul_one, mul_zero]
    rw [sum_comm]
    exact sum_congr rfl fun _ _ => sum_comm
  have hone : (∑ n ∈ Icc 1 N, ν n * primeDivisorCount P n) =
      ∑ p ∈ P, ∑ n ∈ Icc 1 N, if p ∣ n then ν n else 0 := by
    simp only [primeDivisorCount, mul_sum, mul_ite, mul_one, mul_zero]
    rw [sum_comm]
  calc
    _ ≤ ∑ n ∈ Icc 1 N,
        ν n * (primePairDivisorCount P (fun _ => P) n + primeDivisorCount P n) :=
      sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (prime_count_square_le hP n) (hν n hn)
    _ = (∑ p ∈ P, ∑ q ∈ P, ∑ n ∈ Icc 1 N, if p * q ∣ n then ν n else 0) +
        ∑ p ∈ P, ∑ n ∈ Icc 1 N, if p ∣ n then ν n else 0 := by
      simp only [mul_add, sum_add_distrib]
      rw [hpair, hone]
    _ ≤ (∑ p ∈ P, ∑ q ∈ P, A / (p * q : ℕ)) + ∑ p ∈ P, A / p :=
      add_le_add (sum_le_sum fun p hp => sum_le_sum fun q hq =>
        hd (p * q) (Nat.mul_pos (hP p hp).pos (hP q hq).pos))
        (sum_le_sum fun p hp => hd p (hP p hp).pos)
    _ = _ := by
      simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev, one_mul, sq,
        mul_add, mul_sum, sum_mul]
      congr 1
      exact sum_congr rfl fun p _ => sum_congr rfl fun q _ => by ring

/-- Ordinary second moment of prime incidence, with no cutoff-separation loss. -/
theorem primeDivisorCount_second_moment_le {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (N : ℕ) :
    (∑ n ∈ Icc 1 N, primeDivisorCount P n ^ 2) ≤
      (N : ℝ) * ((∑ p ∈ P, 1 / (p : ℝ)) ^ 2 + ∑ p ∈ P, 1 / (p : ℝ)) := by
  have h := count_moment_le hP N (fun _ => 1) N (fun _ _ => zero_le_one)
    (fun d _ => by rw [sum_dvdIndicator_Icc]; exact Nat.cast_div_le)
  simpa only [one_mul] using h

private theorem harmonic_divisibility_le (N : ℕ) {d : ℕ} (hd : 0 < d) :
    (∑ n ∈ Icc 1 N, if d ∣ n then 1 / (n : ℝ) else 0) ≤ harmonicMass N / d := by
  rw [← sum_filter, sum_filter_dvd_eq_sum_scaled hd]
  have hmono : harmonicMass (N / d) ≤ harmonicMass N := by
    apply sum_le_sum_of_subset_of_nonneg
      (Icc_subset_Icc le_rfl (Nat.div_le_self N d))
    intro n _ _
    exact div_nonneg zero_le_one (Nat.cast_nonneg n)
  calc
    (∑ n ∈ Icc 1 (N / d), 1 / (d * n : ℕ)) = harmonicMass (N / d) / d := by
      rw [harmonicMass, sum_div]
      exact sum_congr rfl fun n _ => by rw [Nat.cast_mul]; ring
    _ ≤ _ := div_le_div_of_nonneg_right hmono (Nat.cast_nonneg d)

/-- Harmonic second moment has the same reciprocal-mass bound. -/
theorem primeDivisorCount_harmonic_second_moment_le {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (N : ℕ) :
    (∑ n ∈ Icc 1 N, primeDivisorCount P n ^ 2 / (n : ℝ)) ≤
      harmonicMass N * ((∑ p ∈ P, 1 / (p : ℝ)) ^ 2 + ∑ p ∈ P, 1 / (p : ℝ)) := by
  have h := count_moment_le hP N (fun n => 1 / (n : ℝ)) (harmonicMass N)
    (fun n _ => div_nonneg zero_le_one (Nat.cast_nonneg n))
    (fun _ hd => harmonic_divisibility_le N hd)
  simpa only [one_div_mul_eq_div] using h

/-- The literal harmonic mean of the uncentered prime-incidence count. -/
def primeDivisorHarmonicMean (P : Finset ℕ) (N : ℕ) : ℝ :=
  (∑ n ∈ Icc 1 N, primeDivisorCount P n / (n : ℝ)) / harmonicMass N

private theorem primeDivisorCount_nonneg (P : Finset ℕ) (n : ℕ) :
    0 ≤ primeDivisorCount P n :=
  sum_nonneg fun _ _ => by split_ifs <;> norm_num

/-- Harmonic centering uses a mean between zero and the reciprocal-prime mass. -/
theorem primeDivisorHarmonicMean_bounds {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ primeDivisorHarmonicMean P N ∧
      primeDivisorHarmonicMean P N ≤ ∑ p ∈ P, 1 / (p : ℝ) := by
  have hH := harmonicMass_pos hN
  constructor
  · exact div_nonneg (sum_nonneg fun n _ =>
      div_nonneg (primeDivisorCount_nonneg P n) (Nat.cast_nonneg n)) hH.le
  · rw [primeDivisorHarmonicMean, div_le_iff₀ hH]
    simp only [primeDivisorCount, sum_div, ite_div, zero_div]
    rw [sum_comm, sum_mul]
    apply sum_le_sum
    intro p hp
    exact (harmonic_divisibility_le N (hP p hp).pos).trans_eq (by ring)

/-- Harmonic centering preserves a uniform ordinary mean-square bound. -/
theorem centeredPrimeDivisorCount_second_moment_le {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Icc 1 N, (primeDivisorCount P n - primeDivisorHarmonicMean P N) ^ 2) ≤
      (N : ℝ) * (4 * (∑ p ∈ P, 1 / (p : ℝ)) ^ 2 + 2 * ∑ p ∈ P, 1 / (p : ℝ)) := by
  obtain ⟨h0, h1⟩ := primeDivisorHarmonicMean_bounds hP hN
  have hsq : primeDivisorHarmonicMean P N ^ 2 ≤ (∑ p ∈ P, 1 / (p : ℝ)) ^ 2 :=
    pow_le_pow_left₀ h0 h1 2
  calc
    _ ≤ ∑ n ∈ Icc 1 N,
        (2 * primeDivisorCount P n ^ 2 + 2 * (∑ p ∈ P, 1 / (p : ℝ)) ^ 2) := by
      apply sum_le_sum
      intro n _
      nlinarith only [sq_nonneg (primeDivisorCount P n + primeDivisorHarmonicMean P N), hsq]
    _ = 2 * (∑ n ∈ Icc 1 N, primeDivisorCount P n ^ 2) +
        2 * (N : ℝ) * (∑ p ∈ P, 1 / (p : ℝ)) ^ 2 := by
      rw [sum_add_distrib, ← mul_sum]
      simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      ring
    _ ≤ _ := by
      have h := primeDivisorCount_second_moment_le hP N
      linarith only [h]

/-- The centered harmonic square has the same bound with harmonic mass. -/
theorem centeredPrimeDivisorCount_harmonic_second_moment_le {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Icc 1 N,
      (primeDivisorCount P n - primeDivisorHarmonicMean P N) ^ 2 / (n : ℝ)) ≤
      harmonicMass N *
        (4 * (∑ p ∈ P, 1 / (p : ℝ)) ^ 2 + 2 * ∑ p ∈ P, 1 / (p : ℝ)) := by
  obtain ⟨h0, h1⟩ := primeDivisorHarmonicMean_bounds hP hN
  have hsq : primeDivisorHarmonicMean P N ^ 2 ≤ (∑ p ∈ P, 1 / (p : ℝ)) ^ 2 :=
    pow_le_pow_left₀ h0 h1 2
  calc
    _ ≤ ∑ n ∈ Icc 1 N,
        (2 * primeDivisorCount P n ^ 2 + 2 * (∑ p ∈ P, 1 / (p : ℝ)) ^ 2) / n := by
      apply sum_le_sum
      intro n _
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
      nlinarith only [sq_nonneg (primeDivisorCount P n + primeDivisorHarmonicMean P N), hsq]
    _ = 2 * (∑ n ∈ Icc 1 N, primeDivisorCount P n ^ 2 / (n : ℝ)) +
        2 * harmonicMass N * (∑ p ∈ P, 1 / (p : ℝ)) ^ 2 := by
      simp only [add_div, mul_div_assoc, sum_add_distrib, ← mul_sum]
      rw [harmonicMass, sum_mul]
      congr 1
      rw [mul_sum]
      exact sum_congr rfl fun n _ => by ring
    _ ≤ _ := by
      have h := primeDivisorCount_harmonic_second_moment_le hP N
      linarith only [h]

private theorem prime_charge_packet_eq_count (Q : ℕ) (t : ℝ) (n : ℕ) :
    normalizedConductorPacket Q
      (primeOnly (fun p => (t / primePoleScale Q) * primePoleWitness p)) n =
      (t / primePoleScale Q) * (primeDivisorCount ((Icc 1 Q).filter Nat.Prime) n -
        ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) := by
  rw [normalizedConductorPacket_primeOnly, primeDivisorCount,
    ← sum_sub_distrib, mul_sum]
  apply sum_congr rfl
  intro p hp
  rw [mul_assoc, primePoleWitness_mul_mode (mem_filter.mp hp).2]

private theorem prime_charge_harmonicSum (Q N : ℕ) (t : ℝ) :
    harmonicSum N (conductorHorizonProfile Q
      (primeOnly (fun p => (t / primePoleScale Q) * primePoleWitness p))) =
      (t / primePoleScale Q) *
        ((∑ n ∈ Icc 1 N, primeDivisorCount ((Icc 1 Q).filter Nat.Prime) n / (n : ℝ)) -
          (∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) * harmonicMass N) := by
  have hlinear (f : ℕ → ℝ) (s S : ℝ) :
      (∑ n ∈ Icc 1 N, (s * (f n - S)) / (n : ℝ)) =
        s * ((∑ n ∈ Icc 1 N, f n / (n : ℝ)) - S * harmonicMass N) := by
    simp only [harmonicMass, mul_sub, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun n _ => by ring
  simp only [harmonicSum, conductorHorizonProfile, prime_charge_packet_eq_count,
    div_div, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  exact hlinear _ _ _

/-- The actual harmonic-neutral charge packet is centered prime-divisor count. -/
theorem harmonicPrimeCharge_packet_eq_centeredCount {Q N : ℕ}
    (hQ : 1 ≤ Q) (hN : 1 ≤ N) (t : ℝ) (n : ℕ) :
    normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t) n =
      (t / primePoleScale Q) *
        (primeDivisorCount ((Icc 1 Q).filter Nat.Prime) n -
          primeDivisorHarmonicMean ((Icc 1 Q).filter Nat.Prime) N) := by
  rw [harmonicPrimeChargeCoefficients, harmonicCenteredCoefficients,
    normalizedConductorPacket_addConstantConductor hQ, prime_charge_packet_eq_count,
    prime_charge_harmonicSum, primeDivisorHarmonicMean]
  field_simp [(harmonicMass_pos hN).ne']
  ring

/-- Ordinary square bound for the prescribed charge, valid even at the cutoff horizon. -/
theorem harmonicPrimeCharge_ordinary_square_le {Q N : ℕ}
    (hQ : 1 ≤ Q) (hN : 1 ≤ N) (t : ℝ) :
    (∑ n ∈ Icc 1 N,
      normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t) n ^ 2) ≤
      (t / primePoleScale Q) ^ 2 * N *
        (4 * (∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) ^ 2 +
          2 * ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) := by
  simp only [harmonicPrimeCharge_packet_eq_centeredCount hQ hN, mul_pow, ← mul_sum]
  exact (mul_le_mul_of_nonneg_left
    (centeredPrimeDivisorCount_second_moment_le (fun p hp => (mem_filter.mp hp).2) hN)
    (sq_nonneg (t / primePoleScale Q))).trans_eq (by ring)

/-- Harmonic square bound for the same literal projected packet. -/
theorem harmonicPrimeCharge_harmonic_square_le {Q N : ℕ}
    (hQ : 1 ≤ Q) (hN : 1 ≤ N) (t : ℝ) :
    (∑ n ∈ Icc 1 N,
      normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t) n ^ 2 / (n : ℝ)) ≤
      (t / primePoleScale Q) ^ 2 * harmonicMass N *
        (4 * (∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) ^ 2 +
          2 * ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) := by
  simp only [harmonicPrimeCharge_packet_eq_centeredCount hQ hN, mul_pow, mul_div_assoc, ← mul_sum]
  exact (mul_le_mul_of_nonneg_left
    (centeredPrimeDivisorCount_harmonic_second_moment_le
      (fun p hp => (mem_filter.mp hp).2) hN)
    (sq_nonneg (t / primePoleScale Q))).trans_eq (by ring)

#print axioms primeDivisorCount_second_moment_le
#print axioms primeDivisorCount_harmonic_second_moment_le
#print axioms centeredPrimeDivisorCount_second_moment_le
#print axioms harmonicPrimeCharge_ordinary_square_le
#print axioms harmonicPrimeCharge_harmonic_square_le

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
