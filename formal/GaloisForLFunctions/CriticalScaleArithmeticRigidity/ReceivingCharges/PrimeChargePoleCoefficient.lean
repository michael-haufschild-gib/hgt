import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeBoundaryCorrection

/-!
# The pole coefficient of a neutral coherent charge

Harmonic centering adds a conductor-one coefficient of size `t/H_N`.
Its harmonic mass recovers the receiving charge, with error at most
`8 |t| Q/(N B_Q)`, uniformly for every horizon above the prime cutoff.
-/

noncomputable section

open Finset
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory SelectiveMultiscaleArithmeticPositivity

private theorem harmonic_incidence_mean {p : ℕ} (hp : 0 < p) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ((if p ∣ n then (1 : ℝ) else 0) - 1 / p) / n) =
      (harmonicMass (N / p) - harmonicMass N) / p := by
  simp only [sub_div, sum_sub_distrib, ite_div, zero_div]
  rw [← sum_filter, _root_.RHTower.Sieve.sum_filter_dvd_eq_sum_scaled hp]
  have hscaled : (∑ n ∈ Icc 1 (N / p), 1 / ((p * n : ℕ) : ℝ)) =
      harmonicMass (N / p) / p := by
    rw [harmonicMass, sum_div]
    exact sum_congr rfl fun n _ => by rw [Nat.cast_mul]; ring
  have hconstant : (∑ n ∈ Icc 1 N, 1 / (p : ℝ) / n) = harmonicMass N / p := by
    rw [harmonicMass, sum_div]
    exact sum_congr rfl fun n _ => by ring
  rw [hscaled, hconstant]

private theorem coherent_harmonic_mean (Q N : ℕ) (t : ℝ) :
    harmonicSum N (conductorHorizonProfile Q
      (primeOnly (fun p => (t / primePoleScale Q) * primePoleWitness p))) =
      (t / primePoleScale Q) *
        ∑ p ∈ (Icc 1 Q).filter Nat.Prime,
          (harmonicMass (N / p) - harmonicMass N) / p := by
  simp only [harmonicSum, conductorHorizonProfile, normalizedConductorPacket_primeOnly,
    div_div, Real.mul_self_sqrt (Nat.cast_nonneg _), sum_div]
  rw [sum_comm, mul_sum]
  apply sum_congr rfl
  intro p hp
  have hprime := (mem_filter.mp hp).2
  simp only [mul_assoc, primePoleWitness_mul_mode hprime, mul_div_assoc, ← mul_sum]
  rw [harmonic_incidence_mean hprime.pos]

/-- The centering coefficient is the exact harmonic loss over prime divisibility classes. -/
theorem harmonicPrimeCharge_pole_coefficient {N : ℕ} (hN : 1 ≤ N)
    (Q : ℕ) (t : ℝ) :
    harmonicMass N * harmonicPrimeChargeCoefficients Q N t 1 =
      (t / primePoleScale Q) *
        ∑ p ∈ (Icc 1 Q).filter Nat.Prime,
          (harmonicMass N - harmonicMass (N / p)) / p := by
  have hH := (harmonicMass_pos hN).ne'
  simp only [harmonicPrimeChargeCoefficients, harmonicCenteredCoefficients,
    addConstantConductor, primeOnly, Nat.not_prime_one, if_false, zero_add, ite_true]
  rw [coherent_harmonic_mean]
  have hneg : (∑ p ∈ (Icc 1 Q).filter Nat.Prime,
      (harmonicMass N - harmonicMass (N / p)) / p) =
      -(∑ p ∈ (Icc 1 Q).filter Nat.Prime,
        (harmonicMass (N / p) - harmonicMass N) / p) := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun p _ => by ring
  rw [hneg]
  field_simp [hH]

private theorem harmonic_loss_error {N p : ℕ} (hp : 1 ≤ p) (hpN : p ≤ N) :
    |((harmonicMass N - harmonicMass (N / p)) - Real.log p) / p| ≤ 8 / N := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le hpR
  have hNR : (0 : ℝ) < N := by exact_mod_cast hp.trans hpN
  have hN := _root_.RHTower.RegularizedDivisorHarmonic.abs_harmonic_sub_log_div_le
    (by omega : 1 ≤ (1 : ℕ)) (hp.trans hpN)
  have hP := _root_.RHTower.RegularizedDivisorHarmonic.abs_harmonic_sub_log_div_le hp hpN
  have hcast (n : ℕ) : (harmonic n : ℝ) = harmonicMass n := by
    simpa only [harmonicMass, one_div] using
      _root_.RHTower.RegularizedDivisorHarmonic.harmonic_cast_eq_sum n
  simp only [Nat.div_one, Nat.cast_one, div_one, mul_one, hcast] at hN
  rw [hcast, Real.log_div hNR.ne' hp0.ne'] at hP
  have heq : (harmonicMass N - harmonicMass (N / p)) - Real.log p =
      (harmonicMass N - Real.log N - Real.eulerMascheroniConstant) -
        (harmonicMass (N / p) - (Real.log N - Real.log p) -
          Real.eulerMascheroniConstant) := by ring
  rw [abs_div, abs_of_pos hp0, heq]
  refine (div_le_div_of_nonneg_right ((abs_sub _ _).trans (add_le_add hN hP)) hp0.le).trans ?_
  rw [div_le_iff₀ hp0]
  have h : 4 / (N : ℝ) ≤ 4 * p / N :=
    div_le_div_of_nonneg_right (by linarith only [hpR]) hNR.le
  calc
    4 / (N : ℝ) + 4 * p / N ≤ 4 * p / N + 4 * p / N := add_le_add h le_rfl
    _ = 8 / (N : ℝ) * p := by ring

/-- The harmonic pole coefficient retains the exact receiving charge up to a uniform finite-horizon error. -/
theorem harmonicPrimeCharge_pole_error_le {Q N : ℕ}
    (hQ : 2 ≤ Q) (hQN : Q ≤ N) (t : ℝ) :
    |harmonicMass N * harmonicPrimeChargeCoefficients Q N t 1 - t| ≤
      8 * |t| * Q / ((N : ℝ) * primePoleScale Q) := by
  have hN : 1 ≤ N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hB := primePoleScale_pos hQ
  rw [harmonicPrimeCharge_pole_coefficient hN]
  have herror : (t / primePoleScale Q) *
      (∑ p ∈ (Icc 1 Q).filter Nat.Prime, (harmonicMass N - harmonicMass (N / p)) / p) - t =
      (t / primePoleScale Q) *
        ∑ p ∈ (Icc 1 Q).filter Nat.Prime,
          ((harmonicMass N - harmonicMass (N / p)) - Real.log p) / p := by
    simp only [sub_div, sum_sub_distrib]
    change _ = (t / primePoleScale Q) * (_ - primePoleScale Q)
    field_simp [hB.ne']
  have hsum : (∑ p ∈ (Icc 1 Q).filter Nat.Prime,
      |((harmonicMass N - harmonicMass (N / p)) - Real.log p) / p|) ≤
      (Q : ℝ) * (8 / N) := by
    calc
      _ ≤ ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 8 / (N : ℝ) :=
        sum_le_sum fun p hp => harmonic_loss_error (mem_Icc.mp (mem_filter.mp hp).1).1
          ((mem_Icc.mp (mem_filter.mp hp).1).2.trans hQN)
      _ ≤ ∑ p ∈ Icc 1 Q, 8 / (N : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun _ _ _ => by positivity)
      _ = _ := by simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  rw [herror, abs_mul, abs_div, abs_of_pos hB]
  exact (mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans hsum)
    (by positivity : 0 ≤ |t| / primePoleScale Q)).trans_eq (by ring)

/-- The error is independent of the horizon once it lies above the prime cutoff. -/
theorem harmonicPrimeCharge_pole_error_uniform {Q N : ℕ}
    (hQ : 2 ≤ Q) (hQN : Q ≤ N) (t : ℝ) :
    |harmonicMass N * harmonicPrimeChargeCoefficients Q N t 1 - t| ≤
      8 * |t| / primePoleScale Q := by
  refine (harmonicPrimeCharge_pole_error_le hQ hQN t).trans ?_
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hQR : (Q : ℝ) ≤ N := by exact_mod_cast hQN
  have hB := primePoleScale_pos hQ
  rw [div_le_div_iff₀ (mul_pos hNR hB) hB]
  have h := mul_le_mul_of_nonneg_left hQR (by positivity : 0 ≤ 8 * |t| * primePoleScale Q)
  nlinarith only [h]

#print axioms harmonicPrimeCharge_pole_coefficient
#print axioms harmonicPrimeCharge_pole_error_le
#print axioms harmonicPrimeCharge_pole_error_uniform

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
