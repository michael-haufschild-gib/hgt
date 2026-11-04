import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.PrimeIncidenceReceivingCapacity
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.FiniteHorizonPrimeCharge

/-!
# Exact receiving capacity after harmonic pole removal

Prime incidence coordinates identify the finite capacity charge with the
literal arithmetic generator mean. Harmonic centering preserves both that
charge and dilation energy, so the capacity minimizer remains exact on the
neutral hyperplane.
-/

noncomputable section

open Finset
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory SelectiveMultiscaleArithmeticPositivity
open ArithmeticIntersectionTheory

/-- Arbitrary prime incidence coefficients with exact finite-horizon harmonic centering. -/
def harmonicPrimeIncidenceCoefficients (Q N : ℕ) (b : ℕ → ℝ) : ℕ → ℝ :=
  harmonicCenteredCoefficients Q N (primeIncidenceCoefficients b)

/-- Harmonic centering subtracts only a constant from the incidence profile. -/
theorem harmonicPrimeIncidence_packet {Q : ℕ} (hQ : 1 ≤ Q) (N : ℕ)
    (b : ℕ → ℝ) (n : ℕ) :
    normalizedConductorPacket Q (harmonicPrimeIncidenceCoefficients Q N b) n =
      incidencePacket ((Icc 1 Q).filter Nat.Prime) b n -
        harmonicSum N (conductorHorizonProfile Q (primeIncidenceCoefficients b)) / harmonicMass N := by
  rw [harmonicPrimeIncidenceCoefficients, harmonicCenteredCoefficients,
    normalizedConductorPacket_addConstantConductor hQ, primeIncidencePacket_eq,
    sub_eq_add_neg]
  rfl

/-- The harmonic centering coefficient is the literal harmonic mean of the incidence profile. -/
theorem harmonicPrimeIncidence_packet_formula {Q : ℕ} (hQ : 1 ≤ Q) (N : ℕ)
    (b : ℕ → ℝ) (n : ℕ) :
    normalizedConductorPacket Q (harmonicPrimeIncidenceCoefficients Q N b) n =
      incidencePacket ((Icc 1 Q).filter Nat.Prime) b n -
        (∑ j ∈ Icc 1 N, incidencePacket ((Icc 1 Q).filter Nat.Prime) b j / (j : ℝ)) /
          harmonicMass N := by
  rw [harmonicPrimeIncidence_packet hQ]
  congr 2
  apply sum_congr rfl
  intro j _
  change (normalizedConductorPacket Q (primeIncidenceCoefficients b) j / Real.sqrt j) /
      Real.sqrt j = _
  rw [primeIncidencePacket_eq, div_div, Real.mul_self_sqrt (Nat.cast_nonneg j)]
  rfl

/-- The coherent family is the constant-coefficient instance of harmonic incidence coordinates. -/
theorem harmonicPrimeCharge_eq_incidence (Q N : ℕ) (t : ℝ) :
    harmonicPrimeChargeCoefficients Q N t =
      harmonicPrimeIncidenceCoefficients Q N (fun _ => t / primePoleScale Q) := by
  unfold harmonicPrimeChargeCoefficients harmonicPrimeIncidenceCoefficients primeIncidenceCoefficients
  congr 1
  funext p
  unfold primeOnly
  split_ifs <;> ring

/-- The capacity functional is the literal receiving charge of the arithmetic prime generator. -/
theorem harmonicPrimeIncidence_receiving_charge (Q N : ℕ) (b : ℕ → ℝ) :
    packetMean Q (arithmeticPrimeGenerator Q (harmonicPrimeIncidenceCoefficients Q N b)) =
      primeIncidenceReceivingCharge ((Icc 1 Q).filter Nat.Prime) b := by
  change packetMean Q (fun n => arithmeticPrimeGenerator Q
    (harmonicCenteredCoefficients Q N (primeIncidenceCoefficients b)) n) = _
  simp only [arithmeticPrimeGenerator_harmonicCentered]
  rw [primeIncidenceCoefficients, packetMean_arithmeticPrimeGenerator_primeOnly,
    primePoleResponse, primeIncidenceReceivingCharge]
  apply sum_congr rfl
  intro p hp
  have hp' := (mem_filter.mp hp).2
  have hs : Real.sqrt (p.totient : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr hp'.pos)).ne'
  rw [primePoleWitness]
  field_simp [hs]

/-- Every incidence profile admits exact harmonic neutralization at a positive horizon. -/
theorem harmonicPrimeIncidence_neutral {Q N : ℕ} (hQ : 1 ≤ Q) (hN : 1 ≤ N)
    (b : ℕ → ℝ) :
    harmonicSum N (conductorHorizonProfile Q (harmonicPrimeIncidenceCoefficients Q N b)) = 0 :=
  harmonicSum_centeredCoefficients hQ hN _

/-- In incidence coordinates the adjunction weights are exactly the prime Mertens weights. -/
theorem harmonicPrimeIncidence_adjunction (Q N : ℕ) (b : ℕ → ℝ) :
    primeAdjunctionMass Q (harmonicPrimeIncidenceCoefficients Q N b) =
      ∑ p ∈ (Icc 1 Q).filter Nat.Prime, b p ^ 2 * (Real.log p / p) := by
  rw [harmonicPrimeIncidenceCoefficients, primeAdjunctionMass_harmonicCentered,
    primeIncidenceCoefficients, primeAdjunctionMass_primeOnly]
  apply sum_congr rfl
  intro p hp
  have hp' := (mem_filter.mp hp).2
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp'.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have h : (1 : ℝ) < p := by exact_mod_cast hp'.one_lt
    linarith only [h]
  have ht := tameDifferent_prime_pow hp' (by omega : (1 : ℕ) ≠ 0)
  simp only [pow_one] at ht
  rw [ht, primePoleWitness, mul_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg p.totient),
    Nat.totient_prime hp', Nat.cast_sub hp'.one_lt.le, Nat.cast_one]
  field_simp [hp0, hp1]
  ring

/-- Finite sums of incidence coefficients retain a finite-sum adjunction bound. -/
theorem harmonicPrimeIncidence_sum_adjunction_le {ι : Type*}
    (S : Finset ι) (b : ι → ℕ → ℝ) (Q N : ℕ) :
    primeAdjunctionMass Q
      (harmonicPrimeIncidenceCoefficients Q N (fun p => ∑ i ∈ S, b i p)) ≤
      (S.card : ℝ) * ∑ i ∈ S,
        primeAdjunctionMass Q (harmonicPrimeIncidenceCoefficients Q N (b i)) := by
  simp only [harmonicPrimeIncidence_adjunction]
  have hpoint (p : ℕ) : (∑ i ∈ S, b i p) ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, b i p ^ 2 := by
    simpa only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] using
      sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun i => b i p)
  calc
    _ ≤ ∑ p ∈ (Icc 1 Q).filter Nat.Prime,
        ((S.card : ℝ) * ∑ i ∈ S, b i p ^ 2) * (Real.log p / p) :=
      sum_le_sum fun p _ => mul_le_mul_of_nonneg_right (hpoint p)
        (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
    _ = _ := by
      simp only [mul_assoc, sum_mul, ← mul_sum]
      rw [sum_comm]

/-- The full finite cofactor energy survives harmonic pole removal unchanged. -/
theorem harmonicPrimeIncidence_dilation_energy {Q : ℕ} (hQ : 1 ≤ Q)
    (N : ℕ) (b : ℕ → ℝ) :
    jumpEnergy N (normalizedConductorPacket Q (harmonicPrimeIncidenceCoefficients Q N b)) =
      jumpEnergy N (incidencePacket ((Icc 1 Q).filter Nat.Prime) b) := by
  rw [funext (harmonicPrimeIncidence_packet hQ N b), jumpEnergy_sub_const]

/-- The exact finite charge-cost decomposition holds for the actual neutral conductor packet. -/
theorem harmonicPrimeIncidence_energy_charge_decomposition {Q N : ℕ}
    (hQ : 2 ≤ Q) (hQN : Q ≤ N) (b : ℕ → ℝ) :
    jumpEnergy N (normalizedConductorPacket Q (harmonicPrimeIncidenceCoefficients Q N b)) =
      packetMean Q (arithmeticPrimeGenerator Q (harmonicPrimeIncidenceCoefficients Q N b)) ^ 2 /
          primeIncidenceReceivingCapacity ((Icc 1 Q).filter Nat.Prime) N +
      jumpEnergy N (incidencePacket ((Icc 1 Q).filter Nat.Prime) (fun p => b p -
        primeIncidenceCapacityMinimizer ((Icc 1 Q).filter Nat.Prime) N
          (packetMean Q (arithmeticPrimeGenerator Q (harmonicPrimeIncidenceCoefficients Q N b))) p)) := by
  rw [harmonicPrimeIncidence_receiving_charge,
    harmonicPrimeIncidence_dilation_energy (by omega : 1 ≤ Q)]
  exact primeIncidence_energy_charge_decomposition
    ⟨2, mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, hQ⟩, Nat.prime_two⟩⟩
    (fun p hp => (mem_filter.mp hp).2)
    (fun p hp => (mem_Icc.mp (mem_filter.mp hp).1).2.trans hQN) b

/-- A harmonic-neutral packet attains every prescribed charge at its exact finite dilation cost. -/
theorem harmonicPrimeIncidence_capacity_minimizer {Q N : ℕ}
    (hQ : 2 ≤ Q) (hQN : Q ≤ N) (t : ℝ) :
    let b := primeIncidenceCapacityMinimizer ((Icc 1 Q).filter Nat.Prime) N t
    harmonicSum N (conductorHorizonProfile Q (harmonicPrimeIncidenceCoefficients Q N b)) = 0 ∧
    packetMean Q (arithmeticPrimeGenerator Q (harmonicPrimeIncidenceCoefficients Q N b)) = t ∧
    jumpEnergy N (normalizedConductorPacket Q (harmonicPrimeIncidenceCoefficients Q N b)) =
      t ^ 2 / primeIncidenceReceivingCapacity ((Icc 1 Q).filter Nat.Prime) N := by
  have hne : ((Icc 1 Q).filter Nat.Prime).Nonempty :=
    ⟨2, mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, hQ⟩, Nat.prime_two⟩⟩
  have hP : ∀ p ∈ (Icc 1 Q).filter Nat.Prime, p.Prime := fun p hp => (mem_filter.mp hp).2
  have hPN : ∀ p ∈ (Icc 1 Q).filter Nat.Prime, p ≤ N :=
    fun p hp => (mem_Icc.mp (mem_filter.mp hp).1).2.trans hQN
  refine ⟨harmonicPrimeIncidence_neutral (by omega) (by omega) _, ?_, ?_⟩
  · rw [harmonicPrimeIncidence_receiving_charge]
    exact primeIncidenceCapacityMinimizer_charge hne hP hPN t
  · rw [harmonicPrimeIncidence_dilation_energy (by omega : 1 ≤ Q)]
    exact primeIncidenceCapacityMinimizer_energy hne hP hPN t

#print axioms harmonicPrimeIncidence_receiving_charge
#print axioms harmonicPrimeIncidence_energy_charge_decomposition
#print axioms harmonicPrimeIncidence_capacity_minimizer
#print axioms harmonicPrimeIncidence_adjunction
#print axioms harmonicPrimeIncidence_sum_adjunction_le

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
