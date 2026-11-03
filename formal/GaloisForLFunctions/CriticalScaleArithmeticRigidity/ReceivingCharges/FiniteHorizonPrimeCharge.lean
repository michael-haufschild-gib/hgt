import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.PrimeIncidenceDilationEnergy
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.VanishingEnergyCharge

/-!
# The finite-horizon dilation energy of a prescribed prime charge

Harmonic projection preserves both the receiving charge and every dilation
jump. The projected coherent family therefore has an exact horizon-dependent
dilation energy, distinct from its adjunction mass `t²/B_Q`.
-/

noncomputable section

open Finset
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory SelectiveMultiscaleArithmeticPositivity

/-- Coherent prime coefficients with literal harmonic pole subtraction. -/
def harmonicPrimeChargeCoefficients (Q N : ℕ) (t : ℝ) : ℕ → ℝ :=
  harmonicCenteredCoefficients Q N
    (primeOnly (fun p => (t / primePoleScale Q) * primePoleWitness p))

private theorem normalized_prime_charge_packet (Q : ℕ) (t : ℝ) (n : ℕ) :
    normalizedConductorPacket Q
        (primeOnly (fun p => (t / primePoleScale Q) * primePoleWitness p)) n =
      incidencePacket ((Icc 1 Q).filter Nat.Prime) (fun _ => t / primePoleScale Q) n := by
  rw [normalizedConductorPacket_primeOnly, incidencePacket]
  apply sum_congr rfl
  intro p hp
  rw [mul_assoc, primePoleWitness_mul_mode (mem_filter.mp hp).2]

/-- The harmonic correction subtracts exactly the finite-horizon mean. -/
theorem harmonicPrimeCharge_packet {Q : ℕ} (hQ : 1 ≤ Q) (N : ℕ) (t : ℝ) (n : ℕ) :
    normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t) n =
      incidencePacket ((Icc 1 Q).filter Nat.Prime) (fun _ => t / primePoleScale Q) n -
        harmonicSum N (conductorHorizonProfile Q
          (primeOnly (fun p => (t / primePoleScale Q) * primePoleWitness p))) / harmonicMass N := by
  rw [harmonicPrimeChargeCoefficients, harmonicCenteredCoefficients,
    normalizedConductorPacket_addConstantConductor hQ, normalized_prime_charge_packet,
    sub_eq_add_neg]

/-- The full finite-horizon dilation energy retains the cofactor harmonic masses. -/
theorem harmonicPrimeCharge_jumpEnergy {Q : ℕ} (hQ : 1 ≤ Q) (N : ℕ) (t : ℝ) :
    jumpEnergy N (normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t)) =
      (t / primePoleScale Q) ^ 2 *
        ∑ p ∈ (Icc 1 Q).filter Nat.Prime, Real.log p / p * harmonicMass (N / p) := by
  have hfun := funext (harmonicPrimeCharge_packet hQ N t)
  rw [hfun, jumpEnergy_sub_const,
    jumpEnergy_incidencePacket_diagonal (fun p hp => (mem_filter.mp hp).2), mul_sum]
  rfl

/-- The projected family retains its exact charge and adjunction mass at every horizon. -/
theorem harmonicPrimeCharge_charge_and_adjunction {Q N : ℕ}
    (hQ : 2 ≤ Q) (hN : 1 ≤ N) (t : ℝ) :
    harmonicSum N (conductorHorizonProfile Q (harmonicPrimeChargeCoefficients Q N t)) = 0 ∧
      packetMean Q (arithmeticPrimeGenerator Q (harmonicPrimeChargeCoefficients Q N t)) = t ∧
      primeAdjunctionMass Q (harmonicPrimeChargeCoefficients Q N t) = t ^ 2 / primePoleScale Q := by
  obtain ⟨hcharge, hmass⟩ := normalizedPrimeCharge_response_and_energy hQ t
  refine ⟨harmonicSum_centeredCoefficients (by omega : 1 ≤ Q) hN _, ?_, ?_⟩
  · change packetMean Q (fun n => arithmeticPrimeGenerator Q
      (harmonicCenteredCoefficients Q N
        (primeOnly (fun p => (t / primePoleScale Q) * primePoleWitness p))) n) = t
    simp only [arithmeticPrimeGenerator_harmonicCentered]
    rw [packetMean_arithmeticPrimeGenerator_primeOnly]
    exact hcharge
  · rw [harmonicPrimeChargeCoefficients, primeAdjunctionMass_harmonicCentered]
    exact hmass

#print axioms harmonicPrimeCharge_jumpEnergy
#print axioms harmonicPrimeCharge_charge_and_adjunction

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
