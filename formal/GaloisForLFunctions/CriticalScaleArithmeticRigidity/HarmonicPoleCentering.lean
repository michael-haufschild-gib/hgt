import GaloisForLFunctions.CriticalScaleArithmeticRigidity.PrimeGeneratorPole
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ThePoleProjectionIsTheEuclideanGroundProjection

/-!
# Harmonic pole removal preserves the arithmetic generator

The actual harmonic pole projection changes only the constant conductor.
Its coefficient correction leaves both adjunction energy and the complete
prime-dilation generator unchanged. Coherent prime inputs therefore have
explicit representatives on every finite-horizon pole hyperplane.
-/

noncomputable section

open Finset
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open RenormalizedArithmeticPotentialTheory BezoutValuationIncidence
  SelectiveMultiscaleArithmeticPositivity

/-- The physical packet profile carries the reciprocal-square-root pole weight. -/
def conductorHorizonProfile (Q : ℕ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  normalizedConductorPacket Q a n / Real.sqrt n

/-- Coefficient realization of the actual harmonic pole projection. -/
def harmonicCenteredCoefficients (Q N : ℕ) (a : ℕ → ℝ) : ℕ → ℝ :=
  addConstantConductor a
    (-(harmonicSum N (conductorHorizonProfile Q a) / harmonicMass N))

private theorem normalizedMode_one (n : ℕ) : normalizedRamanujanMode 1 n = 1 := by
  rw [normalizedRamanujanMode_eq_coefficient (by decide : 0 < (1 : ℕ))]
  have h := ramanujanLagCoefficient_of_dvd (one_dvd n)
  simpa only [Nat.totient_one, Nat.cast_one, Real.sqrt_one, div_one] using h

/-- Adding conductor one adds a literal constant to the normalized arithmetic packet. -/
theorem normalizedConductorPacket_addConstantConductor {Q : ℕ} (hQ : 1 ≤ Q)
    (a : ℕ → ℝ) (t : ℝ) (n : ℕ) :
    normalizedConductorPacket Q (addConstantConductor a t) n =
      normalizedConductorPacket Q a n + t := by
  have h1 : 1 ∈ Icc 1 Q := mem_Icc.mpr ⟨le_rfl, hQ⟩
  have hterm (m : ℕ) : addConstantConductor a t m * normalizedRamanujanMode m n =
      a m * normalizedRamanujanMode m n + if m = 1 then t else 0 := by
    by_cases hm : m = 1
    · subst m
      simp [addConstantConductor, normalizedMode_one]
    · simp only [addConstantConductor, if_neg hm, add_zero]
  simp only [normalizedConductorPacket, hterm, sum_add_distrib, sum_ite_eq', if_pos h1]

/-- The coefficient correction is exactly the prescribed physical pole subtraction. -/
theorem conductorHorizonProfile_harmonicCentered {Q : ℕ} (hQ : 1 ≤ Q)
    (N : ℕ) (a : ℕ → ℝ) (n : ℕ) :
    conductorHorizonProfile Q (harmonicCenteredCoefficients Q N a) n =
      poleProj N (conductorHorizonProfile Q a) n := by
  rw [conductorHorizonProfile, harmonicCenteredCoefficients,
    normalizedConductorPacket_addConstantConductor hQ]
  simp only [poleProj, conductorHorizonProfile]
  ring

/-- The projected arithmetic packet lies on the literal finite-horizon pole hyperplane. -/
theorem harmonicSum_centeredCoefficients {Q N : ℕ} (hQ : 1 ≤ Q) (hN : 1 ≤ N)
    (a : ℕ → ℝ) :
    harmonicSum N (conductorHorizonProfile Q (harmonicCenteredCoefficients Q N a)) = 0 := by
  have heq : conductorHorizonProfile Q (harmonicCenteredCoefficients Q N a) =
      poleProj N (conductorHorizonProfile Q a) :=
    funext (conductorHorizonProfile_harmonicCentered hQ N a)
  rw [heq, harmonicSum_poleProj hN]

/-- Exact harmonic pole removal preserves every arithmetic excitation weight. -/
theorem primeAdjunctionMass_harmonicCentered (Q N : ℕ) (a : ℕ → ℝ) :
    primeAdjunctionMass Q (harmonicCenteredCoefficients Q N a) = primeAdjunctionMass Q a :=
  primeAdjunctionMass_addConstantConductor Q a _

/-- The actual complete prime generator is unchanged by harmonic pole removal. -/
theorem arithmeticPrimeGenerator_harmonicCentered (Q N : ℕ) (a : ℕ → ℝ) (n : ℕ) :
    arithmeticPrimeGenerator Q (harmonicCenteredCoefficients Q N a) n =
      arithmeticPrimeGenerator Q a n :=
  arithmeticPrimeGenerator_addConstantConductor Q a _ n

/-- Every harmonic pole hyperplane contains an explicit coherent prime packet attaining
the sharp constant-row response and retaining exactly its original adjunction mass. -/
theorem exists_harmonic_pole_neutral_prime_coherence {Q N : ℕ}
    (hQ : 2 ≤ Q) (hN : 1 ≤ N) :
    ∃ a : ℕ → ℝ,
      harmonicSum N (conductorHorizonProfile Q a) = 0 ∧
      primeAdjunctionMass Q a = primePoleScale Q ∧
      packetMean Q (arithmeticPrimeGenerator Q a) = primePoleScale Q := by
  refine ⟨harmonicCenteredCoefficients Q N (primeOnly primePoleWitness),
    harmonicSum_centeredCoefficients (by omega : 1 ≤ Q) hN _, ?_, ?_⟩
  · rw [primeAdjunctionMass_harmonicCentered]
    exact (primePoleWitness_response_and_energy Q).2
  · change packetMean Q (fun n => arithmeticPrimeGenerator Q
      (harmonicCenteredCoefficients Q N (primeOnly primePoleWitness)) n) = _
    simp only [arithmeticPrimeGenerator_harmonicCentered]
    rw [packetMean_arithmeticPrimeGenerator_primeOnly]
    exact (primePoleWitness_response_and_energy Q).1

/-- Restricting inputs to the actual harmonic pole hyperplane does not remove the
necessary logarithmic cost in the complete-period generator norm. -/
theorem primePoleScale_le_harmonic_neutral_sector_constant {Q N : ℕ}
    (hQ : 2 ≤ Q) (hN : 1 ≤ N) (C : ℝ)
    (hC : ∀ a : ℕ → ℝ, harmonicSum N (conductorHorizonProfile Q a) = 0 →
      packetMean Q (fun n => arithmeticPrimeGenerator Q a n ^ 2) ≤
        C * primeAdjunctionMass Q a) :
    primePoleScale Q ≤ C := by
  obtain ⟨a, ha, hL, hmean⟩ := exists_harmonic_pole_neutral_prime_coherence hQ hN
  have h := (packetMean_sq_le_mean_sq Q (arithmeticPrimeGenerator Q a)).trans (hC a ha)
  rw [hmean, hL] at h
  by_contra hc
  have hm := mul_lt_mul_of_pos_right (lt_of_not_ge hc) (primePoleScale_pos hQ)
  nlinarith only [h, hm]

#print axioms conductorHorizonProfile_harmonicCentered
#print axioms primeAdjunctionMass_harmonicCentered
#print axioms arithmeticPrimeGenerator_harmonicCentered
#print axioms exists_harmonic_pole_neutral_prime_coherence
#print axioms primePoleScale_le_harmonic_neutral_sector_constant

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
