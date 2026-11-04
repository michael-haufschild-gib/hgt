import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeFibreCoordinates
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CoprimePrimeChargeMoments

/-!
# Simultaneous coherent receiving fibres

Exclude the primes of one common conductor multiple before synthesizing
the fibres. Their receiving coordinates are then exactly prescribed,
including after global harmonic pole removal.
-/

noncomputable section

open Finset
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  SelectiveMultiscaleArithmeticPositivity ArithmeticIntersectionTheory

/-- A positive base conductor places each incidence coefficient at one distinct conductor. -/
theorem primeFibreIncidenceCoefficients_mul {m : ℕ} (hm : 0 < m)
    (P : Finset ℕ) (b : ℕ → ℝ) {p : ℕ} (hp : p ∈ P) :
    primeFibreIncidenceCoefficients P m b (m * p) = b p * primePoleWitness p := by
  unfold primeFibreIncidenceCoefficients
  rw [sum_eq_single p
    (fun q _ hqp => if_neg fun h => hqp (Nat.eq_of_mul_eq_mul_left hm h).symm)
    (fun h => absurd hp h), if_pos rfl]

/-- Every zero-preserving coefficient functional reindexes exactly over one prime fibre. -/
theorem sum_primeFibreIncidenceCoefficients {m R : ℕ} (hm : 0 < m)
    (P : Finset ℕ) (b : ℕ → ℝ) (hP : ∀ p ∈ P, 0 < p ∧ m * p ≤ R)
    (F : ℕ → ℝ → ℝ) (hF : ∀ c, F c 0 = 0) :
    (∑ c ∈ Icc 1 R, F c (primeFibreIncidenceCoefficients P m b c)) =
      ∑ p ∈ P, F (m * p) (b p * primePoleWitness p) := by
  have hsub : P.image (fun p => m * p) ⊆ Icc 1 R := by
    intro c hc
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hc
    exact mem_Icc.mpr ⟨Nat.mul_pos hm (hP p hp).1, (hP p hp).2⟩
  rw [← sum_subset hsub (fun c _ hc => by
      rw [show primeFibreIncidenceCoefficients P m b c = 0 from
        sum_eq_zero (fun p hp => if_neg (fun h => hc (mem_image.mpr ⟨p, hp, h.symm⟩))), hF]),
    sum_image (fun p _ q _ h => Nat.eq_of_mul_eq_mul_left hm h)]
  exact sum_congr rfl fun p hp => by rw [primeFibreIncidenceCoefficients_mul hm P b hp]

/-- A finite prime fibre synthesizes the product of its base mode and incidence packet. -/
theorem primeFibreIncidence_packet {m R : ℕ} (hm : 0 < m)
    (P : Finset ℕ) (b : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime ∧ m.Coprime p ∧ m * p ≤ R) (n : ℕ) :
    normalizedConductorPacket R (primeFibreIncidenceCoefficients P m b) n =
      normalizedRamanujanMode m n * incidencePacket P b n := by
  simp only [normalizedConductorPacket, primeFibreIncidenceCoefficients,
    sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  unfold incidencePacket
  rw [mul_sum]
  apply sum_congr rfl
  intro p hp
  have hmp : m * p ∈ Icc 1 R :=
    mem_Icc.mpr ⟨Nat.mul_pos hm (hP p hp).1.pos, (hP p hp).2.2⟩
  rw [sum_ite_eq', if_pos hmp,
    normalizedRamanujanMode_mul_of_coprime hm (hP p hp).1.pos (hP p hp).2.1]
  calc
    _ = normalizedRamanujanMode m n * (b p *
        (primePoleWitness p * normalizedRamanujanMode p n)) := by ring
    _ = _ := by rw [primePoleWitness_mul_mode (hP p hp).1]

/-- Several prescribed fibres with one common prime exclusion and one global harmonic centering. -/
def commonPrimeFibreCoefficients (S : Finset ℕ) (M Q N : ℕ) (t : ℕ → ℝ) : ℕ → ℝ :=
  harmonicCenteredCoefficients (M * Q) N
    (fun c => ∑ m ∈ S, primeFibreIncidenceCoefficients (fibrePrimes M Q) m
      (fun _ => t m / fibreScale M Q) c)

/-- The uncentered profile of the prescribed finite receiving vector. -/
def commonPrimeFibreProfile (S : Finset ℕ) (M Q : ℕ) (t : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ m ∈ S, normalizedRamanujanMode m n *
    incidencePacket (fibrePrimes M Q) (fun _ => t m / fibreScale M Q) n

/-- The uncentered common packet is the literal sum of mode-weighted prime incidences. -/
theorem commonPrimeFibre_uncentered_packet {M : ℕ} (hM : 0 < M)
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m ∧ m ∣ M)
    (Q : ℕ) (t : ℕ → ℝ) (n : ℕ) :
    normalizedConductorPacket (M * Q)
        (fun c => ∑ m ∈ S, primeFibreIncidenceCoefficients (fibrePrimes M Q) m
          (fun _ => t m / fibreScale M Q) c) n =
      ∑ m ∈ S, normalizedRamanujanMode m n *
        incidencePacket (fibrePrimes M Q) (fun _ => t m / fibreScale M Q) n := by
  have hsum : normalizedConductorPacket (M * Q)
      (fun c => ∑ m ∈ S, primeFibreIncidenceCoefficients (fibrePrimes M Q) m
        (fun _ => t m / fibreScale M Q) c) n =
      ∑ m ∈ S, normalizedConductorPacket (M * Q)
        (primeFibreIncidenceCoefficients (fibrePrimes M Q) m
          (fun _ => t m / fibreScale M Q)) n := by
    simp only [normalizedConductorPacket, sum_mul]
    rw [sum_comm]
  rw [hsum]
  apply sum_congr rfl
  intro m hm
  apply primeFibreIncidence_packet (hS m hm).1
  intro p hp
  obtain ⟨hpQ, hpP, hpM⟩ := mem_fibrePrimes.mp hp
  have hmp : m.Coprime p := Nat.coprime_comm.mp
    (hpP.coprime_iff_not_dvd.mpr (fun h => hpM (h.trans (hS m hm).2)))
  exact ⟨hpP, hmp, Nat.mul_le_mul (Nat.le_of_dvd hM (hS m hm).2) (mem_Icc.mp hpQ).2⟩

/-- Common prime exclusion makes the entire finite receiving vector exact. -/
theorem commonPrimeFibre_receiving_coordinates {M l Q : ℕ}
    (hM : 0 < M) (hl : 0 < l) (hlM : l ∣ M)
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m ∧ m ∣ M)
    (N : ℕ) (t : ℕ → ℝ) (hB : 0 < fibreScale M Q) :
    packetMean (M * Q) (fun n =>
      arithmeticPrimeGenerator (M * Q) (commonPrimeFibreCoefficients S M Q N t) n *
        normalizedRamanujanMode l n) = if l ∈ S then t l else 0 := by
  let b (m : ℕ) := primeFibreIncidenceCoefficients (fibrePrimes M Q) m
    (fun _ => t m / fibreScale M Q)
  have hpoint (n : ℕ) : arithmeticPrimeGenerator (M * Q) (fun c => ∑ m ∈ S, b m c) n *
      normalizedRamanujanMode l n =
      ∑ m ∈ S, arithmeticPrimeGenerator (M * Q) (b m) n * normalizedRamanujanMode l n := by
    simp only [arithmeticPrimeGenerator_eq_modeSource, sum_mul]
    rw [sum_comm]
  have hsingle (m : ℕ) (hm : m ∈ S) :
      packetMean (M * Q) (fun n => arithmeticPrimeGenerator (M * Q) (b m) n *
        normalizedRamanujanMode l n) = (if m = l then 1 else 0) * t m := by
    have hP : ∀ p ∈ fibrePrimes M Q, p.Prime ∧ ¬ p ∣ M ∧ M * p ≤ M * Q := by
      intro p hp
      obtain ⟨hpQ, hpP, hpM⟩ := mem_fibrePrimes.mp hp
      exact ⟨hpP, hpM, Nat.mul_le_mul_left M (mem_Icc.mp hpQ).2⟩
    rw [primeFibreIncidence_receiving_coordinates hM (hS m hm).1 hl (hS m hm).2 hlM
      (fibrePrimes M Q) (fun _ => t m / fibreScale M Q) hP, ← mul_sum]
    change _ * (t m / fibreScale M Q * fibreScale M Q) = _
    rw [div_mul_cancel₀ _ hB.ne']
  simp only [commonPrimeFibreCoefficients, arithmeticPrimeGenerator_harmonicCentered]
  change packetMean (M * Q) (fun n => arithmeticPrimeGenerator (M * Q)
    (fun c => ∑ m ∈ S, b m c) n * normalizedRamanujanMode l n) = _
  rw [show (fun n => arithmeticPrimeGenerator (M * Q) (fun c => ∑ m ∈ S, b m c) n *
    normalizedRamanujanMode l n) = (fun n => ∑ m ∈ S,
      arithmeticPrimeGenerator (M * Q) (b m) n * normalizedRamanujanMode l n) from funext hpoint,
    packetMean_sum]
  rw [sum_congr rfl hsingle]
  simp only [ite_mul, one_mul, zero_mul, sum_ite_eq']

/-- Global pole removal is exact for the same simultaneous receiving coefficients. -/
theorem commonPrimeFibre_neutral {M Q N : ℕ}
    (hM : 0 < M) (hQ : 1 ≤ Q) (hN : 1 ≤ N) (S : Finset ℕ) (t : ℕ → ℝ) :
    harmonicSum N (conductorHorizonProfile (M * Q)
      (commonPrimeFibreCoefficients S M Q N t)) = 0 :=
  harmonicSum_centeredCoefficients (Nat.mul_pos hM hQ) hN _

/-- The centered profile subtracts its exact finite harmonic mean. -/
theorem commonPrimeFibre_packet_formula {M Q : ℕ} (hM : 0 < M) (hQ : 1 ≤ Q)
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m ∧ m ∣ M)
    (N : ℕ) (t : ℕ → ℝ) (n : ℕ) :
    normalizedConductorPacket (M * Q) (commonPrimeFibreCoefficients S M Q N t) n =
      commonPrimeFibreProfile S M Q t n -
        (∑ j ∈ Icc 1 N, commonPrimeFibreProfile S M Q t j / (j : ℝ)) / harmonicMass N := by
  rw [commonPrimeFibreCoefficients, harmonicCenteredCoefficients,
    normalizedConductorPacket_addConstantConductor (Nat.mul_pos hM hQ)]
  simp only [SelectiveMultiscaleArithmeticPositivity.harmonicSum, conductorHorizonProfile,
    commonPrimeFibre_uncentered_packet hM S hS, div_div,
    Real.mul_self_sqrt (Nat.cast_nonneg _)]
  rfl

#print axioms primeFibreIncidence_packet
#print axioms sum_primeFibreIncidenceCoefficients
#print axioms commonPrimeFibre_uncentered_packet
#print axioms commonPrimeFibre_receiving_coordinates
#print axioms commonPrimeFibre_neutral
#print axioms commonPrimeFibre_packet_formula

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
