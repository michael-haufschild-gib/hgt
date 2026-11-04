import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CommonPrimeFibreRestriction
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.FixedPacketCriticalCancellation
import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.CompleteFormLinearAlgebra

/-!
# Exact physical centering of common receiving fibres

Finite harmonic centering is linear. The common-prime restriction therefore
splits into the original neutral fibre and one fixed neutral conductor packet,
before applying the complete operator.
-/

noncomputable section

open Finset
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  SelectiveMultiscaleArithmeticPositivity

/-- Physical packet after subtraction of its exact finite harmonic mean. -/
def harmonicCenteredPacketVector (N : ℕ) (F : ℕ → ℝ) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  (Real.sqrt (Real.log N))⁻¹ • packetVector
    (fun n => F n - (∑ j ∈ Icc 1 N, F j / (j : ℝ)) / harmonicMass N) N

/-- Coefficient and profile realizations of harmonic centering are identical. -/
theorem harmonicCenteredPacketVector_conductor {Q : ℕ} (hQ : 1 ≤ Q)
    (N : ℕ) (a : ℕ → ℝ) :
    harmonicCenteredPacketVector N (normalizedConductorPacket Q a) =
      (Real.sqrt (Real.log N))⁻¹ • packetVector
        (normalizedConductorPacket Q (harmonicCenteredCoefficients Q N a)) N := by
  unfold harmonicCenteredPacketVector
  congr 2
  funext n
  rw [harmonicCenteredCoefficients, normalizedConductorPacket_addConstantConductor hQ]
  simp only [SelectiveMultiscaleArithmeticPositivity.harmonicSum, conductorHorizonProfile,
    div_div, Real.mul_self_sqrt (Nat.cast_nonneg _), sub_eq_add_neg]

/-- Harmonic centering commutes with scalar multiplication, including at degenerate horizons. -/
theorem harmonicCenteredPacketVector_smul (N : ℕ) (s : ℝ) (F : ℕ → ℝ) :
    harmonicCenteredPacketVector N (fun n => s * F n) = s • harmonicCenteredPacketVector N F := by
  have hpoint (n : ℕ) : s * F n -
      (∑ j ∈ Icc 1 N, s * F j / (j : ℝ)) / harmonicMass N =
      s * (F n - (∑ j ∈ Icc 1 N, F j / (j : ℝ)) / harmonicMass N) := by
    simp only [mul_div_assoc, ← mul_sum]
    ring
  simp only [harmonicCenteredPacketVector, hpoint, packetVector_const_mul, smul_smul]
  rw [mul_comm]

/-- Harmonic centering commutes with subtraction. -/
theorem harmonicCenteredPacketVector_sub (N : ℕ) (F G : ℕ → ℝ) :
    harmonicCenteredPacketVector N (fun n => F n - G n) =
      harmonicCenteredPacketVector N F - harmonicCenteredPacketVector N G := by
  have hpacket (F G : ℕ → ℝ) : packetVector (fun n => F n - G n) N =
      packetVector F N - packetVector G N := by
    ext n
    change (F n - G n) / Real.sqrt (n : ℕ) =
      F n / Real.sqrt (n : ℕ) - G n / Real.sqrt (n : ℕ)
    exact sub_div _ _ _
  have hpoint (n : ℕ) : (F n - G n) -
      (∑ j ∈ Icc 1 N, (F j - G j) / (j : ℝ)) / harmonicMass N =
      (F n - (∑ j ∈ Icc 1 N, F j / (j : ℝ)) / harmonicMass N) -
        (G n - (∑ j ∈ Icc 1 N, G j / (j : ℝ)) / harmonicMass N) := by
    simp only [sub_div, sum_sub_distrib]
    ring
  simp only [harmonicCenteredPacketVector, hpoint, hpacket, smul_sub]

/-- Harmonic centering commutes with every finite sum. -/
theorem harmonicCenteredPacketVector_sum {ι : Type*} (S : Finset ι)
    (N : ℕ) (F : ι → ℕ → ℝ) :
    harmonicCenteredPacketVector N (fun n => ∑ i ∈ S, F i n) =
      ∑ i ∈ S, harmonicCenteredPacketVector N (F i) := by
  have hmean : (∑ j ∈ Icc 1 N, (∑ i ∈ S, F i j) / (j : ℝ)) / harmonicMass N =
      ∑ i ∈ S, (∑ j ∈ Icc 1 N, F i j / (j : ℝ)) / harmonicMass N := by
    simp only [div_eq_mul_inv, sum_mul]
    rw [sum_comm]
  simp only [harmonicCenteredPacketVector, hmean, ← sum_sub_distrib,
    packetVector_finset_sum, smul_sum]

/-- Exact physical common-exclusion fibre with its prescribed scalar charge. -/
def commonPrimeFibreChargeVector (m M Q N : ℕ) (t : ℝ) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  harmonicCenteredPacketVector N (fun n => normalizedRamanujanMode m n *
    incidencePacket (fibrePrimes M Q) (fun _ => t / fibreScale M Q) n)

/-- The standard coprime charge vector is its literal centered mode-incidence profile. -/
theorem harmonicFibreChargeVector_eq_centered {m Q : ℕ} (hm : 0 < m)
    (hQ : 1 ≤ Q) (N : ℕ) (t : ℝ) :
    harmonicFibreChargeVector m Q N t =
      harmonicCenteredPacketVector N (fun n => normalizedRamanujanMode m n *
        incidencePacket (fibrePrimes m Q) (fun _ => t / fibreScale m Q) n) := by
  rw [harmonicFibreChargeVector, harmonicFibreChargeCoefficients,
    ← harmonicCenteredPacketVector_conductor (Nat.mul_pos hm hQ)]
  congr 1
  funext n
  exact normalizedConductorPacket_fibreCharge_incidence hm Q t n

/-- The additional prime packet is synthesized on a fixed finite conductor block. -/
theorem additionalFibre_packet {m M : ℕ} (hm : 0 < m) :
    normalizedConductorPacket (m * M)
        (primeFibreIncidenceCoefficients (additionalFibrePrimes m M) m (fun _ => 1)) =
      fun n => normalizedRamanujanMode m n *
        incidencePacket (additionalFibrePrimes m M) (fun _ => 1) n := by
  funext n
  apply primeFibreIncidence_packet hm
  intro p hp
  obtain ⟨hp, _⟩ := mem_filter.mp hp
  obtain ⟨hpI, hpP, hpm⟩ := mem_fibrePrimes.mp hp
  exact ⟨hpP, Nat.coprime_comm.mp (hpP.coprime_iff_not_dvd.mpr hpm),
    Nat.mul_le_mul_left m (mem_Icc.mp hpI).2⟩

/-- The physical common fibre is the original neutral fibre minus a fixed finite correction. -/
theorem commonPrimeFibreChargeVector_eq {m M Q : ℕ} (hm : 0 < m)
    (hM : 0 < M) (hmM : m ∣ M) (hMQ : M ≤ Q) (hBm : 0 < fibreScale m Q)
    (N : ℕ) (t : ℝ) :
    commonPrimeFibreChargeVector m M Q N t =
      (fibreScale m Q / fibreScale M Q) • harmonicFibreChargeVector m Q N t -
        (t / fibreScale M Q) • harmonicCenteredPacketVector N
          (normalizedConductorPacket (m * M)
            (primeFibreIncidenceCoefficients (additionalFibrePrimes m M) m (fun _ => 1))) := by
  rw [commonPrimeFibreChargeVector, additionalFibre_packet hm,
    harmonicFibreChargeVector_eq_centered hm (hM.trans_le hMQ)]
  have hpoint (n : ℕ) : normalizedRamanujanMode m n *
      incidencePacket (fibrePrimes M Q) (fun _ => t / fibreScale M Q) n =
      (fibreScale m Q / fibreScale M Q) *
        (normalizedRamanujanMode m n * incidencePacket (fibrePrimes m Q)
          (fun _ => t / fibreScale m Q) n) -
        (t / fibreScale M Q) * (normalizedRamanujanMode m n *
          incidencePacket (additionalFibrePrimes m M) (fun _ => 1) n) := by
    rw [incidencePacket_common_charge hM hmM hMQ hBm]
    ring
  simp only [hpoint, harmonicCenteredPacketVector_sub, harmonicCenteredPacketVector_smul]

#print axioms harmonicCenteredPacketVector_sum
#print axioms commonPrimeFibreChargeVector_eq

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
