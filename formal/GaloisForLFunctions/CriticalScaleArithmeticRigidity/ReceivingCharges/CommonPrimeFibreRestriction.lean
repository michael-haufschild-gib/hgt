import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CommonPrimeFibrePackets

/-!
# A common prime exclusion differs by finitely many conductors

For a base mode dividing a common conductor multiple, the primes removed
from its own coprime fibre are exactly the additional prime divisors of
that multiple. The coherent profiles differ by this fixed finite packet
and the ratio of their prime Mertens masses.
-/

noncomputable section

open Finset
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory

/-- The finitely many extra primes excluded by a common conductor multiple. -/
def additionalFibrePrimes (m M : ℕ) : Finset ℕ :=
  (fibrePrimes m M).filter (fun p => p ∣ M)

/-- A common exclusion only removes primes from each constituent fibre. -/
theorem fibrePrimes_common_subset {m M Q : ℕ} (hmM : m ∣ M) :
    fibrePrimes M Q ⊆ fibrePrimes m Q := by
  intro p hp
  obtain ⟨hpQ, hpP, hpM⟩ := mem_fibrePrimes.mp hp
  exact mem_fibrePrimes.mpr ⟨hpQ, hpP, fun h => hpM (h.trans hmM)⟩

/-- Above the common multiple, the prime-set difference is independent of the cutoff. -/
theorem fibrePrimes_common_difference {m M Q : ℕ} (hM : 0 < M) (hMQ : M ≤ Q) :
    fibrePrimes m Q \ fibrePrimes M Q = additionalFibrePrimes m M := by
  ext p
  constructor
  · intro hp
    obtain ⟨hp, hnot⟩ := mem_sdiff.mp hp
    obtain ⟨hpQ, hpP, hpm⟩ := mem_fibrePrimes.mp hp
    have hpM : p ∣ M := by
      by_contra h
      exact hnot (mem_fibrePrimes.mpr ⟨hpQ, hpP, h⟩)
    exact mem_filter.mpr ⟨mem_fibrePrimes.mpr
      ⟨mem_Icc.mpr ⟨hpP.pos, Nat.le_of_dvd hM hpM⟩, hpP, hpm⟩, hpM⟩
  · intro hp
    obtain ⟨hp, hpM⟩ := mem_filter.mp hp
    obtain ⟨hpI, hpP, hpm⟩ := mem_fibrePrimes.mp hp
    exact mem_sdiff.mpr ⟨mem_fibrePrimes.mpr
      ⟨mem_Icc.mpr ⟨(mem_Icc.mp hpI).1, (mem_Icc.mp hpI).2.trans hMQ⟩, hpP, hpm⟩,
      fun h => (mem_fibrePrimes.mp h).2.2 hpM⟩

/-- Every prime sum splits exactly into the common fibre and its fixed finite deletion. -/
theorem sum_fibrePrimes_common {m M Q : ℕ} (hM : 0 < M) (hmM : m ∣ M)
    (hMQ : M ≤ Q) (f : ℕ → ℝ) :
    (∑ p ∈ fibrePrimes m Q, f p) =
      (∑ p ∈ fibrePrimes M Q, f p) + ∑ p ∈ additionalFibrePrimes m M, f p := by
  have h := sum_sdiff (f := f) (fibrePrimes_common_subset (Q := Q) hmM)
  rw [fibrePrimes_common_difference hM hMQ] at h
  linarith only [h]

/-- The two prime Mertens masses differ by a fixed finite prime sum. -/
theorem fibreScale_common_difference {m M Q : ℕ} (hM : 0 < M) (hmM : m ∣ M)
    (hMQ : M ≤ Q) :
    fibreScale m Q = fibreScale M Q +
      ∑ p ∈ additionalFibrePrimes m M, Real.log p / p :=
  sum_fibrePrimes_common hM hmM hMQ (fun p => Real.log p / p)

/-- Common exclusion changes a unit incidence profile by exactly its finite deleted prime packet. -/
theorem incidencePacket_common_difference {m M Q : ℕ} (hM : 0 < M) (hmM : m ∣ M)
    (hMQ : M ≤ Q) (n : ℕ) :
    incidencePacket (fibrePrimes m Q) (fun _ => 1) n =
      incidencePacket (fibrePrimes M Q) (fun _ => 1) n +
        incidencePacket (additionalFibrePrimes m M) (fun _ => 1) n := by
  exact sum_fibrePrimes_common hM hmM hMQ _

/-- Scalar coherent profiles retain the exact common-exclusion correction. -/
theorem incidencePacket_common_charge {m M Q : ℕ} (hM : 0 < M) (hmM : m ∣ M)
    (hMQ : M ≤ Q) (hBm : 0 < fibreScale m Q) (t : ℝ) (n : ℕ) :
    incidencePacket (fibrePrimes M Q) (fun _ => t / fibreScale M Q) n =
      (fibreScale m Q / fibreScale M Q) *
        incidencePacket (fibrePrimes m Q) (fun _ => t / fibreScale m Q) n -
      (t / fibreScale M Q) * incidencePacket (additionalFibrePrimes m M) (fun _ => 1) n := by
  have hscale (P : Finset ℕ) (s : ℝ) :
      incidencePacket P (fun _ => s) n = s * incidencePacket P (fun _ => 1) n := by
    simp only [incidencePacket, one_mul, mul_sum]
  rw [hscale, hscale, incidencePacket_common_difference hM hmM hMQ]
  have he : (fibreScale m Q / fibreScale M Q) * (t / fibreScale m Q) =
      t / fibreScale M Q := by
    calc
      _ = (fibreScale m Q * (fibreScale m Q)⁻¹) * (t / fibreScale M Q) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hBm.ne', one_mul]
  rw [← mul_assoc, he]
  ring

#print axioms fibreScale_common_difference
#print axioms incidencePacket_common_charge

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
