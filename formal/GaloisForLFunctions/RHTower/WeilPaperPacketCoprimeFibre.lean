import GaloisForLFunctions.RHTower.WeilPaperPacketPrimeMasks
import GaloisForLFunctions.RHTower.WeilPaperPacketRepair

/-!
# Positive integer-null mixtures with an exact coprime energy difference

Even and odd prime-subset masks give actual nonnegative smooth packet mixtures
with identical integer defects. Their common positive correction cancels every
integer logarithm and preserves the full pole-plus-archimedean energy difference.
The resulting variation is exactly the coprime part of the packet covariance.
-/

open Matrix Complex GaloisForLFunctions.HTGeometry
open scoped BigOperators ComplexConjugate Matrix
noncomputable section
namespace RHTower.WeilWorkPBAP

open WeilOneSided WeilSpectral

def paperPacketEvenPrimeMixture {N : ℕ} (L : ℕ) (c : PacketIndex N → ℂ) :
    WeilTestFn →₀ ℝ := packetColumnMixture L (paperPacketEvenPrimeColumns c)

def paperPacketOddPrimeMixture {N : ℕ} (L : ℕ) (c : PacketIndex N → ℂ) :
    WeilTestFn →₀ ℝ := packetColumnMixture L (paperPacketOddPrimeColumns c)

theorem paperPacketEvenPrimeMixture_nonneg {N : ℕ} (L : ℕ)
    (c : PacketIndex N → ℂ) (f : WeilTestFn) : 0 ≤ paperPacketEvenPrimeMixture L c f :=
  packetColumnMixture_nonneg L _ f

theorem paperPacketOddPrimeMixture_nonneg {N : ℕ} (L : ℕ)
    (c : PacketIndex N → ℂ) (f : WeilTestFn) : 0 ≤ paperPacketOddPrimeMixture L c f :=
  packetColumnMixture_nonneg L _ f

/-- The actual positive packet families agree at every native integer constraint. -/
theorem defect_paperPacket_prime_parity {N : ℕ} (L : ℕ) (c : PacketIndex N → ℂ) :
    defect (paperPacketEvenPrimeMixture L c) = defect (paperPacketOddPrimeMixture L c) := by
  ext j
  unfold paperPacketEvenPrimeMixture paperPacketOddPrimeMixture
  rw [defect_packetColumnMixture, defect_packetColumnMixture,
    divisibilityTrace_paperPacket_prime_parity]

/-- Exact full energy difference before correction. -/
theorem energy_paperPacket_prime_parity {N : ℕ} (L : ℕ) (c : PacketIndex N → ℂ) :
    energy (paperPacketEvenPrimeMixture L c) - energy (paperPacketOddPrimeMixture L c) =
      packetArchPairing (L + 1) (paperPacketCoprimeCovariance c) := by
  unfold paperPacketEvenPrimeMixture paperPacketOddPrimeMixture
  rw [energy_packetColumnMixture, energy_packetColumnMixture,
    packetArchEnergy_eq_covariance, packetArchEnergy_eq_covariance,
    ← packetArchPairing_sub, paperPacket_prime_covariance_difference]

/-- The positive corrections are identical, so the signed mixture is unchanged. -/
theorem nullRepair_paperPacket_prime_parity_sub {N : ℕ} (L : ℕ)
    (c : PacketIndex N → ℂ) :
    nullRepair (paperPacketEvenPrimeMixture L c) - nullRepair (paperPacketOddPrimeMixture L c) =
      paperPacketEvenPrimeMixture L c - paperPacketOddPrimeMixture L c := by
  simp only [nullRepair, defect_paperPacket_prime_parity]
  abel

def paperPacketEvenPrimeNullMixture {N : ℕ} (L : ℕ) (c : PacketIndex N → ℂ) :
    WeilTestFn →₀ ℝ := nullRepair (paperPacketEvenPrimeMixture L c)

def paperPacketOddPrimeNullMixture {N : ℕ} (L : ℕ) (c : PacketIndex N → ℂ) :
    WeilTestFn →₀ ℝ := nullRepair (paperPacketOddPrimeMixture L c)

theorem paperPacketEvenPrimeNullMixture_nonneg {N : ℕ} (L : ℕ)
    (c : PacketIndex N → ℂ) (f : WeilTestFn) : 0 ≤ paperPacketEvenPrimeNullMixture L c f :=
  nullRepair_nonneg (paperPacketEvenPrimeMixture_nonneg L c) f

theorem paperPacketOddPrimeNullMixture_nonneg {N : ℕ} (L : ℕ)
    (c : PacketIndex N → ℂ) (f : WeilTestFn) : 0 ≤ paperPacketOddPrimeNullMixture L c f :=
  nullRepair_nonneg (paperPacketOddPrimeMixture_nonneg L c) f

@[simp] theorem defect_paperPacketEvenPrimeNullMixture {N : ℕ} (L : ℕ)
    (c : PacketIndex N → ℂ) : defect (paperPacketEvenPrimeNullMixture L c) = 0 :=
  defect_nullRepair _

@[simp] theorem defect_paperPacketOddPrimeNullMixture {N : ℕ} (L : ℕ)
    (c : PacketIndex N → ℂ) : defect (paperPacketOddPrimeNullMixture L c) = 0 :=
  defect_nullRepair _

/-- The positive integer-null pair retains the exact coprime full-energy variation. -/
theorem energy_paperPacket_prime_null_parity {N : ℕ} (L : ℕ)
    (c : PacketIndex N → ℂ) :
    energy (paperPacketEvenPrimeNullMixture L c) - energy (paperPacketOddPrimeNullMixture L c) =
      packetArchPairing (L + 1) (paperPacketCoprimeCovariance c) := by
  rw [← map_sub]
  change energy (nullRepair (paperPacketEvenPrimeMixture L c) -
    nullRepair (paperPacketOddPrimeMixture L c)) = _
  rw [nullRepair_paperPacket_prime_parity_sub, map_sub, energy_paperPacket_prime_parity]

/-- Exact coefficient sensitivity bounds the full repaired energy gap. -/
theorem energy_paperPacket_prime_null_parity_sq_le {N : ℕ} (L : ℕ)
    (c : PacketIndex N → ℂ) :
    (energy (paperPacketEvenPrimeNullMixture L c) - energy (paperPacketOddPrimeNullMixture L c)) ^ 2 ≤
      paperPacketCoprimeCoefficientEnergy c *
        finiteMatrixHilbertSchmidtSq (packetArchKernel N (L + 1)) := by
  rw [energy_paperPacket_prime_null_parity]
  simpa only [paperPacketCoprimeCovariance_energy] using
    packetArchPairing_sq_le (L + 1) (paperPacketCoprimeCovariance c)

/-- Every coefficient vector yields a positive all-integer-null pair with this exact energy gap. -/
theorem exists_positive_null_packet_pair_coprime_energy {N : ℕ} (L : ℕ)
    (c : PacketIndex N → ℂ) :
    ∃ a b : WeilTestFn →₀ ℝ,
      (∀ f, 0 ≤ a f) ∧ (∀ f, 0 ≤ b f) ∧
      defect a = 0 ∧ defect b = 0 ∧
      energy a - energy b = packetArchPairing (L + 1) (paperPacketCoprimeCovariance c) :=
  ⟨paperPacketEvenPrimeNullMixture L c, paperPacketOddPrimeNullMixture L c,
    paperPacketEvenPrimeNullMixture_nonneg L c, paperPacketOddPrimeNullMixture_nonneg L c,
    defect_paperPacketEvenPrimeNullMixture L c, defect_paperPacketOddPrimeNullMixture L c,
    energy_paperPacket_prime_null_parity L c⟩

end RHTower.WeilWorkPBAP
