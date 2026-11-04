import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.PrimeIncidenceDilationPairing
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargePolynomialScales

/-!
# The exact prime-prefix receiving kernel

Nested prime prefixes pair through their common prefix. The cofactor
harmonic identity therefore determines their polarized logarithmic-scale
kernel, including the negative half-charge boundary correction.
-/

noncomputable section

open Finset Filter Topology
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory SelectiveMultiscaleArithmeticPositivity

theorem primePrefix_filter {Q R : ℕ} (hQR : Q ≤ R) :
    ((Icc 1 R).filter Nat.Prime).filter (fun p => p ≤ Q) = (Icc 1 Q).filter Nat.Prime := by
  ext p
  simp only [mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨⟨hp1, -⟩, hp⟩, hpQ⟩
    exact ⟨⟨hp1, hpQ⟩, hp⟩
  · rintro ⟨⟨hp1, hpQ⟩, hp⟩
    exact ⟨⟨⟨hp1, hpQ.trans hQR⟩, hp⟩, hpQ⟩

/-- Zero extension makes nested prime packets share one finite prime set. -/
theorem incidencePacket_primePrefix_extend {Q R : ℕ} (hQR : Q ≤ R) (b : ℕ → ℝ) (n : ℕ) :
    incidencePacket ((Icc 1 Q).filter Nat.Prime) b n =
      incidencePacket ((Icc 1 R).filter Nat.Prime) (fun p => if p ≤ Q then b p else 0) n := by
  simp only [incidencePacket, ite_mul, zero_mul]
  rw [← sum_filter, primePrefix_filter hQR]

/-- A nested mixed pairing has exactly the common prefix's cofactor mass. -/
theorem jumpPairing_primePrefixes {Q R : ℕ} (hQR : Q ≤ R) (N : ℕ) (b d : ℝ) :
    jumpPairing N
      (incidencePacket ((Icc 1 Q).filter Nat.Prime) (fun _ => b))
      (incidencePacket ((Icc 1 R).filter Nat.Prime) (fun _ => d)) =
      (b * d) * ∑ p ∈ (Icc 1 Q).filter Nat.Prime,
        Real.log p / p * harmonicMass (N / p) := by
  have he := funext (incidencePacket_primePrefix_extend hQR (fun _ => b))
  rw [he, jumpPairing_incidencePacket_diagonal (fun p hp => (mem_filter.mp hp).2)]
  simp only [ite_mul, zero_mul]
  rw [← sum_filter, primePrefix_filter hQR, mul_sum]
  rfl

/-- Harmonic centering leaves the exact prefix kernel unchanged. -/
theorem harmonicPrimeCharge_prefix_pairing {Q R : ℕ}
    (hQ : 2 ≤ Q) (hQR : Q ≤ R) (N : ℕ) (t u : ℝ) :
    jumpPairing N
      (normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t))
      (normalizedConductorPacket R (harmonicPrimeChargeCoefficients R N u)) =
      (t * u) * (primePoleScale Q / primePoleScale R) *
        jumpEnergy N (normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N 1)) := by
  have hR : 2 ≤ R := hQ.trans hQR
  rw [funext (harmonicPrimeCharge_packet (by omega : 1 ≤ Q) N t),
    funext (harmonicPrimeCharge_packet (by omega : 1 ≤ R) N u), jumpPairing_sub_const,
    jumpPairing_primePrefixes hQR, harmonicPrimeCharge_jumpEnergy (by omega : 1 ≤ Q)]
  field_simp [(primePoleScale_pos hQ).ne', (primePoleScale_pos hR).ne']

/-- The nested prime-prefix kernel retains its exact conductor and horizon ratios. -/
theorem tendsto_harmonicPrimeCharge_prefix_pairing {a b d : ℕ}
    (ha : 0 < a) (hab : a ≤ b) (hbd : b ≤ d) (t u : ℝ) :
    Tendsto (fun X : ℕ => jumpPairing (X ^ d)
      (normalizedConductorPacket (X ^ a) (harmonicPrimeChargeCoefficients (X ^ a) (X ^ d) t))
      (normalizedConductorPacket (X ^ b) (harmonicPrimeChargeCoefficients (X ^ b) (X ^ d) u)))
      atTop (𝓝 ((t * u) * ((d : ℝ) / b - (a : ℝ) / (2 * b)))) := by
  have hb : 0 < b := ha.trans_le hab
  have h := ((tendsto_primePoleScale_pow_ratio hb a).mul
    (tendsto_harmonicPrimeCharge_polynomial_dilation_energy ha (hab.trans hbd) 1)).const_mul
      (t * u)
  have he : (t * u) * (((a : ℝ) / b) * ((1 : ℝ) ^ 2 * ((d : ℝ) / a - 1 / 2))) =
      (t * u) * ((d : ℝ) / b - (a : ℝ) / (2 * b)) := by
    have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
    have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
    field_simp [haR, hbR]
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  rw [harmonicPrimeCharge_prefix_pairing (hX.trans (Nat.le_pow ha))
    (Nat.pow_le_pow_right (by omega) hab)]
  ring

#print axioms harmonicPrimeCharge_prefix_pairing
#print axioms tendsto_harmonicPrimeCharge_prefix_pairing

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
