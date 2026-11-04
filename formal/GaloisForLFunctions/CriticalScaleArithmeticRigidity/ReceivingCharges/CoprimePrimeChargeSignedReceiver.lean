import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CoprimePrimeChargeTailVectors
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CoprimePrimeChargeMixedLimits

/-!
# The complete signed receiving law in coprime fibres

At cutoff `X²` and horizon `X⁴⁰`, a charge in any fixed conductor fibre
pairs with its matching exact complementary receiver to `t/80`. Distinct
fixed receiving modes pair to zero. The complete critical form has this
law with every archimedean, shell, pole and horizon term retained.
-/

noncomputable section

open Finset Filter Topology MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  CompletedArithmeticForms

/-- Exact packet coordinates of a fixed receiving mode in the common conductor complement. -/
def fibreChargeTerminalProfile (l R X n : ℕ) : ℝ :=
  Real.sqrt n * primeHorizonExtension (fibreChargeTerminalReceiver l R X) n

theorem packetVector_fibreChargeTerminalProfile (l R X : ℕ) :
    packetVector (fibreChargeTerminalProfile l R X) (X ^ 40) = fibreChargeTerminalReceiver l R X :=
  packetVector_sqrt_extension _

/-- The exact complementary profile is eventually neutral and has norm at most one. -/
theorem eventually_fibreChargeTerminalProfile_neutral_unit {l R : ℕ}
    (hl : 0 < l) (hR : 0 < R) :
    ∀ᶠ X : ℕ in atTop,
      (∑ n ∈ Icc 1 (X ^ 40), fibreChargeTerminalProfile l R X n / (n : ℝ) = 0) ∧
        ‖packetVector (fibreChargeTerminalProfile l R X) (X ^ 40)‖ ≤ 1 := by
  filter_upwards [eventually_ge_atTop 2,
    eventually_fibreChargeTerminalReceiver_norm_le_one hl hR] with X hX hnorm
  have hN : 2 ≤ X ^ 40 := hX.trans (Nat.le_pow (by omega : 0 < 40))
  have hQ : 1 ≤ R * X ^ 2 := Nat.mul_pos hR (Nat.one_le_pow 2 X (by omega))
  refine ⟨harmonic_neutral_of_conductor_complement hQ hN _ ?_, ?_⟩
  · rw [packetVector_fibreChargeTerminalProfile]
    exact fibreChargeTerminalReceiver_mem l R X
  · simpa only [packetVector_fibreChargeTerminalProfile] using hnorm

/-- A common conductor complement annihilates the full adjunction packet of each included fibre. -/
theorem fibreChargeTerminal_dilation_pairing {m R X : ℕ}
    (hmR : m ≤ R) (hX : 2 ≤ X) (l : ℕ) (t : ℝ) :
    jumpPairing (X ^ 40)
      (normalizedConductorPacket (m * X ^ 2)
        (harmonicFibreChargeCoefficients m (X ^ 2) (X ^ 40) t))
      (fibreChargeTerminalProfile l R X) / Real.sqrt (Real.log (X ^ 40 : ℕ)) =
        ⟪fibreChargeTailVector m (X ^ 2) (X ^ 40) t, fibreChargeTerminalReceiver l R X⟫ := by
  have hN : 2 ≤ X ^ 40 := hX.trans (Nat.le_pow (by omega : 0 < 40))
  have hmem : packetVector (fibreChargeTerminalProfile l R X) (X ^ 40) ∈
      (conductorSubspace (m * X ^ 2) (X ^ 40))ᗮ := by
    rw [packetVector_fibreChargeTerminalProfile]
    exact (Submodule.orthogonal_le
      (conductorSubspace_mono (Nat.mul_le_mul_right (X ^ 2) hmR) (X ^ 40)))
        (fibreChargeTerminalReceiver_mem l R X)
  rw [jumpPairing_conductor_complement hN _ _ hmem,
    fibreChargeTailVector, real_inner_smul_left,
    ← packetVector_fibreChargeTerminalProfile, packetVector_inner]
  ring

/-- All complete-form corrections vanish in each fixed-fibre complementary mixed pairing. -/
theorem tendsto_fibreChargeTerminal_complete_sub_dilation {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) {m l R : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hR : 0 < R) (t : ℝ) :
    Tendsto (fun X : ℕ =>
      (completePacketPairing φ (2 * K * Real.log (X ^ 40 : ℕ) ^ (1 / 8 : ℝ)) (X ^ 40)
        (normalizedConductorPacket (m * X ^ 2)
          (harmonicFibreChargeCoefficients m (X ^ 2) (X ^ 40) t))
        (fibreChargeTerminalProfile l R X) -
      jumpPairing (X ^ 40)
        (normalizedConductorPacket (m * X ^ 2)
          (harmonicFibreChargeCoefficients m (X ^ 2) (X ^ 40) t))
        (fibreChargeTerminalProfile l R X)) / Real.sqrt (Real.log (X ^ 40 : ℕ)))
      atTop (𝓝 0) := by
  have hsq := tendsto_harmonicFibreCharge_mixed_error_sq
    hφ hφ0 hsupp hM hK hm (a := 2) (d := 40) (by omega) (by omega) t
    (fibreChargeTerminalProfile l R) (eventually_fibreChargeTerminalProfile_neutral_unit hl hR)
  have h := hsq.sqrt
  simp only [Real.sqrt_zero] at h
  refine squeeze_zero_norm' ?_ h
  filter_upwards [] with X
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs]

/-- The full critical complete form has an exact diagonal signed receiving limit in fixed coprime fibres. -/
theorem tendsto_harmonicFibreCharge_complete_terminalReceiver {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) {m l R : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hmR : m ≤ R) (t : ℝ) :
    Tendsto (fun X : ℕ =>
      ⟪Matrix.toEuclideanLin
          (completeWeilMatrix φ (2 * K * Real.log (X ^ 40 : ℕ) ^ (1 / 8 : ℝ)) (X ^ 40))
          (harmonicFibreChargeVector m (X ^ 2) (X ^ 40) t), fibreChargeTerminalReceiver l R X⟫)
      atTop (𝓝 ((if m = l then 1 else 0) * (t / 80))) := by
  have hR : 0 < R := hm.trans_le hmR
  have h := (tendsto_fibreChargeTerminal_complete_sub_dilation hφ hφ0 hsupp hM hK hm hl hR t).add
    (tendsto_fibreChargeTail_terminalReceiver_pairing hm hl hR t)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  rw [← fibreChargeTerminal_dilation_pairing hmR hX l,
    harmonicFibreChargeVector, map_smul, real_inner_smul_left,
    ← packetVector_fibreChargeTerminalProfile]
  unfold completePacketPairing
  ring

#print axioms fibreChargeTerminal_dilation_pairing
#print axioms tendsto_harmonicFibreCharge_complete_terminalReceiver

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
