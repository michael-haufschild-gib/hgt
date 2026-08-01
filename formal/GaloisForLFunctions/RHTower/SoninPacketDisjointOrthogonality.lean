import GaloisForLFunctions.RHTower.SoninPacketL2

/-!
# Wavepackets on disjoint annuli are orthogonal

Each wavepacket vanishes outside its own annulus, so two packets built on annuli that do not
overlap have pointwise-disjoint supports and their pairing is the integral of the zero function.

Orthogonality is exact here, not asymptotic: it needs no frequency separation and no limit.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory
open scoped InnerProduct InnerProductSpace

/-- **Exact orthogonality.**  Packets on disjoint annuli pair to zero. -/
theorem inner_soninPacketEven_eq_zero_of_disjoint
    (β₁ γ₁ β₂ γ₂ : ℝ) (hβ₁ : 0 < β₁) (h₁ : β₁ < γ₁) (hβ₂ : 0 < β₂) (h₂ : β₂ < γ₂)
    (hdisj : γ₁ ≤ β₂) (κ₁ κ₂ : ℝ) :
    ⟪soninPacketEven β₁ γ₁ hβ₁ h₁ κ₁, soninPacketEven β₂ γ₂ hβ₂ h₂ κ₂⟫_ℂ = 0 := by
  have hcoe : ⟪soninPacketEven β₁ γ₁ hβ₁ h₁ κ₁, soninPacketEven β₂ γ₂ hβ₂ h₂ κ₂⟫_ℂ =
      ⟪soninPacketL2 β₁ γ₁ hβ₁ h₁ κ₁, soninPacketL2 β₂ γ₂ hβ₂ h₂ κ₂⟫_ℂ := rfl
  rw [hcoe, MeasureTheory.L2.inner_def]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [soninPacketL2_coeFn β₁ γ₁ hβ₁ h₁ κ₁,
    soninPacketL2_coeFn β₂ γ₂ hβ₂ h₂ κ₂] with x hx₁ hx₂
  show (inner ℂ ((soninPacketL2 β₁ γ₁ hβ₁ h₁ κ₁ : ℝ → ℂ) x)
    ((soninPacketL2 β₂ γ₂ hβ₂ h₂ κ₂ : ℝ → ℂ) x) : ℂ) = (0 : ℝ → ℂ) x
  rw [hx₁, hx₂]
  by_cases hle : |x| ≤ β₂
  · rw [soninPacket_eq_zero_of_abs_le β₂ γ₂ hβ₂ h₂ κ₂ hle]
    simp
  · push Not at hle
    rw [soninPacket_eq_zero_of_le_abs β₁ γ₁ hβ₁ h₁ κ₁ (hdisj.trans hle.le)]
    simp

/-- The same pairing read in the other order. -/
theorem inner_soninPacketEven_eq_zero_of_disjoint'
    (β₁ γ₁ β₂ γ₂ : ℝ) (hβ₁ : 0 < β₁) (h₁ : β₁ < γ₁) (hβ₂ : 0 < β₂) (h₂ : β₂ < γ₂)
    (hdisj : γ₁ ≤ β₂) (κ₁ κ₂ : ℝ) :
    ⟪soninPacketEven β₂ γ₂ hβ₂ h₂ κ₂, soninPacketEven β₁ γ₁ hβ₁ h₁ κ₁⟫_ℂ = 0 := by
  have h := inner_soninPacketEven_eq_zero_of_disjoint β₁ γ₁ β₂ γ₂ hβ₁ h₁ hβ₂ h₂ hdisj κ₁ κ₂
  rw [← inner_conj_symm, h, map_zero]

end RHTower
