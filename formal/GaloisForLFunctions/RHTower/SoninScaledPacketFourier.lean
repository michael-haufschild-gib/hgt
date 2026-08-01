import GaloisForLFunctions.RHTower.SoninScaledPacketScaling
import GaloisForLFunctions.HTGeometry.FourierIntegralDilation

/-!
# The spectrum of the rescaled packet

The packet at half-width `δ` is the reference packet at frequency `δκ` precomposed with the
dilation, so the dilation rule for the Fourier integral turns its whole spectrum into the reference
spectrum read at `δ` times the frequency, scaled by `δ`.

A frequency band of radius `t` for the family is therefore a band of radius `δt` for the reference:
one spectral statement covers every annulus, instead of one per annulus.
-/

noncomputable section

set_option maxHeartbeats 400000

namespace RHTower

open MeasureTheory
open scoped FourierTransform

/-- **Spectral scaling.**  The transform of the rescaled packet is the reference transform read at
the rescaled frequency. -/
theorem fourier_soninScaledPacket_scaling (m δ κ : ℝ) (hδ : 0 < δ) (ξ : ℝ) :
    𝓕 (fun x : ℝ => (soninScaledPacket m δ κ x : ℂ)) ξ =
      δ • 𝓕 (fun y : ℝ => (soninScaledPacket (m / δ) 1 (δ * κ) y : ℂ)) (δ * ξ) := by
  have hfun : (fun x : ℝ => (soninScaledPacket m δ κ x : ℂ)) =
      fun x : ℝ => (fun y : ℝ => (soninScaledPacket (m / δ) 1 (δ * κ) y : ℂ)) (x / δ) := by
    funext x
    rw [soninScaledPacket_scaling m δ κ hδ x]
  rw [hfun]
  exact GaloisForLFunctions.HTGeometry.fourierIntegral_comp_div
    (fun y : ℝ => (soninScaledPacket (m / δ) 1 (δ * κ) y : ℂ)) δ hδ ξ

/-- The spectral magnitude scales by the half-width. -/
theorem norm_fourier_soninScaledPacket_scaling (m δ κ : ℝ) (hδ : 0 < δ) (ξ : ℝ) :
    ‖𝓕 (fun x : ℝ => (soninScaledPacket m δ κ x : ℂ)) ξ‖ =
      δ * ‖𝓕 (fun y : ℝ => (soninScaledPacket (m / δ) 1 (δ * κ) y : ℂ)) (δ * ξ)‖ := by
  rw [fourier_soninScaledPacket_scaling m δ κ hδ ξ, norm_smul, Real.norm_eq_abs,
    abs_of_pos hδ]

/-- **A band for the family is a band for the reference.**  The spectral density of the packet at a
frequency in the band of radius `t` is the reference density at a frequency in the band of radius
`δ t`. -/
theorem norm_fourier_soninScaledPacket_of_abs_le (m δ κ : ℝ) (hδ : 0 < δ) (t : ℝ) {ξ : ℝ}
    (hξ : |ξ| ≤ t) :
    ‖𝓕 (fun x : ℝ => (soninScaledPacket m δ κ x : ℂ)) ξ‖ =
      δ * ‖𝓕 (fun y : ℝ => (soninScaledPacket (m / δ) 1 (δ * κ) y : ℂ)) (δ * ξ)‖ ∧
    |δ * ξ| ≤ δ * t := by
  refine ⟨norm_fourier_soninScaledPacket_scaling m δ κ hδ ξ, ?_⟩
  rw [abs_mul, abs_of_pos hδ]
  exact mul_le_mul_of_nonneg_left hξ hδ.le

end RHTower
