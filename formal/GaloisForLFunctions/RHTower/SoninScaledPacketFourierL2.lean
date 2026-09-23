import GaloisForLFunctions.RHTower.SoninScaledPacketDensity
import GaloisForLFunctions.RHTower.SoninScaledPacketL2
import GaloisForLFunctions.RHTower.SoninPacketFourierEscape

/-!
# The `L²` transform of the rescaled packet is its classical transform

The rescaled packet is continuous with compact support, hence integrable, so its `L²` Fourier
transform agrees almost everywhere with the classical Fourier integral.

This is the bridge that carries the scaling identities of the classical transform over to the
Fourier cutoffs of the Sonin carrier.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory
open scoped Topology FourierTransform

/-- The rescaled packet is integrable. -/
theorem integrable_soninScaledPacket (m δ κ : ℝ) (hδ : 0 < δ) :
    Integrable (soninScaledPacket m δ κ) :=
  (continuous_soninScaledPacket m δ κ hδ).integrable_of_hasCompactSupport
    (hasCompactSupport_soninScaledPacket m δ κ hδ)

/-- The `L²` Fourier transform of the rescaled packet is the classical Fourier integral. -/
theorem fourierUnitary_soninScaledPacketL2_coeFn (m δ κ : ℝ) (hδ : 0 < δ) :
    ((fourierUnitary (soninScaledPacketL2 m δ κ hδ) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      fun ξ : ℝ => 𝓕 (fun x : ℝ => (soninScaledPacket m δ κ x : ℂ)) ξ := by
  set f : SoninL2 := soninScaledPacketL2 m δ κ hδ with hfdef
  have hcoe := soninScaledPacketL2_coeFn m δ κ hδ
  have hint : Integrable (f : ℝ → ℂ) :=
    ((integrable_soninScaledPacket m δ κ hδ).ofReal).congr hcoe.symm
  have hcoe1 : (((memLp_one_iff_integrable.mpr hint).toLp f : Lp ℂ 1 (volume : Measure ℝ)) :
      ℝ → ℂ) =ᵐ[volume] (f : ℝ → ℂ) :=
    MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr hint)
  have hclassical : ∀ w : ℝ,
      (Real.Lp.fourierTransform ((memLp_one_iff_integrable.mpr hint).toLp f) : ℝ → ℂ) w =
        FourierTransform.fourier (f : ℝ → ℂ) w := by
    intro w
    rw [Real.Lp.fourierTransform_apply]
    exact Real.fourier_congr_ae hcoe1 w
  have h1 := (l2_fourier_coeFn_eq_l1_fourier_of_integrable f hint).trans
    (Filter.Eventually.of_forall hclassical)
  refine h1.trans (Filter.Eventually.of_forall fun w => ?_)
  exact Real.fourier_congr_ae hcoe w

/-- The spectral density of the rescaled packet computes the `L²` transform's modulus. -/
theorem soninScaledPacketSpectralDensity_eq_norm_sq (m δ κ : ℝ) (hδ : 0 < δ) :
    (fun ξ : ℝ => ‖((fourierUnitary (soninScaledPacketL2 m δ κ hδ) : SoninL2) : ℝ → ℂ) ξ‖ ^ (2 : ℕ))
      =ᵐ[volume] soninScaledPacketSpectralDensity m δ κ := by
  filter_upwards [fourierUnitary_soninScaledPacketL2_coeFn m δ κ hδ] with ξ hξ
  rw [hξ, soninScaledPacketSpectralDensity]

end RHTower
