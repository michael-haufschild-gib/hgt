import GaloisForLFunctions.RHTower.SoninScaledPacketFourier

/-!
# The spectral density of the rescaled packet

The density is the squared spectral magnitude, so it scales by the square of the half-width while
its argument is rescaled.  Integrating over a band of radius `t` therefore gives the half-width
times the reference band mass at radius `δ t`: one factor of `δ` is lost to the substitution.

Since the total mass scales the same way, the *fraction* of spectral mass inside a band is a
function of `δ t` and `δ κ` alone — the same for every annulus of the family.
-/

noncomputable section

set_option maxHeartbeats 400000

namespace RHTower

open MeasureTheory
open scoped FourierTransform

/-- The spectral density of the rescaled packet. -/
def soninScaledPacketSpectralDensity (m δ κ : ℝ) : ℝ → ℝ := fun ξ =>
  ‖𝓕 (fun x : ℝ => (soninScaledPacket m δ κ x : ℂ)) ξ‖ ^ 2

/-- **Density scaling.** -/
theorem soninScaledPacketSpectralDensity_scaling (m δ κ : ℝ) (hδ : 0 < δ) (ξ : ℝ) :
    soninScaledPacketSpectralDensity m δ κ ξ =
      δ ^ 2 * soninScaledPacketSpectralDensity (m / δ) 1 (δ * κ) (δ * ξ) := by
  rw [soninScaledPacketSpectralDensity, soninScaledPacketSpectralDensity,
    norm_fourier_soninScaledPacket_scaling m δ κ hδ ξ, mul_pow]

/-- Membership in a band is preserved by the rescaling. -/
theorem abs_le_iff_abs_mul_le (δ : ℝ) (hδ : 0 < δ) (t ξ : ℝ) :
    |ξ| ≤ t ↔ |δ * ξ| ≤ δ * t := by
  rw [abs_mul, abs_of_pos hδ]
  constructor
  · intro h
    exact mul_le_mul_of_nonneg_left h hδ.le
  · intro h
    exact le_of_mul_le_mul_left h hδ

/-- The banded density of the family is the rescaled banded density of the reference. -/
theorem indicator_soninScaledPacketSpectralDensity_scaling (m δ κ t : ℝ) (hδ : 0 < δ) (ξ : ℝ) :
    {η : ℝ | |η| ≤ t}.indicator (soninScaledPacketSpectralDensity m δ κ) ξ =
      δ ^ 2 * {η : ℝ | |η| ≤ δ * t}.indicator
        (soninScaledPacketSpectralDensity (m / δ) 1 (δ * κ)) (δ * ξ) := by
  by_cases hmem : |ξ| ≤ t
  · have hmemset : ξ ∈ {η : ℝ | |η| ≤ t} := hmem
    have hmemset' : (δ * ξ) ∈ {η : ℝ | |η| ≤ δ * t} :=
      (abs_le_iff_abs_mul_le δ hδ t ξ).mp hmem
    rw [Set.indicator_of_mem hmemset, Set.indicator_of_mem hmemset',
      soninScaledPacketSpectralDensity_scaling m δ κ hδ ξ]
  · have hmemset : ξ ∉ {η : ℝ | |η| ≤ t} := hmem
    have hmemset' : (δ * ξ) ∉ {η : ℝ | |η| ≤ δ * t} := fun h =>
      hmem ((abs_le_iff_abs_mul_le δ hδ t ξ).mpr h)
    rw [Set.indicator_of_notMem hmemset, Set.indicator_of_notMem hmemset', mul_zero]

/-- **Band mass scaling.**  The spectral mass inside a band of radius `t` is the half-width times
the reference mass inside the band of radius `δ t`. -/
theorem integral_indicator_soninScaledPacketSpectralDensity_scaling
    (m δ κ t : ℝ) (hδ : 0 < δ) :
    ∫ ξ : ℝ, {η : ℝ | |η| ≤ t}.indicator (soninScaledPacketSpectralDensity m δ κ) ξ =
      δ * ∫ η : ℝ, {η : ℝ | |η| ≤ δ * t}.indicator
        (soninScaledPacketSpectralDensity (m / δ) 1 (δ * κ)) η := by
  have hpoint : ∀ ξ : ℝ,
      {η : ℝ | |η| ≤ t}.indicator (soninScaledPacketSpectralDensity m δ κ) ξ =
        δ ^ 2 * (fun y : ℝ => {η : ℝ | |η| ≤ δ * t}.indicator
          (soninScaledPacketSpectralDensity (m / δ) 1 (δ * κ)) y) (ξ / δ⁻¹) := by
    intro ξ
    have hrw : ξ / δ⁻¹ = δ * ξ := by
      field_simp
    rw [hrw]
    exact indicator_soninScaledPacketSpectralDensity_scaling m δ κ t hδ ξ
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), integral_const_mul,
    MeasureTheory.Measure.integral_comp_div
      (fun y : ℝ => {η : ℝ | |η| ≤ δ * t}.indicator
        (soninScaledPacketSpectralDensity (m / δ) 1 (δ * κ)) y) δ⁻¹,
    abs_of_pos (inv_pos.mpr hδ), smul_eq_mul, ← mul_assoc]
  congr 1
  field_simp

end RHTower
