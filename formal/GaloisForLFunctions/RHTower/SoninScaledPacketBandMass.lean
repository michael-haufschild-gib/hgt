import GaloisForLFunctions.RHTower.SoninScaledPacketFourierL2
import GaloisForLFunctions.RHTower.SoninPacketBandEnergyBound
import GaloisForLFunctions.RHTower.SoninBurnolLogBandComparison

/-!
# The band energy of the rescaled packet, and its scaling

The Fourier cutoff acts by restricting the `L²` transform to a central band, so the band energy of
the rescaled packet is the integral of its spectral density over that band.  The density's scaling
then gives the band energy at radius `t` as the half-width times the reference band energy at radius
`δ t` — the same factor the total energy carries.

So the fraction of energy a band captures is the same for every annulus of the family: it depends on
`δ t` and `δ κ`, not on the annulus.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory
open scoped FourierTransform

/-- The squared band energy of the rescaled packet as an explicit integral. -/
theorem norm_sq_evenFourierCutoff_soninScaledPacketEven
    (m δ κ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    ‖evenFourierCutoff t (soninScaledPacketEven m δ κ hδ)‖ ^ 2 =
      ∫ ξ : ℝ, ‖(centralInterval t).indicator
        (fun η : ℝ => ((fourierUnitary (soninScaledPacketL2 m δ κ hδ) : SoninL2) : ℝ → ℂ) η)
        ξ‖ ^ 2 := by
  have hcoe : ((evenFourierCutoff t (soninScaledPacketEven m δ κ hδ) : evenSubspace) : SoninL2) =
      fourierUnitary.symm (indicatorCutoff (centralInterval t)
        (measurableSet_centralInterval t) (fourierUnitary (soninScaledPacketL2 m δ κ hδ))) := rfl
  have hnorm : ‖evenFourierCutoff t (soninScaledPacketEven m δ κ hδ)‖ =
      ‖indicatorCutoff (centralInterval t) (measurableSet_centralInterval t)
        (fourierUnitary (soninScaledPacketL2 m δ κ hδ))‖ := by
    rw [show ‖evenFourierCutoff t (soninScaledPacketEven m δ κ hδ)‖ =
        ‖((evenFourierCutoff t (soninScaledPacketEven m δ κ hδ) : evenSubspace) : SoninL2)‖
      from rfl, hcoe]
    exact fourierUnitary.symm.norm_map _
  rw [hnorm, norm_sq_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [indicatorCutoff_ae (centralInterval t) (measurableSet_centralInterval t)
    (fourierUnitary (soninScaledPacketL2 m δ κ hδ))] with ξ hξ
  rw [hξ]

/-- The band energy is the spectral density integrated over the band. -/
theorem norm_sq_evenFourierCutoff_soninScaledPacketEven_eq_density
    (m δ κ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    ‖evenFourierCutoff t (soninScaledPacketEven m δ κ hδ)‖ ^ 2 =
      ∫ ξ : ℝ, {η : ℝ | |η| ≤ t}.indicator (soninScaledPacketSpectralDensity m δ κ) ξ := by
  rw [norm_sq_evenFourierCutoff_soninScaledPacketEven m δ κ hδ t]
  refine integral_congr_ae ?_
  filter_upwards [fourierUnitary_soninScaledPacketL2_coeFn m δ κ hδ] with ξ hξ
  rw [norm_sq_indicator]
  by_cases hmem : |ξ| ≤ t
  · have hmem₁ : ξ ∈ centralInterval t := (mem_centralInterval_iff t ξ).mpr hmem
    have hmem₂ : ξ ∈ {η : ℝ | |η| ≤ t} := hmem
    rw [Set.indicator_of_mem hmem₁, Set.indicator_of_mem hmem₂,
      soninScaledPacketSpectralDensity, hξ]
  · have hmem₁ : ξ ∉ centralInterval t := fun h => hmem ((mem_centralInterval_iff t ξ).mp h)
    have hmem₂ : ξ ∉ {η : ℝ | |η| ≤ t} := hmem
    rw [Set.indicator_of_notMem hmem₁, Set.indicator_of_notMem hmem₂]

/-- **Band energy scaling.**  The energy inside a band of radius `t` is the half-width times the
reference energy inside the band of radius `δ t`. -/
theorem norm_sq_evenFourierCutoff_soninScaledPacketEven_scaling
    (m δ κ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    ‖evenFourierCutoff t (soninScaledPacketEven m δ κ hδ)‖ ^ 2 =
      δ * ‖evenFourierCutoff (δ * t)
        (soninScaledPacketEven (m / δ) 1 (δ * κ) one_pos)‖ ^ 2 := by
  rw [norm_sq_evenFourierCutoff_soninScaledPacketEven_eq_density m δ κ hδ t,
    norm_sq_evenFourierCutoff_soninScaledPacketEven_eq_density (m / δ) 1 (δ * κ) one_pos (δ * t),
    integral_indicator_soninScaledPacketSpectralDensity_scaling m δ κ t hδ]

/-- **The captured fraction is annulus independent.**  The band energy relates to the total energy
exactly as the reference band energy relates to the reference total. -/
theorem norm_sq_evenFourierCutoff_soninScaledPacketEven_fraction
    (m δ κ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    ‖evenFourierCutoff t (soninScaledPacketEven m δ κ hδ)‖ ^ 2 *
        ‖soninScaledPacketEven (m / δ) 1 (δ * κ) one_pos‖ ^ 2 =
      ‖evenFourierCutoff (δ * t) (soninScaledPacketEven (m / δ) 1 (δ * κ) one_pos)‖ ^ 2 *
        ‖soninScaledPacketEven m δ κ hδ‖ ^ 2 := by
  rw [norm_sq_evenFourierCutoff_soninScaledPacketEven_scaling m δ κ hδ t,
    norm_sq_soninScaledPacketEven_scaling m δ κ hδ]
  ring

end RHTower
