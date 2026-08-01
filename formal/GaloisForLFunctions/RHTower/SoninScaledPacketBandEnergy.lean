import GaloisForLFunctions.RHTower.SoninReferenceTailSup
import GaloisForLFunctions.RHTower.SoninScaledPacketBandMass

/-!
# The band energy of the rescaled packet is small below the carrier

The band energy is the spectral density integrated over the band, and the uniform in-band bound
majorizes that density by a single constant throughout.  Integrating a constant over a band of
radius `t` costs the band's length, so the band energy is at most `2t` times the square of the
uniform bound.

Both parts of that bound are reference tails, so the whole estimate is driven by the two products
`δ(w - t)` and `δ w`: no matter where the annulus sits, once those are large the packet keeps
almost none of its energy inside the band.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory
open scoped FourierTransform

/-- The rescaled packet's spectral density is integrable. -/
theorem integrable_soninScaledPacketSpectralDensity (m δ κ : ℝ) (hδ : 0 < δ) :
    Integrable (soninScaledPacketSpectralDensity m δ κ) volume := by
  have hLp : Integrable (fun η : ℝ =>
      ‖((fourierUnitary (soninScaledPacketL2 m δ κ hδ) : SoninL2) : ℝ → ℂ) η‖ ^ 2) volume := by
    have := (Lp.memLp (fourierUnitary (soninScaledPacketL2 m δ κ hδ))).integrable_norm_rpow
      (by norm_num) (by norm_num)
    simpa using this
  refine hLp.congr ?_
  filter_upwards [fourierUnitary_soninScaledPacketL2_coeFn m δ κ hδ] with η hη
  unfold soninScaledPacketSpectralDensity
  rw [hη]

/-- The symmetric band is an interval. -/
theorem centralBand_eq_Icc (t : ℝ) : {η : ℝ | |η| ≤ t} = Set.Icc (-t) t := by
  ext η
  simp only [Set.mem_setOf_eq, Set.mem_Icc, abs_le]

theorem measurableSet_centralBand (t : ℝ) : MeasurableSet {η : ℝ | |η| ≤ t} := by
  rw [centralBand_eq_Icc]
  exact measurableSet_Icc

/-- The symmetric band of radius `t` has length `2t`. -/
theorem volume_centralBand_toReal (t : ℝ) (ht : 0 ≤ t) :
    volume.real {η : ℝ | |η| ≤ t} = 2 * t := by
  rw [centralBand_eq_Icc, measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith)]
  ring

/-- **The band energy below the carrier.**  The packet's energy inside a band of radius `t` below
its carrier frequency is at most the band's length times the square of the uniform tail bound. -/
theorem norm_sq_evenFourierCutoff_soninScaledPacketEven_le_uniform
    (m δ w₀ t : ℝ) (hδ : 0 < δ) (ht : 0 ≤ t) (htw : t < w₀) :
    ‖evenFourierCutoff t (soninScaledPacketEven m δ (2 * Real.pi * w₀) hδ)‖ ^ 2 ≤
      2 * t * (2 * δ * soninRefTailSup (δ * (w₀ - t)) +
        |soninScaledPacketMean m δ (2 * Real.pi * w₀)| *
          (2 * δ * soninRefTailSup 0)) ^ 2 := by
  set M : ℝ := 2 * δ * soninRefTailSup (δ * (w₀ - t)) +
    |soninScaledPacketMean m δ (2 * Real.pi * w₀)| * (2 * δ * soninRefTailSup 0) with hM
  have hMnn : 0 ≤ M := by
    have h₁ : (0 : ℝ) ≤ 2 * δ * soninRefTailSup (δ * (w₀ - t)) := by
      have := soninRefTailSup_nonneg (δ * (w₀ - t))
      positivity
    have h₂ : (0 : ℝ) ≤ |soninScaledPacketMean m δ (2 * Real.pi * w₀)| *
        (2 * δ * soninRefTailSup 0) := by
      have := soninRefTailSup_nonneg 0
      have := abs_nonneg (soninScaledPacketMean m δ (2 * Real.pi * w₀))
      positivity
    rw [hM]
    linarith
  have hmeas := measurableSet_centralBand t
  have hL : Integrable ({η : ℝ | |η| ≤ t}.indicator
      (soninScaledPacketSpectralDensity m δ (2 * Real.pi * w₀))) volume :=
    (integrable_soninScaledPacketSpectralDensity m δ (2 * Real.pi * w₀) hδ).indicator hmeas
  have hR : Integrable ({η : ℝ | |η| ≤ t}.indicator (fun _ : ℝ => M ^ 2)) volume := by
    rw [integrable_indicator_iff hmeas, centralBand_eq_Icc]
    exact continuous_const.integrableOn_Icc
  have hmono : ∀ ξ : ℝ, {η : ℝ | |η| ≤ t}.indicator
      (soninScaledPacketSpectralDensity m δ (2 * Real.pi * w₀)) ξ ≤
      {η : ℝ | |η| ≤ t}.indicator (fun _ : ℝ => M ^ 2) ξ := by
    intro ξ
    by_cases hmem : ξ ∈ {η : ℝ | |η| ≤ t}
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
      have hpt := norm_fourier_soninScaledPacket_le_tailSup m δ w₀ t ξ hδ hmem htw
      have hnn := norm_nonneg (𝓕 (fun x : ℝ =>
        (soninScaledPacket m δ (2 * Real.pi * w₀) x : ℂ)) ξ)
      show ‖𝓕 (fun x : ℝ => (soninScaledPacket m δ (2 * Real.pi * w₀) x : ℂ)) ξ‖ ^ 2 ≤ M ^ 2
      nlinarith [hpt, hnn, hMnn]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
  rw [norm_sq_evenFourierCutoff_soninScaledPacketEven_eq_density m δ (2 * Real.pi * w₀) hδ t]
  refine le_trans (integral_mono hL hR hmono) ?_
  rw [integral_indicator_const (M ^ 2) hmeas, smul_eq_mul,
    volume_centralBand_toReal t ht]

end RHTower
