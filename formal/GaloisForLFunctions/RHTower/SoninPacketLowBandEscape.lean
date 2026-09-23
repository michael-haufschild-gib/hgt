import GaloisForLFunctions.RHTower.SoninPacketBandEnergyBound
import GaloisForLFunctions.RHTower.SoninFourierCutoffDilation

/-!
# The wavepacket leaves the bands below its carrier

Tying the aperture and the carrier to a common clock, with the aperture strictly below the carrier
in rate, makes the gap in the band-energy bound grow linearly, so the packet keeps no energy below
its carrier.  Conjugating through the dilation states the same fact for the dilated packet at a
*fixed* aperture, which is the form the aperture flag uses.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter
open scoped Topology

/-- **Low band escape.**  With aperture and carrier on a common clock and the aperture rate
strictly smaller, the packet's energy below the aperture vanishes. -/
theorem tendsto_norm_evenFourierCutoff_soninPacketEven_scaled
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) (q a₀ : ℝ) (ha₀ : 0 < a₀) (hq : a₀ < q)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hr : Tendsto r atTop atTop) :
    Tendsto (fun n : ℕ => ‖evenFourierCutoff (r n * a₀)
        (soninPacketEven b c hb hbc (2 * Real.pi * (r n * q)))‖) atTop (𝓝 0) := by
  have hqpos : 0 < q := ha₀.trans hq
  have hgap : ∀ n : ℕ, |r n * q| - r n * a₀ = r n * (q - a₀) := by
    intro n
    rw [abs_of_pos (mul_pos (hrpos n) hqpos)]
    ring
  -- the spectral tail term
  have hgapTendsto : Tendsto (fun n : ℕ => r n * (q - a₀)) atTop atTop :=
    Filter.Tendsto.atTop_mul_const (by linarith : (0 : ℝ) < q - a₀) hr
  have hTail := tendsto_integral_indicator_outer_soninBumpSpectralDensity b c hb hbc
    (fun n : ℕ => r n * (q - a₀)) hgapTendsto
  -- the mean term
  have hfreq : Tendsto (fun n : ℕ => 2 * Real.pi * (r n * q)) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => r n * q) atTop atTop :=
      Filter.Tendsto.atTop_mul_const hqpos hr
    exact Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi) h1
  have hMean : Tendsto (fun n : ℕ =>
      soninPacketMean b c hbc (2 * Real.pi * (r n * q))) atTop (𝓝 0) :=
    (tendsto_soninPacketMean_atTop b c hb hbc).comp hfreq
  -- the majorant
  have hmaj : Tendsto (fun n : ℕ =>
      3 * ((2 : ℝ)⁻¹ * (∫ η : ℝ, {η : ℝ | r n * (q - a₀) ≤ |η|}.indicator
              (soninBumpSpectralDensity b c hbc) η) +
        (soninPacketMean b c hbc (2 * Real.pi * (r n * q))) ^ (2 : ℕ) *
          ∫ η : ℝ, soninBumpSpectralDensity b c hbc η)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ *
        ∫ η : ℝ, {η : ℝ | r n * (q - a₀) ≤ |η|}.indicator
          (soninBumpSpectralDensity b c hbc) η) atTop (𝓝 0) := by
      simpa using hTail.const_mul ((2 : ℝ)⁻¹)
    have h2 : Tendsto (fun n : ℕ =>
        (soninPacketMean b c hbc (2 * Real.pi * (r n * q))) ^ (2 : ℕ) *
          ∫ η : ℝ, soninBumpSpectralDensity b c hbc η) atTop (𝓝 0) := by
      simpa using (hMean.pow 2).mul_const (∫ η : ℝ, soninBumpSpectralDensity b c hbc η)
    simpa using (h1.add h2).const_mul (3 : ℝ)
  -- squeeze the squared norms
  have hsq : Tendsto (fun n : ℕ => ‖evenFourierCutoff (r n * a₀)
      (soninPacketEven b c hb hbc (2 * Real.pi * (r n * q)))‖ ^ (2 : ℕ)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => sq_nonneg _) (fun n => ?_) hmaj
    have hbnd := norm_sq_evenFourierCutoff_soninPacketEven_le b c hb hbc
      (r n * a₀) (r n * q)
    rw [hgap n] at hbnd
    exact hbnd
  have hsqrt := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  simp only [Function.comp_def, Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun n => ?_
  rw [Real.sqrt_sq (norm_nonneg _)]

/-- **The dilated packet has no energy below a fixed aperture.**  This is the first horn of
`(13)`: the inverse dilate of the packet leaves every fixed Fourier band strictly below the
carrier ratio. -/
theorem tendsto_norm_evenFourierCutoff_soninDilatedPacket
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) (q a₀ : ℝ) (ha₀ : 0 < a₀) (hq : a₀ < q)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hr : Tendsto r atTop atTop) :
    Tendsto (fun n : ℕ => ‖evenFourierCutoff a₀
        (soninDilatedPacket b c hb hbc (2 * Real.pi * (r n * q)) (r n) (hrpos n))‖)
      atTop (𝓝 0) := by
  have hbase := tendsto_norm_evenFourierCutoff_soninPacketEven_scaled b c hb hbc q a₀ ha₀ hq
    r hrpos hr
  refine hbase.congr fun n => ?_
  exact (norm_evenFourierCutoff_evenDilationCLM_inv a₀ (r n) (hrpos n)
    (soninPacketEven b c hb hbc (2 * Real.pi * (r n * q)))).symm

end RHTower
