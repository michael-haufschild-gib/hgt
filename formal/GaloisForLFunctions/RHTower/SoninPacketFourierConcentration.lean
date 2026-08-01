import GaloisForLFunctions.RHTower.SoninPacketHighBandCapture

/-!
# Frequency concentration of the wavepacket

The packet keeps no energy below an aperture growing slower than its carrier, and loses no energy
above an aperture growing faster.  Its spectrum is therefore asymptotically trapped between the two
apertures of the flag, and after conjugating through the dilation the same holds for the dilated
packet at *fixed* apertures.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter
open scoped Topology

/-- **Outer band energy bound.**  The energy the packet leaves above the band of radius `t` is
controlled by the profile's spectral tail beyond the gap plus the squared mean. -/
theorem norm_sq_sub_evenFourierCutoff_soninPacketEven_le
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) (t a : ℝ) :
    ‖soninPacketEven b c hb hbc (2 * Real.pi * a) -
        evenFourierCutoff t (soninPacketEven b c hb hbc (2 * Real.pi * a))‖ ^ 2 ≤
      3 * ((2 : ℝ)⁻¹ * (∫ η : ℝ, {η : ℝ | t - |a| ≤ |η|}.indicator
              (soninBumpSpectralDensity b c hbc) η) +
        (soninPacketMean b c hbc (2 * Real.pi * a)) ^ 2 *
          ∫ η : ℝ, soninBumpSpectralDensity b c hbc η) := by
  set μ : ℝ := soninPacketMean b c hbc (2 * Real.pi * a) with hμ
  set D : ℝ → ℝ := soninBumpSpectralDensity b c hbc with hD
  have hDnn : ∀ η, 0 ≤ D η := soninBumpSpectralDensity_nonneg b c hbc
  have hDint : Integrable D volume := integrable_soninBumpSpectralDensity b c hb hbc
  have hstart := norm_sq_sub_evenFourierCutoff_soninPacketEven_le_outer b c hb hbc t
    (2 * Real.pi * a)
  have hband := integral_indicator_soninPacketSpectralDensity_le b c hb hbc a
    {ξ : ℝ | t ≤ |ξ|} (measurableSet_outer t)
  have hT1 := integral_indicator_outer_comp_add_le hDint hDnn t (-a)
  have hT2 := integral_indicator_outer_comp_add_le hDint hDnn t a
  rw [abs_neg] at hT1
  have hT3 : ∫ ξ : ℝ, {ξ : ℝ | t ≤ |ξ|}.indicator D ξ ≤ ∫ η : ℝ, D η := by
    refine integral_mono (hDint.indicator (measurableSet_outer t)) hDint fun ξ => ?_
    by_cases hmem : ξ ∈ {ξ : ℝ | t ≤ |ξ|}
    · rw [Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem hmem]
      exact hDnn ξ
  have hμsq : (0 : ℝ) ≤ μ ^ 2 := sq_nonneg μ
  refine hstart.trans (hband.trans ?_)
  nlinarith [hT1, hT2, hT3, hμsq, mul_le_mul_of_nonneg_left hT3 hμsq]

/-- **High band capture.**  With the aperture on the same clock as the carrier but at a strictly
larger rate, the packet loses no energy above the aperture. -/
theorem tendsto_norm_sub_evenFourierCutoff_soninPacketEven_scaled
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) (q b₀ : ℝ) (hq : 0 < q) (hqb : q < b₀)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hr : Tendsto r atTop atTop) :
    Tendsto (fun n : ℕ => ‖soninPacketEven b c hb hbc (2 * Real.pi * (r n * q)) -
        evenFourierCutoff (r n * b₀)
          (soninPacketEven b c hb hbc (2 * Real.pi * (r n * q)))‖) atTop (𝓝 0) := by
  have hgap : ∀ n : ℕ, r n * b₀ - |r n * q| = r n * (b₀ - q) := by
    intro n
    rw [abs_of_pos (mul_pos (hrpos n) hq)]
    ring
  have hgapTendsto : Tendsto (fun n : ℕ => r n * (b₀ - q)) atTop atTop :=
    Filter.Tendsto.atTop_mul_const (by linarith : (0 : ℝ) < b₀ - q) hr
  have hTail := tendsto_integral_indicator_outer_soninBumpSpectralDensity b c hb hbc
    (fun n : ℕ => r n * (b₀ - q)) hgapTendsto
  have hfreq : Tendsto (fun n : ℕ => 2 * Real.pi * (r n * q)) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => r n * q) atTop atTop :=
      Filter.Tendsto.atTop_mul_const hq hr
    exact Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi) h1
  have hMean : Tendsto (fun n : ℕ =>
      soninPacketMean b c hbc (2 * Real.pi * (r n * q))) atTop (𝓝 0) :=
    (tendsto_soninPacketMean_atTop b c hb hbc).comp hfreq
  have hmaj : Tendsto (fun n : ℕ =>
      3 * ((2 : ℝ)⁻¹ * (∫ η : ℝ, {η : ℝ | r n * (b₀ - q) ≤ |η|}.indicator
              (soninBumpSpectralDensity b c hbc) η) +
        (soninPacketMean b c hbc (2 * Real.pi * (r n * q))) ^ 2 *
          ∫ η : ℝ, soninBumpSpectralDensity b c hbc η)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ *
        ∫ η : ℝ, {η : ℝ | r n * (b₀ - q) ≤ |η|}.indicator
          (soninBumpSpectralDensity b c hbc) η) atTop (𝓝 0) := by
      simpa using hTail.const_mul ((2 : ℝ)⁻¹)
    have h2 : Tendsto (fun n : ℕ =>
        (soninPacketMean b c hbc (2 * Real.pi * (r n * q))) ^ 2 *
          ∫ η : ℝ, soninBumpSpectralDensity b c hbc η) atTop (𝓝 0) := by
      simpa using (hMean.pow 2).mul_const (∫ η : ℝ, soninBumpSpectralDensity b c hbc η)
    simpa using (h1.add h2).const_mul (3 : ℝ)
  have hsq : Tendsto (fun n : ℕ => ‖soninPacketEven b c hb hbc (2 * Real.pi * (r n * q)) -
      evenFourierCutoff (r n * b₀)
        (soninPacketEven b c hb hbc (2 * Real.pi * (r n * q)))‖ ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => sq_nonneg _) (fun n => ?_) hmaj
    have hbnd := norm_sq_sub_evenFourierCutoff_soninPacketEven_le b c hb hbc
      (r n * b₀) (r n * q)
    rw [hgap n] at hbnd
    exact hbnd
  have hsqrt := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  simp only [Function.comp_def, Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun n => ?_
  rw [Real.sqrt_sq (norm_nonneg _)]

/-- **`(13)`, high horn.**  The dilated packet loses no energy above a fixed aperture beyond the
carrier ratio. -/
theorem tendsto_norm_sub_evenFourierCutoff_soninDilatedPacket
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) (q b₀ : ℝ) (hq : 0 < q) (hqb : q < b₀)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hr : Tendsto r atTop atTop) :
    Tendsto (fun n : ℕ =>
        ‖soninDilatedPacket b c hb hbc (2 * Real.pi * (r n * q)) (r n) (hrpos n) -
          evenFourierCutoff b₀
            (soninDilatedPacket b c hb hbc (2 * Real.pi * (r n * q)) (r n) (hrpos n))‖)
      atTop (𝓝 0) := by
  have hbase := tendsto_norm_sub_evenFourierCutoff_soninPacketEven_scaled b c hb hbc q b₀ hq hqb
    r hrpos hr
  refine hbase.congr fun n => ?_
  exact (norm_sub_evenFourierCutoff_evenDilationCLM_inv b₀ (r n) (hrpos n)
    (soninPacketEven b c hb hbc (2 * Real.pi * (r n * q)))).symm

end RHTower
