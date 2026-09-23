import GaloisForLFunctions.RHTower.SoninPacketFourierConcentration

/-!
# Band limits governed only by the carrier-to-edge gap

The band-energy bounds depend on the aperture and the carrier only through their difference, so the
two concentration limits hold for arbitrary aperture and carrier sequences whose gap grows — the
aperture need not be tied to the carrier by a common clock.

This is what the doubly contracted packet needs: there the carrier moves like `r` while the
aperture moves like `r²`.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter
open scoped Topology

/-- **Low band escape, gap form.**  If the carrier outruns the aperture, the packet keeps no energy
inside the band. -/
theorem tendsto_norm_evenFourierCutoff_soninPacketEven_gap
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) (t A : ℕ → ℝ)
    (hgap : Tendsto (fun n : ℕ => |A n| - t n) atTop atTop)
    (hA : Tendsto (fun n : ℕ => 2 * Real.pi * A n) atTop atTop) :
    Tendsto (fun n : ℕ => ‖evenFourierCutoff (t n)
        (soninPacketEven b c hb hbc (2 * Real.pi * A n))‖) atTop (𝓝 0) := by
  have hTail := tendsto_integral_indicator_outer_soninBumpSpectralDensity b c hb hbc
    (fun n : ℕ => |A n| - t n) hgap
  have hMean : Tendsto (fun n : ℕ =>
      soninPacketMean b c hbc (2 * Real.pi * A n)) atTop (𝓝 0) :=
    (tendsto_soninPacketMean_atTop b c hb hbc).comp hA
  have hmaj : Tendsto (fun n : ℕ =>
      3 * ((2 : ℝ)⁻¹ * (∫ η : ℝ, {η : ℝ | |A n| - t n ≤ |η|}.indicator
              (soninBumpSpectralDensity b c hbc) η) +
        (soninPacketMean b c hbc (2 * Real.pi * A n)) ^ (2 : ℕ) *
          ∫ η : ℝ, soninBumpSpectralDensity b c hbc η)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ *
        ∫ η : ℝ, {η : ℝ | |A n| - t n ≤ |η|}.indicator
          (soninBumpSpectralDensity b c hbc) η) atTop (𝓝 0) := by
      simpa using hTail.const_mul ((2 : ℝ)⁻¹)
    have h2 : Tendsto (fun n : ℕ =>
        (soninPacketMean b c hbc (2 * Real.pi * A n)) ^ (2 : ℕ) *
          ∫ η : ℝ, soninBumpSpectralDensity b c hbc η) atTop (𝓝 0) := by
      simpa using (hMean.pow 2).mul_const (∫ η : ℝ, soninBumpSpectralDensity b c hbc η)
    simpa using (h1.add h2).const_mul (3 : ℝ)
  have hsq : Tendsto (fun n : ℕ => ‖evenFourierCutoff (t n)
      (soninPacketEven b c hb hbc (2 * Real.pi * A n))‖ ^ (2 : ℕ)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => sq_nonneg _) (fun n => ?_) hmaj
    exact norm_sq_evenFourierCutoff_soninPacketEven_le b c hb hbc (t n) (A n)
  have hsqrt := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  simp only [Function.comp_def, Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun n => ?_
  rw [Real.sqrt_sq (norm_nonneg _)]

/-- **High band capture, gap form.**  If the aperture outruns the carrier, the packet loses no
energy above the band. -/
theorem tendsto_norm_sub_evenFourierCutoff_soninPacketEven_gap
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) (t A : ℕ → ℝ)
    (hgap : Tendsto (fun n : ℕ => t n - |A n|) atTop atTop)
    (hA : Tendsto (fun n : ℕ => 2 * Real.pi * A n) atTop atTop) :
    Tendsto (fun n : ℕ => ‖soninPacketEven b c hb hbc (2 * Real.pi * A n) -
        evenFourierCutoff (t n) (soninPacketEven b c hb hbc (2 * Real.pi * A n))‖)
      atTop (𝓝 0) := by
  have hTail := tendsto_integral_indicator_outer_soninBumpSpectralDensity b c hb hbc
    (fun n : ℕ => t n - |A n|) hgap
  have hMean : Tendsto (fun n : ℕ =>
      soninPacketMean b c hbc (2 * Real.pi * A n)) atTop (𝓝 0) :=
    (tendsto_soninPacketMean_atTop b c hb hbc).comp hA
  have hmaj : Tendsto (fun n : ℕ =>
      3 * ((2 : ℝ)⁻¹ * (∫ η : ℝ, {η : ℝ | t n - |A n| ≤ |η|}.indicator
              (soninBumpSpectralDensity b c hbc) η) +
        (soninPacketMean b c hbc (2 * Real.pi * A n)) ^ (2 : ℕ) *
          ∫ η : ℝ, soninBumpSpectralDensity b c hbc η)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ *
        ∫ η : ℝ, {η : ℝ | t n - |A n| ≤ |η|}.indicator
          (soninBumpSpectralDensity b c hbc) η) atTop (𝓝 0) := by
      simpa using hTail.const_mul ((2 : ℝ)⁻¹)
    have h2 : Tendsto (fun n : ℕ =>
        (soninPacketMean b c hbc (2 * Real.pi * A n)) ^ (2 : ℕ) *
          ∫ η : ℝ, soninBumpSpectralDensity b c hbc η) atTop (𝓝 0) := by
      simpa using (hMean.pow 2).mul_const (∫ η : ℝ, soninBumpSpectralDensity b c hbc η)
    simpa using (h1.add h2).const_mul (3 : ℝ)
  have hsq : Tendsto (fun n : ℕ => ‖soninPacketEven b c hb hbc (2 * Real.pi * A n) -
      evenFourierCutoff (t n) (soninPacketEven b c hb hbc (2 * Real.pi * A n))‖ ^ (2 : ℕ))
      atTop (𝓝 0) := by
    refine squeeze_zero (fun n => sq_nonneg _) (fun n => ?_) hmaj
    exact norm_sq_sub_evenFourierCutoff_soninPacketEven_le b c hb hbc (t n) (A n)
  have hsqrt := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  simp only [Function.comp_def, Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun n => ?_
  rw [Real.sqrt_sq (norm_nonneg _)]

end RHTower
