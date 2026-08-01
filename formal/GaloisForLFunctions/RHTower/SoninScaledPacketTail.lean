import GaloisForLFunctions.RHTower.SoninScaledMeanBound

/-!
# The packet's spectral tail

The packet is the profile times a cosine, minus the profile times the mean.  The cosine modulation
rule turns the first into two shifted profile transforms and the second is a multiple of one, so the
packet's spectral magnitude is bounded by three profile tails — at the shifted frequencies and at
the frequency itself.

Each profile tail is the reference tail at the rescaled argument, so the whole bound is a function
of the half-width times the frequencies involved.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory
open scoped FourierTransform

/-- The reference tail bound at a given frequency. -/
def soninScaledBumpTailBound (δ η : ℝ) : ℝ :=
  δ * ‖𝓕 soninUnitBumpC (δ * η)‖ + δ * ‖𝓕 soninUnitBumpC (δ * -η)‖

theorem norm_fourier_soninScaledAnnulusBump_le' (m δ : ℝ) (hδ : 0 < δ) (η : ℝ) :
    ‖𝓕 (fun x : ℝ => ((soninScaledAnnulusBump m δ x : ℝ) : ℂ)) η‖ ≤
      soninScaledBumpTailBound δ η :=
  norm_fourier_soninScaledAnnulusBump_le m δ hδ η

theorem soninScaledBumpTailBound_nonneg (δ η : ℝ) (hδ : 0 < δ) :
    0 ≤ soninScaledBumpTailBound δ η := by
  rw [soninScaledBumpTailBound]
  positivity

/-- The profile is integrable after complexification. -/
theorem integrable_soninScaledAnnulusBumpC (m δ : ℝ) (hδ : 0 < δ) :
    Integrable fun x : ℝ => ((soninScaledAnnulusBump m δ x : ℝ) : ℂ) :=
  (integrable_soninScaledAnnulusBump m δ hδ).ofReal

/-- **The packet's spectral tail.**  Three profile tails: two shifted, one weighted by the mean. -/
theorem norm_fourier_soninScaledPacket_le (m δ w₀ ξ : ℝ) (hδ : 0 < δ) :
    ‖𝓕 (fun x : ℝ => (soninScaledPacket m δ (2 * Real.pi * w₀) x : ℂ)) ξ‖ ≤
      2⁻¹ * soninScaledBumpTailBound δ (ξ - w₀) +
        2⁻¹ * soninScaledBumpTailBound δ (ξ + w₀) +
          |soninScaledPacketMean m δ (2 * Real.pi * w₀)| *
            soninScaledBumpTailBound δ ξ := by
  set μ : ℝ := soninScaledPacketMean m δ (2 * Real.pi * w₀) with hμ
  set B : ℝ → ℂ := fun x : ℝ => ((soninScaledAnnulusBump m δ x : ℝ) : ℂ) with hB
  have hBint : Integrable B := integrable_soninScaledAnnulusBumpC m δ hδ
  have hcosint : Integrable fun x : ℝ => B x * ((Real.cos (2 * Real.pi * w₀ * x) : ℝ) : ℂ) := by
    refine hBint.mul_bdd ?_ ?_
    · exact (Complex.continuous_ofReal.comp
        (Real.continuous_cos.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
    · filter_upwards with x
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact Real.abs_cos_le_one _
  have hmulint : Integrable fun x : ℝ => -((μ : ℂ) * B x) := (hBint.const_mul (μ : ℂ)).neg
  have hsplit : (fun x : ℝ => (soninScaledPacket m δ (2 * Real.pi * w₀) x : ℂ)) =
      fun x : ℝ => B x * ((Real.cos (2 * Real.pi * w₀ * x) : ℝ) : ℂ) + -((μ : ℂ) * B x) := by
    funext x
    rw [soninScaledPacket]
    push_cast
    ring
  rw [hsplit, GaloisForLFunctions.HTGeometry.fourierIntegral_add hcosint hmulint ξ,
    GaloisForLFunctions.HTGeometry.fourierIntegral_mul_cos hBint w₀ ξ]
  have hneg : 𝓕 (fun x : ℝ => -((μ : ℂ) * B x)) ξ = -((μ : ℂ) * 𝓕 B ξ) := by
    have h : (fun x : ℝ => -((μ : ℂ) * B x)) = fun x : ℝ => (-(μ : ℂ)) * B x := by
      funext x
      ring
    rw [h, GaloisForLFunctions.HTGeometry.fourierIntegral_const_mul B (-(μ : ℂ)) ξ]
    ring
  rw [hneg]
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖(2 : ℂ)⁻¹ * 𝓕 B (ξ - w₀) + (2 : ℂ)⁻¹ * 𝓕 B (ξ + w₀)‖ ≤
      2⁻¹ * soninScaledBumpTailBound δ (ξ - w₀) +
        2⁻¹ * soninScaledBumpTailBound δ (ξ + w₀) := by
    refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_) <;>
      · rw [norm_mul]
        simp only [norm_inv, Complex.norm_ofNat]
        exact mul_le_mul_of_nonneg_left
          (norm_fourier_soninScaledAnnulusBump_le' m δ hδ _) (by norm_num)
  have h2 : ‖-((μ : ℂ) * 𝓕 B ξ)‖ ≤ |μ| * soninScaledBumpTailBound δ ξ := by
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (norm_fourier_soninScaledAnnulusBump_le' m δ hδ ξ) (abs_nonneg _)
  linarith

end RHTower
