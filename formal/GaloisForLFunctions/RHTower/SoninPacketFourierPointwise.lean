import GaloisForLFunctions.RHTower.SoninPacketL2
import GaloisForLFunctions.RHTower.SoninFourierUniformDecay

/-!
# The Fourier transform of the wavepacket dies pointwise, uniformly bounded

The Fourier transform of the wavepacket at a fixed frequency is the pairing of the wavepacket
against a unimodular weight, so it tends to zero by the weak escape estimate.  Together with the
uniform bound coming from `|u| <= 2 phi` this is exactly the data a dominated-convergence argument
needs to push the whole central Fourier band to zero.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter
open scoped Topology FourierTransform Real

/-- The Fourier transform of the wavepacket, written as an explicit pairing. -/
theorem fourier_soninPacket_eq (b c : ℝ) (hbc : b < c) (κ ξ : ℝ) :
    𝓕 (fun x : ℝ => (soninPacket b c hbc κ x : ℂ)) ξ =
      ∫ x : ℝ, Complex.exp ((↑(-2 * Real.pi * x * ξ) : ℂ) * Complex.I) *
        (soninPacket b c hbc κ x : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  rfl

/-- **Pointwise Fourier escape.**  At every fixed frequency the transform of the wavepacket tends
to zero. -/
theorem tendsto_fourier_soninPacket_atTop (b c : ℝ) (hb : 0 < b) (hbc : b < c) (ξ : ℝ) :
    Tendsto (fun κ : ℝ => 𝓕 (fun x : ℝ => (soninPacket b c hbc κ x : ℂ)) ξ) atTop (𝓝 0) := by
  have hchar : Continuous fun x : ℝ =>
      Complex.exp ((↑(-2 * Real.pi * x * ξ) : ℂ) * Complex.I) := by
    exact Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const)
  have hint : Integrable (fun x : ℝ =>
      Complex.exp ((↑(-2 * Real.pi * x * ξ) : ℂ) * Complex.I) *
        (soninAnnulusBump b c hbc x : ℂ)) := by
    refine Continuous.integrable_of_hasCompactSupport
      (hchar.mul (Complex.continuous_ofReal.comp (continuous_soninAnnulusBump b c hbc))) ?_
    refine HasCompactSupport.of_support_subset_isCompact
      (hasCompactSupport_soninAnnulusBump b c hb hbc) ?_
    intro x hx
    refine subset_tsupport _ ?_
    intro h0
    exact hx (by simp [h0])
  have hpair := tendsto_integral_mul_soninPacket_atTop b c hb hbc hint
  refine hpair.congr fun κ => (fourier_soninPacket_eq b c hbc κ ξ).symm

/-- **Uniform bound on the transform.**  The wavepacket never exceeds twice the profile, so its
transform never exceeds twice the profile's mass. -/
theorem norm_fourier_soninPacket_le (b c : ℝ) (hb : 0 < b) (hbc : b < c) (κ ξ : ℝ) :
    ‖𝓕 (fun x : ℝ => (soninPacket b c hbc κ x : ℂ)) ξ‖ ≤
      2 * ∫ x : ℝ, soninAnnulusBump b c hbc x := by
  rw [fourier_soninPacket_eq b c hbc κ ξ]
  have hbound : ∀ x : ℝ,
      ‖Complex.exp ((↑(-2 * Real.pi * x * ξ) : ℂ) * Complex.I) *
        (soninPacket b c hbc κ x : ℂ)‖ ≤ 2 * soninAnnulusBump b c hbc x := by
    intro x
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
    exact abs_soninPacket_le b c hb hbc κ x
  calc ‖∫ x : ℝ, Complex.exp ((↑(-2 * Real.pi * x * ξ) : ℂ) * Complex.I) *
          (soninPacket b c hbc κ x : ℂ)‖
      ≤ ∫ x : ℝ, 2 * soninAnnulusBump b c hbc x := by
        refine norm_integral_le_of_norm_le ?_ (Filter.Eventually.of_forall hbound)
        exact (integrable_soninAnnulusBump b c hb hbc).const_mul 2
    _ = 2 * ∫ x : ℝ, soninAnnulusBump b c hbc x := integral_const_mul _ _

end RHTower
