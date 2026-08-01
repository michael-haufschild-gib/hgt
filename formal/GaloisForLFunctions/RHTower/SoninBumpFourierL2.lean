import GaloisForLFunctions.RHTower.SoninPacketFourierEscape
import GaloisForLFunctions.RHTower.SoninDilatedPacketCompactVanishing
import GaloisForLFunctions.RHTower.SoninOuterTailIntegral

/-!
# The profile's Fourier transform as a square-integrable density

The annular profile is continuous with compact support, hence in `L¹ ∩ L²`, so its classical
Fourier integral is the coefficient function of an `L²` vector and its squared modulus is an
integrable energy density.  That density is the fixed function whose tails control every
frequency-concentration estimate for the wavepacket family.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter
open scoped Topology FourierTransform

/-- The `L²` Fourier transform of the profile is the classical Fourier integral. -/
theorem fourierUnitary_soninBumpL2_coeFn (b c : ℝ) (hb : 0 < b) (hbc : b < c) :
    ((fourierUnitary (soninBumpL2 b c hb hbc) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      fun ξ : ℝ => 𝓕 (fun x : ℝ => (soninAnnulusBump b c hbc x : ℂ)) ξ := by
  set f : SoninL2 := soninBumpL2 b c hb hbc with hfdef
  have hcoe : (f : ℝ → ℂ) =ᵐ[volume] fun x : ℝ => (soninAnnulusBump b c hbc x : ℂ) :=
    MemLp.coeFn_toLp (memLp_soninAnnulusBump b c hb hbc)
  have hint : Integrable (f : ℝ → ℂ) :=
    ((integrable_soninAnnulusBump b c hb hbc).ofReal).congr hcoe.symm
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

/-- The profile's spectral energy density. -/
def soninBumpSpectralDensity (b c : ℝ) (hbc : b < c) : ℝ → ℝ := fun η =>
  ‖𝓕 (fun x : ℝ => (soninAnnulusBump b c hbc x : ℂ)) η‖ ^ 2

theorem soninBumpSpectralDensity_nonneg (b c : ℝ) (hbc : b < c) (η : ℝ) :
    0 ≤ soninBumpSpectralDensity b c hbc η := by
  unfold soninBumpSpectralDensity
  positivity

/-- **The spectral energy density is integrable.**  This is Plancherel for the profile. -/
theorem integrable_soninBumpSpectralDensity (b c : ℝ) (hb : 0 < b) (hbc : b < c) :
    Integrable (soninBumpSpectralDensity b c hbc) volume := by
  have hLp : Integrable (fun η : ℝ =>
      ‖((fourierUnitary (soninBumpL2 b c hb hbc) : SoninL2) : ℝ → ℂ) η‖ ^ 2) volume := by
    have := (Lp.memLp (fourierUnitary (soninBumpL2 b c hb hbc))).integrable_norm_rpow
      (by norm_num) (by norm_num)
    simpa using this
  refine hLp.congr ?_
  filter_upwards [fourierUnitary_soninBumpL2_coeFn b c hb hbc] with η hη
  unfold soninBumpSpectralDensity
  rw [hη]

/-- The total spectral energy of the profile. -/
theorem integral_soninBumpSpectralDensity_nonneg (b c : ℝ) (hbc : b < c) :
    0 ≤ ∫ η : ℝ, soninBumpSpectralDensity b c hbc η :=
  integral_nonneg (soninBumpSpectralDensity_nonneg b c hbc)

/-- **The profile's spectral tails vanish.**  Beyond a growing radius the profile carries no
spectral energy. -/
theorem tendsto_integral_indicator_outer_soninBumpSpectralDensity
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) :
    Tendsto (fun n : ℕ =>
        ∫ η : ℝ, {η : ℝ | R n ≤ |η|}.indicator (soninBumpSpectralDensity b c hbc) η)
      atTop (𝓝 0) :=
  tendsto_integral_indicator_outer_atTop (soninBumpSpectralDensity_nonneg b c hbc)
    (integrable_soninBumpSpectralDensity b c hb hbc) R hR

end RHTower
