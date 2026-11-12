import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ModulatedCausalExponentialReflection

/-!
# Exact weighted energy loss for complex-rate reflections

Modulation preserves pointwise norms and commutes with real exponential
weights. Conjugating the verified real-rate reflection therefore preserves
its actual weighted L² domain and its exact positive energy defect.
-/

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped Convolution

namespace GaloisForLFunctions.HTGeometry
open _root_.RHTower

/-- The reflected complex profile remains integrable. -/
theorem integrable_modulatedCausalReflection {a : ℝ} (ha : 0 < a) (b : ℝ)
    {f : ℝ → ℂ} (hf : Integrable f) : Integrable (modulatedCausalReflection a b f) := by
  exact hf.neg.add ((integrable_modulatedCausalConvolution ha b hf).const_mul (2 * a : ℂ))

/-- The modulated resolvent preserves the unweighted actual square domain. -/
theorem memLp_modulatedCausalConvolution {a : ℝ} (ha : 0 < a) (b : ℝ)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    MemLp (modulatedCausalConvolution a b f) 2 volume := by
  rw [modulatedCausalConvolution_eq_conjugate]
  exact memLp_two_causalModulation (-b)
    (memLp_causalExponentialConvolution ha (memLp_two_causalModulation b hf))

/-- The modulated reflection preserves the unweighted actual square domain. -/
theorem memLp_modulatedCausalReflection {a : ℝ} (ha : 0 < a) (b : ℝ)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    MemLp (modulatedCausalReflection a b f) 2 volume :=
  hf.neg.add ((memLp_modulatedCausalConvolution ha b hf).const_mul (2 * a : ℂ))

/-- The modulated resolvent preserves the actual weighted square domain. -/
theorem memLp_weighted_modulatedCausalConvolution {a x : ℝ} (hb : 0 < a + x) (b : ℝ)
    {f : ℝ → ℂ} (hf : MemLp (causalLaplaceWeighted x f) 2 volume) :
    MemLp (causalLaplaceWeighted x (modulatedCausalConvolution a b f)) 2 volume := by
  rw [modulatedCausalConvolution_eq_conjugate, causalLaplaceWeighted_causalModulation]
  apply memLp_two_causalModulation
  apply memLp_weighted_causalExponentialConvolution hb
  rw [causalLaplaceWeighted_causalModulation]
  exact memLp_two_causalModulation b hf

/-- Complex-rate reflection preserves the actual weighted square domain. -/
theorem memLp_weighted_modulatedCausalReflection {a x : ℝ} (hb : 0 < a + x) (b : ℝ)
    {f : ℝ → ℂ} (hf : MemLp (causalLaplaceWeighted x f) 2 volume) :
    MemLp (causalLaplaceWeighted x (modulatedCausalReflection a b f)) 2 volume := by
  rw [modulatedCausalReflection_eq_conjugate, causalLaplaceWeighted_causalModulation]
  apply memLp_two_causalModulation
  apply memLp_weighted_causalBlaschkeStep hb
  rw [causalLaplaceWeighted_causalModulation]
  exact memLp_two_causalModulation b hf

/-- Frequency modulation does not change the exact weighted reflection defect. -/
theorem integral_weighted_modulatedCausalReflection_energy {a x : ℝ}
    (hb : 0 < a + x) (b : ℝ) {f : ℝ → ℂ}
    (hf : MemLp (causalLaplaceWeighted x f) 2 volume) :
    (∫ u, ‖causalLaplaceWeighted x f u‖ ^ 2) =
      (∫ u, ‖causalLaplaceWeighted x (modulatedCausalReflection a b f) u‖ ^ 2) +
      (4 * a * x) * (∫ u, ‖causalLaplaceWeighted x (modulatedCausalConvolution a b f) u‖ ^ 2) := by
  have hm : MemLp (causalLaplaceWeighted x (causalModulation b f)) 2 volume := by
    rw [causalLaplaceWeighted_causalModulation]
    exact memLp_two_causalModulation b hf
  have he := integral_weighted_causalBlaschkeStep_energy hb hm
  simp only [causalLaplaceWeighted_causalModulation, norm_causalModulation] at he
  rw [modulatedCausalReflection_eq_conjugate, modulatedCausalConvolution_eq_conjugate]
  simpa only [causalLaplaceWeighted_causalModulation, norm_causalModulation] using he

/-- Every real Fourier modulus is preserved by the complex-rate reflection. -/
theorem norm_fourier_modulatedCausalReflection {a : ℝ} (ha : 0 < a) (b : ℝ)
    {f : ℝ → ℂ} (hf : Integrable f) (ξ : ℝ) :
    ‖𝓕 (modulatedCausalReflection a b f) ξ‖ = ‖𝓕 f ξ‖ := by
  rw [modulatedCausalReflection_eq_conjugate, fourier_causalModulation,
    norm_fourier_causalBlaschkeStep ha (integrable_causalModulation b hf),
    fourier_causalModulation]
  congr 2
  ring

/-- A zero modulated resolvent forces its actual integrable input to vanish. -/
theorem ae_eq_zero_of_modulatedCausalConvolution_ae_zero {a : ℝ} (ha : 0 < a) (b : ℝ)
    {f : ℝ → ℂ} (hf : Integrable f)
    (hz : modulatedCausalConvolution a b f =ᵐ[volume] 0) : f =ᵐ[volume] 0 := by
  rw [modulatedCausalConvolution_eq_conjugate] at hz
  have hk : (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ]
      causalModulation b f) =ᵐ[volume] 0 := by
    filter_upwards [hz] with u hu
    have hn := congrArg norm hu
    change ‖causalModulation (-b)
      (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] causalModulation b f) u‖ = ‖(0 : ℂ)‖ at hn
    rw [norm_causalModulation, norm_zero] at hn
    exact norm_eq_zero.mp hn
  have hm := ae_eq_zero_of_causalExponentialConvolution_ae_zero ha
    (integrable_causalModulation b hf) hk
  filter_upwards [hm] with u hu
  have hn := congrArg norm hu
  change ‖causalModulation b f u‖ = ‖(0 : ℂ)‖ at hn
  rw [norm_causalModulation, norm_zero] at hn
  exact norm_eq_zero.mp hn

end GaloisForLFunctions.HTGeometry
