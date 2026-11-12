import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheWindowThresholdControlsTheFullHalfLineForm
import GaloisForLFunctions.HTGeometry.RealCausalExponentialReflection
import GaloisForLFunctions.HTGeometry.FourierModulusDeterminesActualCorrelation

/-!
# Causal reflection preserves actual prime and Gamma energy

The literal real Blaschke reflection has unchanged Fourier modulus. Its
Gamma integral is therefore unchanged, as is each translated correlation
and hence the complete prime sum. All claims use actual L¹∩L² profiles.
-/

noncomputable section
open MeasureTheory Filter Set Topology Zeta23 FourierTransform
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri HTGeometry
  CanonicalSystemOfTheWindowTower

private theorem memLp_cx_profile {F : ℝ → ℝ} (hF1 : Integrable F)
    (hF2 : Integrable (fun u => F u ^ 2)) : MemLp (cx F) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (hF1.ofReal (𝕜 := ℂ)).aestronglyMeasurable).mpr
  simpa only [cx, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hF2

/-- The literal paper Fourier modulus is unchanged at every real frequency. -/
theorem norm_paperFT_realCausalReflection {a : ℝ} (ha : 0 < a)
    {F : ℝ → ℝ} (hF : Integrable F) (r : ℝ) :
    ‖paperFT (cx (realCausalReflection a F)) r‖ = ‖paperFT (cx F) r‖ := by
  rw [paperFT_ofReal_eq_fourier, paperFT_ofReal_eq_fourier]
  have he : cx (realCausalReflection a F) = causalBlaschkeStep a (cx F) :=
    funext (coe_realCausalReflection a F)
  rw [he]
  exact norm_fourier_causalBlaschkeStep ha (hF.ofReal (𝕜 := ℂ)) _

/-- Full Gamma energy is invariant, with no additional regularity requirement. -/
theorem archForm_realCausalReflection {a : ℝ} (ha : 0 < a)
    {F : ℝ → ℝ} (hF : Integrable F) :
    archForm (realCausalReflection a F) = archForm F := by
  unfold archForm
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  change ‖paperFT (cx (realCausalReflection a F)) r‖ ^ 2 * EF.gammaBracket r =
    ‖paperFT (cx F) r‖ ^ 2 * EF.gammaBracket r
  rw [norm_paperFT_realCausalReflection ha hF]

/-- Every real translated correlation is preserved by the actual reflection. -/
theorem integral_mul_translate_realCausalReflection {a : ℝ} (ha : 0 < a)
    {F : ℝ → ℝ} (hF1 : Integrable F) (hF2 : Integrable (fun u => F u ^ 2)) (t : ℝ) :
    (∫ u, realCausalReflection a F u * realCausalReflection a F (u + t)) =
      ∫ u, F u * F (u + t) := by
  have hH1 := integrable_realCausalReflection ha hF1
  have hH2 := integrable_sq_realCausalReflection ha hF1 hF2
  have he : cx (realCausalReflection a F) = causalBlaschkeStep a (cx F) :=
    funext (coe_realCausalReflection a F)
  have hmod : ∀ᵐ ξ : ℝ, ‖𝓕 (cx (realCausalReflection a F)) ξ‖ = ‖𝓕 (cx F) ξ‖ :=
    Eventually.of_forall fun ξ => by
      rw [he]
      exact norm_fourier_causalBlaschkeStep ha (hF1.ofReal (𝕜 := ℂ)) ξ
  have hc := integral_conj_mul_translate_eq_of_fourier_norm
    (hH1.ofReal (𝕜 := ℂ)) (memLp_cx_profile hH1 hH2)
    (hF1.ofReal (𝕜 := ℂ)) (memLp_cx_profile hF1 hF2) hmod t
  simp only [cx, Complex.conj_ofReal, ← Complex.ofReal_mul] at hc
  rw [integral_complex_ofReal, integral_complex_ofReal] at hc
  exact Complex.ofReal_inj.mp hc

/-- Reflection preserves each actual prime term, hence the complete prime sum. -/
theorem primeSum_realCausalReflection {a : ℝ} (ha : 0 < a)
    {F : ℝ → ℝ} (hF1 : Integrable F) (hF2 : Integrable (fun u => F u ^ 2)) :
    primeSum (realCausalReflection a F) = primeSum F := by
  unfold primeSum
  apply tsum_congr
  intro n
  have hm := integral_mul_translate_realCausalReflection ha hF1 hF2 (-Real.log n)
  simp only [add_neg_eq_sub] at hm
  rw [hm, integral_mul_translate_realCausalReflection ha hF1 hF2]

/-- The resolvent inherits the actual exponential square integrability. -/
theorem integrable_exponential_realCausalConvolution {a : ℝ} (ha : 0 < a)
    {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    Integrable (fun u => realCausalConvolution a F u ^ 2 * Real.exp (-(8 * u))) := by
  have hx : 2 * Real.pi * (4 / Real.pi) = 8 := by field_simp [Real.pi_ne_zero] <;> ring
  have hw : Integrable (fun u => F u ^ 2 * Real.exp (-(2 * Real.pi * (4 / Real.pi) * u))) := by
    simpa only [hx] using hF.exponential
  simpa only [hx] using integrable_weighted_sq_realCausalConvolution
    (a := a) (x := 4 / Real.pi) (add_pos ha (by positivity)) hF.integrable hw

/-- At a real Laplace zero, reflection stays in the entire actual critical
form domain. The zero supplies support and the Fourier modulus controls Gamma energy. -/
theorem CriticalHalfLineEnergyDomain.realCausalReflection {a : ℝ} (ha : 0 < a)
    {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hz : (∫ u, Real.exp (Real.pi * a * u) * F u) = 0) :
    CriticalHalfLineEnergyDomain (realCausalReflection a F) := by
  refine ⟨measurable_realCausalReflection a hF.meas,
    integrable_realCausalReflection ha hF.integrable,
    integrable_sq_realCausalReflection ha hF.integrable hF.sq,
    ?_, realCausalReflection_support_of_laplace_zero a hF.support hz, ?_⟩
  · have hx : 2 * Real.pi * (4 / Real.pi) = 8 := by
      field_simp [Real.pi_ne_zero] <;> ring
    have hw : Integrable (fun u => F u ^ 2 * Real.exp (-(2 * Real.pi * (4 / Real.pi) * u))) := by
      simpa only [hx] using hF.exponential
    have hb : 0 < a + 4 / Real.pi := add_pos ha (by positivity)
    simpa only [hx] using integrable_weighted_sq_realCausalReflection hb hF.integrable hw
  · apply hF.gamma.congr
    refine Eventually.of_forall fun r => ?_
    change ‖paperFT (cx F) r‖ ^ 2 * EF.gammaBracket r =
      ‖paperFT (cx (realCausalReflection a F)) r‖ ^ 2 * EF.gammaBracket r
    rw [norm_paperFT_realCausalReflection ha hF.integrable]

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
