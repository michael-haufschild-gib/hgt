import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCriticalHalfLineFormHasItsActualDomain
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.PairedCausalReflectionPreservesPoleProduct

/-!
# Conjugate reflection preserves the actual critical-state domain

The real representative inherits physical and exponentially weighted square
integrability from the complex pair. Its unchanged Fourier modulus supplies
full Gamma integrability; the two Laplace zeros supply exact half-line support.
-/

noncomputable section
open MeasureTheory Filter Set Topology Zeta23 FourierTransform
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri HTGeometry

/-- The actual real domain supplies its complex L² representative. -/
theorem CriticalHalfLineEnergyDomain.memLp_complex {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) : MemLp (cx F) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (hF.integrable.ofReal (𝕜 := ℂ)).aestronglyMeasurable).mpr
  apply hF.sq.congr
  refine Eventually.of_forall fun u => ?_
  change F u ^ 2 = ‖(F u : ℂ)‖ ^ 2
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The eighth exponential energy is the squared complex Laplace weight. -/
theorem CriticalHalfLineEnergyDomain.memLp_weightedComplex {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    MemLp (causalLaplaceWeighted (4 / Real.pi) (cx F)) 2 volume := by
  have hm : AEStronglyMeasurable (causalLaplaceWeighted (4 / Real.pi) (cx F)) :=
    (by fun_prop : Continuous (fun u : ℝ =>
      Complex.exp (-(Real.pi * (4 / Real.pi) * u : ℝ)))).aestronglyMeasurable.mul
        (hF.integrable.ofReal (𝕜 := ℂ)).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply hF.exponential.congr
  refine Eventually.of_forall fun u => ?_
  change F u ^ 2 * Real.exp (-(8 * u)) =
    ‖causalLaplaceWeighted (4 / Real.pi) (cx F) u‖ ^ 2
  rw [norm_sq_causalLaplaceWeighted,
    show 2 * Real.pi * (4 / Real.pi) = 8 by field_simp; norm_num]
  change F u ^ 2 * Real.exp (-(8 * u)) = ‖(F u : ℂ)‖ ^ 2 * Real.exp (-(8 * u))
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The literal real representative preserves every real Fourier modulus. -/
theorem norm_fourier_realPairedCausalReflection {a : ℝ} (ha : 0 < a) (b : ℝ)
    {F : ℝ → ℝ} (hF : Integrable F) (ξ : ℝ) :
    ‖𝓕 (cx (realPairedCausalReflection a b F)) ξ‖ = ‖𝓕 (cx F) ξ‖ := by
  have he : cx (realPairedCausalReflection a b F) =ᵐ[volume]
      pairedCausalReflection a b (cx F) := coe_realPairedCausalReflection_ae ha b hF
  rw [Real.fourier_congr_ae he, pairedCausalReflection]
  calc
    _ = ‖𝓕 (modulatedCausalReflection a b (cx F)) ξ‖ :=
      norm_fourier_modulatedCausalReflection ha (-b)
        (integrable_modulatedCausalReflection ha b (hF.ofReal (𝕜 := ℂ))) ξ
    _ = _ := norm_fourier_modulatedCausalReflection ha b (hF.ofReal (𝕜 := ℂ)) ξ

/-- The paper Fourier normalization has the same preserved modulus. -/
theorem norm_paperFT_realPairedCausalReflection {a : ℝ} (ha : 0 < a) (b : ℝ)
    {F : ℝ → ℝ} (hF : Integrable F) (r : ℝ) :
    ‖paperFT (cx (realPairedCausalReflection a b F)) r‖ = ‖paperFT (cx F) r‖ := by
  rw [paperFT_ofReal_eq_fourier, paperFT_ofReal_eq_fourier]
  exact norm_fourier_realPairedCausalReflection ha b hF _

/-- The entire Gamma energy is unchanged by the real conjugate pair. -/
theorem archForm_realPairedCausalReflection {a : ℝ} (ha : 0 < a) (b : ℝ)
    {F : ℝ → ℝ} (hF : Integrable F) :
    archForm (realPairedCausalReflection a b F) = archForm F := by
  unfold archForm
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  change ‖paperFT (cx (realPairedCausalReflection a b F)) r‖ ^ 2 * EF.gammaBracket r =
    ‖paperFT (cx F) r‖ ^ 2 * EF.gammaBracket r
  rw [norm_paperFT_realPairedCausalReflection ha b hF]

/-- A conjugate pair at a nonreal zero stays in every part of the actual domain. -/
theorem CriticalHalfLineEnergyDomain.realPairedCausalReflection {a : ℝ} (ha : 0 < a)
    {b : ℝ} (hb : b ≠ 0) {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hz : negativeHalfLineLaplace (cx F) (modulatedLaplaceRate a b) = 0) :
    CriticalHalfLineEnergyDomain (realPairedCausalReflection a b F) := by
  refine ⟨measurable_realPairedCausalReflection a b hF.meas,
    integrable_realPairedCausalReflection ha b hF.integrable, ?_, ?_, ?_, ?_⟩
  · have hm := memLp_realPairedCausalReflection ha b hF.integrable hF.memLp_complex
    have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
    apply hi.congr
    exact Eventually.of_forall fun u => by
      dsimp only
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  · have hm := memLp_weighted_realPairedCausalReflection ha (add_pos ha (by positivity)) b
      hF.integrable hF.memLp_weightedComplex
    have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
    apply hi.congr
    refine Eventually.of_forall fun u => ?_
    change ‖causalLaplaceWeighted (4 / Real.pi)
      (fun t => (HTGeometry.realPairedCausalReflection a b F t : ℂ)) u‖ ^ 2 =
      HTGeometry.realPairedCausalReflection a b F u ^ 2 * Real.exp (-(8 * u))
    rw [norm_sq_causalLaplaceWeighted,
      show 2 * Real.pi * (4 / Real.pi) = 8 by field_simp; norm_num]
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  · intro u hu
    rw [HTGeometry.realPairedCausalReflection,
      pairedCausalReflection_support_of_nonreal_zero ha hb hF.integrable hF.support hz u hu,
      Complex.zero_re]
  · apply hF.gamma.congr
    refine Eventually.of_forall fun r => ?_
    change ‖paperFT (cx F) r‖ ^ 2 * EF.gammaBracket r =
      ‖paperFT (cx (HTGeometry.realPairedCausalReflection a b F)) r‖ ^ 2 * EF.gammaBracket r
    rw [norm_paperFT_realPairedCausalReflection ha b hF.integrable]

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
