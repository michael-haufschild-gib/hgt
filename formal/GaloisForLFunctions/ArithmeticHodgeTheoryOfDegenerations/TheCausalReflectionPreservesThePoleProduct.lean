import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCausalReflectionPreservesPrimeAndGammaEnergy
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CausalExponentialLaplaceReflection

/-!
# Pole-product preservation on the actual half-line domain

A real Laplace zero permits both causal and anti-causal resolvent formulas.
Their linear moment laws preserve the opposite half-pole product, including
the resonant rate. Every weighted-integrability input follows from the actual
half-line energy domain.
-/

noncomputable section
open MeasureTheory Filter Set Topology Zeta23
open scoped Convolution
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri HTGeometry

private def poleLaplaceRate : ℝ := 1 / (2 * Real.pi)

private theorem pi_mul_poleLaplaceRate : Real.pi * poleLaplaceRate = 1 / 2 := by
  unfold poleLaplaceRate
  field_simp [Real.pi_ne_zero] <;> ring

private theorem poleLaplaceData {F : ℝ → ℝ} (hF : WeightedTwo F) :
    Integrable (causalLaplaceWeighted poleLaplaceRate (cx F)) ∧
    Integrable (causalLaplaceWeighted (-poleLaplaceRate) (cx F)) ∧
    causalLaplaceIntegral poleLaplaceRate (cx F) = ((coshHalfMoment F - sinhHalfMoment F : ℝ) : ℂ) ∧
    causalLaplaceIntegral (-poleLaplaceRate) (cx F) = ((coshHalfMoment F + sinhHalfMoment F : ℝ) : ℂ) := by
  have hc := (abs_integral_mul_kernel_le hF
    (Real.continuous_cosh.comp (continuous_id.div_const 2)) abs_cosh_half_le_exp).1
  have hs := (abs_integral_mul_kernel_le hF
    (Real.continuous_sinh.comp (continuous_id.div_const 2)) abs_sinh_half_le_exp).1
  have hem (u : ℝ) : F u * Real.exp (-u / 2) =
      F u * Real.cosh (u / 2) - F u * Real.sinh (u / 2) := by
    rw [Real.cosh_eq, Real.sinh_eq, show -(u / 2) = -u / 2 by ring]
    ring
  have hep (u : ℝ) : F u * Real.exp (u / 2) =
      F u * Real.cosh (u / 2) + F u * Real.sinh (u / 2) := by
    rw [Real.cosh_eq, Real.sinh_eq]
    ring
  have him : Integrable (fun u => F u * Real.exp (-u / 2)) := by
    apply (hc.sub hs).congr
    exact Eventually.of_forall fun u => (hem u).symm
  have hip : Integrable (fun u => F u * Real.exp (u / 2)) := by
    apply (hc.add hs).congr
    exact Eventually.of_forall fun u => (hep u).symm
  have hargm (u : ℝ) : -(Real.pi * poleLaplaceRate * u) = -u / 2 := by
    rw [pi_mul_poleLaplaceRate]
    ring
  have hargp (u : ℝ) : -(Real.pi * (-poleLaplaceRate) * u) = u / 2 := by
    rw [mul_neg, neg_mul, neg_neg, pi_mul_poleLaplaceRate]
    ring
  have hwm : causalLaplaceWeighted poleLaplaceRate (cx F) =
      fun u => ((F u * Real.exp (-u / 2) : ℝ) : ℂ) := by
    funext u
    change causalLaplaceWeighted poleLaplaceRate (fun t => (F t : ℂ)) u = _
    rw [causalLaplaceWeighted_real_eq, hargm]
  have hwp : causalLaplaceWeighted (-poleLaplaceRate) (cx F) =
      fun u => ((F u * Real.exp (u / 2) : ℝ) : ℂ) := by
    funext u
    change causalLaplaceWeighted (-poleLaplaceRate) (fun t => (F t : ℂ)) u = _
    rw [causalLaplaceWeighted_real_eq, hargp]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hwm]
    exact him.ofReal (𝕜 := ℂ)
  · rw [hwp]
    exact hip.ofReal (𝕜 := ℂ)
  · unfold causalLaplaceIntegral
    rw [hwm, integral_complex_ofReal]
    congr 1
    change (∫ u, F u * Real.exp (-u / 2)) =
      (∫ u, F u * Real.cosh (u / 2)) - ∫ u, F u * Real.sinh (u / 2)
    simp_rw [hem]
    exact integral_sub hc hs
  · unfold causalLaplaceIntegral
    rw [hwp, integral_complex_ofReal]
    congr 1
    change (∫ u, F u * Real.exp (u / 2)) =
      (∫ u, F u * Real.cosh (u / 2)) + ∫ u, F u * Real.sinh (u / 2)
    simp_rw [hep]
    exact integral_add hc hs

/-- The resolvent has finite prime-source weight at a Laplace zero. -/
theorem weighted_realCausalConvolution {a : ℝ} (ha : 0 < a)
    {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hz : (∫ u, Real.exp (Real.pi * a * u) * F u) = 0) :
    WeightedTwo (realCausalConvolution a F) := by
  have h1 := integrable_realCausalConvolution ha hF.integrable
  have h2 := integrable_sq_realCausalConvolution ha hF.integrable hF.sq
  have h8 := integrable_exponential_realCausalConvolution ha hF
  exact (exponentialSourceMass_le_of_support (Y := 0) le_rfl h1.aestronglyMeasurable h2 h8
    (Eventually.of_forall fun u hu => realCausalConvolution_support_of_laplace_zero a hF.support hz u hu.le)).1

/-- The two opposite pole moments have the same product after reflection
at any positive real Laplace zero, including the half-pole rate. -/
theorem poleTerm_realCausalReflection {a : ℝ} (ha : 0 < a)
    {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hz : (∫ u, Real.exp (Real.pi * a * u) * F u) = 0) :
    2 * coshHalfMoment (realCausalReflection a F) ^ 2 -
        2 * sinhHalfMoment (realCausalReflection a F) ^ 2 =
      2 * coshHalfMoment F ^ 2 - 2 * sinhHalfMoment F ^ 2 := by
  have href : Integrable (fun u => (F (-u) : ℂ)) := (hF.integrable.ofReal (𝕜 := ℂ)).comp_neg
  have hcausal : ∀ u < 0, (F (-u) : ℂ) = 0 := by
    intro u hu
    rw [hF.support (-u) (by linarith only [hu]), Complex.ofReal_zero]
  have hi : Integrable (causalLaplaceWeighted (-a) (cx F)) := by
    have hh := (causalLaplaceWeighted_integrable ha.le href hcausal).comp_neg
    change Integrable (fun u => Complex.exp (-(Real.pi * (-a) * u : ℝ)) * (F u : ℂ))
    simpa only [causalLaplaceWeighted, mul_neg, neg_mul, neg_neg, Complex.ofReal_neg] using hh
  have hzc : causalLaplaceIntegral (-a) (cx F) = 0 := by
    change causalLaplaceIntegral (-a) (fun u => (F u : ℂ)) = 0
    rw [causalLaplaceIntegral_real_eq]
    have he : (∫ u, F u * Real.exp (-(Real.pi * (-a) * u))) =
        ∫ u, Real.exp (Real.pi * a * u) * F u := by
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      dsimp only
      simp only [mul_neg, neg_mul, neg_neg, mul_comm]
    rw [he, hz, Complex.ofReal_zero]
  obtain ⟨hFp, hFm, hFvp, hFvm⟩ := poleLaplaceData hF.weighted
  obtain ⟨hKp, hKm, _, _⟩ := poleLaplaceData (weighted_realCausalConvolution ha hF hz)
  obtain ⟨_, _, hHvp, hHvm⟩ := poleLaplaceData (hF.realCausalReflection ha hz).weighted
  have hK : cx (realCausalConvolution a F) =
      causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] cx F :=
    funext (coe_realCausalConvolution a F)
  have hH : cx (realCausalReflection a F) = causalBlaschkeStep a (cx F) :=
    funext (coe_realCausalReflection a F)
  rw [hK] at hKp hKm
  have hp := causalLaplaceIntegral_reflection_pair hi hzc hFp hFm hKp hKm
  rw [← hH, hHvp, hHvm, hFvp, hFvm] at hp
  have hr : (coshHalfMoment (realCausalReflection a F) - sinhHalfMoment (realCausalReflection a F)) *
      (coshHalfMoment (realCausalReflection a F) + sinhHalfMoment (realCausalReflection a F)) =
      (coshHalfMoment F - sinhHalfMoment F) * (coshHalfMoment F + sinhHalfMoment F) := by
    exact_mod_cast hp
  nlinarith only [hr]

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
