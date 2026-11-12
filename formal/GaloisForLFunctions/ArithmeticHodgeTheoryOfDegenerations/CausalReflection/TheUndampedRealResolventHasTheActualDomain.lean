import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.UndampedCausalFourierDecay
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ThePairedReflectionPreservesTheActualDomain

/-!
# The real boundary resolvent belongs to the actual energy domain

Conjugation exchanges the two undamped frequencies. Their average is the
real part of either resolvent, and its Fourier decay gives Gamma admission.
Physical and exponentially weighted square integrability descend by taking
real parts. A boundary Laplace zero supplies the half-line support.
-/

noncomputable section
open MeasureTheory Filter Set Topology Zeta23 FourierTransform
open _root_.RHTower

namespace GaloisForLFunctions.HTGeometry
open ArithmeticCastelnuovoSeveri

/-- The real component of the undamped modulated causal resolvent. -/
def realUndampedCausalConvolution (b : ℝ) (F : ℝ → ℝ) (u : ℝ) : ℝ :=
  (modulatedCausalConvolution 0 b (cx F) u).re

/-- The real boundary resolvent is the average of the two conjugate frequencies. -/
theorem coe_realUndampedCausalConvolution (b : ℝ) (F : ℝ → ℝ) :
    cx (realUndampedCausalConvolution b F) = fun u =>
      (1 / 2 : ℂ) * (modulatedCausalConvolution 0 b (cx F) u +
        modulatedCausalConvolution 0 (-b) (cx F) u) := by
  have hr : (fun u => (starRingEnd ℂ) (cx F u)) = cx F := by
    funext u
    exact Complex.conj_ofReal _
  have hc := conj_modulatedCausalConvolution 0 b (cx F)
  rw [hr] at hc
  funext u
  rw [← congrFun hc u]
  apply Complex.ext
  · simp [cx, realUndampedCausalConvolution]
    ring
  · simp [cx, realUndampedCausalConvolution]

/-- A real profile's boundary zero is accompanied by its conjugate zero. -/
theorem undamped_conjugate_laplace_zero (b : ℝ) {F : ℝ → ℝ}
    (hz : negativeHalfLineLaplace (cx F) (modulatedLaplaceRate 0 b) = 0) :
    negativeHalfLineLaplace (cx F) (modulatedLaplaceRate 0 (-b)) = 0 := by
  have hc := negativeHalfLineLaplace_real_conj F (modulatedLaplaceRate 0 b)
  change negativeHalfLineLaplace (fun u => (F u : ℂ)) (modulatedLaplaceRate 0 b) = 0 at hz
  rw [conj_modulatedLaplaceRate, hz, map_zero] at hc
  exact hc

/-- The paper Fourier transform is the average of the conjugate resolvents' transforms. -/
theorem paperFT_realUndampedCausalConvolution (b : ℝ) {F : ℝ → ℝ}
    (hK : Integrable (modulatedCausalConvolution 0 b (cx F)))
    (hKneg : Integrable (modulatedCausalConvolution 0 (-b) (cx F))) (r : ℝ) :
    paperFT (cx (realUndampedCausalConvolution b F)) r =
      (1 / 2 : ℂ) * (paperFT (modulatedCausalConvolution 0 b (cx F)) r +
        paperFT (modulatedCausalConvolution 0 (-b) (cx F)) r) := by
  rw [coe_realUndampedCausalConvolution, paperFT_const_mul]
  congr 1
  simpa only [one_smul, one_mul, Pi.add_def] using
    WeilSpectral.paperFT_add_smul_real hK hKneg 1 r

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri HTGeometry

/-- The real undamped resolvent inherits every actual energy-domain condition
from the original profile and cancellation of its boundary Laplace value. -/
theorem CriticalHalfLineEnergyDomain.realUndampedCausalConvolution (b : ℝ)
    {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hz : negativeHalfLineLaplace (cx F) (modulatedLaplaceRate 0 b) = 0) :
    CriticalHalfLineEnergyDomain (HTGeometry.realUndampedCausalConvolution b F) := by
  have hm : Measurable (cx F) := Complex.continuous_ofReal.measurable.comp hF.meas
  have hf : Integrable (cx F) := hF.integrable.ofReal (𝕜 := ℂ)
  have hs : ∀ u, 0 ≤ u → cx F u = 0 := by
    intro u hu
    change (F u : ℂ) = 0
    rw [hF.support u hu, Complex.ofReal_zero]
  have hKm := measurable_modulatedCausalConvolution 0 b hm
  obtain ⟨hK2, hK1⟩ := undampedCausalConvolution_memLp_and_integrable
    b hm hF.memLp_weightedComplex hs hz
  have hKw := memLp_weighted_modulatedCausalConvolution
    (a := 0) (x := 4 / Real.pi) (by positivity) b hF.memLp_weightedComplex
  have hHs := modulatedCausalConvolution_support_of_laplace_zero 0 b hs hz
  have hHm : Measurable (HTGeometry.realUndampedCausalConvolution b F) :=
    Complex.continuous_re.measurable.comp hKm
  have hH1 : Integrable (HTGeometry.realUndampedCausalConvolution b F) := hK1.re
  have hsq (u : ℝ) : HTGeometry.realUndampedCausalConvolution b F u ^ 2 ≤
      ‖modulatedCausalConvolution 0 b (cx F) u‖ ^ 2 := by
    change (modulatedCausalConvolution 0 b (cx F) u).re ^ 2 ≤ _
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith only [sq_nonneg (modulatedCausalConvolution 0 b (cx F) u).im]
  refine ⟨hHm, hH1, ?_, ?_, ?_, ?_⟩
  · have hi := (memLp_two_iff_integrable_sq_norm hK2.aestronglyMeasurable).mp hK2
    apply hi.mono' (hHm.aestronglyMeasurable.pow 2)
    refine Eventually.of_forall fun u => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hsq u
  · have hi := (memLp_two_iff_integrable_sq_norm hKw.aestronglyMeasurable).mp hKw
    apply hi.mono' ((hHm.aestronglyMeasurable.pow 2).mul
      (by fun_prop : Continuous (fun u : ℝ => Real.exp (-(8 * u)))).aestronglyMeasurable)
    refine Eventually.of_forall fun u => ?_
    change ‖HTGeometry.realUndampedCausalConvolution b F u ^ 2 * Real.exp (-(8 * u))‖ ≤
      ‖causalLaplaceWeighted (4 / Real.pi) (modulatedCausalConvolution 0 b (cx F)) u‖ ^ 2
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le),
      norm_sq_causalLaplaceWeighted,
      show 2 * Real.pi * (4 / Real.pi) = 8 by field_simp [Real.pi_ne_zero]; norm_num]
    exact mul_le_mul_of_nonneg_right (hsq u) (Real.exp_pos _).le
  · intro u hu
    change (modulatedCausalConvolution 0 b (cx F) u).re = 0
    rw [hHs u hu, Complex.zero_re]
  · have hneg := undamped_conjugate_laplace_zero b hz
    have hKneg := (undampedCausalConvolution_memLp_and_integrable
      (-b) hm hF.memLp_weightedComplex hs hneg).2
    obtain ⟨M, hM⟩ := exists_linear_decay_paperFT_undampedCausalConvolution
      b hm hf hF.memLp_weightedComplex hs hz
    obtain ⟨N, hN⟩ := exists_linear_decay_paperFT_undampedCausalConvolution
      (-b) hm hf hF.memLp_weightedComplex hs hneg
    apply integrable_gammaEnergy_of_linear_decay (continuous_paperFT_cx hH1)
      (M := (M + N) / 2)
    intro r
    rw [paperFT_realUndampedCausalConvolution b hK1 hKneg, norm_mul]
    have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
    rw [hhalf]
    have ht := norm_add_le (paperFT (modulatedCausalConvolution 0 b (cx F)) r)
      (paperFT (modulatedCausalConvolution 0 (-b) (cx F)) r)
    have hmul := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 1 + |r|)
    nlinarith only [hmul, hM r, hN r]

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
