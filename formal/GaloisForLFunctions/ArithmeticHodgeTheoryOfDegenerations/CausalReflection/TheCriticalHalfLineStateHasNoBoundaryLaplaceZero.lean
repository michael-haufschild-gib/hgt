import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.TheUndampedRealResolventIsSkewInFrequency
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.TheUndampedRealResolventCancelsThePoleForm
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CausalResolventMixedEnergy
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.TheCriticalHalfLineStateHasNoRightHalfPlaneLaplaceZero
import GaloisForLFunctions.HTGeometry.FourierUniquenessL1

/-!
# Actual critical states have no imaginary-axis Laplace zero

At a boundary zero the real undamped resolvent is an admitted weak-equation
test. Its prime, Gamma and polar mixed terms cancel. The remaining mixed
exponential mass is a strictly positive multiple of the resolvent's squared
norm. Its vanishing forces the input to vanish by Fourier uniqueness.
-/

noncomputable section
open MeasureTheory Filter Set Topology Zeta23 FourierTransform
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri HTGeometry WindowTowerOfSpecZ

private theorem weighted_real_resolvent_mixed (b : ℝ) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    (∫ u in Iio 0, F u * realUndampedCausalConvolution b F u * Real.exp (-(8 * u))) =
      (4 / Real.pi) * ∫ u, ‖causalLaplaceWeighted (4 / Real.pi)
        (modulatedCausalConvolution 0 b (cx F)) u‖ ^ 2 := by
  have hm := (integral_weighted_modulatedCausalConvolution_mixed_energy
    (a := 0) (x := 4 / Real.pi) (by positivity) b hF.memLp_weightedComplex).2
  have hweight (u : ℝ) : Complex.exp (-(Real.pi * (4 / Real.pi) * u : ℝ)) =
      (Real.exp (-(4 * u)) : ℂ) := by
    rw [show Real.pi * (4 / Real.pi) = 4 by field_simp [Real.pi_ne_zero],
      ← Complex.ofReal_neg, ← Complex.ofReal_exp]
  have hpoint (u : ℝ) :
      ((starRingEnd ℂ) (causalLaplaceWeighted (4 / Real.pi) (cx F) u) *
        causalLaplaceWeighted (4 / Real.pi) (modulatedCausalConvolution 0 b (cx F)) u).re =
        F u * realUndampedCausalConvolution b F u * Real.exp (-(8 * u)) := by
    unfold causalLaplaceWeighted
    simp only [hweight]
    change ((starRingEnd ℂ) ((Real.exp (-(4 * u)) : ℂ) * (F u : ℂ)) *
      ((Real.exp (-(4 * u)) : ℂ) * modulatedCausalConvolution 0 b (cx F) u)).re = _
    rw [map_mul, Complex.conj_ofReal, Complex.conj_ofReal]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    have he : Real.exp (-(8 * u)) = Real.exp (-(4 * u)) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [he]
    unfold realUndampedCausalConvolution
    ring
  have hs : (Iio (0 : ℝ)).indicator
      (fun u => F u * realUndampedCausalConvolution b F u * Real.exp (-(8 * u))) =
      fun u => F u * realUndampedCausalConvolution b F u * Real.exp (-(8 * u)) := by
    funext u
    by_cases hu : u ∈ Iio (0 : ℝ)
    · exact indicator_of_mem hu _
    · rw [indicator_of_notMem hu, hF.support u (le_of_not_gt hu), zero_mul, zero_mul]
  rw [← integral_indicator measurableSet_Iio, hs]
  simpa only [hpoint, zero_add] using hm

/-- Every imaginary-axis Laplace value of the actual critical state is nonzero. -/
theorem criticalHalfLineGroundState_boundaryLaplace_ne_zero
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (b : ℝ) :
    negativeHalfLineLaplace (cx F) (modulatedLaplaceRate 0 b) ≠ 0 := by
  intro hz
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hH := hd.realUndampedCausalConvolution b hz
  have he := criticalHalfLineMixedEnergy_groundState_eq_zero hW hthreshold hF hH
  obtain ⟨hg, hp⟩ := arithmetic_mixed_realUndampedCausalConvolution_eq_zero b hd hz
  have hpolar := pole_mixed_realUndampedCausalConvolution_eq_zero b hd hz
  unfold criticalHalfLineMixedEnergy at he
  rw [hg, hp, hpolar, weighted_real_resolvent_mixed b hd] at he
  simp only [zero_div, sub_zero, zero_add] at he
  have hcoef : criticalAliasCoefficient W₀ * (4 / Real.pi) ≠ 0 :=
    ne_of_gt (mul_pos (criticalAliasCoefficient_positive hW) (by positivity))
  have hmass : (∫ u, ‖causalLaplaceWeighted (4 / Real.pi)
      (modulatedCausalConvolution 0 b (cx F)) u‖ ^ 2) = 0 := by
    rw [← mul_assoc] at he
    exact (mul_eq_zero.mp he).resolve_left hcoef
  have hK := memLp_weighted_modulatedCausalConvolution
    (a := 0) (x := 4 / Real.pi) (by positivity) b hd.memLp_weightedComplex
  have hKi := (memLp_two_iff_integrable_sq_norm hK.aestronglyMeasurable).mp hK
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun u => sq_nonneg
      ‖causalLaplaceWeighted (4 / Real.pi) (modulatedCausalConvolution 0 b (cx F)) u‖) hKi).mp hmass
  have hKzero : modulatedCausalConvolution 0 b (cx F) =ᵐ[volume] 0 := by
    filter_upwards [hae] with u hu
    change ‖causalLaplaceWeighted (4 / Real.pi)
      (modulatedCausalConvolution 0 b (cx F)) u‖ ^ 2 = 0 at hu
    have hn : ‖causalLaplaceWeighted (4 / Real.pi)
        (modulatedCausalConvolution 0 b (cx F)) u‖ = 0 := by nlinarith only [hu]
    have hv := norm_eq_zero.mp hn
    change Complex.exp (-(Real.pi * (4 / Real.pi) * u : ℝ)) *
      modulatedCausalConvolution 0 b (cx F) u = 0 at hv
    exact (mul_eq_zero.mp hv).resolve_left (Complex.exp_ne_zero _)
  have hm : Measurable (cx F) := Complex.continuous_ofReal.measurable.comp hd.meas
  have hf : Integrable (cx F) := hd.integrable.ofReal (𝕜 := ℂ)
  have hs : ∀ u, 0 ≤ u → cx F u = 0 := by
    intro u hu
    change (F u : ℂ) = 0
    rw [hd.support u hu, Complex.ofReal_zero]
  have hFzero : cx F =ᵐ[volume] 0 := by
    apply _root_.HTGeometry.ae_eq_zero_of_fourierIntegral_eq_zero hf
    intro ξ
    have hk : 𝓕 (modulatedCausalConvolution 0 b (cx F)) ξ = 0 := by
      rw [Real.fourier_congr_ae hKzero, Real.fourier_real_eq_integral_exp_smul]
      simp
    have hh := fourier_undampedCausalConvolution_mul b hm hf hd.memLp_weightedComplex hs hz ξ
    rw [hk, mul_zero] at hh
    exact hh.symm
  have hnorm : (∫ u, F u ^ 2) = 0 := by
    calc
      _ = ∫ _u : ℝ, (0 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [hFzero] with u hu
        have hfu : F u = 0 := Complex.ofReal_eq_zero.mp hu
        rw [hfu, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      _ = 0 := by simp
  linarith only [hnorm, hF.2.2.2.1]

/-- The actual critical-state Laplace transform is zero-free on the closed right half-plane. -/
theorem criticalHalfLineGroundState_closedRightHalfPlaneLaplace_ne_zero
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    {z : ℂ} (hz : 0 ≤ z.re) : negativeHalfLineLaplace (cx F) z ≠ 0 := by
  rcases lt_or_eq_of_le hz with hpos | heq
  · exact criticalHalfLineGroundState_complexLaplace_ne_zero hW hthreshold hF hpos
  · have he : modulatedLaplaceRate 0 (z.im / (2 * Real.pi)) = z := by
      apply Complex.ext
      · simpa [modulatedLaplaceRate] using heq
      · simp only [modulatedLaplaceRate, Complex.add_im, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, Complex.I_re,
          mul_one, mul_zero, add_zero, zero_add]
        field_simp [Real.pi_ne_zero]
    rw [← he]
    exact criticalHalfLineGroundState_boundaryLaplace_ne_zero hW hthreshold hF _

/-- Failure of RH supplies an actual critical state whose Laplace transform
has no zero anywhere in the closed right half-plane. -/
theorem riemannHypothesis_or_exists_closedRightHalfPlaneLaplaceZeroFree_criticalHalfLineGroundState :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧
      ∀ z : ℂ, 0 ≤ z.re → negativeHalfLineLaplace (cx F) z ≠ 0 := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl hRH
  · exact Or.inr ⟨W₀, F, hW, ht, hF,
      fun _ hz => criticalHalfLineGroundState_closedRightHalfPlaneLaplace_ne_zero hW ht hF hz⟩

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.riemannHypothesis_or_exists_closedRightHalfPlaneLaplaceZeroFree_criticalHalfLineGroundState
