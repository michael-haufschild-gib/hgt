import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.TheUndampedRealResolventHasTheActualDomain
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ThePairedReflectionPreservesArithmeticEnergy

/-!
# Opposite half-pole moments cancel for the real boundary resolvent

At a real Laplace argument q, the real undamped multiplier is
`-πq/(q²+(2πb)²)`. Its oddness at the opposite half-poles annihilates
the polarized pole form without imposing any polar-charge condition.
-/

noncomputable section
open MeasureTheory Filter Set Topology Zeta23
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri HTGeometry

private theorem real_resolvent_identity (β s p x : ℝ) (w : ℂ)
    (he : ((β : ℂ) * Complex.I - (s : ℂ)) * w = (p * x : ℝ)) :
    (s ^ 2 + β ^ 2) * w.re = -(p * s * x) := by
  have hr := congrArg Complex.re he
  have hi := congrArg Complex.im he
  simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, sub_zero, zero_sub, add_zero] at hr hi
  have hrs := congrArg (fun y : ℝ => s * y) hr
  have hib := congrArg (fun y : ℝ => β * y) hi
  nlinarith only [hrs, hib]

/-- Real-part extraction commutes with every admitted real Laplace moment. -/
theorem integral_realUndampedCausalConvolution_laplace (b s : ℝ) {F : ℝ → ℝ}
    (hi : Integrable (complexLaplaceWeighted (s : ℂ)
      (modulatedCausalConvolution 0 b (cx F)))) :
    (∫ u, realUndampedCausalConvolution b F u * Real.exp (s * u)) =
      (negativeHalfLineLaplace (modulatedCausalConvolution 0 b (cx F)) (s : ℂ)).re := by
  calc
    _ = ∫ u, (complexLaplaceWeighted (s : ℂ)
        (modulatedCausalConvolution 0 b (cx F)) u).re := by
      apply integral_congr_ae
      refine Eventually.of_forall fun u => ?_
      change (modulatedCausalConvolution 0 b (cx F) u).re * Real.exp (s * u) =
        (Complex.exp ((s : ℂ) * (u : ℂ)) * modulatedCausalConvolution 0 b (cx F) u).re
      rw [← Complex.ofReal_mul, ← Complex.ofReal_exp]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      ring
    _ = _ := integral_re hi

/-- The real boundary-resolvent moment law holds throughout the half-pole strip. -/
theorem realUndampedCausalConvolution_real_moment (b : ℝ)
    {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hz : negativeHalfLineLaplace (cx F) (modulatedLaplaceRate 0 b) = 0)
    {s : ℝ} (hs : |s| ≤ 1 / 2) :
    (s ^ 2 + (2 * Real.pi * b) ^ 2) *
        (∫ u, realUndampedCausalConvolution b F u * Real.exp (s * u)) =
      -(Real.pi * s * (∫ u, F u * Real.exp (s * u))) := by
  have hm : Measurable (cx F) := Complex.continuous_ofReal.measurable.comp hF.meas
  have hf : Integrable (cx F) := hF.integrable.ofReal (𝕜 := ℂ)
  have hsupport : ∀ u, 0 ≤ u → cx F u = 0 := by
    intro u hu
    change (F u : ℂ) = 0
    rw [hF.support u hu, Complex.ofReal_zero]
  have hq : |(s : ℂ).re| ≤ 1 / 2 := hs
  have hFs := integrable_complexLaplaceWeighted_of_halfLine_memLp hq
    hF.memLp_complex hF.memLp_weightedComplex hsupport
  have hK2 := (undampedCausalConvolution_memLp_and_integrable
    b hm hF.memLp_weightedComplex hsupport hz).1
  have hKw := memLp_weighted_modulatedCausalConvolution
    (a := 0) (x := 4 / Real.pi) (by positivity) b hF.memLp_weightedComplex
  have hKs := modulatedCausalConvolution_support_of_laplace_zero 0 b hsupport hz
  have hKi := integrable_complexLaplaceWeighted_of_halfLine_memLp hq hK2 hKw hKs
  rw [integral_realUndampedCausalConvolution_laplace b s hKi]
  have he := negativeHalfLineLaplace_undampedCausalConvolution_mul
    b hm hf hF.memLp_weightedComplex hsupport hz hFs
  rw [negativeHalfLineLaplace_ofReal] at he
  have hzrate : modulatedLaplaceRate 0 b = ((2 * Real.pi * b : ℝ) : ℂ) * Complex.I := by
    simp only [modulatedLaplaceRate, mul_zero, Complex.ofReal_zero, zero_add]
  rw [hzrate, ← Complex.ofReal_mul] at he
  exact real_resolvent_identity (2 * Real.pi * b) s Real.pi _ _ he

/-- The full polarized half-pole contribution vanishes for the real
undamped resolvent at a boundary Laplace zero. -/
theorem pole_mixed_realUndampedCausalConvolution_eq_zero (b : ℝ)
    {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hz : negativeHalfLineLaplace (cx F) (modulatedLaplaceRate 0 b) = 0) :
    2 * coshHalfMoment F * coshHalfMoment (realUndampedCausalConvolution b F) -
      2 * sinhHalfMoment F * sinhHalfMoment (realUndampedCausalConvolution b F) = 0 := by
  have hH := hF.realUndampedCausalConvolution b hz
  obtain ⟨hFp, hFm⟩ := negativeHalfLineLaplace_halfPole_real hF.weighted
  obtain ⟨hHp, hHm⟩ := negativeHalfLineLaplace_halfPole_real hH.weighted
  rw [negativeHalfLineLaplace_ofReal] at hFp hHp
  rw [← Complex.ofReal_neg, negativeHalfLineLaplace_ofReal] at hFm hHm
  have hFp' := Complex.ofReal_inj.mp hFp
  have hFm' := Complex.ofReal_inj.mp hFm
  have hHp' := Complex.ofReal_inj.mp hHp
  have hHm' := Complex.ofReal_inj.mp hHm
  have hp := realUndampedCausalConvolution_real_moment b hF hz (s := 1 / 2) (by norm_num)
  have hn := realUndampedCausalConvolution_real_moment b hF hz (s := -(1 / 2)) (by norm_num)
  rw [hFp', hHp'] at hp
  rw [hFm', hHm'] at hn
  have hpm := congrArg (fun y : ℝ => y * (coshHalfMoment F - sinhHalfMoment F)) hp
  have hnp := congrArg (fun y : ℝ => y * (coshHalfMoment F + sinhHalfMoment F)) hn
  have hprod : ((1 / 2 : ℝ) ^ 2 + (2 * Real.pi * b) ^ 2) *
      (2 * coshHalfMoment F * coshHalfMoment (realUndampedCausalConvolution b F) -
        2 * sinhHalfMoment F * sinhHalfMoment (realUndampedCausalConvolution b F)) = 0 := by
    nlinarith only [hpm, hnp]
  exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt (by positivity))

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
