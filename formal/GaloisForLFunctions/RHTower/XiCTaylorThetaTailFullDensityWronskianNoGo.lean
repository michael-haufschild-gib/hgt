import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFullDensityMonotoneCurrent
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCompletedDensityReflection
import GaloisForLFunctions.RHTower.XiCTaylorFluxBoundGate
import GaloisForLFunctions.RHTower.XiHedenmalmDeBrangesSeam

/-!
# Source-exchange obstruction to a pure-transfer Wronskian

The canonical zero-free full-density channel does not share the source and phase of the completed
Xi transform.  Consequently its Wronskian with a finite Xi Taylor section is not a pure Taylor
remainder: it converges to a nonzero full Xi/full-density background.

This file proves the exact pointwise phase obstruction, the full-minus-remainder identity, and a
reflected-channel formula for the surviving background.  It then identifies the actual pointwise
limit of the canonical transfer value, derivative, and current as the quotient `XiC / F`.  Thus the
transfer retains the full Xi divisor; no RH or zero-location hypothesis is used.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- Wronskian kernel of two one-sided full exponential phases. -/
def fullPhaseWronskianKernel (z : ℂ) (x t : ℝ) : ℂ :=
  ((x : ℂ) * I * spectralTranslationPhase x z) *
      spectralTranslationPhase t z -
    spectralTranslationPhase x z *
      ((t : ℂ) * I * spectralTranslationPhase t z)

/-- The full-phase Wronskian retains the source-coordinate difference. -/
theorem fullPhaseWronskianKernel_eq
    (z : ℂ) (x t : ℝ) :
    fullPhaseWronskianKernel z x t =
      (((x - t : ℝ) : ℂ) * I) * spectralTranslationPhase (x + t) z := by
  unfold fullPhaseWronskianKernel
  rw [spectralTranslationPhase_add]
  push_cast
  ring

/-- Full phases cancel pointwise exactly on the source diagonal, not identically. -/
theorem fullPhaseWronskianKernel_eq_zero_iff
    (z : ℂ) (x t : ℝ) :
    fullPhaseWronskianKernel z x t = 0 ↔ x = t := by
  rw [fullPhaseWronskianKernel_eq]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hxt | hphase
    · rcases mul_eq_zero.mp hxt with hsub | hI
      · exact sub_eq_zero.mp (Complex.ofReal_eq_zero.mp hsub)
      · exact (I_ne_zero hI).elim
    · exact (Complex.exp_ne_zero _ hphase).elim
  · rintro rfl
    simp

/-- Full Xi/full-density Wronskian background. -/
def xiFullDensityWronskian (z : ℂ) : ℂ :=
  deriv XiC z * thetaCuspTailSecondDensityPhaseValue z -
    XiC z * thetaCuspTailSecondDensityPhaseDerivative z

/-- Wronskian numerator of one final odd Xi Taylor section against full density. -/
def xiCTaylorFullDensityWronskian (d : ℕ) (z : ℂ) : ℂ :=
  (xiCTaylorPolynomial (2 * d + 3)).derivative.eval z *
      thetaCuspTailSecondDensityPhaseValue z -
    (xiCTaylorPolynomial (2 * d + 3)).eval z *
      thetaCuspTailSecondDensityPhaseDerivative z

/-- Value remainder between full Xi and one final odd Taylor section. -/
def xiCTaylorFullDensityRemainderValue (d : ℕ) (z : ℂ) : ℂ :=
  XiC z - (xiCTaylorPolynomial (2 * d + 3)).eval z

/-- Derivative remainder between full Xi and one final odd Taylor section. -/
def xiCTaylorFullDensityRemainderDerivative (d : ℕ) (z : ℂ) : ℂ :=
  deriv XiC z - (xiCTaylorPolynomial (2 * d + 3)).derivative.eval z

/-- Exact correction to the failed pure-remainder prediction.  The finite Wronskian is the full
source-exchange background minus the genuine Taylor-remainder Wronskian. -/
theorem xiCTaylorFullDensityWronskian_eq_full_sub_remainder
    (d : ℕ) (z : ℂ) :
    xiCTaylorFullDensityWronskian d z =
      xiFullDensityWronskian z -
        (xiCTaylorFullDensityRemainderDerivative d z *
            thetaCuspTailSecondDensityPhaseValue z -
          xiCTaylorFullDensityRemainderValue d z *
            thetaCuspTailSecondDensityPhaseDerivative z) := by
  unfold xiCTaylorFullDensityWronskian xiFullDensityWronskian
    xiCTaylorFullDensityRemainderDerivative
    xiCTaylorFullDensityRemainderValue
  ring

/-- Division-free reflected connection carried by the full Xi/full-density Wronskian. -/
def xiFullDensityReflectedConnection (z : ℂ) : ℂ :=
  2 * z *
      (thetaCuspTailSecondDensityPhaseValue z +
        thetaCuspTailSecondDensityPhaseValue (-z)) *
      thetaCuspTailSecondDensityPhaseValue z -
    (z ^ (2 : ℕ) + 1 / 4) *
      (thetaCuspTailSecondDensityPhaseDerivative (-z) *
          thetaCuspTailSecondDensityPhaseValue z +
        thetaCuspTailSecondDensityPhaseValue (-z) *
          thetaCuspTailSecondDensityPhaseDerivative z) +
    (1 / 2) * thetaCuspTailSecondDensityPhaseDerivative z

/-- The full Wronskian background is exactly the reflected growing channel plus central seam. -/
theorem xiFullDensityReflectedConnection_eq_background
    {z : ℂ} (hz : |z.im| < 1) :
    xiFullDensityReflectedConnection z =
      8 * z * XiC z * thetaCuspTailSecondDensityPhaseValue z +
        4 * z ^ (2 : ℕ) * xiFullDensityWronskian z := by
  have hvalue := thetaCuspTailSecondDensityPhaseValue_twoSided_crossed hz
  have hderivative :=
    thetaCuspTailSecondDensityPhaseValue_twoSided_derivative_crossed hz
  unfold xiFullDensityReflectedConnection xiFullDensityWronskian
  linear_combination
    thetaCuspTailSecondDensityPhaseValue z * hderivative -
      thetaCuspTailSecondDensityPhaseDerivative z * hvalue

/-- At a Xi zero, the reflected connection is the Xi derivative times the zero-free density
channel, including the exact completion monomial. -/
theorem xiFullDensityReflectedConnection_eq_at_XiC_zero
    {z : ℂ} (hzstrip : |z.im| < 1) (hz : XiC z = 0) :
    xiFullDensityReflectedConnection z =
      4 * z ^ (2 : ℕ) * deriv XiC z *
        thetaCuspTailSecondDensityPhaseValue z := by
  rw [xiFullDensityReflectedConnection_eq_background hzstrip]
  unfold xiFullDensityWronskian
  rw [hz]
  ring

/-- A simple off-axis Xi zero has a nonzero reflected full-density connection.  Hence the full
background is the zero signal, not a removable truncation defect. -/
theorem xiFullDensityReflectedConnection_ne_zero_at_simple_upper_zero
    {z : ℂ} (hzstrip : |z.im| < 1) (hzim : 0 < z.im)
    (hz : XiC z = 0) (hsimple : deriv XiC z ≠ 0) :
    xiFullDensityReflectedConnection z ≠ 0 := by
  rw [xiFullDensityReflectedConnection_eq_at_XiC_zero hzstrip hz]
  have hz0 : z ≠ 0 := by
    intro hzero
    rw [hzero] at hzim
    simp at hzim
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hz0))
      hsimple)
    (thetaCuspTailSecondDensityPhaseValue_ne_zero hzim)

/-- Positive first moment of the full canonical second density. -/
def thetaCuspTailSecondDensityFirstMoment : ℝ :=
  ∫ x : ℝ in Ioi 0, x * thetaCuspTailSecondDensity x

/-- Strict positivity of the full-density first moment. -/
theorem thetaCuspTailSecondDensityFirstMoment_pos :
    0 < thetaCuspTailSecondDensityFirstMoment := by
  let f : ℝ → ℝ := fun x => x * thetaCuspTailSecondDensity x
  have hfcont : Continuous f :=
    continuous_id.mul
      (continuous_const.mul
        (differentiable_thetaCuspTailDerivative 2).continuous)
  have hfint : IntegrableOn f (Ioi 0) := by
    simpa only [f, pow_one] using
      integrableOn_pow_mul_thetaCuspTailSecondDensity 1
  have hfnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg hx.le (thetaCuspTailSecondDensity_pos hx).le
  unfold thetaCuspTailSecondDensityFirstMoment
  apply (setIntegral_pos_iff_support_of_nonneg_ae hfnn hfint).2
  have hopen : IsOpen (Function.support f ∩ Ioi (0 : ℝ)) :=
    hfcont.isOpen_support.inter isOpen_Ioi
  apply hopen.measure_pos (volume : Measure ℝ)
  refine ⟨1, ?_, by norm_num⟩
  change f 1 ≠ 0
  exact (mul_pos (by norm_num)
    (thetaCuspTailSecondDensity_pos (x := 1) (by norm_num))).ne'

/-- At the reflection center, the full-density derivative is `i` times its positive first
moment. -/
theorem thetaCuspTailSecondDensityPhaseDerivative_zero :
    thetaCuspTailSecondDensityPhaseDerivative 0 =
      I * (thetaCuspTailSecondDensityFirstMoment : ℂ) := by
  unfold thetaCuspTailSecondDensityPhaseDerivative spectralTranslationPhase
  simp only [mul_zero, Complex.exp_zero, mul_one]
  rw [show (fun x : ℝ =>
      (thetaCuspTailSecondDensity x : ℂ) * ((x : ℂ) * I)) =
      fun x : ℝ => I * (((x * thetaCuspTailSecondDensity x : ℝ) : ℂ)) by
    funext x
    push_cast
    ring,
    MeasureTheory.integral_const_mul]
  unfold thetaCuspTailSecondDensityFirstMoment
  have hcast :
      (∫ x : ℝ in Ioi 0,
        (((x * thetaCuspTailSecondDensity x : ℝ) : ℂ))) =
        ((∫ x : ℝ in Ioi 0,
          x * thetaCuspTailSecondDensity x : ℝ) : ℂ) :=
    integral_ofReal
  rw [hcast]

/-- Xi parity forces its central derivative to vanish. -/
theorem deriv_XiC_zero : deriv XiC 0 = 0 := by
  have h := deriv_XiC_neg 0
  simp only [neg_zero] at h
  linear_combination (1 / 2 : ℂ) * h

/-- Exact central value of the full source-exchange Wronskian. -/
theorem xiFullDensityWronskian_zero_eq :
    xiFullDensityWronskian 0 =
      -(XiC 0 * (I * (thetaCuspTailSecondDensityFirstMoment : ℂ))) := by
  unfold xiFullDensityWronskian
  rw [deriv_XiC_zero, thetaCuspTailSecondDensityPhaseDerivative_zero]
  ring

/-- The full Xi/full-density Wronskian background is not identically zero; it is already nonzero
at the reflection center. -/
theorem xiFullDensityWronskian_zero_ne :
    xiFullDensityWronskian 0 ≠ 0 := by
  rw [xiFullDensityWronskian_zero_eq]
  exact neg_ne_zero.mpr
    (mul_ne_zero XiC_zero_ne
      (mul_ne_zero I_ne_zero
        (Complex.ofReal_ne_zero.mpr
          thetaCuspTailSecondDensityFirstMoment_pos.ne')))

/-- Finite Taylor/full-density Wronskians converge pointwise to the full source-exchange
background. -/
theorem tendsto_xiCTaylorFullDensityWronskian
    (z : ℂ) :
    Tendsto (fun d : ℕ => xiCTaylorFullDensityWronskian d z)
      atTop (nhds (xiFullDensityWronskian z)) := by
  have hindex : Tendsto (fun d : ℕ => 2 * d + 3) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    apply eventually_atTop.2
    refine ⟨b, ?_⟩
    intro a ha
    omega
  have hvalue :=
    xiCTaylorApprox_tendstoLocallyUniformly.tendstoLocallyUniformlyOn.tendsto_at
      (Set.mem_univ z) |>.comp hindex
  have hderivative :=
    xiCTaylorApprox_deriv_tendstoLocallyUniformly.tendstoLocallyUniformlyOn.tendsto_at
      (Set.mem_univ z) |>.comp hindex
  have hcombined :=
    (hderivative.mul_const (thetaCuspTailSecondDensityPhaseValue z)).sub
      (hvalue.mul_const (thetaCuspTailSecondDensityPhaseDerivative z))
  simpa only [xiCTaylorFullDensityWronskian, xiFullDensityWronskian,
    xiCTaylorPolynomial_eval, xiCTaylorPolynomial_derivative_eval,
    Function.comp_apply] using hcombined

/-- In particular, the finite Wronskians do not tend to zero at the center. -/
theorem not_tendsto_xiCTaylorFullDensityWronskian_zero_at_zero :
    ¬ Tendsto (fun d : ℕ => xiCTaylorFullDensityWronskian d 0)
      atTop (nhds 0) := by
  intro hzero
  have hlimit := tendsto_xiCTaylorFullDensityWronskian 0
  have := tendsto_nhds_unique hzero hlimit
  exact xiFullDensityWronskian_zero_ne this.symm

/-- Actual full limit of the canonical transfer values. -/
def xiFullDensityQuotientValue (z : ℂ) : ℂ :=
  XiC z / thetaCuspTailSecondDensityPhaseValue z

/-- Quotient-rule derivative of the full Xi/full-density quotient. -/
def xiFullDensityQuotientDerivative (z : ℂ) : ℂ :=
  xiFullDensityWronskian z /
    thetaCuspTailSecondDensityPhaseValue z ^ (2 : ℕ)

/-- Oriented current of the full Xi/full-density quotient. -/
def xiFullDensityQuotientCurrent (z : ℂ) : ℝ :=
  (xiFullDensityQuotientDerivative z *
    starRingEnd ℂ (xiFullDensityQuotientValue z)).im

/-- The full quotient retains exactly the Xi zero set in the open upper half-plane. -/
theorem xiFullDensityQuotientValue_eq_zero_iff
    {z : ℂ} (hz : 0 < z.im) :
    xiFullDensityQuotientValue z = 0 ↔ XiC z = 0 := by
  simp only [xiFullDensityQuotientValue, div_eq_zero_iff]
  exact or_iff_left (thetaCuspTailSecondDensityPhaseValue_ne_zero hz)

/-- The finite transfer derivative numerator is exactly the finite Wronskian. -/
theorem xiCTaylorFullDensityTransferDerivative_eq_wronskian_div
    (d : ℕ) (z : ℂ) :
    xiCTaylorFullDensityTransferDerivative d z =
      xiCTaylorFullDensityWronskian d z /
        thetaCuspTailSecondDensityPhaseValue z ^ (2 : ℕ) := by
  rfl

private theorem tendsto_xiCTaylorOddIndex :
    Tendsto (fun d : ℕ => 2 * d + 3) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  apply eventually_atTop.2
  refine ⟨b, ?_⟩
  intro a ha
  omega

/-- Canonical transfer values converge pointwise to `XiC / F`, not to a truncation defect. -/
theorem tendsto_xiCTaylorFullDensityTransferValue
    (z : ℂ) :
    Tendsto (fun d : ℕ => xiCTaylorFullDensityTransferValue d z)
      atTop (nhds (xiFullDensityQuotientValue z)) := by
  have hvalue :=
    xiCTaylorApprox_tendstoLocallyUniformly.tendstoLocallyUniformlyOn.tendsto_at
      (Set.mem_univ z) |>.comp tendsto_xiCTaylorOddIndex
  have h2 : Tendsto (fun d : ℕ =>
      xiCTaylorApprox (2 * d + 3) z / thetaCuspTailSecondDensityPhaseValue z)
      atTop (nhds (XiC z / thetaCuspTailSecondDensityPhaseValue z)) :=
    hvalue.div_const (thetaCuspTailSecondDensityPhaseValue z)
  simpa only [xiCTaylorFullDensityTransferValue, xiFullDensityQuotientValue,
    xiCTaylorPolynomial_eval] using h2

/-- Canonical transfer derivatives converge pointwise to the derivative of `XiC / F`. -/
theorem tendsto_xiCTaylorFullDensityTransferDerivative
    (z : ℂ) :
    Tendsto (fun d : ℕ => xiCTaylorFullDensityTransferDerivative d z)
      atTop (nhds (xiFullDensityQuotientDerivative z)) := by
  simpa only [xiCTaylorFullDensityTransferDerivative_eq_wronskian_div,
    xiFullDensityQuotientDerivative] using
    (tendsto_xiCTaylorFullDensityWronskian z).div_const
      (thetaCuspTailSecondDensityPhaseValue z ^ (2 : ℕ))

/-- Canonical transfer currents converge pointwise to the current of the full Xi quotient. -/
theorem tendsto_xiCTaylorFullDensityTransferCurrent
    (z : ℂ) :
    Tendsto (fun d : ℕ => xiCTaylorFullDensityTransferCurrent d z)
      atTop (nhds (xiFullDensityQuotientCurrent z)) := by
  have hd := tendsto_xiCTaylorFullDensityTransferDerivative z
  have hv := tendsto_xiCTaylorFullDensityTransferValue z
  have hc := Complex.continuous_conj.continuousAt.tendsto.comp hv
  have hm := hd.mul hc
  have hi := Complex.continuous_im.continuousAt.tendsto.comp hm
  have h2 : Tendsto (fun d : ℕ =>
      (xiCTaylorFullDensityTransferDerivative d z *
        (starRingEnd ℂ) (xiCTaylorFullDensityTransferValue d z)).im)
      atTop (nhds ((xiFullDensityQuotientDerivative z *
        (starRingEnd ℂ) (xiFullDensityQuotientValue z)).im)) := hi
  simpa only [xiCTaylorFullDensityTransferCurrent,
    xiFullDensityQuotientCurrent] using h2

end

end RHTower
