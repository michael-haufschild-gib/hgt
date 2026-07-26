import GaloisForLFunctions.RHTower.XiWardEdgeL2CrossKernel

/-!
# The sharp real-channel edge deposit

For a strict-right Schwarz pair with centered zero `λ = a + ib` and
`x = a + 1/2`, the edge real part is `2L₁ + 2L₂` with Lorentzian halves
`L₁, L₂` at shifts `±b`.  A same-side kernel product integrates to zero —
its two poles share a half-plane, exposed by a constant-difference partial
fraction and the shift-difference log limit — so all cross-Lorentzian mass
comes from the anti-causal/causal pairing:
`∫ L_{β₁} L_{β₂} = 2πx/(4x² + (β₁−β₂)²)`.  The exact real-channel deposit
follows: `∫ (Re pair)² = 4π(1/x + x/(x²+b²))`, exactly half the
modulus-squared deposit — the edge energy equipartitions between the real
and imaginary channels.
-/

open Complex MeasureTheory Real

namespace RHTower

noncomputable section

/-- A same-side kernel product has the cross-kernel modulus, hence is
integrable. -/
theorem integrable_sameSideKernelMul {x : ℝ} (hx : 0 < x) (β₁ β₂ : ℝ) :
    Integrable fun t : ℝ =>
      ((x : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ *
        ((x : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹ := by
  apply Integrable.mono' ((integrable_edgeCrossKernel hx hx β₁ β₂).norm)
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · apply Continuous.inv₀
      · exact continuous_const.add (continuous_const.mul
          (Complex.continuous_ofReal.comp
            (continuous_id.add continuous_const)))
      · exact edgeCrossKernel_denom_ne_zero₁ hx β₁
    · apply Continuous.inv₀
      · exact continuous_const.add (continuous_const.mul
          (Complex.continuous_ofReal.comp
            (continuous_id.add continuous_const)))
      · exact edgeCrossKernel_denom_ne_zero₁ hx β₂
  · filter_upwards with t
    have hconj : ‖((x : ℂ) - I * ((t + β₂ : ℝ) : ℂ))‖ =
        ‖((x : ℂ) + I * ((t + β₂ : ℝ) : ℂ))‖ := by
      have hc : ((x : ℂ) - I * ((t + β₂ : ℝ) : ℂ)) =
          (starRingEnd ℂ) ((x : ℂ) + I * ((t + β₂ : ℝ) : ℂ)) := by
        rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I,
          Complex.conj_ofReal]
        ring
      rw [hc, Complex.norm_conj]
    have heq : ‖((x : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ *
        ((x : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹‖ =
        ‖edgeCrossKernel x x β₁ β₂ t‖ := by
      rw [edgeCrossKernel, norm_mul, norm_mul, norm_inv, norm_inv,
        norm_inv, hconj]
    exact le_of_eq heq

/-- **Same-side vanishing**: the product of two anti-causal kernels of one
width integrates to zero — both poles lie in one half-plane. -/
theorem integral_sameSideKernelMul_zero {x : ℝ} (hx : 0 < x) {β₁ β₂ : ℝ}
    (hne : β₁ ≠ β₂) :
    (∫ t : ℝ, ((x : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ *
      ((x : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹) = 0 := by
  have hd : (I * ((β₂ - β₁ : ℝ) : ℂ)) ≠ 0 := by
    intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact Complex.I_ne_zero h1
    · exact hne (by
        have h3 := Complex.ofReal_eq_zero.mp h2
        linarith)
  have hpf : ∀ t : ℝ,
      ((x : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ *
        ((x : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹ =
      (I * ((β₂ - β₁ : ℝ) : ℂ))⁻¹ *
        (((x : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ -
          ((x : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹) := by
    intro t
    have h1 := edgeCrossKernel_denom_ne_zero₁ hx β₁ t
    have h2 := edgeCrossKernel_denom_ne_zero₁ hx β₂ t
    have hd2 : ((β₂ - β₁ : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]
      intro h
      exact hne (by linarith)
    field_simp
    push_cast
    ring
  have hdiffint : Integrable (fun t : ℝ =>
      ((x : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ -
        ((x : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹) := by
    have h := (integrable_sameSideKernelMul hx β₁ β₂).const_mul
      (I * ((β₂ - β₁ : ℝ) : ℂ))
    apply h.congr
    filter_upwards with t
    rw [hpf t, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]
  have hreval : (∫ t : ℝ, ((((x : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ -
      ((x : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹)).re) = 0 := by
    rw [show (fun t : ℝ => ((((x : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ -
        ((x : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹)).re) =
        fun t : ℝ => x / (x ^ 2 + (t + β₁) ^ 2) -
          x / (x ^ 2 + (t + β₂) ^ 2) from funext fun t => by
      rw [Complex.sub_re, re_rightKernel_inv, re_rightKernel_inv]]
    rw [MeasureTheory.integral_sub (lorentzianHalf_integrable hx β₁)
      (lorentzianHalf_integrable hx β₂),
      integral_lorentzianHalf hx β₁, integral_lorentzianHalf hx β₂]
    ring
  have hsdInt : Integrable (fun t : ℝ =>
      (t + β₂) / (x ^ 2 + (t + β₂) ^ 2) -
        (t + β₁) / (x ^ 2 + (t + β₁) ^ 2)) := by
    have h1 := hdiffint.im
    apply h1.congr
    filter_upwards with t
    simp only [RCLike.im_to_complex]
    rw [Complex.sub_im, im_rightKernel_inv, im_rightKernel_inv]
    ring
  have himval : (∫ t : ℝ, ((((x : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ -
      ((x : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹)).im) = 0 := by
    rw [show (fun t : ℝ => ((((x : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ -
        ((x : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹)).im) =
        fun t : ℝ => (t + β₂) / (x ^ 2 + (t + β₂) ^ 2) -
          (t + β₁) / (x ^ 2 + (t + β₁) ^ 2) from funext fun t => by
      rw [Complex.sub_im, im_rightKernel_inv, im_rightKernel_inv]
      ring]
    exact integral_shiftDiffPiece_zero hx β₁ β₂ hsdInt
  have hdiffval : (∫ t : ℝ, (((x : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ -
      ((x : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹)) = 0 := by
    rw [← integral_re_add_im hdiffint]
    simp only [RCLike.re_to_complex, RCLike.im_to_complex,
      RCLike.I_to_complex]
    rw [hreval, himval]
    simp
  rw [show (fun t : ℝ => ((x : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ *
      ((x : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹) =
      fun t : ℝ => (I * ((β₂ - β₁ : ℝ) : ℂ))⁻¹ *
        (((x : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ -
          ((x : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹) from funext hpf]
  rw [MeasureTheory.integral_const_mul, hdiffval, mul_zero]

/-- Products of Lorentzian halves of one width are integrable. -/
theorem integrable_mul_lorentzianHalves {x : ℝ} (hx : 0 < x) (β₁ β₂ : ℝ) :
    Integrable fun t : ℝ =>
      (x / (x ^ 2 + (t + β₁) ^ 2)) * (x / (x ^ 2 + (t + β₂) ^ 2)) := by
  apply Integrable.mono' ((lorentzianHalf_integrable hx β₁).const_mul (1 / x))
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · exact continuous_const.div
        (continuous_const.add ((continuous_id.add continuous_const).pow 2))
        (fun t => by positivity)
    · exact continuous_const.div
        (continuous_const.add ((continuous_id.add continuous_const).pow 2))
        (fun t => by positivity)
  · filter_upwards with t
    have hD1 : (0 : ℝ) < x ^ 2 + (t + β₁) ^ 2 := by positivity
    have hD2 : (0 : ℝ) < x ^ 2 + (t + β₂) ^ 2 := by positivity
    have hL1 : 0 ≤ x / (x ^ 2 + (t + β₁) ^ 2) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hle : x / (x ^ 2 + (t + β₂) ^ 2) ≤ 1 / x := by
      rw [div_le_div_iff₀ hD2 hx]
      nlinarith [sq_nonneg (t + β₂)]
    calc (x / (x ^ 2 + (t + β₁) ^ 2)) * (x / (x ^ 2 + (t + β₂) ^ 2))
        ≤ (x / (x ^ 2 + (t + β₁) ^ 2)) * (1 / x) :=
          mul_le_mul_of_nonneg_left hle hL1
      _ = 1 / x * (x / (x ^ 2 + (t + β₁) ^ 2)) := by ring

/-- **Cross-Lorentzian mass**: `∫ L_{β₁} L_{β₂} = 2πx/(4x² + (β₁−β₂)²)`.
All the mass comes from the anti-causal/causal pairing; the same-side
product contributes zero. -/
theorem integral_mul_lorentzianHalves {x : ℝ} (hx : 0 < x) (β₁ β₂ : ℝ) :
    ∫ t : ℝ, (x / (x ^ 2 + (t + β₁) ^ 2)) * (x / (x ^ 2 + (t + β₂) ^ 2)) =
      2 * π * x / (4 * x ^ 2 + (β₁ - β₂) ^ 2) := by
  rcases eq_or_ne β₁ β₂ with heq | hne
  · subst heq
    rw [show (fun t : ℝ => (x / (x ^ 2 + (t + β₁) ^ 2)) *
        (x / (x ^ 2 + (t + β₁) ^ 2))) =
        fun t : ℝ => (x / (x ^ 2 + (t + β₁) ^ 2)) ^ 2 from
      funext fun t => by ring]
    rw [integral_sq_lorentzianHalf hx β₁, sub_self]
    have hxne := hx.ne'
    field_simp
    ring
  · have hpt : ∀ t : ℝ, (x / (x ^ 2 + (t + β₁) ^ 2)) *
        (x / (x ^ 2 + (t + β₂) ^ 2)) =
        (1 / 2 : ℝ) * (((((x : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ *
            ((x : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹)).re +
          (edgeCrossKernel x x β₁ β₂ t).re) := by
      intro t
      simp only [edgeCrossKernel, Complex.mul_re, re_rightKernel_inv,
        im_rightKernel_inv, re_leftKernel_inv, im_leftKernel_inv]
      ring
    have h1re : Integrable (fun t : ℝ =>
        ((((x : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ *
          ((x : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹)).re) volume :=
      (integrable_sameSideKernelMul hx β₁ β₂).re
    have h2re : Integrable (fun t : ℝ =>
        (edgeCrossKernel x x β₁ β₂ t).re) volume :=
      (integrable_edgeCrossKernel hx hx β₁ β₂).re
    rw [show (fun t : ℝ => (x / (x ^ 2 + (t + β₁) ^ 2)) *
        (x / (x ^ 2 + (t + β₂) ^ 2))) =
        fun t : ℝ =>
          (1 / 2 : ℝ) * (((((x : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ *
              ((x : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹)).re +
            (edgeCrossKernel x x β₁ β₂ t).re) from funext hpt]
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add h1re h2re]
    have hre0 : (∫ t : ℝ,
        ((((x : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ *
          ((x : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹)).re) = 0 := by
      have hcomm := Complex.reCLM.integral_comp_comm
        (integrable_sameSideKernelMul hx β₁ β₂)
      rw [integral_sameSideKernelMul_zero hx hne] at hcomm
      simpa using hcomm
    rw [hre0, integral_re_edgeCrossKernel hx β₁ β₂]
    have hpos : (0 : ℝ) < (2 * x) ^ 2 + (β₁ - β₂) ^ 2 := by positivity
    have hpos2 : (0 : ℝ) < 4 * x ^ 2 + (β₁ - β₂) ^ 2 := by positivity
    field_simp
    ring

/-- **Sharp real-channel deposit**: one strict-right pair's edge real part
carries squared mass exactly `4π(1/x + x/(x²+b²))`, `x = Re λ + 1/2`,
`b = Im λ`. -/
theorem integral_sq_re_xiAntiCausalWardSchwarzPairResponse_eulerEdge
    (q : XiRightUpperZeroCopy) :
    ∫ t : ℝ, ((xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) ^ 2 =
      4 * π * (1 / ((xiRightCenteredZero q.1).re + 1 / 2) +
        ((xiRightCenteredZero q.1).re + 1 / 2) /
          (((xiRightCenteredZero q.1).re + 1 / 2) ^ 2 +
            (xiRightCenteredZero q.1).im ^ 2)) := by
  have hre := xiRightCenteredZero_re_pos q.1
  have hx : 0 < (xiRightCenteredZero q.1).re + 1 / 2 := by linarith
  have h4a : Integrable (fun t : ℝ =>
      4 * (((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + (xiRightCenteredZero q.1).im) ^ 2)) ^ 2) volume :=
    (integrable_sq_lorentzianHalf hx
      ((xiRightCenteredZero q.1).im)).const_mul 4
  have h4b : Integrable (fun t : ℝ =>
      4 * (((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + -(xiRightCenteredZero q.1).im) ^ 2)) ^ 2) volume :=
    (integrable_sq_lorentzianHalf hx
      (-(xiRightCenteredZero q.1).im)).const_mul 4
  have h8c : Integrable (fun t : ℝ =>
      8 * ((((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + (xiRightCenteredZero q.1).im) ^ 2)) *
        (((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + -(xiRightCenteredZero q.1).im) ^ 2)))) volume :=
    (integrable_mul_lorentzianHalves hx ((xiRightCenteredZero q.1).im)
      (-(xiRightCenteredZero q.1).im)).const_mul 8
  have h45 : Integrable (fun t : ℝ =>
      4 * (((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + (xiRightCenteredZero q.1).im) ^ 2)) ^ 2 +
        4 * (((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + -(xiRightCenteredZero q.1).im) ^ 2)) ^ 2) volume :=
    h4a.add h4b
  rw [show (fun t : ℝ => ((xiAntiCausalWardSchwarzPairResponse q
      ((1 / 2 : ℂ) + I * (t : ℂ))).re) ^ 2) =
      fun t : ℝ =>
        (4 * (((xiRightCenteredZero q.1).re + 1 / 2) /
            ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
              (t + (xiRightCenteredZero q.1).im) ^ 2)) ^ 2 +
          4 * (((xiRightCenteredZero q.1).re + 1 / 2) /
            ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
              (t + -(xiRightCenteredZero q.1).im) ^ 2)) ^ 2) +
        8 * ((((xiRightCenteredZero q.1).re + 1 / 2) /
            ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
              (t + (xiRightCenteredZero q.1).im) ^ 2)) *
          (((xiRightCenteredZero q.1).re + 1 / 2) /
            ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
              (t + -(xiRightCenteredZero q.1).im) ^ 2))) from
    funext fun t => by
      rw [re_xiAntiCausalWardSchwarzPairResponse_eulerEdge_eq]
      ring]
  rw [MeasureTheory.integral_add h45 h8c,
    MeasureTheory.integral_add h4a h4b,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul,
    integral_sq_lorentzianHalf hx ((xiRightCenteredZero q.1).im),
    integral_sq_lorentzianHalf hx (-(xiRightCenteredZero q.1).im),
    integral_mul_lorentzianHalves hx ((xiRightCenteredZero q.1).im)
      (-(xiRightCenteredZero q.1).im)]
  have hb2 : (0 : ℝ) < ((xiRightCenteredZero q.1).re + 1 / 2) ^ 2 +
      (xiRightCenteredZero q.1).im ^ 2 := by positivity
  have hb4 : (0 : ℝ) < 4 * ((xiRightCenteredZero q.1).re + 1 / 2) ^ 2 +
      ((xiRightCenteredZero q.1).im - -(xiRightCenteredZero q.1).im) ^ 2 :=
    by positivity
  field_simp
  ring

/-- **Edge equipartition**: the real channel carries exactly half of one
pair's squared edge modulus — real and imaginary parts deposit equally. -/
theorem integral_sq_re_eq_half_integral_normSq_xiPairEdge
    (q : XiRightUpperZeroCopy) :
    ∫ t : ℝ, ((xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) ^ 2 =
      (1 / 2 : ℝ) * ∫ t : ℝ, Complex.normSq
        (xiAntiCausalWardSchwarzPairResponse q
          ((1 / 2 : ℂ) + I * (t : ℂ))) := by
  rw [integral_sq_re_xiAntiCausalWardSchwarzPairResponse_eulerEdge q,
    integral_normSq_xiPairEdge q]
  ring

/-- The squared edge real part of one pair is integrable. -/
theorem integrable_sq_re_xiAntiCausalWardSchwarzPairResponse_eulerEdge
    (q : XiRightUpperZeroCopy) :
    Integrable (fun t : ℝ => ((xiAntiCausalWardSchwarzPairResponse q
      ((1 / 2 : ℂ) + I * (t : ℂ))).re) ^ 2) volume := by
  have hre := xiRightCenteredZero_re_pos q.1
  have hx : 0 < (xiRightCenteredZero q.1).re + 1 / 2 := by linarith
  have h4a : Integrable (fun t : ℝ =>
      4 * (((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + (xiRightCenteredZero q.1).im) ^ 2)) ^ 2) volume :=
    (integrable_sq_lorentzianHalf hx
      ((xiRightCenteredZero q.1).im)).const_mul 4
  have h4b : Integrable (fun t : ℝ =>
      4 * (((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + -(xiRightCenteredZero q.1).im) ^ 2)) ^ 2) volume :=
    (integrable_sq_lorentzianHalf hx
      (-(xiRightCenteredZero q.1).im)).const_mul 4
  have h8c : Integrable (fun t : ℝ =>
      8 * ((((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + (xiRightCenteredZero q.1).im) ^ 2)) *
        (((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + -(xiRightCenteredZero q.1).im) ^ 2)))) volume :=
    (integrable_mul_lorentzianHalves hx ((xiRightCenteredZero q.1).im)
      (-(xiRightCenteredZero q.1).im)).const_mul 8
  have h := (h4a.add h4b).add h8c
  apply h.congr
  filter_upwards with t
  simp only [Pi.add_apply]
  rw [re_xiAntiCausalWardSchwarzPairResponse_eulerEdge_eq]
  ring

/-- Over any finite family of strict-right pairs the sum of squared edge
real parts is dominated by the squared edge modulus of the continued
response. -/
theorem sum_sq_re_xiAntiCausalWardSchwarzPairResponse_le_normSq
    (F : Finset XiRightUpperZeroCopy) (t : ℝ) :
    ∑ q ∈ F, ((xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) ^ 2 ≤
      Complex.normSq (continuedXiAntiCausalWardResponse
        ((1 / 2 : ℂ) + I * (t : ℂ))) := by
  have hw : (0 : ℝ) < ((1 / 2 : ℂ) + I * (t : ℂ)).re := by
    norm_num [Complex.add_re, Complex.mul_re]
  have hsum := summable_xiAntiCausalWardSchwarzPairResponse hw
  have hsumre : Summable fun p : XiRightUpperZeroCopy =>
      (xiAntiCausalWardSchwarzPairResponse p
        ((1 / 2 : ℂ) + I * (t : ℂ))).re :=
    (Complex.hasSum_re hsum.hasSum).summable
  have h2 : ∑ q ∈ F, ((xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) ^ 2 ≤
      (∑ q ∈ F, (xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg fun q _ =>
      (re_xiAntiCausalWardSchwarzPairResponse_pos q hw).le
  have h3 : (∑ q ∈ F, (xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) ≤
      (continuedXiAntiCausalWardResponse
        ((1 / 2 : ℂ) + I * (t : ℂ))).re := by
    rw [continuedXiAntiCausalWardResponse_eq_tsum_schwarzPairs hw,
      Complex.re_tsum hsum]
    exact hsumre.sum_le_tsum F fun q _ =>
      (re_xiAntiCausalWardSchwarzPairResponse_pos q hw).le
  have h3' : (∑ q ∈ F, (xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) ^ 2 ≤
      ((continuedXiAntiCausalWardResponse
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) ^ 2 :=
    pow_le_pow_left₀
      (Finset.sum_nonneg fun q _ =>
        (re_xiAntiCausalWardSchwarzPairResponse_pos q hw).le) h3 2
  have h4 : ((continuedXiAntiCausalWardResponse
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) ^ 2 ≤
      Complex.normSq (continuedXiAntiCausalWardResponse
        ((1 / 2 : ℂ) + I * (t : ℂ))) := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg (continuedXiAntiCausalWardResponse
      ((1 / 2 : ℂ) + I * (t : ℂ))).im]
  linarith

/-- **Graded counting law**: every finite family of strict-right pairs
deposits its full position-graded real-channel masses into the edge
quadratic energy. -/
theorem sum_sharp_le_xiWardEdgeQuadEnergy
    (F : Finset XiRightUpperZeroCopy) :
    ENNReal.ofReal (∑ q ∈ F, 4 * π *
      (1 / ((xiRightCenteredZero q.1).re + 1 / 2) +
        ((xiRightCenteredZero q.1).re + 1 / 2) /
          (((xiRightCenteredZero q.1).re + 1 / 2) ^ 2 +
            (xiRightCenteredZero q.1).im ^ 2))) ≤
    xiWardEdgeQuadEnergy := by
  have hintF : Integrable (fun t : ℝ =>
      ∑ q ∈ F, ((xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) ^ 2) volume :=
    integrable_finsetSum F fun q _ =>
      integrable_sq_re_xiAntiCausalWardSchwarzPairResponse_eulerEdge q
  have hval : (∫ t : ℝ, ∑ q ∈ F, ((xiAntiCausalWardSchwarzPairResponse q
      ((1 / 2 : ℂ) + I * (t : ℂ))).re) ^ 2)
      = ∑ q ∈ F, 4 * π *
        (1 / ((xiRightCenteredZero q.1).re + 1 / 2) +
          ((xiRightCenteredZero q.1).re + 1 / 2) /
            (((xiRightCenteredZero q.1).re + 1 / 2) ^ 2 +
              (xiRightCenteredZero q.1).im ^ 2)) := by
    rw [MeasureTheory.integral_finsetSum F fun q _ =>
      integrable_sq_re_xiAntiCausalWardSchwarzPairResponse_eulerEdge q]
    exact Finset.sum_congr rfl fun q _ =>
      integral_sq_re_xiAntiCausalWardSchwarzPairResponse_eulerEdge q
  unfold xiWardEdgeQuadEnergy
  calc ENNReal.ofReal (∑ q ∈ F, 4 * π *
      (1 / ((xiRightCenteredZero q.1).re + 1 / 2) +
        ((xiRightCenteredZero q.1).re + 1 / 2) /
          (((xiRightCenteredZero q.1).re + 1 / 2) ^ 2 +
            (xiRightCenteredZero q.1).im ^ 2)))
      = (∫⁻ t : ℝ, ENNReal.ofReal
          (∑ q ∈ F, ((xiAntiCausalWardSchwarzPairResponse q
            ((1 / 2 : ℂ) + I * (t : ℂ))).re) ^ 2)) := by
        rw [← hval]
        exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintF
          (Filter.Eventually.of_forall fun t =>
            Finset.sum_nonneg fun q _ => sq_nonneg _)
    _ ≤ (∫⁻ t : ℝ, ENNReal.ofReal (Complex.normSq
          (continuedXiAntiCausalWardResponse
            ((1 / 2 : ℂ) + I * (t : ℂ))))) := by
        apply MeasureTheory.lintegral_mono
        intro t
        exact ENNReal.ofReal_le_ofReal
          (sum_sq_re_xiAntiCausalWardSchwarzPairResponse_le_normSq F t)

/-- **Graded explicit-formula inequality**: the full series of
position-graded pair deposits is dominated by the edge quadratic energy.
The series lives in `ℝ≥0∞`, where the total is the supremum of its finite
partial sums — no rearrangement or product-series interchange enters. -/
theorem tsum_sharp_le_xiWardEdgeQuadEnergy :
    ∑' q : XiRightUpperZeroCopy, ENNReal.ofReal (4 * π *
      (1 / ((xiRightCenteredZero q.1).re + 1 / 2) +
        ((xiRightCenteredZero q.1).re + 1 / 2) /
          (((xiRightCenteredZero q.1).re + 1 / 2) ^ 2 +
            (xiRightCenteredZero q.1).im ^ 2))) ≤
    xiWardEdgeQuadEnergy := by
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro F
  rw [← ENNReal.ofReal_sum_of_nonneg (fun q _ => by
    have hre := xiRightCenteredZero_re_pos q.1
    positivity)]
  exact sum_sharp_le_xiWardEdgeQuadEnergy F

/-- Two-width same-side kernel products carry the cross-kernel modulus,
hence are integrable. -/
theorem integrable_sameSideKernelMul_general {x₁ x₂ : ℝ} (hx₁ : 0 < x₁)
    (hx₂ : 0 < x₂) (β₁ β₂ : ℝ) :
    Integrable fun t : ℝ =>
      ((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ *
        ((x₂ : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹ := by
  apply Integrable.mono' ((integrable_edgeCrossKernel hx₁ hx₂ β₁ β₂).norm)
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · apply Continuous.inv₀
      · exact continuous_const.add (continuous_const.mul
          (Complex.continuous_ofReal.comp
            (continuous_id.add continuous_const)))
      · exact edgeCrossKernel_denom_ne_zero₁ hx₁ β₁
    · apply Continuous.inv₀
      · exact continuous_const.add (continuous_const.mul
          (Complex.continuous_ofReal.comp
            (continuous_id.add continuous_const)))
      · exact edgeCrossKernel_denom_ne_zero₁ hx₂ β₂
  · filter_upwards with t
    have hconj : ‖((x₂ : ℂ) - I * ((t + β₂ : ℝ) : ℂ))‖ =
        ‖((x₂ : ℂ) + I * ((t + β₂ : ℝ) : ℂ))‖ := by
      have hcc : ((x₂ : ℂ) - I * ((t + β₂ : ℝ) : ℂ)) =
          (starRingEnd ℂ) ((x₂ : ℂ) + I * ((t + β₂ : ℝ) : ℂ)) := by
        rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I,
          Complex.conj_ofReal]
        ring
      rw [hcc, Complex.norm_conj]
    have heq : ‖((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ *
        ((x₂ : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹‖ =
        ‖edgeCrossKernel x₁ x₂ β₁ β₂ t‖ := by
      rw [edgeCrossKernel, norm_mul, norm_mul, norm_inv, norm_inv,
        norm_inv, hconj]
    exact le_of_eq heq

/-- **Two-width same-side vanishing**: distinct anti-causal kernels have
vanishing product integral — both poles lie in one half-plane. -/
theorem integral_sameSideKernelMul_general_zero {x₁ x₂ : ℝ}
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) {β₁ β₂ : ℝ}
    (hc : (((x₂ - x₁ : ℝ) : ℂ) + I * ((β₂ - β₁ : ℝ) : ℂ)) ≠ 0) :
    (∫ t : ℝ, ((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ *
      ((x₂ : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹) = 0 := by
  have hpf : ∀ t : ℝ,
      ((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ *
        ((x₂ : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹ =
      (((x₂ - x₁ : ℝ) : ℂ) + I * ((β₂ - β₁ : ℝ) : ℂ))⁻¹ *
        (((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ -
          ((x₂ : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹) := by
    intro t
    have h1 := edgeCrossKernel_denom_ne_zero₁ hx₁ β₁ t
    have h2 := edgeCrossKernel_denom_ne_zero₁ hx₂ β₂ t
    field_simp
    push_cast
    ring
  have hdiffint : Integrable (fun t : ℝ =>
      ((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ -
        ((x₂ : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹) := by
    have h := (integrable_sameSideKernelMul_general hx₁ hx₂ β₁ β₂).const_mul
      (((x₂ - x₁ : ℝ) : ℂ) + I * ((β₂ - β₁ : ℝ) : ℂ))
    apply h.congr
    filter_upwards with t
    rw [hpf t, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  have hreval : (∫ t : ℝ, ((((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ -
      ((x₂ : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹)).re) = 0 := by
    rw [show (fun t : ℝ => ((((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ -
        ((x₂ : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹)).re) =
        fun t : ℝ => x₁ / (x₁ ^ 2 + (t + β₁) ^ 2) -
          x₂ / (x₂ ^ 2 + (t + β₂) ^ 2) from funext fun t => by
      rw [Complex.sub_re, re_rightKernel_inv, re_rightKernel_inv]]
    rw [MeasureTheory.integral_sub (lorentzianHalf_integrable hx₁ β₁)
      (lorentzianHalf_integrable hx₂ β₂),
      integral_lorentzianHalf hx₁ β₁, integral_lorentzianHalf hx₂ β₂]
    ring
  have hoddInt := integrable_oddPieceShifted hx₁ hx₂ β₁
  have hsdInt : Integrable (fun t : ℝ =>
      (t + β₂) / (x₂ ^ 2 + (t + β₂) ^ 2) -
        (t + β₁) / (x₂ ^ 2 + (t + β₁) ^ 2)) := by
    have h1 := hdiffint.im.sub hoddInt
    apply h1.congr
    filter_upwards with t
    simp only [Pi.sub_apply, RCLike.im_to_complex]
    rw [Complex.sub_im, im_rightKernel_inv, im_rightKernel_inv]
    ring
  have himval : (∫ t : ℝ, ((((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ -
      ((x₂ : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹)).im) = 0 := by
    rw [show (fun t : ℝ => ((((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ -
        ((x₂ : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹)).im) =
        fun t : ℝ =>
          ((t + β₂) / (x₂ ^ 2 + (t + β₂) ^ 2) -
            (t + β₁) / (x₂ ^ 2 + (t + β₁) ^ 2)) +
          ((t + β₁) / (x₂ ^ 2 + (t + β₁) ^ 2) -
            (t + β₁) / (x₁ ^ 2 + (t + β₁) ^ 2)) from funext fun t => by
      rw [Complex.sub_im, im_rightKernel_inv, im_rightKernel_inv]
      ring]
    rw [MeasureTheory.integral_add hsdInt hoddInt,
      integral_shiftDiffPiece_zero hx₂ β₁ β₂ hsdInt,
      integral_oddPieceShifted_zero x₁ x₂ β₁]
    ring
  have hdiffval : (∫ t : ℝ, (((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ -
      ((x₂ : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹)) = 0 := by
    rw [← integral_re_add_im hdiffint]
    simp only [RCLike.re_to_complex, RCLike.im_to_complex,
      RCLike.I_to_complex]
    rw [hreval, himval]
    simp
  rw [show (fun t : ℝ => ((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ *
      ((x₂ : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹) =
      fun t : ℝ => (((x₂ - x₁ : ℝ) : ℂ) + I * ((β₂ - β₁ : ℝ) : ℂ))⁻¹ *
        (((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ -
          ((x₂ : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹) from funext hpf]
  rw [MeasureTheory.integral_const_mul, hdiffval, mul_zero]

/-- Real part of the master cross-kernel integral in closed form. -/
theorem integral_re_edgeCrossKernel_general {x₁ x₂ : ℝ} (hx₁ : 0 < x₁)
    (hx₂ : 0 < x₂) (β₁ β₂ : ℝ) :
    (∫ t : ℝ, (edgeCrossKernel x₁ x₂ β₁ β₂ t).re) =
      2 * π * (x₁ + x₂) / ((x₁ + x₂) ^ 2 + (β₁ - β₂) ^ 2) := by
  have hcomm := Complex.reCLM.integral_comp_comm
    (integrable_edgeCrossKernel hx₁ hx₂ β₁ β₂)
  rw [integral_edgeCrossKernel_eq hx₁ hx₂ β₁ β₂] at hcomm
  have hKre : (((x₁ + x₂ : ℝ) : ℂ) + I * ((β₁ - β₂ : ℝ) : ℂ)).re =
      x₁ + x₂ := by
    norm_num [Complex.add_re, Complex.mul_re]
  have hKim : (((x₁ + x₂ : ℝ) : ℂ) + I * ((β₁ - β₂ : ℝ) : ℂ)).im =
      β₁ - β₂ := by
    norm_num [Complex.add_im, Complex.mul_im]
  simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.inv_re,
    Complex.normSq_apply, hKre, hKim] at hcomm
  rw [hcomm]
  have hD : (0 : ℝ) < (x₁ + x₂) ^ 2 + (β₁ - β₂) ^ 2 := by positivity
  field_simp

/-- Two-width Lorentzian products are integrable. -/
theorem integrable_mul_lorentzianHalves_general {x₁ x₂ : ℝ}
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (β₁ β₂ : ℝ) :
    Integrable fun t : ℝ =>
      (x₁ / (x₁ ^ 2 + (t + β₁) ^ 2)) * (x₂ / (x₂ ^ 2 + (t + β₂) ^ 2)) := by
  apply Integrable.mono'
    ((lorentzianHalf_integrable hx₁ β₁).const_mul (1 / x₂))
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · exact continuous_const.div
        (continuous_const.add ((continuous_id.add continuous_const).pow 2))
        (fun t => by positivity)
    · exact continuous_const.div
        (continuous_const.add ((continuous_id.add continuous_const).pow 2))
        (fun t => by positivity)
  · filter_upwards with t
    have hD1 : (0 : ℝ) < x₁ ^ 2 + (t + β₁) ^ 2 := by positivity
    have hD2 : (0 : ℝ) < x₂ ^ 2 + (t + β₂) ^ 2 := by positivity
    have hL1 : 0 ≤ x₁ / (x₁ ^ 2 + (t + β₁) ^ 2) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hle : x₂ / (x₂ ^ 2 + (t + β₂) ^ 2) ≤ 1 / x₂ := by
      rw [div_le_div_iff₀ hD2 hx₂]
      nlinarith [sq_nonneg (t + β₂)]
    calc (x₁ / (x₁ ^ 2 + (t + β₁) ^ 2)) * (x₂ / (x₂ ^ 2 + (t + β₂) ^ 2))
        ≤ (x₁ / (x₁ ^ 2 + (t + β₁) ^ 2)) * (1 / x₂) :=
          mul_le_mul_of_nonneg_left hle hL1
      _ = 1 / x₂ * (x₁ / (x₁ ^ 2 + (t + β₁) ^ 2)) := by ring

/-- **General cross-Lorentzian mass**:
`∫ L_{x₁,β₁} L_{x₂,β₂} = π(x₁+x₂)/((x₁+x₂)² + (β₁−β₂)²)`. -/
theorem integral_mul_lorentzianHalves_general {x₁ x₂ : ℝ}
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (β₁ β₂ : ℝ) :
    ∫ t : ℝ, (x₁ / (x₁ ^ 2 + (t + β₁) ^ 2)) *
      (x₂ / (x₂ ^ 2 + (t + β₂) ^ 2)) =
      π * (x₁ + x₂) / ((x₁ + x₂) ^ 2 + (β₁ - β₂) ^ 2) := by
  by_cases hxx : x₁ = x₂
  · subst hxx
    rw [integral_mul_lorentzianHalves hx₁ β₁ β₂]
    have hD : (0 : ℝ) < 4 * x₁ ^ 2 + (β₁ - β₂) ^ 2 := by positivity
    have hD2 : (0 : ℝ) < (x₁ + x₁) ^ 2 + (β₁ - β₂) ^ 2 := by positivity
    field_simp
    ring
  · have hc : (((x₂ - x₁ : ℝ) : ℂ) + I * ((β₂ - β₁ : ℝ) : ℂ)) ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im,
        Complex.zero_re] at hre
      exact hxx (by linarith)
    have hpt : ∀ t : ℝ, (x₁ / (x₁ ^ 2 + (t + β₁) ^ 2)) *
        (x₂ / (x₂ ^ 2 + (t + β₂) ^ 2)) =
        (1 / 2 : ℝ) * (((((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ *
            ((x₂ : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹)).re +
          (edgeCrossKernel x₁ x₂ β₁ β₂ t).re) := by
      intro t
      simp only [edgeCrossKernel, Complex.mul_re, re_rightKernel_inv,
        im_rightKernel_inv, re_leftKernel_inv, im_leftKernel_inv]
      ring
    have h1re : Integrable (fun t : ℝ =>
        ((((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ *
          ((x₂ : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹)).re) volume :=
      (integrable_sameSideKernelMul_general hx₁ hx₂ β₁ β₂).re
    have h2re : Integrable (fun t : ℝ =>
        (edgeCrossKernel x₁ x₂ β₁ β₂ t).re) volume :=
      (integrable_edgeCrossKernel hx₁ hx₂ β₁ β₂).re
    rw [show (fun t : ℝ => (x₁ / (x₁ ^ 2 + (t + β₁) ^ 2)) *
        (x₂ / (x₂ ^ 2 + (t + β₂) ^ 2))) =
        fun t : ℝ =>
          (1 / 2 : ℝ) * (((((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ *
              ((x₂ : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹)).re +
            (edgeCrossKernel x₁ x₂ β₁ β₂ t).re) from funext hpt]
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add h1re h2re]
    have hre0 : (∫ t : ℝ,
        ((((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ *
          ((x₂ : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹)).re) = 0 := by
      have hcomm := Complex.reCLM.integral_comp_comm
        (integrable_sameSideKernelMul_general hx₁ hx₂ β₁ β₂)
      rw [integral_sameSideKernelMul_general_zero hx₁ hx₂ hc] at hcomm
      simpa using hcomm
    rw [hre0, integral_re_edgeCrossKernel_general hx₁ hx₂ β₁ β₂]
    have hD : (0 : ℝ) < (x₁ + x₂) ^ 2 + (β₁ - β₂) ^ 2 := by positivity
    field_simp
    ring

noncomputable local instance : Countable XiRightZeroCopy := inferInstance

noncomputable local instance : Countable XiRightUpperZeroCopy := inferInstance

/-- Distributivity of `ℝ≥0∞` series products over the product index. -/
theorem ennreal_tsum_mul_tsum {ι κ : Type*} (f : ι → ENNReal)
    (g : κ → ENNReal) :
    (∑' i, f i) * (∑' j, g j) = ∑' p : ι × κ, f p.1 * g p.2 := by
  rw [ENNReal.tsum_prod', ← ENNReal.tsum_mul_right]
  exact tsum_congr fun i => (ENNReal.tsum_mul_left).symm

/-- Products of edge real parts of two pairs are integrable. -/
theorem integrable_mul_re_xiPairs (q q' : XiRightUpperZeroCopy) :
    Integrable (fun t : ℝ =>
      ((xiAntiCausalWardSchwarzPairResponse q
          ((1 / 2 : ℂ) + I * (t : ℂ))).re) *
        ((xiAntiCausalWardSchwarzPairResponse q'
          ((1 / 2 : ℂ) + I * (t : ℂ))).re)) volume := by
  have hre := xiRightCenteredZero_re_pos q.1
  have hre' := xiRightCenteredZero_re_pos q'.1
  have hx : 0 < (xiRightCenteredZero q.1).re + 1 / 2 := by linarith
  have hx' : 0 < (xiRightCenteredZero q'.1).re + 1 / 2 := by linarith
  have h11 : Integrable (fun t : ℝ =>
      4 * ((((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + (xiRightCenteredZero q.1).im) ^ 2)) *
        ((((xiRightCenteredZero q'.1).re + 1 / 2)) /
          ((((xiRightCenteredZero q'.1).re + 1 / 2)) ^ 2 +
            (t + (xiRightCenteredZero q'.1).im) ^ 2)))) volume :=
    (integrable_mul_lorentzianHalves_general hx hx'
      ((xiRightCenteredZero q.1).im)
      ((xiRightCenteredZero q'.1).im)).const_mul 4
  have h12 : Integrable (fun t : ℝ =>
      4 * ((((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + (xiRightCenteredZero q.1).im) ^ 2)) *
        ((((xiRightCenteredZero q'.1).re + 1 / 2)) /
          ((((xiRightCenteredZero q'.1).re + 1 / 2)) ^ 2 +
            (t + -(xiRightCenteredZero q'.1).im) ^ 2)))) volume :=
    (integrable_mul_lorentzianHalves_general hx hx'
      ((xiRightCenteredZero q.1).im)
      (-(xiRightCenteredZero q'.1).im)).const_mul 4
  have h21 : Integrable (fun t : ℝ =>
      4 * ((((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + -(xiRightCenteredZero q.1).im) ^ 2)) *
        ((((xiRightCenteredZero q'.1).re + 1 / 2)) /
          ((((xiRightCenteredZero q'.1).re + 1 / 2)) ^ 2 +
            (t + (xiRightCenteredZero q'.1).im) ^ 2)))) volume :=
    (integrable_mul_lorentzianHalves_general hx hx'
      (-(xiRightCenteredZero q.1).im)
      ((xiRightCenteredZero q'.1).im)).const_mul 4
  have h22 : Integrable (fun t : ℝ =>
      4 * ((((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + -(xiRightCenteredZero q.1).im) ^ 2)) *
        ((((xiRightCenteredZero q'.1).re + 1 / 2)) /
          ((((xiRightCenteredZero q'.1).re + 1 / 2)) ^ 2 +
            (t + -(xiRightCenteredZero q'.1).im) ^ 2)))) volume :=
    (integrable_mul_lorentzianHalves_general hx hx'
      (-(xiRightCenteredZero q.1).im)
      (-(xiRightCenteredZero q'.1).im)).const_mul 4
  have h := ((h11.add h12).add h21).add h22
  apply h.congr
  filter_upwards with t
  simp only [Pi.add_apply]
  rw [re_xiAntiCausalWardSchwarzPairResponse_eulerEdge_eq,
    re_xiAntiCausalWardSchwarzPairResponse_eulerEdge_eq]
  ring

/-- **Pair-pair real-channel deposit** in closed form: with
`x = Re λ + 1/2`, `x′ = Re λ′ + 1/2`, `b = Im λ`, `b′ = Im λ′`, the mixed
edge deposit of two strict-right pairs is
`8π(x+x′)(1/((x+x′)²+(b−b′)²) + 1/((x+x′)²+(b+b′)²))`. -/
theorem integral_mul_re_xiPairs (q q' : XiRightUpperZeroCopy) :
    ∫ t : ℝ, ((xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) *
      ((xiAntiCausalWardSchwarzPairResponse q'
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) =
      8 * π * (((xiRightCenteredZero q.1).re + 1 / 2) +
          (((xiRightCenteredZero q'.1).re + 1 / 2))) *
        (1 / (((((xiRightCenteredZero q.1).re + 1 / 2) +
              (((xiRightCenteredZero q'.1).re + 1 / 2)))) ^ 2 +
            ((xiRightCenteredZero q.1).im -
              (xiRightCenteredZero q'.1).im) ^ 2) +
          1 / (((((xiRightCenteredZero q.1).re + 1 / 2) +
              (((xiRightCenteredZero q'.1).re + 1 / 2)))) ^ 2 +
            ((xiRightCenteredZero q.1).im +
              (xiRightCenteredZero q'.1).im) ^ 2)) := by
  have hre := xiRightCenteredZero_re_pos q.1
  have hre' := xiRightCenteredZero_re_pos q'.1
  have hx : 0 < (xiRightCenteredZero q.1).re + 1 / 2 := by linarith
  have hx' : 0 < (xiRightCenteredZero q'.1).re + 1 / 2 := by linarith
  have h11 : Integrable (fun t : ℝ =>
      4 * ((((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + (xiRightCenteredZero q.1).im) ^ 2)) *
        ((((xiRightCenteredZero q'.1).re + 1 / 2)) /
          ((((xiRightCenteredZero q'.1).re + 1 / 2)) ^ 2 +
            (t + (xiRightCenteredZero q'.1).im) ^ 2)))) volume :=
    (integrable_mul_lorentzianHalves_general hx hx'
      ((xiRightCenteredZero q.1).im)
      ((xiRightCenteredZero q'.1).im)).const_mul 4
  have h12 : Integrable (fun t : ℝ =>
      4 * ((((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + (xiRightCenteredZero q.1).im) ^ 2)) *
        ((((xiRightCenteredZero q'.1).re + 1 / 2)) /
          ((((xiRightCenteredZero q'.1).re + 1 / 2)) ^ 2 +
            (t + -(xiRightCenteredZero q'.1).im) ^ 2)))) volume :=
    (integrable_mul_lorentzianHalves_general hx hx'
      ((xiRightCenteredZero q.1).im)
      (-(xiRightCenteredZero q'.1).im)).const_mul 4
  have h21 : Integrable (fun t : ℝ =>
      4 * ((((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + -(xiRightCenteredZero q.1).im) ^ 2)) *
        ((((xiRightCenteredZero q'.1).re + 1 / 2)) /
          ((((xiRightCenteredZero q'.1).re + 1 / 2)) ^ 2 +
            (t + (xiRightCenteredZero q'.1).im) ^ 2)))) volume :=
    (integrable_mul_lorentzianHalves_general hx hx'
      (-(xiRightCenteredZero q.1).im)
      ((xiRightCenteredZero q'.1).im)).const_mul 4
  have h22 : Integrable (fun t : ℝ =>
      4 * ((((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + -(xiRightCenteredZero q.1).im) ^ 2)) *
        ((((xiRightCenteredZero q'.1).re + 1 / 2)) /
          ((((xiRightCenteredZero q'.1).re + 1 / 2)) ^ 2 +
            (t + -(xiRightCenteredZero q'.1).im) ^ 2)))) volume :=
    (integrable_mul_lorentzianHalves_general hx hx'
      (-(xiRightCenteredZero q.1).im)
      (-(xiRightCenteredZero q'.1).im)).const_mul 4
  have h1122 : Integrable (fun t : ℝ =>
      (4 * ((((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + (xiRightCenteredZero q.1).im) ^ 2)) *
        ((((xiRightCenteredZero q'.1).re + 1 / 2)) /
          ((((xiRightCenteredZero q'.1).re + 1 / 2)) ^ 2 +
            (t + (xiRightCenteredZero q'.1).im) ^ 2))) +
       4 * ((((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + (xiRightCenteredZero q.1).im) ^ 2)) *
        ((((xiRightCenteredZero q'.1).re + 1 / 2)) /
          ((((xiRightCenteredZero q'.1).re + 1 / 2)) ^ 2 +
            (t + -(xiRightCenteredZero q'.1).im) ^ 2))))) volume :=
    h11.add h12
  have h2122 : Integrable (fun t : ℝ =>
      (4 * ((((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + -(xiRightCenteredZero q.1).im) ^ 2)) *
        ((((xiRightCenteredZero q'.1).re + 1 / 2)) /
          ((((xiRightCenteredZero q'.1).re + 1 / 2)) ^ 2 +
            (t + (xiRightCenteredZero q'.1).im) ^ 2))) +
       4 * ((((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + -(xiRightCenteredZero q.1).im) ^ 2)) *
        ((((xiRightCenteredZero q'.1).re + 1 / 2)) /
          ((((xiRightCenteredZero q'.1).re + 1 / 2)) ^ 2 +
            (t + -(xiRightCenteredZero q'.1).im) ^ 2))))) volume :=
    h21.add h22
  rw [show (fun t : ℝ => ((xiAntiCausalWardSchwarzPairResponse q
      ((1 / 2 : ℂ) + I * (t : ℂ))).re) *
      ((xiAntiCausalWardSchwarzPairResponse q'
        ((1 / 2 : ℂ) + I * (t : ℂ))).re)) =
      fun t : ℝ =>
        ((4 * ((((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + (xiRightCenteredZero q.1).im) ^ 2)) *
        ((((xiRightCenteredZero q'.1).re + 1 / 2)) /
          ((((xiRightCenteredZero q'.1).re + 1 / 2)) ^ 2 +
            (t + (xiRightCenteredZero q'.1).im) ^ 2))) +
       4 * ((((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + (xiRightCenteredZero q.1).im) ^ 2)) *
        ((((xiRightCenteredZero q'.1).re + 1 / 2)) /
          ((((xiRightCenteredZero q'.1).re + 1 / 2)) ^ 2 +
            (t + -(xiRightCenteredZero q'.1).im) ^ 2))))) +
        ((4 * ((((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + -(xiRightCenteredZero q.1).im) ^ 2)) *
        ((((xiRightCenteredZero q'.1).re + 1 / 2)) /
          ((((xiRightCenteredZero q'.1).re + 1 / 2)) ^ 2 +
            (t + (xiRightCenteredZero q'.1).im) ^ 2))) +
       4 * ((((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + -(xiRightCenteredZero q.1).im) ^ 2)) *
        ((((xiRightCenteredZero q'.1).re + 1 / 2)) /
          ((((xiRightCenteredZero q'.1).re + 1 / 2)) ^ 2 +
            (t + -(xiRightCenteredZero q'.1).im) ^ 2))))) from
    funext fun t => by
      rw [re_xiAntiCausalWardSchwarzPairResponse_eulerEdge_eq,
        re_xiAntiCausalWardSchwarzPairResponse_eulerEdge_eq]
      ring]
  rw [MeasureTheory.integral_add h1122 h2122,
    MeasureTheory.integral_add h11 h12,
    MeasureTheory.integral_add h21 h22,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    integral_mul_lorentzianHalves_general hx hx'
      ((xiRightCenteredZero q.1).im) ((xiRightCenteredZero q'.1).im),
    integral_mul_lorentzianHalves_general hx hx'
      ((xiRightCenteredZero q.1).im) (-(xiRightCenteredZero q'.1).im),
    integral_mul_lorentzianHalves_general hx hx'
      (-(xiRightCenteredZero q.1).im) ((xiRightCenteredZero q'.1).im),
    integral_mul_lorentzianHalves_general hx hx'
      (-(xiRightCenteredZero q.1).im) (-(xiRightCenteredZero q'.1).im)]
  have hxx : (0 : ℝ) < ((xiRightCenteredZero q.1).re + 1 / 2) +
      ((xiRightCenteredZero q'.1).re + 1 / 2) := by linarith
  have hA : (0 : ℝ) < (((xiRightCenteredZero q.1).re + 1 / 2) +
      ((xiRightCenteredZero q'.1).re + 1 / 2)) ^ 2 +
      ((xiRightCenteredZero q.1).im - (xiRightCenteredZero q'.1).im) ^ 2 :=
    by positivity
  have hB : (0 : ℝ) < (((xiRightCenteredZero q.1).re + 1 / 2) +
      ((xiRightCenteredZero q'.1).re + 1 / 2)) ^ 2 +
      ((xiRightCenteredZero q.1).im + (xiRightCenteredZero q'.1).im) ^ 2 :=
    by positivity
  have hC : (0 : ℝ) < (((xiRightCenteredZero q.1).re + 1 / 2) +
      ((xiRightCenteredZero q'.1).re + 1 / 2)) ^ 2 +
      (-(xiRightCenteredZero q.1).im - (xiRightCenteredZero q'.1).im) ^ 2 :=
    by positivity
  have hD : (0 : ℝ) < (((xiRightCenteredZero q.1).re + 1 / 2) +
      ((xiRightCenteredZero q'.1).re + 1 / 2)) ^ 2 +
      (-(xiRightCenteredZero q.1).im - -(xiRightCenteredZero q'.1).im) ^ 2 :=
    by positivity
  field_simp
  ring

/-- **Quadratic explicit formula, real channel**: the edge quadratic energy
of the real part of the continued Ward response equals the positive lattice
sum of all ordered pair-pair deposits.  The identity lives in `ℝ≥0∞`, where
series are suprema of finite partial sums and Tonelli interchange carries
no side conditions: the formula is unconditional. -/
theorem lintegral_sq_re_continuedXiAntiCausalWardResponse_eq_tsum :
    ∫⁻ t : ℝ, ENNReal.ofReal
      (((continuedXiAntiCausalWardResponse
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) ^ 2) =
    ∑' p : XiRightUpperZeroCopy × XiRightUpperZeroCopy,
      ENNReal.ofReal (8 * π * (((xiRightCenteredZero p.1.1).re + 1 / 2) +
          (((xiRightCenteredZero p.2.1).re + 1 / 2))) *
        (1 / (((((xiRightCenteredZero p.1.1).re + 1 / 2) +
              (((xiRightCenteredZero p.2.1).re + 1 / 2)))) ^ 2 +
            ((xiRightCenteredZero p.1.1).im -
              (xiRightCenteredZero p.2.1).im) ^ 2) +
          1 / (((((xiRightCenteredZero p.1.1).re + 1 / 2) +
              (((xiRightCenteredZero p.2.1).re + 1 / 2)))) ^ 2 +
            ((xiRightCenteredZero p.1.1).im +
              (xiRightCenteredZero p.2.1).im) ^ 2))) := by
  have hpt : ∀ t : ℝ, ENNReal.ofReal
      (((continuedXiAntiCausalWardResponse
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) ^ 2) =
      ∑' p : XiRightUpperZeroCopy × XiRightUpperZeroCopy,
        ENNReal.ofReal ((xiAntiCausalWardSchwarzPairResponse p.1
            ((1 / 2 : ℂ) + I * (t : ℂ))).re *
          (xiAntiCausalWardSchwarzPairResponse p.2
            ((1 / 2 : ℂ) + I * (t : ℂ))).re) := by
    intro t
    have hw : (0 : ℝ) < ((1 / 2 : ℂ) + I * (t : ℂ)).re := by
      norm_num [Complex.add_re, Complex.mul_re]
    have hsum := summable_xiAntiCausalWardSchwarzPairResponse hw
    have hsumre : Summable fun p : XiRightUpperZeroCopy =>
        (xiAntiCausalWardSchwarzPairResponse p
          ((1 / 2 : ℂ) + I * (t : ℂ))).re :=
      (Complex.hasSum_re hsum.hasSum).summable
    have hnn : ∀ p : XiRightUpperZeroCopy,
        0 ≤ (xiAntiCausalWardSchwarzPairResponse p
          ((1 / 2 : ℂ) + I * (t : ℂ))).re :=
      fun p => (re_xiAntiCausalWardSchwarzPairResponse_pos p hw).le
    have hre : (continuedXiAntiCausalWardResponse
        ((1 / 2 : ℂ) + I * (t : ℂ))).re =
        ∑' p : XiRightUpperZeroCopy,
          (xiAntiCausalWardSchwarzPairResponse p
            ((1 / 2 : ℂ) + I * (t : ℂ))).re := by
      rw [continuedXiAntiCausalWardResponse_eq_tsum_schwarzPairs hw,
        Complex.re_tsum hsum]
    rw [hre, ENNReal.ofReal_pow (tsum_nonneg hnn),
      ENNReal.ofReal_tsum_of_nonneg hnn hsumre, pow_two,
      ennreal_tsum_mul_tsum]
    exact tsum_congr fun p => (ENNReal.ofReal_mul (hnn p.1)).symm
  rw [show (fun t : ℝ => ENNReal.ofReal
      (((continuedXiAntiCausalWardResponse
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) ^ 2)) =
      fun t : ℝ =>
        ∑' p : XiRightUpperZeroCopy × XiRightUpperZeroCopy,
          ENNReal.ofReal ((xiAntiCausalWardSchwarzPairResponse p.1
              ((1 / 2 : ℂ) + I * (t : ℂ))).re *
            (xiAntiCausalWardSchwarzPairResponse p.2
              ((1 / 2 : ℂ) + I * (t : ℂ))).re) from funext hpt]
  have hmeas : ∀ p : XiRightUpperZeroCopy × XiRightUpperZeroCopy,
      AEMeasurable (fun t : ℝ =>
        ENNReal.ofReal ((xiAntiCausalWardSchwarzPairResponse p.1
            ((1 / 2 : ℂ) + I * (t : ℂ))).re *
          (xiAntiCausalWardSchwarzPairResponse p.2
            ((1 / 2 : ℂ) + I * (t : ℂ))).re)) volume := by
    intro p
    exact ((ENNReal.continuous_ofReal.comp
      ((re_xiAntiCausalWardSchwarzPairResponse_eulerEdge_continuous p.1).mul
        (re_xiAntiCausalWardSchwarzPairResponse_eulerEdge_continuous
          p.2))).measurable).aemeasurable
  rw [MeasureTheory.lintegral_tsum hmeas]
  refine tsum_congr fun p => ?_
  have hw : ∀ t : ℝ, (0 : ℝ) < ((1 / 2 : ℂ) + I * (t : ℂ)).re := by
    intro t
    norm_num [Complex.add_re, Complex.mul_re]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (integrable_mul_re_xiPairs p.1 p.2)
    (Filter.Eventually.of_forall fun t =>
      mul_nonneg (re_xiAntiCausalWardSchwarzPairResponse_pos p.1
        (hw t)).le
        (re_xiAntiCausalWardSchwarzPairResponse_pos p.2 (hw t)).le),
    integral_mul_re_xiPairs p.1 p.2]

/-- The real-channel edge energy is dominated by the full edge quadratic
energy. -/
theorem lintegral_sq_re_le_xiWardEdgeQuadEnergy :
    (∫⁻ t : ℝ, ENNReal.ofReal
      (((continuedXiAntiCausalWardResponse
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) ^ 2)) ≤ xiWardEdgeQuadEnergy := by
  unfold xiWardEdgeQuadEnergy
  apply MeasureTheory.lintegral_mono
  intro t
  apply ENNReal.ofReal_le_ofReal
  rw [Complex.normSq_apply]
  nlinarith [sq_nonneg (continuedXiAntiCausalWardResponse
    ((1 / 2 : ℂ) + I * (t : ℂ))).im]

/-- **Lattice-sum floor for the edge energy**: the full ordered pair-pair
deposit sum is dominated by the edge quadratic energy. -/
theorem tsum_pairPair_le_xiWardEdgeQuadEnergy :
    (∑' p : XiRightUpperZeroCopy × XiRightUpperZeroCopy,
      ENNReal.ofReal (8 * π * (((xiRightCenteredZero p.1.1).re + 1 / 2) +
          (((xiRightCenteredZero p.2.1).re + 1 / 2))) *
        (1 / (((((xiRightCenteredZero p.1.1).re + 1 / 2) +
              (((xiRightCenteredZero p.2.1).re + 1 / 2)))) ^ 2 +
            ((xiRightCenteredZero p.1.1).im -
              (xiRightCenteredZero p.2.1).im) ^ 2) +
          1 / (((((xiRightCenteredZero p.1.1).re + 1 / 2) +
              (((xiRightCenteredZero p.2.1).re + 1 / 2)))) ^ 2 +
            ((xiRightCenteredZero p.1.1).im +
              (xiRightCenteredZero p.2.1).im) ^ 2)))) ≤
    xiWardEdgeQuadEnergy := by
  rw [← lintegral_sq_re_continuedXiAntiCausalWardResponse_eq_tsum]
  exact lintegral_sq_re_le_xiWardEdgeQuadEnergy

end

end RHTower
