import GaloisForLFunctions.RHTower.XiWardEdgeReChannelDeposit

/-!
# The imaginary channel and the pair Gram matrix

The edge imaginary part of a strict-right Schwarz pair is a sum of two odd
kernels `O(x,β) = (t+β)/(x²+(t+β)²)`.  The odd-kernel product calculus
mirrors the Lorentzian one exactly — same-side products vanish and
`∫ O₁O₂ = π(x₁+x₂)/((x₁+x₂)²+(β₁−β₂)²)` — so every pair-pair imaginary
deposit EQUALS the corresponding real deposit: the two channels
equipartition pairwise, not only on the diagonal.  Consequently the real
`L²` inner products of the pair family form an explicit Gram matrix
`G(q,q′) = 16π(x+x′)(1/((x+x′)²+(b−b′)²) + 1/((x+x′)²+(b+b′)²))`. -/

open Complex MeasureTheory Real

namespace RHTower

noncomputable section

/-- Squared odd kernels are integrable: `O² ≤ x⁻¹ · (Lorentzian half)`. -/
theorem integrable_sq_oddKernel {x : ℝ} (hx : 0 < x) (β : ℝ) :
    Integrable fun t : ℝ =>
      ((t + β) / (x ^ 2 + (t + β) ^ 2)) ^ 2 := by
  apply Integrable.mono' ((lorentzianHalf_integrable hx β).const_mul (1 / x))
  · apply Continuous.aestronglyMeasurable
    apply Continuous.pow
    exact (continuous_id.add continuous_const).div
      (continuous_const.add ((continuous_id.add continuous_const).pow 2))
      (fun t => by positivity)
  · filter_upwards with t
    have hD : (0 : ℝ) < x ^ 2 + (t + β) ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [div_pow, div_le_iff₀ (by positivity : (0 : ℝ) < (x ^ 2 + (t + β) ^ 2) ^ 2)]
    have hexp : 1 / x * (x / (x ^ 2 + (t + β) ^ 2)) *
        (x ^ 2 + (t + β) ^ 2) ^ 2 = x ^ 2 + (t + β) ^ 2 := by
      field_simp
    rw [hexp]
    nlinarith [sq_nonneg x, sq_nonneg (t + β)]

/-- Products of odd kernels are integrable (arithmetic–geometric bound). -/
theorem integrable_mul_oddKernels_general {x₁ x₂ : ℝ} (hx₁ : 0 < x₁)
    (hx₂ : 0 < x₂) (β₁ β₂ : ℝ) :
    Integrable fun t : ℝ =>
      ((t + β₁) / (x₁ ^ 2 + (t + β₁) ^ 2)) *
        ((t + β₂) / (x₂ ^ 2 + (t + β₂) ^ 2)) := by
  apply Integrable.mono'
    (((integrable_sq_oddKernel hx₁ β₁).const_mul (1 / 2)).add
      ((integrable_sq_oddKernel hx₂ β₂).const_mul (1 / 2)))
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · exact (continuous_id.add continuous_const).div
        (continuous_const.add ((continuous_id.add continuous_const).pow 2))
        (fun t => by positivity)
    · exact (continuous_id.add continuous_const).div
        (continuous_const.add ((continuous_id.add continuous_const).pow 2))
        (fun t => by positivity)
  · filter_upwards with t
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |( t + β₁) / (x₁ ^ 2 + (t + β₁) ^ 2)| ^ 2 =
        ((t + β₁) / (x₁ ^ 2 + (t + β₁) ^ 2)) ^ 2 := sq_abs _
    have h2 : |(t + β₂) / (x₂ ^ 2 + (t + β₂) ^ 2)| ^ 2 =
        ((t + β₂) / (x₂ ^ 2 + (t + β₂) ^ 2)) ^ 2 := sq_abs _
    nlinarith [sq_nonneg (|(t + β₁) / (x₁ ^ 2 + (t + β₁) ^ 2)| -
      |(t + β₂) / (x₂ ^ 2 + (t + β₂) ^ 2)|),
      abs_nonneg ((t + β₁) / (x₁ ^ 2 + (t + β₁) ^ 2)),
      abs_nonneg ((t + β₂) / (x₂ ^ 2 + (t + β₂) ^ 2))]

/-- **Odd-kernel cross mass**: identical to the Lorentzian one,
`∫ O₁O₂ = π(x₁+x₂)/((x₁+x₂)² + (β₁−β₂)²)`. -/
theorem integral_mul_oddKernels_general {x₁ x₂ : ℝ} (hx₁ : 0 < x₁)
    (hx₂ : 0 < x₂) (β₁ β₂ : ℝ) :
    ∫ t : ℝ, ((t + β₁) / (x₁ ^ 2 + (t + β₁) ^ 2)) *
      ((t + β₂) / (x₂ ^ 2 + (t + β₂) ^ 2)) =
      π * (x₁ + x₂) / ((x₁ + x₂) ^ 2 + (β₁ - β₂) ^ 2) := by
  by_cases hb : x₁ = x₂ ∧ β₁ = β₂
  · obtain ⟨hxx, hbb⟩ := hb
    subst hxx
    subst hbb
    have hpt : ∀ t : ℝ, ((t + β₁) / (x₁ ^ 2 + (t + β₁) ^ 2)) *
        ((t + β₁) / (x₁ ^ 2 + (t + β₁) ^ 2)) =
        (1 / 2 : ℝ) * ((edgeCrossKernel x₁ x₁ β₁ β₁ t).re -
          ((((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ *
            ((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹)).re) := by
      intro t
      simp only [edgeCrossKernel, Complex.mul_re, re_rightKernel_inv,
        im_rightKernel_inv, re_leftKernel_inv, im_leftKernel_inv]
      ring
    have h1re : Integrable (fun t : ℝ =>
        (edgeCrossKernel x₁ x₁ β₁ β₁ t).re) volume :=
      (integrable_edgeCrossKernel hx₁ hx₁ β₁ β₁).re
    have h2re : Integrable (fun t : ℝ =>
        ((((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ *
          ((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹)).re) volume :=
      (integrable_sameSideKernelMul_general hx₁ hx₁ β₁ β₁).re
    rw [show (fun t : ℝ => ((t + β₁) / (x₁ ^ 2 + (t + β₁) ^ 2)) *
        ((t + β₁) / (x₁ ^ 2 + (t + β₁) ^ 2))) =
        fun t : ℝ =>
          (1 / 2 : ℝ) * ((edgeCrossKernel x₁ x₁ β₁ β₁ t).re -
            ((((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ *
              ((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹)).re) from funext hpt]
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_sub h1re h2re]
    have hsq0 : (∫ t : ℝ,
        ((((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ *
          ((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹)).re) = 0 := by
      have hint : Integrable fun t : ℝ =>
          ((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ *
            ((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ :=
        integrable_sameSideKernelMul_general hx₁ hx₁ β₁ β₁
      have hcomm := Complex.reCLM.integral_comp_comm hint
      have hzero : (∫ t : ℝ,
          ((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ *
            ((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹) = 0 := by
        rw [show (fun t : ℝ =>
            ((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ *
              ((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹) =
            fun t : ℝ =>
              (((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹) ^ 2 from
          funext fun t => by rw [pow_two]]
        exact integral_sq_rightKernel_inv hx₁ β₁
      rw [hzero] at hcomm
      simpa using hcomm
    rw [hsq0, integral_re_edgeCrossKernel_general hx₁ hx₁ β₁ β₁]
    have hD : (0 : ℝ) < (x₁ + x₁) ^ 2 + (β₁ - β₁) ^ 2 := by positivity
    field_simp
    ring
  · have hc : (((x₂ - x₁ : ℝ) : ℂ) + I * ((β₂ - β₁ : ℝ) : ℂ)) ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      have him := congrArg Complex.im h
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.zero_re,
        Complex.add_im, Complex.mul_im, Complex.zero_im] at hre him
      exact hb ⟨by linarith, by linarith⟩
    have hpt : ∀ t : ℝ, ((t + β₁) / (x₁ ^ 2 + (t + β₁) ^ 2)) *
        ((t + β₂) / (x₂ ^ 2 + (t + β₂) ^ 2)) =
        (1 / 2 : ℝ) * ((edgeCrossKernel x₁ x₂ β₁ β₂ t).re -
          ((((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ *
            ((x₂ : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹)).re) := by
      intro t
      simp only [edgeCrossKernel, Complex.mul_re, re_rightKernel_inv,
        im_rightKernel_inv, re_leftKernel_inv, im_leftKernel_inv]
      ring
    have h1re : Integrable (fun t : ℝ =>
        (edgeCrossKernel x₁ x₂ β₁ β₂ t).re) volume :=
      (integrable_edgeCrossKernel hx₁ hx₂ β₁ β₂).re
    have h2re : Integrable (fun t : ℝ =>
        ((((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ *
          ((x₂ : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹)).re) volume :=
      (integrable_sameSideKernelMul_general hx₁ hx₂ β₁ β₂).re
    rw [show (fun t : ℝ => ((t + β₁) / (x₁ ^ 2 + (t + β₁) ^ 2)) *
        ((t + β₂) / (x₂ ^ 2 + (t + β₂) ^ 2))) =
        fun t : ℝ =>
          (1 / 2 : ℝ) * ((edgeCrossKernel x₁ x₂ β₁ β₂ t).re -
            ((((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ *
              ((x₂ : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹)).re) from funext hpt]
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_sub h1re h2re]
    have hss0 : (∫ t : ℝ,
        ((((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ *
          ((x₂ : ℂ) + I * ((t + β₂ : ℝ) : ℂ))⁻¹)).re) = 0 := by
      have hcomm := Complex.reCLM.integral_comp_comm
        (integrable_sameSideKernelMul_general hx₁ hx₂ β₁ β₂)
      rw [integral_sameSideKernelMul_general_zero hx₁ hx₂ hc] at hcomm
      simpa using hcomm
    rw [hss0, integral_re_edgeCrossKernel_general hx₁ hx₂ β₁ β₂]
    have hD : (0 : ℝ) < (x₁ + x₂) ^ 2 + (β₁ - β₂) ^ 2 := by positivity
    field_simp
    ring

/-- Edge imaginary part of one pair: two odd kernels. -/
theorem im_xiAntiCausalWardSchwarzPairResponse_eulerEdge_eq
    (q : XiRightUpperZeroCopy) (t : ℝ) :
    (xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).im =
      -(2 * ((t + (xiRightCenteredZero q.1).im) /
        (((xiRightCenteredZero q.1).re + 1 / 2) ^ 2 +
          (t + (xiRightCenteredZero q.1).im) ^ 2))) +
      -(2 * ((t + -(xiRightCenteredZero q.1).im) /
        (((xiRightCenteredZero q.1).re + 1 / 2) ^ 2 +
          (t + -(xiRightCenteredZero q.1).im) ^ 2))) := by
  rw [xiAntiCausalWardSchwarzPairResponse_eulerEdge_eq_kernels]
  rw [Complex.mul_im, Complex.add_im, im_rightKernel_inv,
    im_rightKernel_inv, Complex.add_re, re_rightKernel_inv,
    re_rightKernel_inv]
  simp only [Complex.re_ofNat, Complex.im_ofNat]
  ring

/-- Products of edge imaginary parts of two pairs are integrable. -/
theorem integrable_mul_im_xiPairs (q q' : XiRightUpperZeroCopy) :
    Integrable (fun t : ℝ =>
      ((xiAntiCausalWardSchwarzPairResponse q
          ((1 / 2 : ℂ) + I * (t : ℂ))).im) *
        ((xiAntiCausalWardSchwarzPairResponse q'
          ((1 / 2 : ℂ) + I * (t : ℂ))).im)) volume := by
  have hre := xiRightCenteredZero_re_pos q.1
  have hre' := xiRightCenteredZero_re_pos q'.1
  have hx : 0 < (xiRightCenteredZero q.1).re + 1 / 2 := by linarith
  have hx' : 0 < (xiRightCenteredZero q'.1).re + 1 / 2 := by linarith
  have h11 : Integrable (fun t : ℝ =>
      4 * (((t + (xiRightCenteredZero q.1).im) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + (xiRightCenteredZero q.1).im) ^ 2)) *
        ((t + (xiRightCenteredZero q'.1).im) /
          ((((xiRightCenteredZero q'.1).re + 1 / 2)) ^ 2 +
            (t + (xiRightCenteredZero q'.1).im) ^ 2)))) volume :=
    (integrable_mul_oddKernels_general hx hx'
      ((xiRightCenteredZero q.1).im)
      ((xiRightCenteredZero q'.1).im)).const_mul 4
  have h12 : Integrable (fun t : ℝ =>
      4 * (((t + (xiRightCenteredZero q.1).im) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + (xiRightCenteredZero q.1).im) ^ 2)) *
        ((t + -(xiRightCenteredZero q'.1).im) /
          ((((xiRightCenteredZero q'.1).re + 1 / 2)) ^ 2 +
            (t + -(xiRightCenteredZero q'.1).im) ^ 2)))) volume :=
    (integrable_mul_oddKernels_general hx hx'
      ((xiRightCenteredZero q.1).im)
      (-(xiRightCenteredZero q'.1).im)).const_mul 4
  have h21 : Integrable (fun t : ℝ =>
      4 * (((t + -(xiRightCenteredZero q.1).im) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + -(xiRightCenteredZero q.1).im) ^ 2)) *
        ((t + (xiRightCenteredZero q'.1).im) /
          ((((xiRightCenteredZero q'.1).re + 1 / 2)) ^ 2 +
            (t + (xiRightCenteredZero q'.1).im) ^ 2)))) volume :=
    (integrable_mul_oddKernels_general hx hx'
      (-(xiRightCenteredZero q.1).im)
      ((xiRightCenteredZero q'.1).im)).const_mul 4
  have h22 : Integrable (fun t : ℝ =>
      4 * (((t + -(xiRightCenteredZero q.1).im) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + -(xiRightCenteredZero q.1).im) ^ 2)) *
        ((t + -(xiRightCenteredZero q'.1).im) /
          ((((xiRightCenteredZero q'.1).re + 1 / 2)) ^ 2 +
            (t + -(xiRightCenteredZero q'.1).im) ^ 2)))) volume :=
    (integrable_mul_oddKernels_general hx hx'
      (-(xiRightCenteredZero q.1).im)
      (-(xiRightCenteredZero q'.1).im)).const_mul 4
  have h := ((h11.add h12).add h21).add h22
  apply h.congr
  filter_upwards with t
  simp only [Pi.add_apply]
  rw [im_xiAntiCausalWardSchwarzPairResponse_eulerEdge_eq,
    im_xiAntiCausalWardSchwarzPairResponse_eulerEdge_eq]
  ring

/-- **Pair-pair imaginary-channel deposit**: identical closed form to the
real channel. -/
theorem integral_mul_im_xiPairs (q q' : XiRightUpperZeroCopy) :
    ∫ t : ℝ, ((xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).im) *
      ((xiAntiCausalWardSchwarzPairResponse q'
        ((1 / 2 : ℂ) + I * (t : ℂ))).im) =
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
  have h := integral_mul_mirroredKernelPair
    (k := fun x β t => (t + β) / (x ^ 2 + (t + β) ^ 2)) hx hx'
    (integrable_mul_oddKernels_general hx hx')
    (integral_mul_oddKernels_general hx hx')
    (-2) (-2) ((xiRightCenteredZero q.1).im) ((xiRightCenteredZero q'.1).im)
    (f := fun t => (xiAntiCausalWardSchwarzPairResponse q ((1 / 2 : ℂ) + I * (t : ℂ))).im)
    (f' := fun t => (xiAntiCausalWardSchwarzPairResponse q' ((1 / 2 : ℂ) + I * (t : ℂ))).im)
    (fun t => by dsimp only; rw [im_xiAntiCausalWardSchwarzPairResponse_eulerEdge_eq]; ring)
    (fun t => by dsimp only; rw [im_xiAntiCausalWardSchwarzPairResponse_eulerEdge_eq]; ring)
  rw [h]
  ring

/-- **Pairwise channel equipartition**: every pair-pair imaginary deposit
equals its real counterpart. -/
theorem integral_mul_im_eq_integral_mul_re_xiPairs
    (q q' : XiRightUpperZeroCopy) :
    (∫ t : ℝ, ((xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).im) *
      ((xiAntiCausalWardSchwarzPairResponse q'
        ((1 / 2 : ℂ) + I * (t : ℂ))).im)) =
    ∫ t : ℝ, ((xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) *
      ((xiAntiCausalWardSchwarzPairResponse q'
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) := by
  rw [integral_mul_im_xiPairs q q', integral_mul_re_xiPairs q q']

/-- **The pair Gram matrix**: real `L²` inner products of the Schwarz pair
family in closed form,
`G(q,q′) = 16π(x+x′)(1/((x+x′)²+(b−b′)²) + 1/((x+x′)²+(b+b′)²))`. -/
theorem integral_inner_xiPairs (q q' : XiRightUpperZeroCopy) :
    ∫ t : ℝ, (((xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) *
      ((xiAntiCausalWardSchwarzPairResponse q'
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) +
      ((xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).im) *
      ((xiAntiCausalWardSchwarzPairResponse q'
        ((1 / 2 : ℂ) + I * (t : ℂ))).im)) =
      16 * π * (((xiRightCenteredZero q.1).re + 1 / 2) +
          (((xiRightCenteredZero q'.1).re + 1 / 2))) *
        (1 / (((((xiRightCenteredZero q.1).re + 1 / 2) +
              (((xiRightCenteredZero q'.1).re + 1 / 2)))) ^ 2 +
            ((xiRightCenteredZero q.1).im -
              (xiRightCenteredZero q'.1).im) ^ 2) +
          1 / (((((xiRightCenteredZero q.1).re + 1 / 2) +
              (((xiRightCenteredZero q'.1).re + 1 / 2)))) ^ 2 +
            ((xiRightCenteredZero q.1).im +
              (xiRightCenteredZero q'.1).im) ^ 2)) := by
  rw [MeasureTheory.integral_add (integrable_mul_re_xiPairs q q')
    (integrable_mul_im_xiPairs q q'),
    integral_mul_re_xiPairs q q', integral_mul_im_xiPairs q q']
  ring

/-- The pair Gram term `G(q,q′)`. -/
def xiPairGramTerm (q q' : XiRightUpperZeroCopy) : ℝ :=
  16 * π * (((xiRightCenteredZero q.1).re + 1 / 2) +
      (((xiRightCenteredZero q'.1).re + 1 / 2))) *
    (1 / (((((xiRightCenteredZero q.1).re + 1 / 2) +
          (((xiRightCenteredZero q'.1).re + 1 / 2)))) ^ 2 +
        ((xiRightCenteredZero q.1).im -
          (xiRightCenteredZero q'.1).im) ^ 2) +
      1 / (((((xiRightCenteredZero q.1).re + 1 / 2) +
          (((xiRightCenteredZero q'.1).re + 1 / 2)))) ^ 2 +
        ((xiRightCenteredZero q.1).im +
          (xiRightCenteredZero q'.1).im) ^ 2))

theorem xiPairGramTerm_nonneg (q q' : XiRightUpperZeroCopy) :
    0 ≤ xiPairGramTerm q q' := by
  have hre := xiRightCenteredZero_re_pos q.1
  have hre' := xiRightCenteredZero_re_pos q'.1
  unfold xiPairGramTerm
  positivity

theorem integral_inner_xiPairs_eq_gramTerm (q q' : XiRightUpperZeroCopy) :
    ∫ t : ℝ, (((xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) *
      ((xiAntiCausalWardSchwarzPairResponse q'
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) +
      ((xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).im) *
      ((xiAntiCausalWardSchwarzPairResponse q'
        ((1 / 2 : ℂ) + I * (t : ℂ))).im)) = xiPairGramTerm q q' := by
  unfold xiPairGramTerm
  exact integral_inner_xiPairs q q'

/-- Diagonal Gram entries exceed `8π`. -/
theorem eightPi_le_xiPairGramTerm_diag (q : XiRightUpperZeroCopy) :
    8 * π ≤ xiPairGramTerm q q := by
  have hre := xiRightCenteredZero_re_pos q.1
  have hlt := (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q.1)).2
  have hx : 0 < (xiRightCenteredZero q.1).re + 1 / 2 := by linarith
  unfold xiPairGramTerm
  have h1 : (((xiRightCenteredZero q.1).re + 1 / 2) +
      ((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
      ((xiRightCenteredZero q.1).im - (xiRightCenteredZero q.1).im) ^ 2 =
      4 * ((xiRightCenteredZero q.1).re + 1 / 2) ^ 2 := by ring
  have h3 : 16 * π * (((xiRightCenteredZero q.1).re + 1 / 2) +
      ((xiRightCenteredZero q.1).re + 1 / 2)) *
      (1 / (4 * ((xiRightCenteredZero q.1).re + 1 / 2) ^ 2)) =
      8 * π / ((xiRightCenteredZero q.1).re + 1 / 2) := by
    field_simp
    ring
  have h2 : 0 ≤ 16 * π * (((xiRightCenteredZero q.1).re + 1 / 2) +
      ((xiRightCenteredZero q.1).re + 1 / 2)) *
      (1 / ((((xiRightCenteredZero q.1).re + 1 / 2) +
          ((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
        ((xiRightCenteredZero q.1).im +
          (xiRightCenteredZero q.1).im) ^ 2)) := by positivity
  have h4 : 8 * π ≤ 8 * π / ((xiRightCenteredZero q.1).re + 1 / 2) := by
    rw [le_div_iff₀ hx]
    nlinarith [pi_pos]
  rw [mul_add, h1]
  linarith [h2, h3, h4]

/-- **The quadratic explicit formula**: the total edge quadratic energy
equals the Gram lattice sum over all ordered pairs of strict-right zeros.
Unconditional: for an infinite divisor both sides are infinite; for a
finite divisor every interchange is a finite sum. -/
theorem xiWardEdgeQuadEnergy_eq_tsum_gram :
    xiWardEdgeQuadEnergy =
    ∑' p : XiRightUpperZeroCopy × XiRightUpperZeroCopy,
      ENNReal.ofReal (xiPairGramTerm p.1 p.2) := by
  rcases finite_or_infinite XiRightUpperZeroCopy with hfin | hinf
  · letI : Fintype XiRightUpperZeroCopy := Fintype.ofFinite _
    have hw : ∀ t : ℝ, (0 : ℝ) < ((1 / 2 : ℂ) + I * (t : ℂ)).re := by
      intro t
      norm_num [Complex.add_re, Complex.mul_re]
    have hIntTerm : ∀ q q' : XiRightUpperZeroCopy,
        Integrable (fun t : ℝ =>
          (((xiAntiCausalWardSchwarzPairResponse q
              ((1 / 2 : ℂ) + I * (t : ℂ))).re) *
            ((xiAntiCausalWardSchwarzPairResponse q'
              ((1 / 2 : ℂ) + I * (t : ℂ))).re) +
            ((xiAntiCausalWardSchwarzPairResponse q
              ((1 / 2 : ℂ) + I * (t : ℂ))).im) *
            ((xiAntiCausalWardSchwarzPairResponse q'
              ((1 / 2 : ℂ) + I * (t : ℂ))).im))) volume :=
      fun q q' => (integrable_mul_re_xiPairs q q').add
        (integrable_mul_im_xiPairs q q')
    have hpt : ∀ t : ℝ, Complex.normSq
        (continuedXiAntiCausalWardResponse ((1 / 2 : ℂ) + I * (t : ℂ))) =
        ∑ q : XiRightUpperZeroCopy, ∑ q' : XiRightUpperZeroCopy,
          (((xiAntiCausalWardSchwarzPairResponse q
              ((1 / 2 : ℂ) + I * (t : ℂ))).re) *
            ((xiAntiCausalWardSchwarzPairResponse q'
              ((1 / 2 : ℂ) + I * (t : ℂ))).re) +
            ((xiAntiCausalWardSchwarzPairResponse q
              ((1 / 2 : ℂ) + I * (t : ℂ))).im) *
            ((xiAntiCausalWardSchwarzPairResponse q'
              ((1 / 2 : ℂ) + I * (t : ℂ))).im)) := by
      intro t
      rw [continuedXiAntiCausalWardResponse_eq_tsum_schwarzPairs (hw t),
        tsum_fintype, Complex.normSq_apply, Complex.re_sum, Complex.im_sum,
        Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun q _ => (Finset.sum_add_distrib).symm
    have hInt : Integrable (fun t : ℝ =>
        ∑ q : XiRightUpperZeroCopy, ∑ q' : XiRightUpperZeroCopy,
          (((xiAntiCausalWardSchwarzPairResponse q
              ((1 / 2 : ℂ) + I * (t : ℂ))).re) *
            ((xiAntiCausalWardSchwarzPairResponse q'
              ((1 / 2 : ℂ) + I * (t : ℂ))).re) +
            ((xiAntiCausalWardSchwarzPairResponse q
              ((1 / 2 : ℂ) + I * (t : ℂ))).im) *
            ((xiAntiCausalWardSchwarzPairResponse q'
              ((1 / 2 : ℂ) + I * (t : ℂ))).im))) volume :=
      integrable_finsetSum _ fun q _ =>
        integrable_finsetSum _ fun q' _ => hIntTerm q q'
    unfold xiWardEdgeQuadEnergy
    rw [show (fun t : ℝ => ENNReal.ofReal (Complex.normSq
        (continuedXiAntiCausalWardResponse ((1 / 2 : ℂ) + I * (t : ℂ))))) =
        fun t : ℝ => ENNReal.ofReal
          (∑ q : XiRightUpperZeroCopy, ∑ q' : XiRightUpperZeroCopy,
            (((xiAntiCausalWardSchwarzPairResponse q
                ((1 / 2 : ℂ) + I * (t : ℂ))).re) *
              ((xiAntiCausalWardSchwarzPairResponse q'
                ((1 / 2 : ℂ) + I * (t : ℂ))).re) +
              ((xiAntiCausalWardSchwarzPairResponse q
                ((1 / 2 : ℂ) + I * (t : ℂ))).im) *
              ((xiAntiCausalWardSchwarzPairResponse q'
                ((1 / 2 : ℂ) + I * (t : ℂ))).im))) from
      funext fun t => by rw [hpt t]]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt
      (Filter.Eventually.of_forall fun t => by
        have h := Complex.normSq_nonneg
          (continuedXiAntiCausalWardResponse ((1 / 2 : ℂ) + I * (t : ℂ)))
        rw [hpt t] at h
        simpa using h)]
    have hval : (∫ t : ℝ,
        ∑ q : XiRightUpperZeroCopy, ∑ q' : XiRightUpperZeroCopy,
          (((xiAntiCausalWardSchwarzPairResponse q
              ((1 / 2 : ℂ) + I * (t : ℂ))).re) *
            ((xiAntiCausalWardSchwarzPairResponse q'
              ((1 / 2 : ℂ) + I * (t : ℂ))).re) +
            ((xiAntiCausalWardSchwarzPairResponse q
              ((1 / 2 : ℂ) + I * (t : ℂ))).im) *
            ((xiAntiCausalWardSchwarzPairResponse q'
              ((1 / 2 : ℂ) + I * (t : ℂ))).im))) =
        ∑ q : XiRightUpperZeroCopy, ∑ q' : XiRightUpperZeroCopy,
          xiPairGramTerm q q' := by
      rw [MeasureTheory.integral_finsetSum _ fun q _ =>
        integrable_finsetSum _ fun q' _ => hIntTerm q q']
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [MeasureTheory.integral_finsetSum _ fun q' _ => hIntTerm q q']
      exact Finset.sum_congr rfl fun q' _ =>
        integral_inner_xiPairs_eq_gramTerm q q'
    rw [hval, tsum_fintype, Fintype.sum_prod_type,
      ENNReal.ofReal_sum_of_nonneg (fun q _ => Finset.sum_nonneg
        fun q' _ => xiPairGramTerm_nonneg q q')]
    exact Finset.sum_congr rfl fun q _ =>
      ENNReal.ofReal_sum_of_nonneg fun q' _ => xiPairGramTerm_nonneg q q'
  · haveI := hinf
    have htop : xiWardEdgeQuadEnergy = ⊤ := by
      by_contra hne
      exact (not_finite_iff_infinite.mpr hinf)
        (finite_xiRightUpperZeroCopy_of_xiWardEdgeQuadEnergy_ne_top hne)
    have hdiag : ∀ q : XiRightUpperZeroCopy,
        ENNReal.ofReal (8 * π) ≤ ENNReal.ofReal (xiPairGramTerm q q) :=
      fun q => ENNReal.ofReal_le_ofReal (eightPi_le_xiPairGramTerm_diag q)
    have hinj : Function.Injective
        (fun q : XiRightUpperZeroCopy => (q, q)) :=
      fun a b h => (Prod.ext_iff.mp h).1
    have h2 := ENNReal.tsum_comp_le_tsum_of_injective hinj
      (fun p : XiRightUpperZeroCopy × XiRightUpperZeroCopy =>
        ENNReal.ofReal (xiPairGramTerm p.1 p.2))
    have h1 := ENNReal.tsum_le_tsum hdiag
    have h3 : (∑' _ : XiRightUpperZeroCopy, ENNReal.ofReal (8 * π)) = ⊤ :=
      ENNReal.tsum_const_eq_top_of_ne_zero
        (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))
    rw [htop]
    symm
    rw [← top_le_iff]
    calc (⊤ : ENNReal)
        = ∑' _ : XiRightUpperZeroCopy, ENNReal.ofReal (8 * π) := h3.symm
      _ ≤ ∑' q : XiRightUpperZeroCopy,
            ENNReal.ofReal (xiPairGramTerm q q) := h1
      _ ≤ ∑' p : XiRightUpperZeroCopy × XiRightUpperZeroCopy,
            ENNReal.ofReal (xiPairGramTerm p.1 p.2) := h2

/-- **RH as lattice arithmetic**: for any budget `0 ≤ c ≤ 4π` the Riemann
Hypothesis is equivalent to the Gram lattice sum over ordered pairs of
strict-right zeros staying within `c`.  Each diagonal entry alone exceeds
`8π`, so the sum is `0` exactly when the divisor is empty. -/
theorem riemannHypothesis_iff_tsum_gram_le {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c ≤ 4 * π) :
    RiemannHypothesis ↔
      (∑' p : XiRightUpperZeroCopy × XiRightUpperZeroCopy,
        ENNReal.ofReal (xiPairGramTerm p.1 p.2)) ≤ ENNReal.ofReal c := by
  rw [← xiWardEdgeQuadEnergy_eq_tsum_gram]
  exact riemannHypothesis_iff_continuedXiWardEdgeQuadEnergyLaw hc0 hc

end

end RHTower
