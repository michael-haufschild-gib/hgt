import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularVerticalDecay

/-!
# Uniform integrated Cauchy control on the Xi vertical edge

Pointwise resolvent bounds lose the reciprocal distance from a contour to a nearby zero.  The
integrated Cauchy kernel does not: every centered Xi zero lies between heights `-1/2` and `1/2`,
whereas the symmetric Guinand--Weil edge runs from `-1` to `1`.  Its two endpoints therefore stay
uniformly separated from every pole.  A logarithmic primitive gives a bound independent of the
horizontal pole--edge distance.

This is the cancellation input that allows reciprocal-`3/2` divisor summability, rather than a
pointwise zero-density estimate, to eliminate the vertical edge.
-/

open Complex intervalIntegral Set

namespace RHTower

noncomputable section

/-- A fixed uniform bound for an integrated vertical Cauchy kernel across the centered Xi strip. -/
def xiVerticalCauchyKernelBound : ℝ :=
  2 * (Real.log 3 + Real.pi)

theorem xiVerticalCauchyKernelBound_nonneg :
    0 ≤ xiVerticalCauchyKernelBound := by
  unfold xiVerticalCauchyKernelBound
  positivity

private theorem norm_log_le_log_three_add_pi {z : ℂ}
    (hlower : (1 / 2 : ℝ) ≤ ‖z‖) (hupper : ‖z‖ ≤ 3) :
    ‖Complex.log z‖ ≤ Real.log 3 + Real.pi := by
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) hlower
  have hlowerThird : (3 : ℝ)⁻¹ ≤ ‖z‖ := by
    norm_num at hlower ⊢
    linarith
  have hlogLower : -Real.log 3 ≤ Real.log ‖z‖ := by
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 3⁻¹) hlowerThird
    rwa [Real.log_inv] at this
  have hlogUpper : Real.log ‖z‖ ≤ Real.log 3 :=
    Real.log_le_log hzpos hupper
  have habsLog : |Real.log ‖z‖| ≤ Real.log 3 :=
    abs_le.mpr ⟨hlogLower, hlogUpper⟩
  rw [Complex.log]
  calc
    ‖(Real.log ‖z‖ : ℂ) + (z.arg : ℂ) * I‖ ≤
        ‖(Real.log ‖z‖ : ℂ)‖ + ‖(z.arg : ℂ) * I‖ := norm_add_le _ _
    _ = |Real.log ‖z‖| + |z.arg| := by simp
    _ ≤ Real.log 3 + Real.pi :=
      add_le_add habsLog (Complex.abs_arg_le_pi z)

theorem I_mul_integral_vertical_cauchyKernel_eq_log_sub_of_lt
    {p : ℂ} {R a b : ℝ} (hR : p.re < R) :
    I * (∫ y in a..b, (((R : ℂ) + y * I) - p)⁻¹) =
      Complex.log (((R : ℂ) + b * I) - p) -
        Complex.log (((R : ℂ) + a * I) - p) := by
  have hslit : ∀ y : ℝ, (((R : ℂ) + y * I) - p) ∈ slitPlane := by
    intro y
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      zero_mul, mul_zero, sub_zero]
    linarith
  have hHD : ∀ y ∈ uIcc a b,
      HasDerivAt (fun y : ℝ => -I * Complex.log (((R : ℂ) + y * I) - p))
        ((((R : ℂ) + y * I) - p)⁻¹) y := by
    intro y hy
    have hin : HasDerivAt (fun y : ℝ => (R : ℂ) + (y : ℂ) * I) I y := by
      have hmul : HasDerivAt (fun y : ℝ => (y : ℂ) * I) I y := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I
      simpa using hmul.const_add (R : ℂ)
    have hout : HasDerivAt (fun z : ℂ => Complex.log (z - p))
        (((R : ℂ) + y * I - p)⁻¹) ((R : ℂ) + y * I) := by
      simpa using! (Complex.hasDerivAt_log (hslit y)).comp
        ((R : ℂ) + y * I) ((hasDerivAt_id _).sub_const p)
    have hchain := (hout.comp y hin).const_mul (-I)
    have hval : -I * ((((R : ℂ) + y * I - p)⁻¹) * I) =
        (((R : ℂ) + y * I - p)⁻¹) := by
      calc
        -I * ((((R : ℂ) + y * I - p)⁻¹) * I) =
            ((-I) * I) * (((R : ℂ) + y * I - p)⁻¹) := by ring
        _ = (((R : ℂ) + y * I - p)⁻¹) := by
          rw [neg_mul, Complex.I_mul_I, neg_neg, one_mul]
    simpa only [hval] using! hchain
  have hcont : ContinuousOn
      (fun y : ℝ => (((R : ℂ) + y * I) - p)⁻¹) (uIcc a b) :=
    (continuousOn_of_forall_continuousAt (fun y => by fun_prop)).inv₀
      (fun y _ => Complex.slitPlane_ne_zero (hslit y))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hHD hcont.intervalIntegrable,
    mul_sub]
  rw [show I * (-I * Complex.log (((R : ℂ) + b * I) - p)) =
        Complex.log (((R : ℂ) + b * I) - p) by
      rw [show I * (-I * Complex.log (((R : ℂ) + b * I) - p)) =
        (I * -I) * Complex.log (((R : ℂ) + b * I) - p) by ring,
        mul_neg, Complex.I_mul_I, neg_neg, one_mul],
    show I * (-I * Complex.log (((R : ℂ) + a * I) - p)) =
        Complex.log (((R : ℂ) + a * I) - p) by
      rw [show I * (-I * Complex.log (((R : ℂ) + a * I) - p)) =
        (I * -I) * Complex.log (((R : ℂ) + a * I) - p) by ring,
        mul_neg, Complex.I_mul_I, neg_neg, one_mul]]

theorem I_mul_integral_vertical_cauchyKernel_eq_log_neg_sub_of_gt
    {p : ℂ} {R a b : ℝ} (hR : R < p.re) :
    I * (∫ y in a..b, (((R : ℂ) + y * I) - p)⁻¹) =
      Complex.log (-(((R : ℂ) + b * I) - p)) -
        Complex.log (-(((R : ℂ) + a * I) - p)) := by
  have hslit : ∀ y : ℝ, -(((R : ℂ) + y * I) - p) ∈ slitPlane := by
    intro y
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [neg_re, sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      zero_mul, mul_zero, sub_zero]
    linarith
  have hHD : ∀ y ∈ uIcc a b,
      HasDerivAt (fun y : ℝ => -I * Complex.log (-(((R : ℂ) + y * I) - p)))
        ((((R : ℂ) + y * I) - p)⁻¹) y := by
    intro y hy
    have hin : HasDerivAt (fun y : ℝ => (R : ℂ) + (y : ℂ) * I) I y := by
      have hmul : HasDerivAt (fun y : ℝ => (y : ℂ) * I) I y := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I
      simpa using hmul.const_add (R : ℂ)
    have hout0 := (Complex.hasDerivAt_log (hslit y)).comp
      ((R : ℂ) + y * I)
      (((hasDerivAt_id ((R : ℂ) + y * I)).sub_const p).neg)
    have hout : HasDerivAt (fun z : ℂ => Complex.log (-(z - p)))
        (((R : ℂ) + y * I - p)⁻¹) ((R : ℂ) + y * I) := by
      have hval : (-(((R : ℂ) + y * I) - p))⁻¹ * (-1) =
          (((R : ℂ) + y * I) - p)⁻¹ := by
        rw [inv_neg]
        ring
      simpa only [hval] using! hout0
    have hchain := (hout.comp y hin).const_mul (-I)
    have hval : -I * ((((R : ℂ) + y * I - p)⁻¹) * I) =
        (((R : ℂ) + y * I - p)⁻¹) := by
      calc
        -I * ((((R : ℂ) + y * I - p)⁻¹) * I) =
            ((-I) * I) * (((R : ℂ) + y * I - p)⁻¹) := by ring
        _ = (((R : ℂ) + y * I - p)⁻¹) := by
          rw [neg_mul, Complex.I_mul_I, neg_neg, one_mul]
    simpa only [hval] using! hchain
  have hcont : ContinuousOn
      (fun y : ℝ => (((R : ℂ) + y * I) - p)⁻¹) (uIcc a b) :=
    (continuousOn_of_forall_continuousAt (fun y => by fun_prop)).inv₀
      (fun y _ => neg_ne_zero.mp (Complex.slitPlane_ne_zero (hslit y)))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hHD hcont.intervalIntegrable,
    mul_sub]
  rw [show I * (-I * Complex.log (-(((R : ℂ) + b * I) - p))) =
        Complex.log (-(((R : ℂ) + b * I) - p)) by
      rw [show I * (-I * Complex.log (-(((R : ℂ) + b * I) - p))) =
        (I * -I) * Complex.log (-(((R : ℂ) + b * I) - p)) by ring,
        mul_neg, Complex.I_mul_I, neg_neg, one_mul],
    show I * (-I * Complex.log (-(((R : ℂ) + a * I) - p))) =
        Complex.log (-(((R : ℂ) + a * I) - p)) by
      rw [show I * (-I * Complex.log (-(((R : ℂ) + a * I) - p))) =
        (I * -I) * Complex.log (-(((R : ℂ) + a * I) - p)) by ring,
        mul_neg, Complex.I_mul_I, neg_neg, one_mul]]

/-- The Cauchy kernel integrated over the complete depth-one vertical edge has a bound independent
of its horizontal distance from any pole in the centered Xi strip. -/
theorem norm_integral_vertical_cauchyKernel_le
    {p : ℂ} (hpim : (-1 / 2 : ℝ) < p.im ∧ p.im < 1 / 2)
    {R : ℝ} (hR : R ≠ p.re) :
    ‖∫ y in (-1 : ℝ)..1, (((R : ℂ) + y * I) - p)⁻¹‖ ≤
      xiVerticalCauchyKernelBound := by
  by_cases hnear : |R - p.re| < 1
  · have htopLower : (1 / 2 : ℝ) ≤ ‖((R : ℂ) + (1 : ℝ) * I) - p‖ := by
      have him := Complex.abs_im_le_norm (((R : ℂ) + (1 : ℝ) * I) - p)
      simp only [sub_im, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
        zero_mul, mul_one, zero_add] at him
      rw [abs_of_pos (by linarith [hpim.2])] at him
      linarith
    have hbotLower : (1 / 2 : ℝ) ≤ ‖((R : ℂ) + (-1 : ℝ) * I) - p‖ := by
      have him := Complex.abs_im_le_norm (((R : ℂ) + (-1 : ℝ) * I) - p)
      simp only [sub_im, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
        zero_mul, mul_one, zero_add] at him
      rw [abs_of_neg (by linarith [hpim.1])] at him
      linarith
    have htopUpper : ‖((R : ℂ) + (1 : ℝ) * I) - p‖ ≤ 3 := by
      apply le_of_lt
      calc
        ‖((R : ℂ) + (1 : ℝ) * I) - p‖ ≤
            |(((R : ℂ) + (1 : ℝ) * I) - p).re| +
              |(((R : ℂ) + (1 : ℝ) * I) - p).im| :=
          Complex.norm_le_abs_re_add_abs_im _
        _ = |R - p.re| + |1 - p.im| := by simp
        _ < 1 + 3 / 2 := by
          gcongr
          rw [abs_of_pos (by linarith [hpim.2])]
          linarith [hpim.1]
        _ < 3 := by norm_num
    have hbotUpper : ‖((R : ℂ) + (-1 : ℝ) * I) - p‖ ≤ 3 := by
      apply le_of_lt
      calc
        ‖((R : ℂ) + (-1 : ℝ) * I) - p‖ ≤
            |(((R : ℂ) + (-1 : ℝ) * I) - p).re| +
              |(((R : ℂ) + (-1 : ℝ) * I) - p).im| :=
          Complex.norm_le_abs_re_add_abs_im _
        _ = |R - p.re| + |-1 - p.im| := by simp
        _ < 1 + 3 / 2 := by
          gcongr
          rw [abs_of_neg (by linarith [hpim.1])]
          linarith [hpim.2]
        _ < 3 := by norm_num
    have htopLog := norm_log_le_log_three_add_pi htopLower htopUpper
    have hbotLog := norm_log_le_log_three_add_pi hbotLower hbotUpper
    rcases lt_or_gt_of_ne hR with hlt | hgt
    · have heq := I_mul_integral_vertical_cauchyKernel_eq_log_neg_sub_of_gt
        (p := p) (R := R) (a := -1) (b := 1) hlt
      have htopNeg : ‖-(((R : ℂ) + (1 : ℝ) * I) - p)‖ =
          ‖((R : ℂ) + (1 : ℝ) * I) - p‖ := norm_neg _
      have hbotNeg : ‖-(((R : ℂ) + (-1 : ℝ) * I) - p)‖ =
          ‖((R : ℂ) + (-1 : ℝ) * I) - p‖ := norm_neg _
      have htopLogNeg : ‖Complex.log (-(((R : ℂ) + (1 : ℝ) * I) - p))‖ ≤
          Real.log 3 + Real.pi := by
        apply norm_log_le_log_three_add_pi
        · rwa [htopNeg]
        · rwa [htopNeg]
      have hbotLogNeg : ‖Complex.log (-(((R : ℂ) + (-1 : ℝ) * I) - p))‖ ≤
          Real.log 3 + Real.pi := by
        apply norm_log_le_log_three_add_pi
        · rwa [hbotNeg]
        · rwa [hbotNeg]
      calc
        ‖∫ y in (-1 : ℝ)..1, (((R : ℂ) + y * I) - p)⁻¹‖ =
            ‖I * (∫ y in (-1 : ℝ)..1, (((R : ℂ) + y * I) - p)⁻¹)‖ := by simp
        _ = ‖Complex.log (-(((R : ℂ) + (1 : ℝ) * I) - p)) -
              Complex.log (-(((R : ℂ) + (-1 : ℝ) * I) - p))‖ := by rw [heq]
        _ ≤ ‖Complex.log (-(((R : ℂ) + (1 : ℝ) * I) - p))‖ +
              ‖Complex.log (-(((R : ℂ) + (-1 : ℝ) * I) - p))‖ := norm_sub_le _ _
        _ ≤ xiVerticalCauchyKernelBound := by
          unfold xiVerticalCauchyKernelBound
          linarith
    · have heq := I_mul_integral_vertical_cauchyKernel_eq_log_sub_of_lt
        (p := p) (R := R) (a := -1) (b := 1) hgt
      calc
        ‖∫ y in (-1 : ℝ)..1, (((R : ℂ) + y * I) - p)⁻¹‖ =
            ‖I * (∫ y in (-1 : ℝ)..1, (((R : ℂ) + y * I) - p)⁻¹)‖ := by simp
        _ = ‖Complex.log (((R : ℂ) + (1 : ℝ) * I) - p) -
              Complex.log (((R : ℂ) + (-1 : ℝ) * I) - p)‖ := by rw [heq]
        _ ≤ ‖Complex.log (((R : ℂ) + (1 : ℝ) * I) - p)‖ +
              ‖Complex.log (((R : ℂ) + (-1 : ℝ) * I) - p)‖ := norm_sub_le _ _
        _ ≤ xiVerticalCauchyKernelBound := by
          unfold xiVerticalCauchyKernelBound
          linarith
  · have hfar : 1 ≤ |R - p.re| := le_of_not_gt hnear
    have hpoint : ∀ y ∈ uIoc (-1 : ℝ) 1,
        ‖(((R : ℂ) + y * I) - p)⁻¹‖ ≤ (1 : ℝ) := by
      intro y hy
      have hre := Complex.abs_re_le_norm (((R : ℂ) + y * I) - p)
      have hre' : |R - p.re| ≤ ‖((R : ℂ) + y * I) - p‖ := by
        simpa only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
          zero_mul, mul_zero, sub_zero, add_zero] using hre
      have hden : 0 < ‖((R : ℂ) + y * I) - p‖ :=
        zero_lt_one.trans_le (hfar.trans hre')
      rw [norm_inv]
      exact (inv_le_one₀ hden).2 (hfar.trans hre')
    calc
      ‖∫ y in (-1 : ℝ)..1, (((R : ℂ) + y * I) - p)⁻¹‖ ≤
          (1 : ℝ) * |1 - (-1)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hpoint
      _ = 2 := by norm_num
      _ ≤ xiVerticalCauchyKernelBound := by
        unfold xiVerticalCauchyKernelBound
        have hlog : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
        nlinarith [Real.pi_gt_three]

/-- A slowly varying weight preserves the uniform vertical Cauchy bound.  Subtracting the weight
at the pole height makes the remainder vanish linearly there, exactly cancelling the pointwise
Cauchy singularity. -/
theorem norm_integral_mul_vertical_cauchyKernel_le
    {h : ℝ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hdiff : ∀ y ∈ Icc (-1 : ℝ) 1, DifferentiableAt ℝ h y)
    (hderiv : ∀ y ∈ Icc (-1 : ℝ) 1, ‖deriv h y‖ ≤ M)
    {p : ℂ} (hpim : (-1 / 2 : ℝ) < p.im ∧ p.im < 1 / 2)
    {R : ℝ} (hR : R ≠ p.re) :
    ‖∫ y in (-1 : ℝ)..1,
        h y * ((((R : ℂ) + y * I) - p)⁻¹)‖ ≤
      ‖h p.im‖ * xiVerticalCauchyKernelBound + 2 * M := by
  let k : ℝ → ℂ := fun y => ((((R : ℂ) + y * I) - p)⁻¹)
  let r : ℝ → ℂ := fun y => (h y - h p.im) * k y
  have hpMem : p.im ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hpim.1, hpim.2]
  have hden (y : ℝ) : ((R : ℂ) + y * I) - p ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      zero_mul, mul_zero, sub_zero, add_zero, zero_re] at hre
    exact hR (sub_eq_zero.mp hre)
  have hhcont : ContinuousOn h (Icc (-1 : ℝ) 1) := by
    intro y hy
    exact (hdiff y hy).continuousAt.continuousWithinAt
  have hkcont : ContinuousOn k (Icc (-1 : ℝ) 1) := by
    apply (continuousOn_of_forall_continuousAt (fun y => by
      fun_prop)).inv₀
    intro y hy
    exact hden y
  have hrcont : ContinuousOn r (Icc (-1 : ℝ) 1) := by
    exact (hhcont.sub continuousOn_const).mul hkcont
  have hkInt : IntervalIntegrable k MeasureTheory.volume (-1 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hkcont
  have hconstInt : IntervalIntegrable (fun y => h p.im * k y)
      MeasureTheory.volume (-1 : ℝ) 1 := hkInt.const_mul _
  have hrInt : IntervalIntegrable r MeasureTheory.volume (-1 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hrcont
  have hsplit :
      (∫ y in (-1 : ℝ)..1, h y * k y) =
        h p.im * (∫ y in (-1 : ℝ)..1, k y) +
          ∫ y in (-1 : ℝ)..1, r y := by
    calc
      (∫ y in (-1 : ℝ)..1, h y * k y) =
          ∫ y in (-1 : ℝ)..1, h p.im * k y + r y := by
        apply integral_congr
        intro y hy
        dsimp only [r]
        ring
      _ = (∫ y in (-1 : ℝ)..1, h p.im * k y) +
          ∫ y in (-1 : ℝ)..1, r y := integral_add hconstInt hrInt
      _ = _ := by rw [integral_const_mul]
  have hconstant :
      ‖h p.im * (∫ y in (-1 : ℝ)..1, k y)‖ ≤
        ‖h p.im‖ * xiVerticalCauchyKernelBound := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (by
        simpa only [k] using
          norm_integral_vertical_cauchyKernel_le hpim hR)
      (norm_nonneg _)
  have hrPoint : ∀ y ∈ uIoc (-1 : ℝ) 1, ‖r y‖ ≤ M := by
    intro y hy
    have hyIoc : y ∈ Ioc (-1 : ℝ) 1 := by
      simpa [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hy
    have hyMem : y ∈ Icc (-1 : ℝ) 1 := Ioc_subset_Icc_self hyIoc
    have hmv0 := Convex.norm_image_sub_le_of_norm_deriv_le
      hdiff hderiv (convex_Icc (-1 : ℝ) 1) hpMem hyMem
    have hmv : ‖h y - h p.im‖ ≤ M * |y - p.im| := by
      simpa only [Real.norm_eq_abs] using hmv0
    have himdist : |y - p.im| ≤ ‖((R : ℂ) + y * I) - p‖ := by
      have := Complex.abs_im_le_norm (((R : ℂ) + y * I) - p)
      simpa only [sub_im, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
        zero_mul, mul_one, zero_add, add_zero] using this
    have hdenPos : 0 < ‖((R : ℂ) + y * I) - p‖ :=
      norm_pos_iff.mpr (hden y)
    dsimp only [r, k]
    rw [norm_mul, norm_inv]
    calc
      ‖h y - h p.im‖ * ‖((R : ℂ) + y * I) - p‖⁻¹ ≤
          (M * |y - p.im|) * ‖((R : ℂ) + y * I) - p‖⁻¹ :=
        mul_le_mul_of_nonneg_right hmv (inv_nonneg.mpr (norm_nonneg _))
      _ = M * (|y - p.im| / ‖((R : ℂ) + y * I) - p‖) := by
        rw [div_eq_mul_inv]
        ring
      _ ≤ M * 1 := mul_le_mul_of_nonneg_left
        ((div_le_one hdenPos).2 himdist) hM
      _ = M := mul_one M
  have hremainder : ‖∫ y in (-1 : ℝ)..1, r y‖ ≤ 2 * M := by
    have hraw := intervalIntegral.norm_integral_le_of_norm_le_const hrPoint
    norm_num at hraw ⊢
    nlinarith
  change ‖∫ y in (-1 : ℝ)..1, h y * k y‖ ≤ _
  rw [hsplit]
  exact (norm_add_le _ _).trans (by linarith)

end
end RHTower
