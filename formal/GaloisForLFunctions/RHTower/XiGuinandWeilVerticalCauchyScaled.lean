import GaloisForLFunctions.RHTower.XiGuinandWeilVerticalCauchy

/-!
# Gap-free vertical Cauchy control at arbitrary depth

The fixed-depth Cauchy estimate only uses that both vertical endpoints lie a positive distance
outside the universal centered Xi strip.  This module exposes that invariant: every depth
`c > 1/2` has a distance-independent integrated Cauchy bound, and every slowly varying weight
pays only interval length `2c` in the mean-value remainder.
-/

open Complex intervalIntegral Set

namespace RHTower

noncomputable section

/-- Explicit Cauchy-kernel bound at vertical depth `c`. -/
def xiVerticalCauchyKernelBoundAt (c : ℝ) : ℝ :=
  2 * (|Real.log (c - 1 / 2)| + |Real.log (c + 3 / 2)| + Real.pi) + 2 * c

theorem xiVerticalCauchyKernelBoundAt_nonneg {c : ℝ} (hc : 1 / 2 < c) :
    0 ≤ xiVerticalCauchyKernelBoundAt c := by
  unfold xiVerticalCauchyKernelBoundAt
  positivity

private theorem norm_log_le_abs_logs_add_pi {z : ℂ} {d C : ℝ}
    (hd : 0 < d) (hlower : d ≤ ‖z‖) (hupper : ‖z‖ ≤ C) :
    ‖Complex.log z‖ ≤ |Real.log d| + |Real.log C| + Real.pi := by
  have hzpos : 0 < ‖z‖ := hd.trans_le hlower
  have hlogLower : Real.log d ≤ Real.log ‖z‖ := Real.log_le_log hd hlower
  have hlogUpper : Real.log ‖z‖ ≤ Real.log C := Real.log_le_log hzpos hupper
  have habsLog : |Real.log ‖z‖| ≤ |Real.log d| + |Real.log C| := by
    rw [abs_le]
    constructor
    · have hdabs : -|Real.log d| ≤ Real.log d := neg_abs_le _
      linarith [abs_nonneg (Real.log C)]
    · have hCabs : Real.log C ≤ |Real.log C| := le_abs_self _
      linarith [abs_nonneg (Real.log d)]
  rw [Complex.log]
  calc
    ‖(Real.log ‖z‖ : ℂ) + (z.arg : ℂ) * I‖ ≤
        ‖(Real.log ‖z‖ : ℂ)‖ + ‖(z.arg : ℂ) * I‖ := norm_add_le _ _
    _ = |Real.log ‖z‖| + |z.arg| := by simp
    _ ≤ |Real.log d| + |Real.log C| + Real.pi :=
      add_le_add habsLog (Complex.abs_arg_le_pi z)

private theorem I_mul_integral_vertical_cauchyKernel_eq_log_sub_of_lt_at
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
    intro y _
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

private theorem I_mul_integral_vertical_cauchyKernel_eq_log_neg_sub_of_gt_at
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
    intro y _
    have hin : HasDerivAt (fun y : ℝ => (R : ℂ) + (y : ℂ) * I) I y := by
      have hmul : HasDerivAt (fun y : ℝ => (y : ℂ) * I) I y := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I
      simpa using hmul.const_add (R : ℂ)
    have hout0 := (Complex.hasDerivAt_log (hslit y)).comp
      ((R : ℂ) + y * I) (((hasDerivAt_id ((R : ℂ) + y * I)).sub_const p).neg)
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

/-- The complete depth-`c` Cauchy kernel is uniformly bounded as the vertical edge approaches a
centered Xi pole horizontally. -/
theorem norm_integral_vertical_cauchyKernel_le_at
    {c : ℝ} (hc : 1 / 2 < c) {p : ℂ}
    (hpim : (-1 / 2 : ℝ) < p.im ∧ p.im < 1 / 2)
    {R : ℝ} (hR : R ≠ p.re) :
    ‖∫ y in -c..c, (((R : ℂ) + y * I) - p)⁻¹‖ ≤
      xiVerticalCauchyKernelBoundAt c := by
  have hd : 0 < c - 1 / 2 := sub_pos.mpr hc
  have hC : 0 < c + 3 / 2 := by linarith
  by_cases hnear : |R - p.re| < 1
  · have htopLower : c - 1 / 2 ≤ ‖((R : ℂ) + c * I) - p‖ := by
      have him := Complex.abs_im_le_norm (((R : ℂ) + c * I) - p)
      simp only [sub_im, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
        zero_mul, mul_one, zero_add] at him
      rw [abs_of_pos (by linarith [hpim.2])] at him
      linarith
    have hbotLower : c - 1 / 2 ≤ ‖((R : ℂ) + (-c) * I) - p‖ := by
      have him := Complex.abs_im_le_norm (((R : ℂ) + (-c) * I) - p)
      have himcoord : (((R : ℂ) + (-c) * I) - p).im = -c - p.im := by simp
      rw [himcoord] at him
      rw [abs_of_neg (by linarith [hpim.1])] at him
      linarith
    have htopUpper : ‖((R : ℂ) + c * I) - p‖ ≤ c + 3 / 2 := by
      apply le_of_lt
      calc
        ‖((R : ℂ) + c * I) - p‖ ≤
            |(((R : ℂ) + c * I) - p).re| + |(((R : ℂ) + c * I) - p).im| :=
          Complex.norm_le_abs_re_add_abs_im _
        _ = |R - p.re| + |c - p.im| := by simp
        _ < 1 + (c + 1 / 2) := by
          gcongr
          rw [abs_of_pos (by linarith [hpim.2])]
          linarith [hpim.1]
        _ = c + 3 / 2 := by ring
    have hbotUpper : ‖((R : ℂ) + (-c) * I) - p‖ ≤ c + 3 / 2 := by
      apply le_of_lt
      calc
        ‖((R : ℂ) + (-c) * I) - p‖ ≤
            |(((R : ℂ) + (-c) * I) - p).re| + |(((R : ℂ) + (-c) * I) - p).im| :=
          Complex.norm_le_abs_re_add_abs_im _
        _ = |R - p.re| + |-c - p.im| := by simp
        _ < 1 + (c + 1 / 2) := by
          gcongr
          rw [abs_of_neg (by linarith [hpim.1])]
          linarith [hpim.2]
        _ = c + 3 / 2 := by ring
    rcases lt_or_gt_of_ne hR with hlt | hgt
    · have heq := I_mul_integral_vertical_cauchyKernel_eq_log_neg_sub_of_gt_at
        (p := p) (R := R) (a := -c) (b := c) hlt
      have htopLog : ‖Complex.log (-(((R : ℂ) + c * I) - p))‖ ≤
          |Real.log (c - 1 / 2)| + |Real.log (c + 3 / 2)| + Real.pi := by
        apply norm_log_le_abs_logs_add_pi hd
        · rw [norm_neg]
          exact htopLower
        · rw [norm_neg]
          exact htopUpper
      have hbotLog : ‖Complex.log (-(((R : ℂ) + (-c) * I) - p))‖ ≤
          |Real.log (c - 1 / 2)| + |Real.log (c + 3 / 2)| + Real.pi := by
        apply norm_log_le_abs_logs_add_pi hd
        · rw [norm_neg]
          exact hbotLower
        · rw [norm_neg]
          exact hbotUpper
      have henorm := congrArg norm heq
      calc
        ‖∫ y in -c..c, (((R : ℂ) + y * I) - p)⁻¹‖ =
            ‖I * (∫ y in -c..c, (((R : ℂ) + y * I) - p)⁻¹)‖ := by simp
        _ = ‖Complex.log (-(((R : ℂ) + c * I) - p)) -
              Complex.log (-(((R : ℂ) + (-c) * I) - p))‖ := by
          simpa only [norm_mul, norm_I, one_mul, ofReal_neg] using henorm
        _ ≤ ‖Complex.log (-(((R : ℂ) + c * I) - p))‖ +
              ‖Complex.log (-(((R : ℂ) + (-c) * I) - p))‖ := norm_sub_le _ _
        _ ≤ xiVerticalCauchyKernelBoundAt c := by
          unfold xiVerticalCauchyKernelBoundAt
          nlinarith
    · have heq := I_mul_integral_vertical_cauchyKernel_eq_log_sub_of_lt_at
        (p := p) (R := R) (a := -c) (b := c) hgt
      have htopLog := norm_log_le_abs_logs_add_pi hd htopLower htopUpper
      have hbotLog := norm_log_le_abs_logs_add_pi hd hbotLower hbotUpper
      have henorm := congrArg norm heq
      calc
        ‖∫ y in -c..c, (((R : ℂ) + y * I) - p)⁻¹‖ =
            ‖I * (∫ y in -c..c, (((R : ℂ) + y * I) - p)⁻¹)‖ := by simp
        _ = ‖Complex.log (((R : ℂ) + c * I) - p) -
              Complex.log (((R : ℂ) + (-c) * I) - p)‖ := by
          simpa only [norm_mul, norm_I, one_mul, ofReal_neg] using henorm
        _ ≤ ‖Complex.log (((R : ℂ) + c * I) - p)‖ +
              ‖Complex.log (((R : ℂ) + (-c) * I) - p)‖ := norm_sub_le _ _
        _ ≤ xiVerticalCauchyKernelBoundAt c := by
          unfold xiVerticalCauchyKernelBoundAt
          nlinarith
  · have hfar : 1 ≤ |R - p.re| := le_of_not_gt hnear
    have hpoint : ∀ y ∈ uIoc (-c) c,
        ‖(((R : ℂ) + y * I) - p)⁻¹‖ ≤ (1 : ℝ) := by
      intro y _
      have hre := Complex.abs_re_le_norm (((R : ℂ) + y * I) - p)
      have hre' : |R - p.re| ≤ ‖((R : ℂ) + y * I) - p‖ := by
        simpa only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
          zero_mul, mul_zero, sub_zero, add_zero] using hre
      have hden : 0 < ‖((R : ℂ) + y * I) - p‖ :=
        zero_lt_one.trans_le (hfar.trans hre')
      rw [norm_inv]
      exact (inv_le_one₀ hden).2 (hfar.trans hre')
    calc
      ‖∫ y in -c..c, (((R : ℂ) + y * I) - p)⁻¹‖ ≤
          (1 : ℝ) * |c - (-c)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hpoint
      _ = 2 * c := by rw [abs_of_pos (by linarith)]; ring
      _ ≤ xiVerticalCauchyKernelBoundAt c := by
        unfold xiVerticalCauchyKernelBoundAt
        nlinarith [abs_nonneg (Real.log (c - 1 / 2)),
          abs_nonneg (Real.log (c + 3 / 2)), Real.pi_pos.le]

/-- Slowly varying weighted Cauchy estimate on the complete depth-`c` vertical edge. -/
theorem norm_integral_mul_vertical_cauchyKernel_le_at
    {c : ℝ} (hc : 1 / 2 < c) {h : ℝ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hdiff : ∀ y ∈ Icc (-c) c, DifferentiableAt ℝ h y)
    (hderiv : ∀ y ∈ Icc (-c) c, ‖deriv h y‖ ≤ M)
    {p : ℂ} (hpim : (-1 / 2 : ℝ) < p.im ∧ p.im < 1 / 2)
    {R : ℝ} (hR : R ≠ p.re) :
    ‖∫ y in -c..c, h y * ((((R : ℂ) + y * I) - p)⁻¹)‖ ≤
      ‖h p.im‖ * xiVerticalCauchyKernelBoundAt c + (2 * c) * M := by
  let k : ℝ → ℂ := fun y => ((((R : ℂ) + y * I) - p)⁻¹)
  let r : ℝ → ℂ := fun y => (h y - h p.im) * k y
  have hcpos : 0 < c := lt_trans (by norm_num) hc
  have hpMem : p.im ∈ Icc (-c) c := by constructor <;> linarith [hpim.1, hpim.2]
  have hden (y : ℝ) : ((R : ℂ) + y * I) - p ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      zero_mul, mul_zero, sub_zero, add_zero, zero_re] at hre
    exact hR (sub_eq_zero.mp hre)
  have hhcont : ContinuousOn h (Icc (-c) c) := by
    intro y hy
    exact (hdiff y hy).continuousAt.continuousWithinAt
  have hkcont : ContinuousOn k (Icc (-c) c) := by
    apply (continuousOn_of_forall_continuousAt (fun y => by fun_prop)).inv₀
    intro y _
    exact hden y
  have hrcont : ContinuousOn r (Icc (-c) c) :=
    (hhcont.sub continuousOn_const).mul hkcont
  have hkInt : IntervalIntegrable k MeasureTheory.volume (-c) c := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le (by linarith : -c ≤ c)] using hkcont
  have hconstInt : IntervalIntegrable (fun y => h p.im * k y)
      MeasureTheory.volume (-c) c := hkInt.const_mul _
  have hrInt : IntervalIntegrable r MeasureTheory.volume (-c) c := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le (by linarith : -c ≤ c)] using hrcont
  have hsplit :
      (∫ y in -c..c, h y * k y) =
        h p.im * (∫ y in -c..c, k y) + ∫ y in -c..c, r y := by
    calc
      (∫ y in -c..c, h y * k y) =
          ∫ y in -c..c, h p.im * k y + r y := by
        apply integral_congr
        intro y _
        dsimp only [r]
        ring
      _ = (∫ y in -c..c, h p.im * k y) + ∫ y in -c..c, r y :=
        integral_add hconstInt hrInt
      _ = _ := by rw [integral_const_mul]
  have hconstant :
      ‖h p.im * (∫ y in -c..c, k y)‖ ≤
        ‖h p.im‖ * xiVerticalCauchyKernelBoundAt c := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [k] using norm_integral_vertical_cauchyKernel_le_at hc hpim hR)
      (norm_nonneg _)
  have hrPoint : ∀ y ∈ uIoc (-c) c, ‖r y‖ ≤ M := by
    intro y hy
    have hyIoc : y ∈ Ioc (-c) c := by
      simpa [uIoc_of_le (by linarith : -c ≤ c)] using hy
    have hyMem : y ∈ Icc (-c) c := Ioc_subset_Icc_self hyIoc
    have hmv0 := Convex.norm_image_sub_le_of_norm_deriv_le
      hdiff hderiv (convex_Icc (-c) c) hpMem hyMem
    have hmv : ‖h y - h p.im‖ ≤ M * |y - p.im| := by
      simpa only [Real.norm_eq_abs] using hmv0
    have himdist : |y - p.im| ≤ ‖((R : ℂ) + y * I) - p‖ := by
      have := Complex.abs_im_le_norm (((R : ℂ) + y * I) - p)
      simpa only [sub_im, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
        zero_mul, mul_one, zero_add, add_zero] using this
    have hdenPos : 0 < ‖((R : ℂ) + y * I) - p‖ := norm_pos_iff.mpr (hden y)
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
  have hremainder : ‖∫ y in -c..c, r y‖ ≤ (2 * c) * M := by
    have hraw := intervalIntegral.norm_integral_le_of_norm_le_const hrPoint
    have habs : |c - -c| = 2 * c := by rw [abs_of_pos (by linarith)]; ring
    rw [habs] at hraw
    simpa [mul_comm] using hraw
  change ‖∫ y in -c..c, h y * k y‖ ≤ _
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add hconstant hremainder)

end

end RHTower
