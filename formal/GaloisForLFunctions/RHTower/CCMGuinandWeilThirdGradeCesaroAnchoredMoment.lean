import GaloisForLFunctions.RHTower.CCMUnitRieszFUCurvatureTransport
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Anchored positive-kernel form of the CCM-FU open core

The literal third-grade Cesàro primitive is one signed average of completed-error increments.
Prime and polar terms are never separated, and the averaging kernel is pointwise positive on the
physical window.  This identifies the exact cancellation that any CCM-FU producer must control.
-/

open Set MeasureTheory

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- Positive finite-window kernel forced by one more primitive of the cubic completed-error flux. -/
def ccmGuinandWeilThirdGradeCesaroErrorKernel (H h : ℝ) : ℝ :=
  (96 - 64 * h / H) / h ^ 4

/-- Anchored signed completed-error moment.  The anchoring retains the lower-wall coefficient. -/
def ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment (b H : ℝ) : ℝ :=
  ∫ h in b..H,
    ccmGuinandWeilThirdGradeCesaroErrorKernel H h *
      (criticalMellinCompletedError b - criticalMellinCompletedError h)

private theorem integral_intervalIntegral_eq_endpoint_mul_sub_moment
    {g : ℝ → ℝ} {b H : ℝ} (hbH : b ≤ H)
    (hg : IntervalIntegrable g volume b H) :
    (∫ s in b..H, ∫ h in b..s, g h) =
      H * (∫ h in b..H, g h) - ∫ h in b..H, h * g h := by
  let A : ℝ → ℝ := fun s => ∫ h in b..s, g h
  let G : ℝ → ℝ := fun s => s
  have hAac : AbsolutelyContinuousOnInterval A b H :=
    hg.absolutelyContinuousOnInterval_intervalIntegral
      (show b ∈ Set.uIcc b H by simp [hbH])
  have hGcd : ContDiff ℝ 1 G := by fun_prop
  have hGac : AbsolutelyContinuousOnInterval G b H :=
    hGcd.contDiffOn.absolutelyContinuousOnInterval
  have hibp := hGac.integral_mul_deriv_eq_deriv_mul hAac
  have hleft : (∫ s in b..H, G s * deriv A s) =
      ∫ s in b..H, s * g s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hg.ae_hasDerivAt_integral] with s hs hmem
    have hd : HasDerivAt A (g s) s :=
      hs (uIoc_subset_uIcc hmem) b (by simp [hbH])
    rw [hd.deriv]
  have hright : (∫ s in b..H, deriv G s * A s) =
      ∫ s in b..H, A s := by
    apply intervalIntegral.integral_congr
    intro s _
    have hd : deriv G s = 1 := (hasDerivAt_id s).deriv
    change deriv G s * A s = A s
    rw [hd, one_mul]
  have hAb : A b = 0 := by simp [A]
  rw [hleft, hright, hAb, mul_zero, sub_zero] at hibp
  dsimp only [A, G] at hibp ⊢
  linarith

private theorem intervalIntegrable_completedError_div_fourth
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    IntervalIntegrable
      (fun h : ℝ => 96 * criticalMellinCompletedError h / h ^ 4)
      volume b H := by
  have hE := intervalIntegrable_criticalMellinCompletedError_on_Icc hbH
  have hc : ContinuousOn (fun h : ℝ => 96 / h ^ 4) (Set.uIcc b H) := by
    rw [Set.uIcc_of_le hbH]
    intro h hh
    exact (continuousAt_const.div (continuousAt_id.pow 4)
      (pow_ne_zero 4 (ne_of_gt (hb.trans_le hh.1)))).continuousWithinAt
  have hmul := hE.mul_continuousOn hc
  apply hmul.congr
  intro h _
  ring

/-- The second primitive of the literal third-grade source is an exact signed completed-error
moment.  No absolute value, sign-region split, or asymptotic hypothesis occurs. -/
theorem ccmCesaroPrimitive_thirdGradeCumulative_eq_errorMoment
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    ccmCesaroPrimitive
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H =
      32 * criticalMellinCompletedError b / b ^ 3 * (H - b) +
        64 * (∫ h in b..H, criticalMellinCompletedError h / h ^ 3) -
          96 * H * (∫ h in b..H, criticalMellinCompletedError h / h ^ 4) := by
  let E := criticalMellinCompletedError
  let g : ℝ → ℝ := fun h => 96 * E h / h ^ 4
  have hg : IntervalIntegrable g volume b H :=
    intervalIntegrable_completedError_div_fourth hb hbH
  have hdouble := integral_intervalIntegral_eq_endpoint_mul_sub_moment hbH hg
  unfold ccmCesaroPrimitive
  calc
    (∫ s in b..H, ccmGuinandWeilThirdGradeCumulativeMeasurable b s) =
        ∫ s in b..H,
          (32 * E b / b ^ 3 - 32 * E s / s ^ 3 - ∫ h in b..s, g h) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le hbH] at hs
      rw [thirdGradeCumulative_eq_completedErrorFlux hb hs.1]
      unfold ccmGuinandWeilThirdGradeWeight ccmGuinandWeilThirdGradeWeightDeriv
      dsimp only [E, g]
      have hint :
          (∫ v in b..s, criticalMellinCompletedError v * (-96 / v ^ 4)) =
            -(∫ v in b..s, 96 * criticalMellinCompletedError v / v ^ 4) := by
        rw [← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_congr
        intro v _
        ring
      rw [hint]
      ring
    _ = (∫ s in b..H, 32 * E b / b ^ 3) -
          (∫ s in b..H, 32 * E s / s ^ 3) -
            ∫ s in b..H, ∫ h in b..s, g h := by
      have hE := intervalIntegrable_criticalMellinCompletedError_on_Icc hbH
      have hc3 : ContinuousOn (fun h : ℝ => 32 / h ^ 3) (Set.uIcc b H) := by
        rw [Set.uIcc_of_le hbH]
        intro h hh
        exact (continuousAt_const.div (continuousAt_id.pow 3)
          (pow_ne_zero 3 (ne_of_gt (hb.trans_le hh.1)))).continuousWithinAt
      have hthird : IntervalIntegrable (fun s : ℝ => 32 * E s / s ^ 3) volume b H := by
        have hm := hE.mul_continuousOn hc3
        apply hm.congr
        intro s _
        ring
      have hprimitive : IntervalIntegrable (fun s : ℝ => ∫ h in b..s, g h) volume b H :=
        (hg.absolutelyContinuousOnInterval_intervalIntegral
          (show b ∈ Set.uIcc b H by simp [hbH])).continuousOn.intervalIntegrable
      rw [intervalIntegral.integral_sub
          ((intervalIntegrable_const : IntervalIntegrable
            (fun _ : ℝ => 32 * E b / b ^ 3) volume b H).sub hthird) hprimitive,
        intervalIntegral.integral_sub
          (intervalIntegrable_const : IntervalIntegrable
            (fun _ : ℝ => 32 * E b / b ^ 3) volume b H) hthird]
    _ = _ := by
      rw [intervalIntegral.integral_const, hdouble]
      dsimp only [g, E]
      have hthirdScale :
          (∫ s in b..H, 32 * criticalMellinCompletedError s / s ^ 3) =
            32 * ∫ s in b..H, criticalMellinCompletedError s / s ^ 3 := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro s _
        ring
      have hfourthScale :
          (∫ h in b..H, 96 * criticalMellinCompletedError h / h ^ 4) =
            96 * ∫ h in b..H, criticalMellinCompletedError h / h ^ 4 := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro h _
        ring
      have hmomentScale :
          (∫ h in b..H, h * (96 * criticalMellinCompletedError h / h ^ 4)) =
            96 * ∫ h in b..H, criticalMellinCompletedError h / h ^ 3 := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro h hh
        rw [Set.uIcc_of_le hbH] at hh
        have hh0 : h ≠ 0 := ne_of_gt (hb.trans_le hh.1)
        field_simp [hh0]
      rw [hthirdScale, hfourthScale, hmomentScale]
      ring

/-- The positive Cesàro kernel has exactly the mass needed to cancel the lower-wall coefficient. -/
theorem integral_ccmGuinandWeilThirdGradeCesaroErrorKernel
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    (∫ h in b..H, ccmGuinandWeilThirdGradeCesaroErrorKernel H h) =
      32 / b ^ 3 * (1 - b / H) := by
  have hH : 0 < H := hb.trans_le hbH
  change (∫ h in b..H, (96 - 64 * h / H) / h ^ 4) = _
  have hfun : ∀ h ∈ Set.uIcc b H,
      (96 - 64 * h / H) / h ^ 4 =
        96 / h ^ 4 - (64 / H) / h ^ 3 := by
    intro h hh
    rw [Set.uIcc_of_le hbH] at hh
    have hh0 : h ≠ 0 := ne_of_gt (hb.trans_le hh.1)
    field_simp [hh0, hH.ne']
  rw [intervalIntegral.integral_congr hfun]
  have hfour :
      (∫ h in b..H, 96 / h ^ 4) = 32 / b ^ 3 - 32 / H ^ 3 := by
    have hint : IntervalIntegrable (fun h : ℝ => 96 / h ^ 4) volume b H := by
      have hc : ContinuousOn (fun h : ℝ => 96 / h ^ 4) (Set.uIcc b H) := by
        rw [Set.uIcc_of_le hbH]
        intro h hh
        exact (continuousAt_const.div (continuousAt_id.pow 4)
          (pow_ne_zero 4 (ne_of_gt (hb.trans_le hh.1)))).continuousWithinAt
      exact hc.intervalIntegrable
    have hderiv : ∀ h ∈ Set.uIcc b H,
        HasDerivAt (fun x : ℝ => -32 * (x ^ 3)⁻¹) (96 / h ^ 4) h := by
      intro h hh
      rw [Set.uIcc_of_le hbH] at hh
      have hh0 : h ≠ 0 := ne_of_gt (hb.trans_le hh.1)
      have hraw := ((hasDerivAt_id h).pow 3).inv (pow_ne_zero 3 hh0)
      have hscaled := hraw.const_mul (-32)
      apply hscaled.congr_deriv
      simp only [id_eq, Pi.pow_apply]
      field_simp [hh0]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    ring
  have hthree :
      (∫ h in b..H, (64 / H) / h ^ 3) =
        32 / (H * b ^ 2) - 32 / H ^ 3 := by
    have hint : IntervalIntegrable (fun h : ℝ => (64 / H) / h ^ 3) volume b H := by
      have hc : ContinuousOn (fun h : ℝ => (64 / H) / h ^ 3) (Set.uIcc b H) := by
        rw [Set.uIcc_of_le hbH]
        intro h hh
        exact (continuousAt_const.div (continuousAt_id.pow 3)
          (pow_ne_zero 3 (ne_of_gt (hb.trans_le hh.1)))).continuousWithinAt
      exact hc.intervalIntegrable
    have hderiv : ∀ h ∈ Set.uIcc b H,
        HasDerivAt (fun x : ℝ => -(32 / H) * (x ^ 2)⁻¹) ((64 / H) / h ^ 3) h := by
      intro h hh
      rw [Set.uIcc_of_le hbH] at hh
      have hh0 : h ≠ 0 := ne_of_gt (hb.trans_le hh.1)
      have hraw := ((hasDerivAt_id h).pow 2).inv (pow_ne_zero 2 hh0)
      have hscaled := hraw.const_mul (-(32 / H))
      apply hscaled.congr_deriv
      simp only [id_eq, Pi.pow_apply]
      field_simp [hh0, hH.ne']
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    field_simp [hb.ne', hH.ne']
    ring
  have hfourInt : IntervalIntegrable (fun h : ℝ => 96 / h ^ 4) volume b H := by
    have hc : ContinuousOn (fun h : ℝ => 96 / h ^ 4) (Set.uIcc b H) := by
      rw [Set.uIcc_of_le hbH]
      intro h hh
      exact (continuousAt_const.div (continuousAt_id.pow 4)
        (pow_ne_zero 4 (ne_of_gt (hb.trans_le hh.1)))).continuousWithinAt
    exact hc.intervalIntegrable
  have hthreeInt : IntervalIntegrable (fun h : ℝ => (64 / H) / h ^ 3) volume b H := by
    have hc : ContinuousOn (fun h : ℝ => (64 / H) / h ^ 3) (Set.uIcc b H) := by
      rw [Set.uIcc_of_le hbH]
      intro h hh
      exact (continuousAt_const.div (continuousAt_id.pow 3)
        (pow_ne_zero 3 (ne_of_gt (hb.trans_le hh.1)))).continuousWithinAt
    exact hc.intervalIntegrable
  rw [intervalIntegral.integral_sub hfourInt hthreeInt, hfour, hthree]
  field_simp [hb.ne', hH.ne']
  ring

/-- **Anchored positive-kernel law.**  Normalizing the literal FU Cesàro primitive by its moving
wall gives one positive-kernel signed average of completed-error increments from the actual lower
wall.  This preserves prime--polar cancellation pointwise before averaging. -/
theorem ccmCesaroPrimitive_thirdGradeCumulative_div_eq_anchoredErrorMoment
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    ccmCesaroPrimitive
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H / H =
      ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H := by
  have hH : 0 < H := hb.trans_le hbH
  rw [ccmCesaroPrimitive_thirdGradeCumulative_eq_errorMoment hb hbH]
  rw [ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment]
  rw [show (fun h : ℝ =>
      ccmGuinandWeilThirdGradeCesaroErrorKernel H h *
        (criticalMellinCompletedError b - criticalMellinCompletedError h)) =
      fun h => criticalMellinCompletedError b *
          ccmGuinandWeilThirdGradeCesaroErrorKernel H h -
        ccmGuinandWeilThirdGradeCesaroErrorKernel H h *
          criticalMellinCompletedError h by
    funext h; ring]
  rw [intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul,
    integral_ccmGuinandWeilThirdGradeCesaroErrorKernel hb hbH]
  · change
      (32 * criticalMellinCompletedError b / b ^ 3 * (H - b) +
          64 * (∫ h in b..H, criticalMellinCompletedError h / h ^ 3) -
            96 * H * (∫ h in b..H, criticalMellinCompletedError h / h ^ 4)) / H =
        criticalMellinCompletedError b * (32 / b ^ 3 * (1 - b / H)) -
          ∫ h in b..H,
            (96 - 64 * h / H) / h ^ 4 * criticalMellinCompletedError h
    have hsplit :
        (∫ h in b..H,
          (96 - 64 * h / H) / h ^ 4 * criticalMellinCompletedError h) =
          96 * (∫ h in b..H, criticalMellinCompletedError h / h ^ 4) -
            (64 / H) * (∫ h in b..H,
              criticalMellinCompletedError h / h ^ 3) := by
      have hE4 := intervalIntegrable_completedError_div_fourth hb hbH
      have hE := intervalIntegrable_criticalMellinCompletedError_on_Icc hbH
      have hc3 : ContinuousOn (fun h : ℝ => (64 / H) / h ^ 3) (Set.uIcc b H) := by
        rw [Set.uIcc_of_le hbH]
        intro h hh
        exact (continuousAt_const.div (continuousAt_id.pow 3)
          (pow_ne_zero 3 (ne_of_gt (hb.trans_le hh.1)))).continuousWithinAt
      have hE3raw := hE.mul_continuousOn hc3
      have hE3 : IntervalIntegrable
          (fun h : ℝ => (64 / H) * (criticalMellinCompletedError h / h ^ 3))
          volume b H := by
        apply hE3raw.congr
        intro h _
        ring
      calc
        (∫ h in b..H,
            (96 - 64 * h / H) / h ^ 4 * criticalMellinCompletedError h) =
            ∫ h in b..H,
              (96 * criticalMellinCompletedError h / h ^ 4 -
                (64 / H) * (criticalMellinCompletedError h / h ^ 3)) := by
          apply intervalIntegral.integral_congr
          intro h hh
          rw [Set.uIcc_of_le hbH] at hh
          have hh0 : h ≠ 0 := ne_of_gt (hb.trans_le hh.1)
          field_simp [hh0, hH.ne']
        _ = (∫ h in b..H, 96 * criticalMellinCompletedError h / h ^ 4) -
              ∫ h in b..H, (64 / H) *
                (criticalMellinCompletedError h / h ^ 3) :=
          intervalIntegral.integral_sub hE4 hE3
        _ = _ := by
          rw [← intervalIntegral.integral_const_mul,
            ← intervalIntegral.integral_const_mul]
          congr 1
          · apply intervalIntegral.integral_congr
            intro h _
            ring
    rw [hsplit]
    field_simp [hb.ne', hH.ne']
    ring
  · exact (by
      have hc : ContinuousOn
          (ccmGuinandWeilThirdGradeCesaroErrorKernel H) (Set.uIcc b H) := by
        change ContinuousOn
          (fun h : ℝ => ((96 : ℝ) - 64 * h / H) / h ^ 4) (Set.uIcc b H)
        rw [Set.uIcc_of_le hbH]
        intro h hh
        exact ((continuousAt_const.sub
          ((continuousAt_const.mul continuousAt_id).div_const H)).div
            (continuousAt_id.pow 4)
            (pow_ne_zero 4 (ne_of_gt (hb.trans_le hh.1)))).continuousWithinAt
      exact hc.intervalIntegrable.const_mul _)
  · have hE := intervalIntegrable_criticalMellinCompletedError_on_Icc hbH
    have hc : ContinuousOn
        (ccmGuinandWeilThirdGradeCesaroErrorKernel H) (Set.uIcc b H) := by
      change ContinuousOn
        (fun h : ℝ => ((96 : ℝ) - 64 * h / H) / h ^ 4) (Set.uIcc b H)
      rw [Set.uIcc_of_le hbH]
      intro h hh
      exact ((continuousAt_const.sub
        ((continuousAt_const.mul continuousAt_id).div_const H)).div
          (continuousAt_id.pow 4)
          (pow_ne_zero 4 (ne_of_gt (hb.trans_le hh.1)))).continuousWithinAt
    have hm := hE.mul_continuousOn hc
    apply hm.congr
    intro h _
    ring

/-- On the physical window the anchored averaging kernel is strictly positive. -/
theorem ccmGuinandWeilThirdGradeCesaroErrorKernel_pos
    {b H h : ℝ} (hb : 0 < b) (hbH : b ≤ H) (hh : h ∈ Set.Icc b H) :
    0 < ccmGuinandWeilThirdGradeCesaroErrorKernel H h := by
  have hH : 0 < H := hb.trans_le hbH
  have hh0 : 0 < h := hb.trans_le hh.1
  unfold ccmGuinandWeilThirdGradeCesaroErrorKernel
  have hratio : h / H ≤ 1 := (div_le_one hH).mpr hh.2
  have hscaled : 64 * (h / H) ≤ 64 := by
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 64))
  have hterm : 64 * h / H ≤ 64 := by
    calc
      64 * h / H = 64 * (h / H) := by ring
      _ ≤ 64 := hscaled
  have hnum : 0 < 96 - 64 * h / H := by linarith
  exact div_pos hnum (pow_pos hh0 4)

/-- The positive kernel stays between its endpoint cubic grades throughout the physical window. -/
theorem ccmGuinandWeilThirdGradeCesaroErrorKernel_bounds
    {b H h : ℝ} (hb : 0 < b) (hbH : b ≤ H) (hh : h ∈ Set.Icc b H) :
    32 / h ^ 4 ≤ ccmGuinandWeilThirdGradeCesaroErrorKernel H h ∧
      ccmGuinandWeilThirdGradeCesaroErrorKernel H h ≤ 96 / h ^ 4 := by
  have hH : 0 < H := hb.trans_le hbH
  have hh0 : 0 < h := hb.trans_le hh.1
  have hratio0 : 0 ≤ h / H := div_nonneg hh0.le hH.le
  have hratio1 : h / H ≤ 1 := (div_le_one hH).mpr hh.2
  have hscaled0 : 0 ≤ 64 * (h / H) := mul_nonneg (by norm_num) hratio0
  have hscaled1 : 64 * (h / H) ≤ 64 := by
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left hratio1 (by norm_num : (0 : ℝ) ≤ 64))
  have hnumLower : 32 ≤ 96 - 64 * h / H := by
    have hterm : 64 * h / H ≤ 64 := by
      calc
        64 * h / H = 64 * (h / H) := by ring
        _ ≤ 64 := hscaled1
    linarith
  have hnumUpper : 96 - 64 * h / H ≤ 96 := by
    have hterm : 0 ≤ 64 * h / H := by
      calc
        0 ≤ 64 * (h / H) := hscaled0
        _ = 64 * h / H := by ring
    linarith
  unfold ccmGuinandWeilThirdGradeCesaroErrorKernel
  exact ⟨div_le_div_of_nonneg_right hnumLower (by positivity),
    div_le_div_of_nonneg_right hnumUpper (by positivity)⟩

/-- Uniform boundedness of the anchored signed completed-error moment. -/
def CCMGuinandWeilThirdGradeCesaroAnchoredMomentBound (b : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℝ, b < H →
    |ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H| ≤ C

/-- **Exact CCM-FU frontier classification.**  Linear growth of the literal Cesàro primitive is
equivalent to uniform boundedness of one source-faithful anchored signed moment.  The positive
kernel is kept intact; its positive and negative arithmetic regions are never bounded separately. -/
theorem ccmGuinandWeilThirdGradeCesaroLinearBound_iff_anchoredMomentBound
    {b : ℝ} (hb : 0 < b) :
    CCMGuinandWeilThirdGradeCesaroLinearBound b ↔
      CCMGuinandWeilThirdGradeCesaroAnchoredMomentBound b := by
  constructor
  · rintro ⟨C, hC, hbound⟩
    let D : ℝ := C * (1 + 1 / b)
    have hD : 0 ≤ D := by
      dsimp only [D]
      exact mul_nonneg hC (by positivity)
    refine ⟨D, hD, ?_⟩
    intro H hbH
    have hH : 0 < H := hb.trans hbH
    have hEq := ccmCesaroPrimitive_thirdGradeCumulative_div_eq_anchoredErrorMoment
      hb hbH.le
    rw [← hEq, abs_div, abs_of_pos hH]
    have hgeom : H + 1 ≤ (1 + 1 / b) * H := by
      have hone : 1 ≤ H / b := (le_div_iff₀ hb).2 (by simpa using hbH.le)
      calc
        H + 1 ≤ H + H / b := by linarith
        _ = (1 + 1 / b) * H := by ring
    have hnumerator :
        |ccmCesaroPrimitive
          (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H| ≤ D * H := by
      calc
        _ ≤ C * (H + 1) := hbound H hbH
        _ ≤ C * ((1 + 1 / b) * H) :=
          mul_le_mul_of_nonneg_left hgeom hC
        _ = D * H := by simp only [D]; ring
    exact (div_le_iff₀ hH).2 hnumerator
  · rintro ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro H hbH
    have hH : 0 < H := hb.trans hbH
    have hEq := ccmCesaroPrimitive_thirdGradeCumulative_div_eq_anchoredErrorMoment
      hb hbH.le
    have hrecover :
        ccmCesaroPrimitive
            (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b H =
          ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H * H := by
      apply (div_eq_iff hH.ne').mp
      exact hEq
    rw [hrecover, abs_mul, abs_of_pos hH]
    calc
      |ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H| * H ≤ C * H :=
        mul_le_mul_of_nonneg_right (hbound H hbH) hH.le
      _ ≤ C * (H + 1) := mul_le_mul_of_nonneg_left (by linarith) hC

/-- The anchored positive-kernel bound is an unconditional sufficient criterion for RH because it
is exactly the literal CCM-FU open core, not a reporter-only coercivity surrogate. -/
theorem riemannHypothesis_of_ccmGuinandWeilThirdGradeCesaroAnchoredMomentBound
    {b : ℝ} (hb : 0 < b)
    (hbound : CCMGuinandWeilThirdGradeCesaroAnchoredMomentBound b) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_ccmGuinandWeilThirdGradeCesaroLinearBound hb
    ((ccmGuinandWeilThirdGradeCesaroLinearBound_iff_anchoredMomentBound hb).2 hbound)

end GaloisForLFunctions.RHTower

end
