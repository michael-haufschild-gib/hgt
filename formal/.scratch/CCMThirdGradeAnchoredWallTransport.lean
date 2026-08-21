import GaloisForLFunctions.RHTower.CCMGuinandWeilThirdGradeRectangularPrimitiveCurrent

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

private theorem intervalIntegrable_anchoredKernelProduct
    {a b c H : ℝ} (hb : 0 < b) (hbc : b ≤ c) :
    IntervalIntegrable
      (fun h : ℝ =>
        ccmGuinandWeilThirdGradeCesaroErrorKernel H h *
          (criticalMellinCompletedError a - criticalMellinCompletedError h))
      volume b c := by
  have hE := intervalIntegrable_criticalMellinCompletedError_on_Icc hbc
  have hdiff : IntervalIntegrable
      (fun h : ℝ => criticalMellinCompletedError a - criticalMellinCompletedError h)
      volume b c := intervalIntegrable_const.sub hE
  have hkernel : ContinuousOn
      (ccmGuinandWeilThirdGradeCesaroErrorKernel H) (uIcc b c) := by
    rw [uIcc_of_le hbc]
    intro h hh
    unfold ccmGuinandWeilThirdGradeCesaroErrorKernel
    exact ((continuousAt_const.sub
      ((continuousAt_const.mul continuousAt_id).div_const H)).div
        (continuousAt_id.pow 4)
        (pow_ne_zero 4 (ne_of_gt (hb.trans_le hh.1)))).continuousWithinAt
  apply (hdiff.mul_continuousOn hkernel).congr
  intro h _
  ring

private theorem intervalIntegrable_anchoredCubicProduct
    {a b c : ℝ} (hb : 0 < b) (hbc : b ≤ c) :
    IntervalIntegrable
      (fun h : ℝ =>
        (criticalMellinCompletedError a - criticalMellinCompletedError h) / h ^ 3)
      volume b c := by
  have hE := intervalIntegrable_criticalMellinCompletedError_on_Icc hbc
  have hdiff : IntervalIntegrable
      (fun h : ℝ => criticalMellinCompletedError a - criticalMellinCompletedError h)
      volume b c := intervalIntegrable_const.sub hE
  have hcubic : ContinuousOn (fun h : ℝ => 1 / h ^ 3) (uIcc b c) := by
    rw [uIcc_of_le hbc]
    intro h hh
    exact (continuousAt_const.div (continuousAt_id.pow 3)
      (pow_ne_zero 3 (ne_of_gt (hb.trans_le hh.1)))).continuousWithinAt
  apply (hdiff.mul_continuousOn hcubic).congr
  intro h _
  ring

/-- **Fixed-wall transport law.** Reanchoring the RH-bearing CCM-FU moment at an intermediate
positive wall preserves the completed prime--polar source exactly. The only memory terms are one
coefficient-faithful endpoint increment and one compact cubic moment; their dependence on the
moving upper wall is explicit. -/
theorem ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment_wallTransport
    {b c H : ℝ} (hb : 0 < b) (hbc : b ≤ c) (hcH : c ≤ H) :
    ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H =
      ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b c +
        ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment c H +
        ccmGuinandWeilThirdGradeCesaroTriangularWeight H c *
          (criticalMellinCompletedError b - criticalMellinCompletedError c) +
        64 * (1 / c - 1 / H) *
          (∫ h in b..c,
            (criticalMellinCompletedError b - criticalMellinCompletedError h) / h ^ 3) := by
  have hc : 0 < c := hb.trans_le hbc
  have hH : 0 < H := hc.trans_le hcH
  let F : ℝ → ℝ := fun h =>
    criticalMellinCompletedError b - criticalMellinCompletedError h
  let G : ℝ → ℝ := fun h =>
    criticalMellinCompletedError c - criticalMellinCompletedError h
  let KH : ℝ → ℝ := ccmGuinandWeilThirdGradeCesaroErrorKernel H
  let KC : ℝ → ℝ := ccmGuinandWeilThirdGradeCesaroErrorKernel c
  have hKHbc : IntervalIntegrable (fun h => KH h * F h) volume b c :=
    intervalIntegrable_anchoredKernelProduct (a := b) hb hbc
  have hKHcH : IntervalIntegrable (fun h => KH h * F h) volume c H :=
    intervalIntegrable_anchoredKernelProduct (a := b) hc hcH
  have hsplit : (∫ h in b..H, KH h * F h) =
      (∫ h in b..c, KH h * F h) + ∫ h in c..H, KH h * F h :=
    (intervalIntegral.integral_add_adjacent_intervals hKHbc hKHcH).symm
  have hKCbc : IntervalIntegrable (fun h => KC h * F h) volume b c :=
    intervalIntegrable_anchoredKernelProduct (a := b) hb hbc
  have hJ : IntervalIntegrable (fun h => F h / h ^ 3) volume b c :=
    intervalIntegrable_anchoredCubicProduct (a := b) hb hbc
  have hprefix : (∫ h in b..c, KH h * F h) =
      (∫ h in b..c, KC h * F h) +
        64 * (1 / c - 1 / H) * ∫ h in b..c, F h / h ^ 3 := by
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_add hKCbc
      (hJ.const_mul (64 * (1 / c - 1 / H)))]
    apply intervalIntegral.integral_congr
    intro h hh
    rw [uIcc_of_le hbc] at hh
    have hh0 : h ≠ 0 := ne_of_gt (hb.trans_le hh.1)
    dsimp only [KH, KC, F]
    unfold ccmGuinandWeilThirdGradeCesaroErrorKernel
    field_simp [hh0, hc.ne', hH.ne']
    ring
  have hGcH : IntervalIntegrable (fun h => KH h * G h) volume c H :=
    intervalIntegrable_anchoredKernelProduct (a := c) hc hcH
  have hKcH : IntervalIntegrable KH volume c H := by
    have hcont : ContinuousOn KH (uIcc c H) := by
      rw [uIcc_of_le hcH]
      intro h hh
      dsimp only [KH]
      unfold ccmGuinandWeilThirdGradeCesaroErrorKernel
      exact ((continuousAt_const.sub
        ((continuousAt_const.mul continuousAt_id).div_const H)).div
          (continuousAt_id.pow 4)
          (pow_ne_zero 4 (ne_of_gt (hc.trans_le hh.1)))).continuousWithinAt
    exact hcont.intervalIntegrable
  have htail : (∫ h in c..H, KH h * F h) =
      (∫ h in c..H, KH h * G h) +
        ccmGuinandWeilThirdGradeCesaroTriangularWeight H c *
          (criticalMellinCompletedError b - criticalMellinCompletedError c) := by
    have hpoint : ∀ h, F h =
        (criticalMellinCompletedError b - criticalMellinCompletedError c) + G h := by
      intro h
      dsimp only [F, G]
      ring
    rw [show (fun h => KH h * F h) = fun h =>
        KH h * (criticalMellinCompletedError b - criticalMellinCompletedError c) +
          KH h * G h by funext h; rw [hpoint]; ring]
    rw [intervalIntegral.integral_add
      (hKcH.mul_const _) hGcH, intervalIntegral.integral_mul_const]
    rw [integral_ccmGuinandWeilThirdGradeCesaroErrorKernel hc hcH]
    unfold ccmGuinandWeilThirdGradeCesaroTriangularWeight
      ccmGuinandWeilThirdGradeWeight
    ring
  unfold ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment
  change (∫ h in b..H, KH h * F h) = _
  rw [hsplit, hprefix, htail]
  change _ =
    (∫ h in b..c, KC h * F h) +
      (∫ h in c..H, KH h * G h) + _
  ring

end GaloisForLFunctions.RHTower
