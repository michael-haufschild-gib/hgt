import GaloisForLFunctions.RHTower.CCMGuinandWeilThirdGradeRectangularPrimitiveCurrent
import GaloisForLFunctions.RHTower.XiMassCriticalPrimeCone

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
  dsimp only [KC, KH, F, G]
  ring

/-- **Exact cofinal wall cocycle.** For two fixed positive anchors, the difference of the
RH-bearing signed currents is not merely bounded: it is exactly an affine function of `H⁻¹`.
Thus every fixed-anchor current represents the same cofinal germ modulo
`span {1, H ↦ H⁻¹}` while retaining the literal completed prime--polar coefficients. -/
theorem ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment_sub_eq_wallCofinalCocycle
    {b c H : ℝ} (hb : 0 < b) (hbc : b ≤ c) (hcH : c ≤ H) :
    ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H -
        ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment c H =
      ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b c +
        (32 / c ^ 3) *
          (criticalMellinCompletedError b - criticalMellinCompletedError c) +
        (64 / c) *
          (∫ h in b..c,
            (criticalMellinCompletedError b - criticalMellinCompletedError h) / h ^ 3) -
        (1 / H) *
          ((32 / c ^ 2) *
              (criticalMellinCompletedError b - criticalMellinCompletedError c) +
            64 *
              (∫ h in b..c,
                (criticalMellinCompletedError b - criticalMellinCompletedError h) / h ^ 3)) := by
  have hc : 0 < c := hb.trans_le hbc
  have hH : 0 < H := hc.trans_le hcH
  have htransport :=
    ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment_wallTransport
      hb hbc hcH
  rw [htransport]
  unfold ccmGuinandWeilThirdGradeCesaroTriangularWeight
    ccmGuinandWeilThirdGradeWeight
  field_simp [hc.ne', hH.ne']
  ring

/-- **Canonical cofinal anchor class.** The exact cocycle has a finite source-faithful limit.
No asymptotic estimate on the completed error is used: only the explicit `H⁻¹` wall memory
vanishes. -/
theorem tendsto_ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment_sub
    {b c : ℝ} (hb : 0 < b) (hbc : b ≤ c) :
    Filter.Tendsto
      (fun H : ℝ =>
        ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H -
          ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment c H)
      Filter.atTop
      (nhds
        (ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b c +
          (32 / c ^ 3) *
            (criticalMellinCompletedError b - criticalMellinCompletedError c) +
          (64 / c) *
            (∫ h in b..c,
              (criticalMellinCompletedError b - criticalMellinCompletedError h) / h ^ 3))) := by
  let L := ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b c +
    (32 / c ^ 3) *
      (criticalMellinCompletedError b - criticalMellinCompletedError c) +
    (64 / c) *
      (∫ h in b..c,
        (criticalMellinCompletedError b - criticalMellinCompletedError h) / h ^ 3)
  let Q := (32 / c ^ 2) *
      (criticalMellinCompletedError b - criticalMellinCompletedError c) +
    64 *
      (∫ h in b..c,
        (criticalMellinCompletedError b - criticalMellinCompletedError h) / h ^ 3)
  have hinv : Filter.Tendsto (fun H : ℝ => (1 / H) * Q)
      Filter.atTop (nhds 0) := by
    simpa only [one_div, mul_comm, zero_mul] using
      (tendsto_inv_atTop_zero.const_mul Q)
  have hlimit : Filter.Tendsto (fun H : ℝ => L - (1 / H) * Q)
      Filter.atTop (nhds L) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hinv
  apply hlimit.congr'
  filter_upwards [Filter.eventually_ge_atTop c] with H hcH
  dsimp only [L, Q]
  symm
  exact ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment_sub_eq_wallCofinalCocycle
    hb hbc hcH

/-- Raising the fixed positive lower wall cannot create a new CCM-FU obstruction. All source
information removed from the aperture is retained in the two explicit compact memory terms of
`ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment_wallTransport`. -/
theorem ccmGuinandWeilThirdGradeCesaroAnchoredMomentBound_of_le
    {b c : ℝ} (hb : 0 < b) (hbc : b ≤ c)
    (hbound : CCMGuinandWeilThirdGradeCesaroAnchoredMomentBound b) :
    CCMGuinandWeilThirdGradeCesaroAnchoredMomentBound c := by
  rcases hbound with ⟨B, hB, hbound⟩
  have hc : 0 < c := hb.trans_le hbc
  let A := ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b c
  let D := criticalMellinCompletedError b - criticalMellinCompletedError c
  let J := ∫ h in b..c,
    (criticalMellinCompletedError b - criticalMellinCompletedError h) / h ^ 3
  let C := B + |A| + (32 / c ^ 3) * |D| + (64 / c) * |J|
  have h32 : 0 ≤ 32 / c ^ 3 := by positivity
  have h64 : 0 ≤ 64 / c := by positivity
  refine ⟨C, by
    dsimp only [C]
    positivity, ?_⟩
  intro H hcH
  have hH : 0 < H := hc.trans hcH
  have hbH : b < H := lt_of_le_of_lt hbc hcH
  have hsource := hbound H hbH
  have htransport :=
    ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment_wallTransport
      hb hbc hcH.le
  let T := ccmGuinandWeilThirdGradeCesaroTriangularWeight H c
  let R := 64 * (1 / c - 1 / H)
  have hfac0 : 0 ≤ 1 - c / H := by
    rw [sub_nonneg, div_le_one hH]
    exact hcH.le
  have hfac1 : 1 - c / H ≤ 1 := by
    have : 0 ≤ c / H := by positivity
    linarith
  have hT : |T| ≤ 32 / c ^ 3 := by
    have hTeq : T = (32 / c ^ 3) * (1 - c / H) := by
      dsimp only [T]
      unfold ccmGuinandWeilThirdGradeCesaroTriangularWeight
        ccmGuinandWeilThirdGradeWeight
      ring
    rw [hTeq, abs_of_nonneg (mul_nonneg h32 hfac0)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hfac1 h32
  have hR0 : 0 ≤ R := by
    dsimp only [R]
    have : 1 / H ≤ 1 / c := one_div_le_one_div_of_le hc hcH.le
    positivity
  have hR : |R| ≤ 64 / c := by
    rw [abs_of_nonneg hR0]
    dsimp only [R]
    have hInvH : 0 ≤ 1 / H := by positivity
    calc
      64 * (1 / c - 1 / H) ≤ 64 * (1 / c) := by nlinarith
      _ = 64 / c := by ring
  have hTD : |T * D| ≤ (32 / c ^ 3) * |D| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hT (abs_nonneg D)
  have hRJ : |R * J| ≤ (64 / c) * |J| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hR (abs_nonneg J)
  have hEq : ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment c H =
      ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H - A - T * D - R * J := by
    dsimp only [A, T, D, R, J] at htransport ⊢
    linarith
  rw [hEq]
  have h1 := abs_sub
    (ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H - A - T * D) (R * J)
  have h2 := abs_sub
    (ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H - A) (T * D)
  have h3 := abs_sub
    (ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H) A
  dsimp only [C]
  linarith

/-- Uniform elementary control on every compact interval of upper walls. This isolates the
cofinal arithmetic problem: no bounded interval of apertures contributes to CCM-FU hardness. -/
theorem abs_ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment_le_of_mem
    {b c H : ℝ} (hb : 0 < b) (hbH : b ≤ H) (hHc : H ≤ c) :
    |ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H| ≤
      (96 / b ^ 4) *
        (|criticalMellinCompletedError b| + 23 * Real.exp (c / 2)) * (c - b) := by
  have hH : 0 < H := hb.trans_le hbH
  have hbc : b ≤ c := hbH.trans hHc
  let M := (96 / b ^ 4) *
    (|criticalMellinCompletedError b| + 23 * Real.exp (c / 2))
  have h96 : 0 ≤ 96 / b ^ 4 := by positivity
  have hM : 0 ≤ M := by
    dsimp only [M]
    positivity
  have hpoint : ∀ h ∈ uIoc b H,
      ‖ccmGuinandWeilThirdGradeCesaroErrorKernel H h *
        (criticalMellinCompletedError b - criticalMellinCompletedError h)‖ ≤ M := by
    intro h hh
    have hh' : h ∈ Icc b H := by
      simpa only [uIcc_of_le hbH] using (uIoc_subset_uIcc hh)
    have hh0 : 0 < h := hb.trans_le hh'.1
    have hhc : h ≤ c := hh'.2.trans hHc
    have hkernel :=
      (ccmGuinandWeilThirdGradeCesaroErrorKernel_bounds hb hbH hh').2
    have hpow : b ^ 4 ≤ h ^ 4 := pow_le_pow_left₀ hb.le hh'.1 4
    have hb4 : 0 < b ^ 4 := pow_pos hb 4
    have hkernel' : ccmGuinandWeilThirdGradeCesaroErrorKernel H h ≤ 96 / b ^ 4 :=
      hkernel.trans (div_le_div_of_nonneg_left (by norm_num) hb4 hpow)
    have hkernel0 :=
      (ccmGuinandWeilThirdGradeCesaroErrorKernel_pos hb hbH hh').le
    have hE := abs_criticalMellinCompletedError_le_sqrt hh0.le
    have hexp : Real.exp (h / 2) ≤ Real.exp (c / 2) := by
      exact Real.exp_le_exp.mpr (by linarith)
    have hEh : |criticalMellinCompletedError h| ≤ 23 * Real.exp (c / 2) :=
      hE.trans (mul_le_mul_of_nonneg_left hexp (by norm_num))
    have hdiff : |criticalMellinCompletedError b - criticalMellinCompletedError h| ≤
        |criticalMellinCompletedError b| + 23 * Real.exp (c / 2) :=
      by
        have htri := abs_sub
          (criticalMellinCompletedError b) (criticalMellinCompletedError h)
        linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hkernel0]
    dsimp only [M]
    exact mul_le_mul hkernel' hdiff
      (abs_nonneg (criticalMellinCompletedError b - criticalMellinCompletedError h)) h96
  unfold ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment
  rw [← Real.norm_eq_abs]
  calc
    ‖∫ h in b..H,
        ccmGuinandWeilThirdGradeCesaroErrorKernel H h *
          (criticalMellinCompletedError b - criticalMellinCompletedError h)‖ ≤
        M * |H - b| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = M * (H - b) := by rw [abs_of_nonneg (sub_nonneg.mpr hbH)]
    _ ≤ M * (c - b) := mul_le_mul_of_nonneg_left (by linarith) hM
    _ = _ := by rfl

/-- Lowering a fixed positive source wall also preserves the CCM-FU bound. The only additional
work is the explicit elementary estimate on the bounded aperture interval between the two walls. -/
theorem ccmGuinandWeilThirdGradeCesaroAnchoredMomentBound_lower_of_le
    {b c : ℝ} (hb : 0 < b) (hbc : b ≤ c)
    (hbound : CCMGuinandWeilThirdGradeCesaroAnchoredMomentBound c) :
    CCMGuinandWeilThirdGradeCesaroAnchoredMomentBound b := by
  rcases hbound with ⟨B, hB, hbound⟩
  have hc : 0 < c := hb.trans_le hbc
  let A := ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b c
  let D := criticalMellinCompletedError b - criticalMellinCompletedError c
  let J := ∫ h in b..c,
    (criticalMellinCompletedError b - criticalMellinCompletedError h) / h ^ 3
  let TAIL := B + |A| + (32 / c ^ 3) * |D| + (64 / c) * |J|
  let LOCAL := (96 / b ^ 4) *
    (|criticalMellinCompletedError b| + 23 * Real.exp (c / 2)) * (c - b)
  let C := max TAIL LOCAL
  have h32 : 0 ≤ 32 / c ^ 3 := by positivity
  have h64 : 0 ≤ 64 / c := by positivity
  have hTAIL : 0 ≤ TAIL := by
    dsimp only [TAIL]
    positivity
  have hLOCAL : 0 ≤ LOCAL := by
    dsimp only [LOCAL]
    positivity
  refine ⟨C, le_trans hTAIL (le_max_left _ _), ?_⟩
  intro H hbH
  by_cases hHc : H ≤ c
  · exact (abs_ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment_le_of_mem
      hb hbH.le hHc).trans (le_max_right _ _)
  · have hcH : c < H := lt_of_not_ge hHc
    have hH : 0 < H := hc.trans hcH
    have hsource := hbound H hcH
    have htransport :=
      ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment_wallTransport
        hb hbc hcH.le
    let T := ccmGuinandWeilThirdGradeCesaroTriangularWeight H c
    let R := 64 * (1 / c - 1 / H)
    have hfac0 : 0 ≤ 1 - c / H := by
      rw [sub_nonneg, div_le_one hH]
      exact hcH.le
    have hfac1 : 1 - c / H ≤ 1 := by
      have : 0 ≤ c / H := by positivity
      linarith
    have hT : |T| ≤ 32 / c ^ 3 := by
      have hTeq : T = (32 / c ^ 3) * (1 - c / H) := by
        dsimp only [T]
        unfold ccmGuinandWeilThirdGradeCesaroTriangularWeight
          ccmGuinandWeilThirdGradeWeight
        ring
      rw [hTeq, abs_of_nonneg (mul_nonneg h32 hfac0)]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hfac1 h32
    have hR0 : 0 ≤ R := by
      dsimp only [R]
      have : 1 / H ≤ 1 / c := one_div_le_one_div_of_le hc hcH.le
      positivity
    have hR : |R| ≤ 64 / c := by
      rw [abs_of_nonneg hR0]
      dsimp only [R]
      have hInvH : 0 ≤ 1 / H := by positivity
      calc
        64 * (1 / c - 1 / H) ≤ 64 * (1 / c) := by nlinarith
        _ = 64 / c := by ring
    have hTD : |T * D| ≤ (32 / c ^ 3) * |D| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hT (abs_nonneg D)
    have hRJ : |R * J| ≤ (64 / c) * |J| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hR (abs_nonneg J)
    have hEq : ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H =
        A + ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment c H + T * D + R * J := by
      dsimp only [A, T, D, R, J] at htransport ⊢
      exact htransport
    rw [hEq]
    have h1 := abs_add_le
      (A + ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment c H + T * D) (R * J)
    have h2 := abs_add_le
      (A + ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment c H) (T * D)
    have h3 := abs_add_le A
      (ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment c H)
    apply le_trans (show
      |A + ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment c H + T * D + R * J| ≤
        TAIL by
          dsimp only [TAIL]
          linarith) (le_max_left _ _)

/-- **Lower-wall invariance of the CCM-FU hard core.** Uniform boundedness of the literal signed
anchored moment is independent of which positive source wall is fixed. No asymptotic premise and
no prime/polar separation is used. -/
theorem ccmGuinandWeilThirdGradeCesaroAnchoredMomentBound_iff
    {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    CCMGuinandWeilThirdGradeCesaroAnchoredMomentBound b ↔
      CCMGuinandWeilThirdGradeCesaroAnchoredMomentBound c := by
  rcases le_total b c with hbc | hcb
  · exact ⟨ccmGuinandWeilThirdGradeCesaroAnchoredMomentBound_of_le hb hbc,
      ccmGuinandWeilThirdGradeCesaroAnchoredMomentBound_lower_of_le hb hbc⟩
  · exact ⟨ccmGuinandWeilThirdGradeCesaroAnchoredMomentBound_lower_of_le hc hcb,
      ccmGuinandWeilThirdGradeCesaroAnchoredMomentBound_of_le hc hcb⟩

/-- Eventual uniform boundedness of the anchored signed completed-error moment. -/
def CCMGuinandWeilThirdGradeCesaroAnchoredMomentTailBound (b : ℝ) : Prop :=
  ∃ U C : ℝ, b < U ∧ 0 ≤ C ∧ ∀ H : ℝ, U ≤ H →
    |ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H| ≤ C

/-- Finite upper-wall intervals are elementary, so only an eventual tail bound is needed. -/
theorem ccmGuinandWeilThirdGradeCesaroAnchoredMomentBound_iff_tailBound
    {b : ℝ} (hb : 0 < b) :
    CCMGuinandWeilThirdGradeCesaroAnchoredMomentBound b ↔
      CCMGuinandWeilThirdGradeCesaroAnchoredMomentTailBound b := by
  constructor
  · rintro ⟨C, hC, hbound⟩
    refine ⟨b + 1, C, by linarith, hC, ?_⟩
    intro H hH
    exact hbound H (lt_of_lt_of_le (by linarith) hH)
  · rintro ⟨U, C, hbU, hC, htail⟩
    let B : ℝ :=
      (96 / b ^ 4) *
        (|criticalMellinCompletedError b| + 23 * Real.exp (U / 2)) * (U - b)
    refine ⟨max C B, hC.trans (le_max_left _ _), ?_⟩
    intro H hbH
    rcases le_total H U with hHU | hUH
    · exact
        (abs_ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment_le_of_mem
          hb hbH.le hHU).trans (le_max_right _ _)
    · exact (htail H hUH).trans (le_max_left _ _)

/-- The eventual-tail burden is independent of the chosen positive anchor. -/
theorem ccmGuinandWeilThirdGradeCesaroAnchoredMomentTailBound_iff
    {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    CCMGuinandWeilThirdGradeCesaroAnchoredMomentTailBound b ↔
      CCMGuinandWeilThirdGradeCesaroAnchoredMomentTailBound c :=
  (ccmGuinandWeilThirdGradeCesaroAnchoredMomentBound_iff_tailBound hb).symm.trans
    ((ccmGuinandWeilThirdGradeCesaroAnchoredMomentBound_iff hb hc).trans
      (ccmGuinandWeilThirdGradeCesaroAnchoredMomentBound_iff_tailBound hc))

/-- Eventual boundedness of one anchored prime--polar tail suffices for RH. -/
theorem riemannHypothesis_of_ccmGuinandWeilThirdGradeCesaroAnchoredMomentTailBound
    {b : ℝ} (hb : 0 < b)
    (htail : CCMGuinandWeilThirdGradeCesaroAnchoredMomentTailBound b) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_ccmGuinandWeilThirdGradeCesaroAnchoredMomentBound hb
  exact
    (ccmGuinandWeilThirdGradeCesaroAnchoredMomentBound_iff_tailBound hb).2 htail

end GaloisForLFunctions.RHTower
