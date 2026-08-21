import GaloisForLFunctions.RHTower.CCMGuinandWeilThirdGradeRectangularMixture
import GaloisForLFunctions.RHTower.IntervalAutocorrelation

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- Positive-lag autocorrelation of a rectangular interval head. -/
def ccmPositiveLagRectangularTriangle (T h : ℝ) : ℝ := max 0 (T - h)

theorem ccmPositiveLagRectangularTriangle_eq_intervalAutocorrelation
    {T h : ℝ} (hh : 0 ≤ h) :
    ccmPositiveLagRectangularTriangle T h =
      ∫ x : ℝ, (Set.Icc (0 : ℝ) T).indicator (fun _ => (1 : ℝ)) (x + h) *
        (Set.Icc (0 : ℝ) T).indicator (fun _ => (1 : ℝ)) x := by
  rw [_root_.RHTower.integral_indicator_Icc_shift_mul]
  simp [ccmPositiveLagRectangularTriangle, abs_of_nonneg hh, max_comm]

/-- Fixed marked-aperture mixture: rectangular heads are assembled before scalar readout. -/
def ccmThirdGradeCesaroFixedRectangularMixture (b H h : ℝ) : ℝ :=
  (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t *
      ccmPositiveLagRectangularTriangle t h) +
    (32 / H ^ 4) * ccmPositiveLagRectangularTriangle H h

private theorem continuousOn_rectangularMixDensity_mul_triangle
    {b H h : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    ContinuousOn (fun t => ccmThirdGradeCesaroRectangularMixDensity H t *
      ccmPositiveLagRectangularTriangle t h) (Set.Icc b H) := by
  have hH : 0 < H := hb.trans_le hbH
  intro t ht
  have ht0 : t ≠ 0 := ne_of_gt (hb.trans_le ht.1)
  have hdensity : ContinuousAt (ccmThirdGradeCesaroRectangularMixDensity H) t := by
    unfold ccmThirdGradeCesaroRectangularMixDensity
    exact (continuousAt_const.mul (continuousAt_const.sub continuousAt_id)).div
      (continuousAt_const.mul (continuousAt_id.pow 5))
      (mul_ne_zero hH.ne' (pow_ne_zero 5 ht0))
  have htriangle : ContinuousAt (fun t => ccmPositiveLagRectangularTriangle t h) t := by
    unfold ccmPositiveLagRectangularTriangle
    fun_prop
  exact (hdensity.mul htriangle).continuousWithinAt

/-- On the physical window, the fixed marked mixture reduces to the moving-lower-tail formula. -/
theorem ccmThirdGradeCesaroFixedRectangularMixture_eq_tail
    {b H h : ℝ} (hb : 0 < b) (hbh : b ≤ h) (hhH : h ≤ H) :
    ccmThirdGradeCesaroFixedRectangularMixture b H h =
      (∫ t in h..H, ccmThirdGradeCesaroRectangularMixDensity H t * (t - h)) +
        (32 / H ^ 4) * (H - h) := by
  have hbH : b ≤ H := hbh.trans hhH
  let F : ℝ → ℝ := fun t => ccmThirdGradeCesaroRectangularMixDensity H t *
    ccmPositiveLagRectangularTriangle t h
  have hcont := continuousOn_rectangularMixDensity_mul_triangle (h := h) hb hbH
  have hleft : IntervalIntegrable F volume b h :=
    (hcont.mono (by
      intro t ht
      rw [Set.uIcc_of_le hbh] at ht
      exact ⟨ht.1, ht.2.trans hhH⟩)).intervalIntegrable
  have hright : IntervalIntegrable F volume h H :=
    (hcont.mono (by
      intro t ht
      rw [Set.uIcc_of_le hhH] at ht
      exact ⟨hbh.trans ht.1, ht.2⟩)).intervalIntegrable
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hleft hright
  have hzero : (∫ t in b..h, F t) = 0 := by
    calc
      (∫ t in b..h, F t) = ∫ _t in b..h, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hbh] at ht
        dsimp only [F]
        rw [show ccmPositiveLagRectangularTriangle t h = 0 by
          simp [ccmPositiveLagRectangularTriangle, sub_nonpos.mpr ht.2]]
        ring
      _ = 0 := by simp
  have htail : (∫ t in h..H, F t) =
      ∫ t in h..H, ccmThirdGradeCesaroRectangularMixDensity H t * (t - h) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hhH] at ht
    dsimp only [F]
    rw [show ccmPositiveLagRectangularTriangle t h = t - h by
      simp [ccmPositiveLagRectangularTriangle, sub_nonneg.mpr ht.1]]
  rw [ccmThirdGradeCesaroFixedRectangularMixture]
  change (∫ t in b..H, F t) + _ = _
  rw [← hsplit, hzero, zero_add, htail]
  rw [show ccmPositiveLagRectangularTriangle H h = H - h by
    simp [ccmPositiveLagRectangularTriangle, sub_nonneg.mpr hhH]]

/-- Literal third-grade reporter is one positive marked direct mixture of rectangular
autocorrelations; no spectral factor or reporter surrogate is needed. -/
theorem ccmGuinandWeilThirdGradeCesaroTriangularWeight_eq_fixedRectangularMixture
    {b H h : ℝ} (hb : 0 < b) (hbh : b ≤ h) (hhH : h ≤ H) :
    ccmGuinandWeilThirdGradeCesaroTriangularWeight H h =
      ccmThirdGradeCesaroFixedRectangularMixture b H h := by
  rw [ccmThirdGradeCesaroFixedRectangularMixture_eq_tail hb hbh hhH]
  exact ccmGuinandWeilThirdGradeCesaroTriangularWeight_eq_rectangularMixture
    (hb.trans_le hbh) hhH

end GaloisForLFunctions.RHTower
