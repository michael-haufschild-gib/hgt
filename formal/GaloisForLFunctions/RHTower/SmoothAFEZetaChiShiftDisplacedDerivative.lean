import GaloisForLFunctions.RHTower.SmoothAFEZetaChiUniformMovingRightLine
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiShiftDerivative

/-!
# Height derivative of displaced chi ratios

Quotient-rule and logarithmic-derivative identities for the exact shifted
chi ratio based at `1/2-d+iτ`, specialized to the negative contour used by
the conductor-localized dual weight.
-/

noncomputable section

namespace RHTower

open Complex Filter

theorem hasDerivAt_displacedLinePt (d τ : ℝ) :
    HasDerivAt (displacedLinePt d) I τ := by
  exact ((hasDerivAt_linePt τ).sub_const (d : ℂ)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun u => by
      unfold displacedLinePt linePt
      push_cast
      ring)

theorem hasDerivAt_smoothAFEZetaChiShiftRatio_displaced
    {d τ : ℝ} {w : ℂ}
    (hd : 0 < d) (hdhalf : d < 1 / 2)
    (hnum : Gammaℝ (1 - (displacedLinePt d τ + w)) ≠ 0) :
    HasDerivAt
      (fun u : ℝ => smoothAFEZetaChiShiftRatio (displacedLinePt d u) w)
      (((deriv zetaChi (displacedLinePt d τ + w) * I) *
          zetaChi (displacedLinePt d τ) -
        zetaChi (displacedLinePt d τ + w) *
          (deriv zetaChi (displacedLinePt d τ) * I)) /
        zetaChi (displacedLinePt d τ) ^ (2 : ℕ)) τ := by
  have hn := ((zetaChi_analyticAt hnum).differentiableAt.hasDerivAt.comp τ
    ((hasDerivAt_displacedLinePt d τ).add_const w))
  have hbaseGamma : Gammaℝ (1 - displacedLinePt d τ) ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos
    simp [displacedLinePt]
    linarith
  have hden := ((zetaChi_analyticAt hbaseGamma).differentiableAt.hasDerivAt.comp τ
    (hasDerivAt_displacedLinePt d τ))
  have hbase0 : zetaChi (displacedLinePt d τ) ≠ 0 :=
    zetaChi_ne_zero_of_mem_openStrip
      (displacedLinePt_mem_openStrip hd hdhalf τ).1
      (displacedLinePt_mem_openStrip hd hdhalf τ).2
  unfold smoothAFEZetaChiShiftRatio
  exact (hn.div hden hbase0).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)

theorem hasDerivAt_smoothAFEZetaChiShiftRatio_displaced_logDeriv
    {d τ : ℝ} {w : ℂ}
    (hd : 0 < d) (hdhalf : d < 1 / 2)
    (hnumA : Gammaℝ (1 - (displacedLinePt d τ + w)) ≠ 0)
    (hnum0 : zetaChi (displacedLinePt d τ + w) ≠ 0) :
    HasDerivAt
      (fun u : ℝ => smoothAFEZetaChiShiftRatio (displacedLinePt d u) w)
      (I * smoothAFEZetaChiShiftRatio (displacedLinePt d τ) w *
        (logDeriv zetaChi (displacedLinePt d τ + w) -
          logDeriv zetaChi (displacedLinePt d τ))) τ := by
  have hraw := hasDerivAt_smoothAFEZetaChiShiftRatio_displaced
    hd hdhalf hnumA
  convert hraw using 1
  unfold smoothAFEZetaChiShiftRatio
  rw [logDeriv_apply, logDeriv_apply]
  have hbase0 : zetaChi (displacedLinePt d τ) ≠ 0 :=
    zetaChi_ne_zero_of_mem_openStrip
      (displacedLinePt_mem_openStrip hd hdhalf τ).1
      (displacedLinePt_mem_openStrip hd hdhalf τ).2
  field_simp [hnum0, hbase0]

/-- Exact height derivative on the displaced negative contour
`Re w = -(d+η)`. -/
theorem hasDerivAt_smoothAFEZetaChiShiftRatio_displaced_neg
    {d η : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (hη : 0 < η) (hηhalf : η < 1 / 2) (τ v : ℝ) :
    HasDerivAt
      (fun u : ℝ => smoothAFEZetaChiShiftRatio (displacedLinePt d u)
        (-(((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I)))
      (I * smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
          (-(((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I)) *
        (logDeriv zetaChi
            (displacedLinePt d τ -
              (((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I)) -
          logDeriv zetaChi (displacedLinePt d τ))) τ := by
  let z : ℂ := displacedLinePt d τ -
    (((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I)
  have hz : z = (((1 / 2 + η : ℝ) : ℂ) + ((τ - v : ℝ) : ℂ) * I) := by
    dsimp only [z]
    unfold displacedLinePt
    push_cast
    ring
  have hnumA : Gammaℝ (1 - z) ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos
    rw [hz]
    simp
    linarith
  have hnum0 : zetaChi z ≠ 0 := by
    apply zetaChi_ne_zero_of_mem_openStrip
    · rw [hz]
      simp
      linarith
    · rw [hz]
      simp
      linarith
  have hbase := hasDerivAt_smoothAFEZetaChiShiftRatio_displaced_logDeriv
    hd hdhalf (w := -(((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I))
    (by simpa [z, sub_eq_add_neg] using hnumA)
    (by simpa [z, sub_eq_add_neg] using hnum0)
  simpa only [sub_eq_add_neg] using hbase

end RHTower
