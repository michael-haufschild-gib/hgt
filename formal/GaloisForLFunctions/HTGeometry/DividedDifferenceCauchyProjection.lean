import GaloisForLFunctions.HTGeometry.EntireDividedDifferenceContour
import GaloisForLFunctions.HTGeometry.RectangleBorelLaplaceInversion

/-! # Cauchy laws for the entire divisor projector

The same entire function equals `F - f * H` inside a contour and `-f * H`
outside it. Here `H` is holomorphic off the contour. Consequently full divisor
germs are selected as groups, without any simple-zero assumption.
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped Interval

namespace HTGeometry
noncomputable section

def rectangleCauchyTransform (A : ℂ → ℂ) (a b z : ℂ) : ℂ :=
  RectangleIntegral' (fun w => A w / (w-z)) a b

private theorem differentiableAt_intervalIntegral_cauchy
    {A γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hA : ContinuousOn A (Icc a b)) (hγ : ContinuousOn γ (Icc a b))
    {z₀ : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ t ∈ Icc a b, δ ≤ ‖γ t-z₀‖) :
    DifferentiableAt ℂ (fun z => ∫ t in a..b, A t / (γ t-z)) z₀ := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  have hdist : ∀ t ∈ Icc a b, ∀ z ∈ ball z₀ (δ/2), δ/2 ≤ ‖γ t-z‖ := by
    intro t ht z hz
    have hz' : ‖z-z₀‖ < δ/2 := by simpa only [mem_ball, dist_eq_norm] using hz
    have hn := norm_add_le (γ t-z) (z-z₀)
    have he : γ t-z+(z-z₀) = γ t-z₀ := by abel
    rw [he] at hn
    have := hsep t ht
    linarith
  have hnz : ∀ t ∈ Icc a b, ∀ z ∈ ball z₀ (δ/2), γ t-z ≠ 0 := by
    intro t ht z hz
    exact norm_pos_iff.mp (lt_of_lt_of_le (by positivity : 0 < δ/2) (hdist t ht z hz))
  refine differentiableAt_intervalIntegral_of_bound hab (by positivity : 0 < δ/2)
    (C := |M|/(δ/2)) ?_ ?_ ?_
  · intro z hz
    exact hA.div (hγ.sub continuousOn_const) (fun t ht => hnz t ht z hz)
  · intro t ht
    exact (differentiableOn_const (c := A t)).div
      ((differentiableOn_const (c := γ t)).sub differentiableOn_id)
      (fun z hz => hnz t ht z hz)
  · intro t ht z hz
    rw [norm_div]
    exact div_le_div₀ (abs_nonneg _) ((hM t ht).trans (le_abs_self _))
      (by positivity) (hdist t ht z hz)

/-- The Cauchy coefficient is holomorphic at every point off the contour. -/
theorem differentiableAt_rectangleCauchyTransform
    {A : ℂ → ℂ} {a b z : ℂ} (hab : a.re ≤ b.re) (hab' : a.im ≤ b.im)
    (hA : ContinuousOn A (RectangleBorder a b)) (hz : z ∉ RectangleBorder a b) :
    DifferentiableAt ℂ (rectangleCauchyTransform A a b) z := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp
    (GaloisForLFunctions.HTGeometry.isCompact_rectangleBorder a b).isClosed.isOpen_compl z hz
  have hsep : ∀ w ∈ RectangleBorder a b, δ ≤ ‖w-z‖ := by
    intro w hw
    by_contra hn
    exact hball (by simpa only [mem_ball, dist_eq_norm] using lt_of_not_ge hn) hw
  have hbottom : MapsTo (fun t : ℝ => (t : ℂ) + a.im * I)
      (Icc a.re b.re) (RectangleBorder a b) := by
    simpa only [uIcc_of_le hab] using mapsTo_rectangleBorder_left_im a b
  have htop : MapsTo (fun t : ℝ => (t : ℂ) + b.im * I)
      (Icc a.re b.re) (RectangleBorder a b) := by
    simpa only [uIcc_of_le hab] using mapsTo_rectangleBorder_right_im a b
  have hleft : MapsTo (fun t : ℝ => (a.re : ℂ) + t * I)
      (Icc a.im b.im) (RectangleBorder a b) := by
    simpa only [uIcc_of_le hab'] using mapsTo_rectangleBorder_left_re a b
  have hright : MapsTo (fun t : ℝ => (b.re : ℂ) + t * I)
      (Icc a.im b.im) (RectangleBorder a b) := by
    simpa only [uIcc_of_le hab'] using mapsTo_rectangleBorder_right_re a b
  have hB := differentiableAt_intervalIntegral_cauchy
    (γ := fun t : ℝ => (t : ℂ) + a.im * I)
    (A := fun t : ℝ => A ((t : ℂ) + a.im * I)) hab
    (hA.comp (by fun_prop) hbottom) (by fun_prop) hδ (fun t ht => hsep _ (hbottom ht))
  have hT := differentiableAt_intervalIntegral_cauchy
    (γ := fun t : ℝ => (t : ℂ) + b.im * I)
    (A := fun t : ℝ => A ((t : ℂ) + b.im * I)) hab
    (hA.comp (by fun_prop) htop) (by fun_prop) hδ (fun t ht => hsep _ (htop ht))
  have hL := differentiableAt_intervalIntegral_cauchy
    (γ := fun t : ℝ => (a.re : ℂ) + t * I)
    (A := fun t : ℝ => A ((a.re : ℂ) + t * I)) hab'
    (hA.comp (by fun_prop) hleft) (by fun_prop) hδ (fun t ht => hsep _ (hleft ht))
  have hR := differentiableAt_intervalIntegral_cauchy
    (γ := fun t : ℝ => (b.re : ℂ) + t * I)
    (A := fun t : ℝ => A ((b.re : ℂ) + t * I)) hab'
    (hA.comp (by fun_prop) hright) (by fun_prop) hδ (fun t ht => hsep _ (hright ht))
  exact ((hB.sub hT).add (hR.const_mul I) |>.sub (hL.const_mul I)).const_mul _

theorem rectangleIntegral'_const_mul (c : ℂ) (F : ℂ → ℂ) (a b : ℂ) :
    RectangleIntegral' (fun w => c * F w) a b = c * RectangleIntegral' F a b := by
  simp only [RectangleIntegral', rectangleIntegral_const_mul, smul_eq_mul]
  ring

theorem rectangleIntegral'_sub {F G : ℂ → ℂ} {a b : ℂ}
    (hF : RectangleBorderIntegrable F a b) (hG : RectangleBorderIntegrable G a b) :
    RectangleIntegral' (fun w => F w-G w) a b =
      RectangleIntegral' F a b-RectangleIntegral' G a b := by
  dsimp [RectangleIntegral', RectangleIntegral, HIntegral, VIntegral]
  rw [intervalIntegral.integral_sub hF.1 hG.1,
    intervalIntegral.integral_sub hF.2.1 hG.2.1,
    intervalIntegral.integral_sub hF.2.2.1 hG.2.2.1,
    intervalIntegral.integral_sub hF.2.2.2 hG.2.2.2]
  ring

/-- Algebraic decomposition off the integration contour. -/
theorem entireDividedDifferenceContour_eq_cauchy_sub
    {f F : ℂ → ℂ} {a b z : ℂ}
    (hf : ContinuousOn f (RectangleBorder a b))
    (hF : ContinuousOn F (RectangleBorder a b))
    (hnz : ∀ w ∈ RectangleBorder a b, f w ≠ 0) (hz : z ∉ RectangleBorder a b) :
    entireDividedDifferenceContour f (fun w => F w/f w) a b z =
      rectangleCauchyTransform F a b z -
        f z * rectangleCauchyTransform (fun w => F w/f w) a b z := by
  have hwz : ∀ w ∈ RectangleBorder a b, w-z ≠ 0 := by
    intro w hw
    exact sub_ne_zero.mpr (fun h => hz (h ▸ hw))
  have hD : ContinuousOn (fun w => F w/(w-z)) (RectangleBorder a b) :=
    hF.div (continuousOn_id.sub continuousOn_const) hwz
  have hE : ContinuousOn (fun w => f z*(F w/f w/(w-z))) (RectangleBorder a b) :=
    continuousOn_const.mul ((hF.div hf hnz).div
      (continuousOn_id.sub continuousOn_const) hwz)
  unfold entireDividedDifferenceContour
  calc
    RectangleIntegral' (fun w => F w/f w*dslope f w z) a b =
        RectangleIntegral' (fun w => F w/(w-z)-f z*(F w/f w/(w-z))) a b := by
      apply RectangleIntegral'_congr
      intro w hw
      dsimp only
      rw [dslope_symm, dslope_of_ne _ (sub_ne_zero.mp (hwz w hw)), slope_def_field]
      field_simp [hnz w hw, hwz w hw]
    _ = _ := by
      rw [rectangleIntegral'_sub hD.rectangleBorder_integrable hE.rectangleBorder_integrable,
        rectangleIntegral'_const_mul]
      rfl

theorem entireDividedDifferenceContour_inside
    {f F : ℂ → ℂ} {a b z : ℂ} (hF : Differentiable ℂ F)
    (hf : ContinuousOn f (RectangleBorder a b))
    (hnz : ∀ w ∈ RectangleBorder a b, f w ≠ 0)
    (hab : a.re ≤ b.re) (hab' : a.im ≤ b.im) (hz : Rectangle a b ∈ 𝓝 z) :
    entireDividedDifferenceContour f (fun w => F w/f w) a b z =
      F z-f z*rectangleCauchyTransform (fun w => F w/f w) a b z := by
  rw [entireDividedDifferenceContour_eq_cauchy_sub hf hF.continuous.continuousOn hnz
    (not_mem_rectangleBorder_of_rectangle_mem_nhds hz)]
  rw [rectangleCauchyTransform, rectangleIntegral'_div_sub_eq (subset_univ _)
    hF.differentiableOn hab hab' hz]

theorem entireDividedDifferenceContour_outside
    {f F : ℂ → ℂ} {a b z : ℂ} (hF : Differentiable ℂ F)
    (hf : ContinuousOn f (RectangleBorder a b))
    (hnz : ∀ w ∈ RectangleBorder a b, f w ≠ 0) (hz : z ∉ Rectangle a b) :
    entireDividedDifferenceContour f (fun w => F w/f w) a b z =
      -f z*rectangleCauchyTransform (fun w => F w/f w) a b z := by
  rw [entireDividedDifferenceContour_eq_cauchy_sub hf hF.continuous.continuousOn hnz
    (fun h => hz (rectangleBorder_subset_rectangle a b h))]
  have hzero : rectangleCauchyTransform F a b z = 0 := by
    unfold rectangleCauchyTransform RectangleIntegral'
    rw [rectangleIntegral_div_sub_eq_zero (subset_univ _) hF.differentiableOn hz, smul_zero]
  rw [hzero, zero_sub, neg_mul]

end
end HTGeometry
