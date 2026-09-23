import GaloisForLFunctions.HTGeometry.CompactProjectiveSeparationAtlas
import Mathlib.Analysis.Calculus.MeanValue

namespace GaloisForLFunctions.HTGeometry

open Complex Metric

noncomputable section

/-- Numerator of the derivative of the affine projective parameter `-D/C`. -/
def projectiveDerivativeNumerator (C D : ℂ → ℂ) (z : ℂ) : ℂ :=
  D z * deriv C z - deriv D z * C z

/-- The projective derivative numerator of two entire functions is entire. -/
theorem projectiveDerivativeNumerator_differentiable
    {C D : ℂ → ℂ} (hC : Differentiable ℂ C) (hD : Differentiable ℂ D) :
    Differentiable ℂ (projectiveDerivativeNumerator C D) := by
  have hCan : AnalyticOnNhd ℂ C Set.univ :=
    hC.differentiableOn.analyticOnNhd isOpen_univ
  have hDan : AnalyticOnNhd ℂ D Set.univ :=
    hD.differentiableOn.analyticOnNhd isOpen_univ
  have hCd : Differentiable ℂ (deriv C) := by
    rw [← differentiableOn_univ]
    exact hCan.deriv.differentiableOn
  have hDd : Differentiable ℂ (deriv D) := by
    rw [← differentiableOn_univ]
    exact hDan.deriv.differentiableOn
  unfold projectiveDerivativeNumerator
  exact (hD.mul hCd).sub (hDd.mul hC)

/-- At a regular denominator point, `q'` is the projective derivative numerator divided by `C²`. -/
theorem deriv_neg_div_eq_projectiveDerivativeNumerator_div_sq
    {C D : ℂ → ℂ} (hC : Differentiable ℂ C) (hD : Differentiable ℂ D)
    {z : ℂ} (hCz : C z ≠ 0) :
    deriv (fun w => -D w / C w) z =
      projectiveDerivativeNumerator C D z / C z ^ (2 : ℕ) := by
  have hneg : HasDerivAt (fun w => -D w) (-deriv D z) z :=
    (hD z).hasDerivAt.neg
  have hdiv := hneg.div (hC z).hasDerivAt hCz
  change deriv (((fun w => -D w) / C)) z = _
  rw [hdiv.deriv]
  unfold projectiveDerivativeNumerator
  ring

/-- **Nonconstant projective row law.** If `C,D` are entire, have no common zero, and `C` has both
a zero and a nonzero value, then the derivative numerator of `-D/C` is not identically zero. -/
theorem projectiveDerivativeNumerator_ne_zero
    {C D : ℂ → ℂ} (hC : Differentiable ℂ C) (hD : Differentiable ℂ D)
    (hnoCommon : ∀ z, ¬ (C z = 0 ∧ D z = 0))
    {p c : ℂ} (hCp : C p = 0) (hCc : C c ≠ 0) :
    projectiveDerivativeNumerator C D ≠ 0 := by
  intro hW
  have hopen : IsOpen {z : ℂ | C z ≠ 0} :=
    hC.continuous.isOpen_preimage {w : ℂ | w ≠ 0} isOpen_ne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen c hCc
  let q : ℂ → ℂ := fun z => -D z / C z
  have hqdiff : DifferentiableOn ℂ q (ball c r) := by
    apply DifferentiableOn.div hD.neg.differentiableOn hC.differentiableOn
    intro z hz
    exact hball hz
  have hqderiv : (ball c r).EqOn (deriv q) 0 := by
    intro z hz
    rw [deriv_neg_div_eq_projectiveDerivativeNumerator_div_sq hC hD (hball hz)]
    have hWz : projectiveDerivativeNumerator C D z = 0 := by
      simpa using congrFun hW z
    rw [hWz, zero_div]
    rfl
  have hqconst : ∀ z ∈ ball c r, q z = q c := by
    intro z hz
    exact isOpen_ball.is_const_of_deriv_eq_zero
      (convex_ball c r).isPreconnected hqdiff hqderiv hz (mem_ball_self hr)
  let F : ℂ → ℂ := fun z => D z * C c - D c * C z
  have hFdiff : Differentiable ℂ F := by
    dsimp [F]
    fun_prop
  have hFzeroBall : ∀ z ∈ ball c r, F z = 0 := by
    intro z hz
    have hqeq := hqconst z hz
    have hcross := (div_eq_div_iff (hball hz) hCc).mp hqeq
    dsimp [F]
    rw [sub_eq_zero]
    simpa only [neg_mul, neg_inj] using hcross
  have hFevent : F =ᶠ[nhds c] 0 := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
    exact hFzeroBall z hz
  have hFan : AnalyticOnNhd ℂ F Set.univ :=
    hFdiff.differentiableOn.analyticOnNhd isOpen_univ
  have hzeroAn : AnalyticOnNhd ℂ (0 : ℂ → ℂ) Set.univ :=
    differentiable_zero.differentiableOn.analyticOnNhd isOpen_univ
  have hFzero : F = 0 := hFan.eq_of_eventuallyEq hzeroAn hFevent
  have hFp := congrFun hFzero p
  have hDp : D p ≠ 0 := by
    intro h
    exact hnoCommon p ⟨hCp, h⟩
  dsimp [F] at hFp
  rw [hCp, mul_zero, sub_zero] at hFp
  exact hDp (mul_eq_zero.mp hFp |>.resolve_right hCc)

/-- Regular points with nonzero projective derivative numerator are precisely regular points where
`q=-D/C` has nonzero derivative. -/
theorem deriv_neg_div_ne_zero_of_projectiveDerivativeNumerator_ne_zero
    {C D : ℂ → ℂ} (hC : Differentiable ℂ C) (hD : Differentiable ℂ D)
    {z : ℂ} (hCz : C z ≠ 0) (hWz : projectiveDerivativeNumerator C D z ≠ 0) :
    deriv (fun w => -D w / C w) z ≠ 0 := by
  rw [deriv_neg_div_eq_projectiveDerivativeNumerator_div_sq hC hD hCz]
  exact div_ne_zero hWz (pow_ne_zero 2 hCz)

end
end GaloisForLFunctions.HTGeometry
