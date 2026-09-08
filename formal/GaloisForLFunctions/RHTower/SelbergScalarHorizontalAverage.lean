import GaloisForLFunctions.RHTower.SelbergMaassTraceEnergy

/-!
# Actual real horizontal averages and their derivatives

Real averages reuse the established complex finite-integral differentiation theorem
through the real-to-complex inclusion. C² regularity and actual period-one symmetry
identify the vertical-current derivative with the mean planar Laplacian. All
regularity and periodicity inputs remain explicit for source verification.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergScalarHorizontalAverage
open SelbergMaassMean SelbergMaassTraceEnergy
noncomputable section

/-- Literal real horizontal average on the unit interval. -/
def average (F : ℂ → ℝ) (y : ℝ) : ℝ := ∫ x in Ioc (0 : ℝ) 1, F (point x y)

/-- The unit average is the usual positively oriented interval integral. -/
theorem average_eq_interval (F : ℂ → ℝ) (y : ℝ) :
    average F y = ∫ x in (0 : ℝ)..1, F (point x y) := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rfl

/-- Real directional differentiation commutes with the literal complex inclusion. -/
theorem directional_ofReal {F : ℂ → ℝ} {z : ℂ} (hF : DifferentiableAt ℝ F z) (v : ℂ) :
    directional v (fun w => (F w : ℂ)) z = ((dir v F z : ℝ) : ℂ) := by
  have h := congrArg (fun L => L v) (Complex.ofRealCLM.hasFDerivAt.comp z hF.hasFDerivAt).fderiv
  exact h

/-- Continuous scalar chart functions have continuous horizontal slices. -/
theorem slice_continuous {F : ℂ → ℝ} (hF : ContinuousOn F {z : ℂ | 0 < z.im})
    {y : ℝ} (hy : 0 < y) : Continuous (fun x => F (point x y)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hp : 0 < (point x y).im := by simpa [point] using hy
  exact (hF.continuousAt (isOpen_upperHalfPlaneSet.mem_nhds hp)).comp
    (f := fun t : ℝ => point t y) (point_horizontal x y).continuousAt

/-- C¹ real chart regularity gives the actual derivative of the horizontal mean. -/
theorem average_hasDerivAt {F : ℂ → ℝ} (hF : ContDiffOn ℝ 1 F {z : ℂ | 0 < z.im})
    {y : ℝ} (hy : 0 < y) : HasDerivAt (average F) (average (dir Complex.I F) y) y := by
  let G : ℂ → ℂ := fun z => (F z : ℂ)
  have hG : ContDiffOn ℝ 1 G {z : ℂ | 0 < z.im} :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hF
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt y (periodIntegral_hasDerivAt 1 hG hy)
  have he : (fun t => (periodIntegral 1 G t).re) = average F := by
    funext t
    simp only [periodIntegral, G, integral_complex_ofReal, Complex.ofReal_re, average]
  change HasDerivAt (fun t => (periodIntegral 1 G t).re)
    (periodIntegral 1 (directional Complex.I G) y).re y at h
  rw [he] at h
  have hd (x : ℝ) : directional Complex.I G (point x y) = ((dir Complex.I F (point x y) : ℝ) : ℂ) := by
    have hp : 0 < (point x y).im := by simpa [point] using hy
    exact directional_ofReal ((hF.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds hp)).differentiableAt (by simp)) _
  have hv : (periodIntegral 1 (directional Complex.I G) y).re = average (dir Complex.I F) y := by
    unfold periodIntegral average
    simp_rw [hd]
    rw [integral_complex_ofReal, Complex.ofReal_re]
  rwa [hv] at h

/-- C² regularity identifies the actual derivative of the mean's vertical-current average. -/
theorem average_current_hasDerivAt {F : ℂ → ℝ} (hF : ContDiffOn ℝ 2 F {z : ℂ | 0 < z.im})
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (average (dir Complex.I F)) (average (dir Complex.I (dir Complex.I F)) y) y :=
  average_hasDerivAt (dir_contDiffOn hF (by norm_num) Complex.I) hy

/-- Actual scalar horizontal derivatives inherit period one from the source. -/
theorem dir_horizontal_periodic {F : ℂ → ℝ} (hF : ContDiffOn ℝ 1 F {z : ℂ | 0 < z.im})
    {y : ℝ} (hy : 0 < y) (hp : Function.Periodic (fun x => F (point x y)) 1) :
    Function.Periodic (fun x => dir 1 F (point x y)) 1 := by
  have hd (x : ℝ) : HasDerivAt (fun t => F (point t y)) (dir 1 F (point x y)) x := by
    have hx : 0 < (point x y).im := by simpa [point] using hy
    exact ((hF.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt x (point_horizontal x y)
  intro x
  have h1 := (hd (x + 1)).scomp x ((hasDerivAt_id x).add_const 1)
  have he : (fun t => F (point (t + 1) y)) = (fun t => F (point t y)) := funext hp
  have h1' : HasDerivAt (fun t => F (point t y)) (dir 1 F (point (x + 1) y)) x := by
    simpa only [Function.comp_def, id_eq, one_smul, he] using h1
  exact h1'.unique (hd x)

/-- Periodicity cancels the literal horizontal second derivative in the real mean. -/
theorem average_horizontal_second_eq_zero {F : ℂ → ℝ} (hF : ContDiffOn ℝ 2 F {z : ℂ | 0 < z.im})
    {y : ℝ} (hy : 0 < y) (hp : Function.Periodic (fun x => F (point x y)) 1) :
    average (dir 1 (dir 1 F)) y = 0 := by
  have hd := dir_contDiffOn hF (m := 1) (by norm_num) (1 : ℂ)
  have hdd := dir_contDiffOn hd (m := 0) (by norm_num) (1 : ℂ)
  rw [average_eq_interval]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
    (fun x _ => by
      have hx : 0 < (point x y).im := by simpa [point] using hy
      exact ((hd.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt x (point_horizontal x y))
    ((slice_continuous hdd.continuousOn hy).intervalIntegrable _ _)
  rw [h]
  have hper := dir_horizontal_periodic (hF.of_le (by simp)) hy hp 0
  simpa only [zero_add, Function.comp_apply] using sub_eq_zero.mpr hper

/-- The scalar mean's vertical curvature is the actual mean of its planar Laplacian. -/
theorem average_vertical_second_eq_laplacian {F : ℂ → ℝ} (hF : ContDiffOn ℝ 2 F {z : ℂ | 0 < z.im})
    {y : ℝ} (hy : 0 < y) (hp : Function.Periodic (fun x => F (point x y)) 1) :
    average (dir Complex.I (dir Complex.I F)) y = average (realLaplacian F) y := by
  have hi (v : ℂ) : IntegrableOn (fun x => dir v (dir v F) (point x y)) (Ioc (0 : ℝ) 1) :=
    ((slice_continuous (dir_contDiffOn (dir_contDiffOn hF (m := 1) (by norm_num) v)
      (m := 0) (by norm_num) v).continuousOn hy).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  unfold average realLaplacian
  rw [integral_add (hi 1) (hi Complex.I)]
  change _ = average (dir 1 (dir 1 F)) y + _
  rw [average_horizontal_second_eq_zero hF hy hp, zero_add]

end
end GaloisForLFunctions.RHTower.SelbergScalarHorizontalAverage
