import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-!
# Boundary positivity of the Poisson representation

A harmonic function on a disc is the Poisson average of its boundary values.  The Poisson kernel is
strictly positive at every interior point, so a harmonic function nonnegative on the bounding circle
is nonnegative throughout the disc, and its boundary values form a nonnegative density whose total
mass is pinned to the value at the centre by the mean value property.

Those three facts — representation, nonnegative density, fixed total mass — are what a
Herglotz-type representation consumes: they exhibit a uniformly bounded family of positive boundary
data indexed by the radius.

The imaginary part of an analytic function is harmonic, so an anti-Herglotz function supplies such
data on every disc contained in the upper half-plane, with no further hypotheses.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex InnerProductSpace MeasureTheory Metric Real

/-- **The Poisson kernel is strictly positive at interior points.**  Its numerator compares the
boundary radius against the interior one, and its denominator cannot vanish because a boundary point
and an interior point are at different distances from the centre. -/
theorem poissonKernel_pos {c w z : ℂ} {R : ℝ} (hz : z ∈ sphere c R) (hw : w ∈ ball c R) :
    0 < poissonKernel c w z := by
  rw [poissonKernel_def]
  have hzn : ‖z - c‖ = R := by rwa [mem_sphere_iff_norm] at hz
  have hwn : ‖w - c‖ < R := by rwa [mem_ball_iff_norm] at hw
  have hnum : 0 < ‖z - c‖ ^ 2 - ‖w - c‖ ^ 2 := by
    rw [hzn]
    nlinarith [norm_nonneg (w - c)]
  have hne : (z - c) - (w - c) ≠ 0 := by
    intro hc
    rw [sub_eq_zero] at hc
    rw [hc] at hzn
    linarith
  exact div_pos hnum (pow_pos (norm_pos_iff.mpr hne) 2)

/-- **Positivity propagates inward.**  A harmonic function nonnegative on the bounding circle is
nonnegative throughout the disc, because it is the average of its boundary values against a strictly
positive kernel. -/
theorem nonneg_of_nonneg_on_sphere {u : ℂ → ℝ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hu : HarmonicContOnCl u (ball c R)) (hnn : ∀ z ∈ sphere c R, 0 ≤ u z)
    {w : ℂ} (hw : w ∈ ball c R) : 0 ≤ u w := by
  rw [← hu.circleAverage_poissonKernel_smul hw, Real.circleAverage_def]
  refine smul_nonneg (by positivity) ?_
  refine intervalIntegral.integral_nonneg (by positivity) fun θ _ => ?_
  have hmem : circleMap c R θ ∈ sphere c R := circleMap_mem_sphere c hR.le θ
  exact mul_nonneg (poissonKernel_pos hmem hw).le (hnn _ hmem)

/-- **The boundary data of a nonnegative harmonic function.**  On every disc it reproduces the
function against the Poisson kernel, it is nonnegative, and its total mass is the value at the
centre.  These are exactly the three properties a Herglotz representation needs of the family
indexed by the radius. -/
theorem poissonBoundaryData {u : ℂ → ℝ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hu : HarmonicContOnCl u (ball c R)) (hnn : ∀ z ∈ sphere c R, 0 ≤ u z) :
    (∀ w ∈ ball c R, Real.circleAverage (poissonKernel c w • u) c R = u w) ∧
      (∀ θ : ℝ, 0 ≤ u (circleMap c R θ)) ∧
      Real.circleAverage u c R = u c := by
  refine ⟨fun w hw => hu.circleAverage_poissonKernel_smul hw,
    fun θ => hnn _ (circleMap_mem_sphere c hR.le θ), ?_⟩
  exact _root_.HarmonicContOnCl.circleAverage_eq (by rwa [abs_of_pos hR])

/-- The negated imaginary part of an analytic function is harmonic. -/
theorem harmonicAt_neg_im {q : ℂ → ℂ} {x : ℂ} (h : AnalyticAt ℂ q x) :
    HarmonicAt (fun z => -(q z).im) x :=
  h.harmonicAt_im.neg

/-- **An anti-Herglotz function supplies nonnegative boundary data.**  On a circle contained in the
upper half-plane its negated imaginary part is nonnegative, with no hypothesis beyond the sign. -/
theorem nonneg_neg_im_on_sphere {q : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hq : ∀ z : ℂ, 0 < z.im → (q z).im ≤ 0) (hsub : ∀ z ∈ sphere c R, 0 < z.im) :
    ∀ z ∈ sphere c R, 0 ≤ -(q z).im :=
  fun z hz => neg_nonneg.mpr (hq z (hsub z hz))

/-- **The anti-Herglotz sign propagates inward from a circle.**  If the whole circle lies in the
upper half-plane and the function is anti-Herglotz there, the negated imaginary part is nonnegative
on the entire disc — the disc need not be assumed to lie in the half-plane. -/
theorem nonneg_neg_im_of_antiHerglotz_on_sphere {q : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hu : HarmonicContOnCl (fun z => -(q z).im) (ball c R))
    (hq : ∀ z : ℂ, 0 < z.im → (q z).im ≤ 0) (hsub : ∀ z ∈ sphere c R, 0 < z.im)
    {w : ℂ} (hw : w ∈ ball c R) : (q w).im ≤ 0 := by
  have := nonneg_of_nonneg_on_sphere hR hu (nonneg_neg_im_on_sphere hq hsub) hw
  linarith

/-! ## The boundary measure

Packaging the boundary values as a measure in the angle is what makes them the object a weak-*
limit acts on.  The representation, the nonnegativity and the total mass then read as statements
about integrals against that measure, uniformly in the radius. -/

/-- The boundary values, as a density in the angle. -/
noncomputable def poissonBoundaryMeasure (u : ℂ → ℝ) (c : ℂ) (R : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioc 0 (2 * π))).withDensity
    fun θ => ENNReal.ofReal ((2 * π)⁻¹ * u (circleMap c R θ))

/-- Boundary values are continuous in the angle. -/
theorem continuous_comp_circleMap {u : ℂ → ℝ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hu : HarmonicContOnCl u (ball c R)) : Continuous fun θ : ℝ => u (circleMap c R θ) := by
  refine hu.2.comp_continuous (continuous_circleMap c R) fun θ => ?_
  rw [closure_ball c hR.ne']
  exact sphere_subset_closedBall (circleMap_mem_sphere c hR.le θ)

/-- **Integration against the boundary measure** is the angular average weighted by the boundary
values. -/
theorem integral_poissonBoundaryMeasure {u : ℂ → ℝ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hu : HarmonicContOnCl u (ball c R)) (hnn : ∀ z ∈ sphere c R, 0 ≤ u z) (g : ℝ → ℝ) :
    ∫ θ, g θ ∂(poissonBoundaryMeasure u c R)
      = (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), u (circleMap c R θ) * g θ := by
  have hcont := continuous_comp_circleMap hR hu
  have hnn' : ∀ θ : ℝ, 0 ≤ (2 * π)⁻¹ * u (circleMap c R θ) := fun θ =>
    mul_nonneg (by positivity) (hnn _ (circleMap_mem_sphere c hR.le θ))
  rw [poissonBoundaryMeasure, integral_withDensity_eq_integral_toReal_smul
    ((hcont.measurable.const_mul ((2 * π)⁻¹)).ennreal_ofReal)
    (Filter.Eventually.of_forall fun θ => ENNReal.ofReal_lt_top),
    ← intervalIntegral.integral_of_le (by positivity),
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [ENNReal.toReal_ofReal (hnn' θ), smul_eq_mul]
  ring

/-- **The total mass is the centre value**, for every radius.  This is the uniform bound: it does
not depend on the radius at all. -/
theorem integral_one_poissonBoundaryMeasure {u : ℂ → ℝ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hu : HarmonicContOnCl u (ball c R)) (hnn : ∀ z ∈ sphere c R, 0 ≤ u z) :
    ∫ _θ, (1 : ℝ) ∂(poissonBoundaryMeasure u c R) = u c := by
  rw [integral_poissonBoundaryMeasure hR hu hnn]
  have : ∀ θ : ℝ, u (circleMap c R θ) * 1 = u (circleMap c R θ) := fun θ => mul_one _
  rw [intervalIntegral.integral_congr fun θ _ => this θ]
  have hmv := _root_.HarmonicContOnCl.circleAverage_eq (f := u) (c := c) (R := R)
    (by rwa [abs_of_pos hR])
  rwa [Real.circleAverage_def, smul_eq_mul] at hmv

/-- **The representation against the boundary measure.**  Testing it with the Poisson kernel
returns the value of the function. -/
theorem integral_poissonKernel_poissonBoundaryMeasure {u : ℂ → ℝ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hu : HarmonicContOnCl u (ball c R)) (hnn : ∀ z ∈ sphere c R, 0 ≤ u z)
    {w : ℂ} (hw : w ∈ ball c R) :
    ∫ θ, poissonKernel c w (circleMap c R θ) ∂(poissonBoundaryMeasure u c R) = u w := by
  rw [integral_poissonBoundaryMeasure hR hu hnn]
  have hrep := hu.circleAverage_poissonKernel_smul hw
  rw [Real.circleAverage_def, smul_eq_mul] at hrep
  rw [← hrep]
  congr 1
  exact intervalIntegral.integral_congr fun θ _ => mul_comm _ _

/-! ## Scale invariance and the fixed-kernel family

To compare the boundary measures of different radii one needs them tested against the *same*
function.  The Poisson kernel makes this possible: it is invariant under scaling the evaluation point
and the boundary point together, because numerator and denominator are both quadratic.  So the
family of boundary measures indexed by the radius represents the dilated values of `u` against one
fixed kernel on the unit circle — a bounded family of measures paired with a fixed continuous test
function, which is what a weak-* limit consumes. -/

/-- **The Poisson kernel is scale invariant.**  Numerator and denominator are both quadratic, so a
common real dilation cancels. -/
theorem poissonKernel_mul_ofReal {a : ℝ} (ha : a ≠ 0) (w z : ℂ) :
    poissonKernel 0 ((a : ℂ) * w) ((a : ℂ) * z) = poissonKernel 0 w z := by
  have hnorm : ∀ v : ℂ, ‖(a : ℂ) * v‖ = |a| * ‖v‖ := by
    intro v
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hsq : |a| ^ 2 = a ^ 2 := sq_abs a
  simp only [poissonKernel_def, sub_zero]
  rw [show (a : ℂ) * z - (a : ℂ) * w = (a : ℂ) * (z - w) by ring]
  rw [hnorm, hnorm, hnorm, mul_pow, mul_pow, mul_pow, hsq, ← mul_sub]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 ha)

/-- The circle of radius `r` is the dilate of the unit circle. -/
theorem circleMap_zero_eq_mul (r θ : ℝ) :
    circleMap 0 r θ = (r : ℂ) * circleMap 0 1 θ := by
  simp [circleMap]

/-- **The fixed-kernel family.**  For a nonnegative harmonic function on the unit disc, the boundary
measures of every radius represent the dilated values of the function against one and the same
kernel on the unit circle.  With `integral_one_poissonBoundaryMeasure` pinning every total mass to
`u 0`, this is a bounded family tested by a fixed continuous function. -/
theorem integral_unitPoissonKernel_poissonBoundaryMeasure {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u (ball 0 1)) (hnn : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ u z)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    ∫ θ, poissonKernel 0 w (circleMap 0 1 θ) ∂(poissonBoundaryMeasure u 0 r)
      = u ((r : ℂ) * w) := by
  have hsub : closedBall (0 : ℂ) r ⊆ ball (0 : ℂ) 1 := fun x hx => by
    rw [mem_closedBall_zero_iff] at hx
    rw [mem_ball_zero_iff]
    linarith
  have hur : HarmonicContOnCl u (ball (0 : ℂ) r) := by
    refine HarmonicOnNhd.harmonicContOnCl ?_
    rw [closure_ball (0 : ℂ) hr.ne']
    exact hu.mono hsub
  have hnnr : ∀ z ∈ sphere (0 : ℂ) r, 0 ≤ u z := fun z hz =>
    hnn z (hsub (sphere_subset_closedBall hz))
  have hwr : (r : ℂ) * w ∈ ball (0 : ℂ) r := by
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    have : ‖w‖ < 1 := by rwa [mem_ball_zero_iff] at hw
    nlinarith
  rw [← integral_poissonKernel_poissonBoundaryMeasure hr hur hnnr hwr]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  show poissonKernel 0 w (circleMap 0 1 θ) = poissonKernel 0 ((r : ℂ) * w) (circleMap 0 r θ)
  rw [circleMap_zero_eq_mul r θ, poissonKernel_mul_ofReal hr.ne']

/-! ## Finiteness and compact support

The boundary measures are finite because their density is a continuous function on a compact
circle, and they vanish outside a fixed compact interval of angles.  The second fact makes any
family of them tight without further argument, which is the hypothesis of Prokhorov's theorem. -/

/-- The boundary measure is finite: its density is continuous on a compact circle. -/
theorem isFiniteMeasure_poissonBoundaryMeasure {u : ℂ → ℝ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hu : HarmonicContOnCl u (ball c R)) : IsFiniteMeasure (poissonBoundaryMeasure u c R) := by
  obtain ⟨z₀, -, hmax⟩ := (isCompact_sphere c R).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr hR.le)
    (hu.continuousOn_ball.mono sphere_subset_closedBall)
  refine ⟨?_⟩
  rw [poissonBoundaryMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hbound : ∫⁻ θ in Set.Ioc 0 (2 * π), ENNReal.ofReal ((2 * π)⁻¹ * u (circleMap c R θ))
      ≤ ∫⁻ _θ in Set.Ioc 0 (2 * π), ENNReal.ofReal ((2 * π)⁻¹ * u z₀) :=
    lintegral_mono fun θ => ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (hmax (circleMap_mem_sphere c hR.le θ)) (by positivity))
  refine lt_of_le_of_lt hbound ?_
  rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- **The boundary measure is carried by a fixed compact interval of angles.**  Hence any family of
them is tight, with no estimate: the carrier does not move with the radius. -/
theorem poissonBoundaryMeasure_compl_eq_zero {u : ℂ → ℝ} {c : ℂ} {R : ℝ} :
    poissonBoundaryMeasure u c R (Set.Ioc 0 (2 * π))ᶜ = 0 := by
  rw [poissonBoundaryMeasure, withDensity_apply _ measurableSet_Ioc.compl,
    Measure.restrict_restrict measurableSet_Ioc.compl]
  simp

/-- The boundary measure lives on the compact interval of angles. -/
theorem poissonBoundaryMeasure_compl_Icc_eq_zero {u : ℂ → ℝ} {c : ℂ} {R : ℝ} :
    poissonBoundaryMeasure u c R (Set.Icc 0 (2 * π))ᶜ = 0 := by
  refine measure_mono_null (Set.compl_subset_compl.mpr Set.Ioc_subset_Icc_self) ?_
  exact poissonBoundaryMeasure_compl_eq_zero

/-! ## Total mass, the degenerate case, and normalization

Stating the total mass as a measure of the whole space rather than as an integral makes the
degenerate case immediate: a positive measure of total mass zero *is* the zero measure, so the
representation returns zero at every interior point.  That is the minimum principle, obtained
without any almost-everywhere argument.  Away from that case the measures normalize to probability
measures, which is the form Prokhorov's theorem takes. -/

/-- The total mass of the boundary measure is the centre value. -/
theorem poissonBoundaryMeasure_univ {u : ℂ → ℝ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hu : HarmonicContOnCl u (ball c R)) (hnn : ∀ z ∈ sphere c R, 0 ≤ u z) :
    poissonBoundaryMeasure u c R Set.univ = ENNReal.ofReal (u c) := by
  haveI := isFiniteMeasure_poissonBoundaryMeasure hR hu
  have h1 := integral_one_poissonBoundaryMeasure hR hu hnn
  rw [integral_const, smul_eq_mul, mul_one] at h1
  rw [← h1, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- A boundary measure with vanishing centre value is the zero measure. -/
theorem poissonBoundaryMeasure_eq_zero {u : ℂ → ℝ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hu : HarmonicContOnCl u (ball c R)) (hnn : ∀ z ∈ sphere c R, 0 ≤ u z) (h0 : u c = 0) :
    poissonBoundaryMeasure u c R = 0 := by
  rw [← Measure.measure_univ_eq_zero, poissonBoundaryMeasure_univ hR hu hnn, h0,
    ENNReal.ofReal_zero]

/-- **The minimum principle.**  A harmonic function nonnegative on the bounding circle and vanishing
at the centre vanishes on the whole disc: its boundary measure has total mass zero, so it is the
zero measure, and the representation returns zero everywhere inside. -/
theorem eq_zero_of_center_eq_zero {u : ℂ → ℝ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hu : HarmonicContOnCl u (ball c R)) (hnn : ∀ z ∈ sphere c R, 0 ≤ u z) (h0 : u c = 0)
    {w : ℂ} (hw : w ∈ ball c R) : u w = 0 := by
  rw [← integral_poissonKernel_poissonBoundaryMeasure hR hu hnn hw,
    poissonBoundaryMeasure_eq_zero hR hu hnn h0, integral_zero_measure]

/-- **Normalization.**  Away from the degenerate case the boundary measures are probability measures
after dividing by the centre value — the form Prokhorov's theorem consumes, and the divisor is the
same for every radius. -/
theorem isProbabilityMeasure_poissonBoundaryMeasure_smul {u : ℂ → ℝ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hu : HarmonicContOnCl u (ball c R)) (hnn : ∀ z ∈ sphere c R, 0 ≤ u z) (h0 : 0 < u c) :
    IsProbabilityMeasure ((ENNReal.ofReal (u c))⁻¹ • poissonBoundaryMeasure u c R) := by
  refine ⟨?_⟩
  rw [Measure.smul_apply, smul_eq_mul, poissonBoundaryMeasure_univ hR hu hnn]
  exact ENNReal.inv_mul_cancel (by simpa using h0) ENNReal.ofReal_ne_top

end GaloisForLFunctions.HTGeometry
