import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.Prokhorov
import GaloisForLFunctions.HTGeometry.CompactClusterLimit

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

/-- A closed disc of radius below one sits inside the unit disc. -/
theorem closedBall_subset_ball_one {r : ℝ} (hr1 : r < 1) :
    closedBall (0 : ℂ) r ⊆ ball (0 : ℂ) 1 := fun x hx => by
  rw [mem_closedBall_zero_iff] at hx
  rw [mem_ball_zero_iff]
  linarith

/-- A function harmonic on the unit disc is harmonic-up-to-the-boundary on every smaller disc. -/
theorem harmonicContOnCl_of_lt_one {u : ℂ → ℝ} (hu : HarmonicOnNhd u (ball 0 1))
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) : HarmonicContOnCl u (ball (0 : ℂ) r) := by
  refine HarmonicOnNhd.harmonicContOnCl ?_
  rw [closure_ball (0 : ℂ) hr.ne']
  exact hu.mono (closedBall_subset_ball_one hr1)

/-- **The fixed-kernel family.**  For a nonnegative harmonic function on the unit disc, the boundary
measures of every radius represent the dilated values of the function against one and the same
kernel on the unit circle.  With `integral_one_poissonBoundaryMeasure` pinning every total mass to
`u 0`, this is a bounded family tested by a fixed continuous function. -/
theorem integral_unitPoissonKernel_poissonBoundaryMeasure {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u (ball 0 1)) (hnn : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ u z)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    ∫ θ, poissonKernel 0 w (circleMap 0 1 θ) ∂(poissonBoundaryMeasure u 0 r)
      = u ((r : ℂ) * w) := by
  have hsub := closedBall_subset_ball_one hr1
  have hur := harmonicContOnCl_of_lt_one hu hr hr1
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

/-! ## The kernel as a bounded continuous test function

Weak convergence of measures is tested against bounded continuous functions, so the Poisson kernel
on the unit circle must be presented as one.  Both properties are explicit: on the unit circle the
numerator is the constant `1 - ‖w‖²`, and the denominator is bounded below by `(1 - ‖w‖)²` because a
boundary point and an interior point are separated by at least that distance. -/

/-- The Poisson kernel on the unit circle, with the numerator constant. -/
theorem poissonKernel_circleMap_one (w : ℂ) (θ : ℝ) :
    poissonKernel 0 w (circleMap 0 1 θ) = (1 - ‖w‖ ^ 2) / ‖circleMap 0 1 θ - w‖ ^ 2 := by
  simp only [poissonKernel_def, sub_zero, norm_circleMap_zero, abs_one, one_pow]

/-- A point of the unit circle is separated from an interior point. -/
theorem one_sub_norm_le_norm_circleMap_sub (w : ℂ) (θ : ℝ) :
    1 - ‖w‖ ≤ ‖circleMap 0 1 θ - w‖ := by
  have h := norm_sub_norm_le (circleMap 0 1 θ) w
  rwa [norm_circleMap_zero, abs_one] at h

theorem poissonKernel_circleMap_one_nonneg {w : ℂ} (hw : ‖w‖ < 1) (θ : ℝ) :
    0 ≤ poissonKernel 0 w (circleMap 0 1 θ) := by
  rw [poissonKernel_circleMap_one]
  have : ‖w‖ ^ 2 < 1 := by nlinarith [norm_nonneg w]
  positivity

theorem continuous_poissonKernel_circleMap {w : ℂ} (hw : ‖w‖ < 1) :
    Continuous fun θ : ℝ => poissonKernel 0 w (circleMap 0 1 θ) := by
  simp only [poissonKernel_circleMap_one]
  refine continuous_const.div (((continuous_circleMap 0 1).sub continuous_const).norm.pow 2)
    fun θ => ?_
  have h1 : (0 : ℝ) < 1 - ‖w‖ := by linarith
  exact ne_of_gt (pow_pos (lt_of_lt_of_le h1 (one_sub_norm_le_norm_circleMap_sub w θ)) 2)

/-- **The explicit bound.**  The kernel on the unit circle is bounded by a constant depending only on
the distance of the evaluation point from the boundary. -/
theorem poissonKernel_circleMap_one_le {w : ℂ} (hw : ‖w‖ < 1) (θ : ℝ) :
    poissonKernel 0 w (circleMap 0 1 θ) ≤ (1 - ‖w‖ ^ 2) / (1 - ‖w‖) ^ 2 := by
  rw [poissonKernel_circleMap_one]
  have h1 : (0 : ℝ) < 1 - ‖w‖ := by linarith
  have hnum : (0 : ℝ) ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  exact div_le_div_of_nonneg_left hnum (pow_pos h1 2)
    (pow_le_pow_left₀ h1.le (one_sub_norm_le_norm_circleMap_sub w θ) 2)

/-- The Poisson kernel on the unit circle as a bounded continuous function of the angle — the test
function weak convergence of the boundary measures is paired against. -/
noncomputable def unitPoissonTest {w : ℂ} (hw : ‖w‖ < 1) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun θ => poissonKernel 0 w (circleMap 0 1 θ))
    (continuous_poissonKernel_circleMap hw)
    ((1 - ‖w‖ ^ 2) / (1 - ‖w‖) ^ 2)
    fun θ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (poissonKernel_circleMap_one_nonneg hw θ)]
      exact poissonKernel_circleMap_one_le hw θ

@[simp]
theorem unitPoissonTest_apply {w : ℂ} (hw : ‖w‖ < 1) (θ : ℝ) :
    unitPoissonTest hw θ = poissonKernel 0 w (circleMap 0 1 θ) := rfl

/-! ## Tightness and the degenerate case on the unit disc

A family of measures all carried by one compact set is tight with no estimate, which is the
hypothesis of Prokhorov's theorem.  On the unit disc the degenerate case is settled by the minimum
principle applied on an intermediate radius. -/

/-- **Tightness for free.**  A family of measures all carried by one compact set is tight. -/
theorem isTightMeasureSet_of_forall_compl_eq_zero {S : Set (Measure ℝ)} (K : Set ℝ)
    (hK : IsCompact K) (hS : ∀ μ ∈ S, μ Kᶜ = 0) : IsTightMeasureSet S := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  exact fun ε hε => ⟨K, hK, fun μ hμ => by simp [hS μ hμ]⟩

/-- The boundary measures of a nonnegative harmonic function on the unit disc form a tight family:
every one of them is carried by the same compact interval of angles. -/
theorem isTightMeasureSet_poissonBoundaryMeasure (u : ℂ → ℝ) (c : ℂ) (T : Set ℝ) :
    IsTightMeasureSet {μ : Measure ℝ | ∃ R ∈ T, μ = poissonBoundaryMeasure u c R} := by
  refine isTightMeasureSet_of_forall_compl_eq_zero (Set.Icc 0 (2 * π)) isCompact_Icc ?_
  rintro μ ⟨R, -, rfl⟩
  exact poissonBoundaryMeasure_compl_Icc_eq_zero

/-- **The minimum principle on the unit disc.**  A nonnegative harmonic function on the unit disc
vanishing at the origin vanishes identically: apply the disc version at any intermediate radius. -/
theorem eq_zero_of_center_eq_zero_ball {u : ℂ → ℝ} (hu : HarmonicOnNhd u (ball 0 1))
    (hnn : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ u z) (h0 : u 0 = 0) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    u w = 0 := by
  have hwn : ‖w‖ < 1 := by rwa [mem_ball_zero_iff] at hw
  have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  set r := (‖w‖ + 1) / 2 with hrdef
  have hr : 0 < r := by rw [hrdef]; linarith
  have hr1 : r < 1 := by rw [hrdef]; linarith
  have hwr : w ∈ ball (0 : ℂ) r := by
    rw [mem_ball_zero_iff, hrdef]
    linarith
  exact eq_zero_of_center_eq_zero hr (harmonicContOnCl_of_lt_one hu hr hr1)
    (fun z hz => hnn z (closedBall_subset_ball_one hr1 (sphere_subset_closedBall hz))) h0 hwr

/-! ## The normalized family and the radial limit

The two ingredients the cluster-point argument pairs: the value of the fixed test function against
the normalized measure of radius `r`, and the fact that this value converges as `r` approaches the
boundary — because it is the dilated value of `u`, and `u` is continuous. -/

/-- The fixed test function against the normalized boundary measure. -/
theorem integral_unitPoissonKernel_normalized {u : ℂ → ℝ} (hu : HarmonicOnNhd u (ball 0 1))
    (hnn : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ u z) (hc : 0 < u 0)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    ∫ θ, poissonKernel 0 w (circleMap 0 1 θ)
        ∂((ENNReal.ofReal (u 0))⁻¹ • poissonBoundaryMeasure u 0 r)
      = (u 0)⁻¹ * u ((r : ℂ) * w) := by
  rw [integral_smul_measure, integral_unitPoissonKernel_poissonBoundaryMeasure hu hnn hr hr1 hw,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hc.le, smul_eq_mul]

/-- Dilating an interior point is continuous at the boundary radius. -/
theorem continuousAt_dilate {u : ℂ → ℝ} (hu : HarmonicOnNhd u (ball 0 1)) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) 1) : ContinuousAt (fun r : ℝ => u ((r : ℂ) * w)) 1 := by
  have hmap : ContinuousAt (fun r : ℝ => (r : ℂ) * w) 1 := by fun_prop
  have hcont : ContinuousAt u (((1 : ℝ) : ℂ) * w) := by
    rw [Complex.ofReal_one, one_mul]
    exact (hu w hw).1.continuousAt
  exact ContinuousAt.comp (f := fun r : ℝ => (r : ℂ) * w) hcont hmap

/-- **The radial limit.**  The dilated values converge to the value at the point as the radius
approaches one. -/
theorem tendsto_dilate {u : ℂ → ℝ} (hu : HarmonicOnNhd u (ball 0 1)) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) 1) :
    Filter.Tendsto (fun r : ℝ => u ((r : ℂ) * w)) (nhdsWithin 1 (Set.Iio 1)) (nhds (u w)) := by
  have h : Filter.Tendsto (fun r : ℝ => u ((r : ℂ) * w)) (nhdsWithin 1 (Set.Iio 1))
      (nhds (u (((1 : ℝ) : ℂ) * w))) := (continuousAt_dilate hu hw).mono_left nhdsWithin_le_nhds
  rwa [Complex.ofReal_one, one_mul] at h

/-! ## The Herglotz representation on the disc

Everything assembles.  The normalized boundary measures form a tight family of probability measures,
so they have a cluster point; the fixed kernel is a continuous functional of the measure; and the
values it takes along the family converge because they are the dilated values of `u`.  The cluster
point therefore represents `u` at every interior point at once. -/

/-- **The Herglotz representation on the disc.**  A nonnegative harmonic function on the unit disc is
the Poisson integral of a finite positive measure on the circle of angles.

The measure is a cluster point of the normalized boundary measures.  Nothing here is an estimate:
tightness comes from the angles living in a fixed compact interval, the uniform mass bound from the
mean value property, and the limit from continuity of `u` along radii. -/
theorem exists_poissonRepresentation {u : ℂ → ℝ} (hu : HarmonicOnNhd u (ball 0 1))
    (hnn : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ u z) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
      ∀ w ∈ ball (0 : ℂ) 1, ∫ θ, poissonKernel 0 w (circleMap 0 1 θ) ∂ν = u w := by
  classical
  have hzero : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by simp
  rcases (hnn 0 hzero).eq_or_lt with hc | hc
  · exact ⟨0, inferInstance, fun w hw => by
      rw [integral_zero_measure]
      exact (eq_zero_of_center_eq_zero_ball hu hnn hc.symm hw).symm⟩
  -- the normalized family
  set P : ℝ → ProbabilityMeasure ℝ := fun r =>
    if h : 0 < r ∧ r < 1 then
      ⟨(ENNReal.ofReal (u 0))⁻¹ • poissonBoundaryMeasure u 0 r,
        isProbabilityMeasure_poissonBoundaryMeasure_smul h.1
          (harmonicContOnCl_of_lt_one hu h.1 h.2)
          (fun z hz => hnn z (closedBall_subset_ball_one h.2 (sphere_subset_closedBall hz))) hc⟩
    else ⟨Measure.dirac 0, inferInstance⟩ with hPdef
  set S : Set (ProbabilityMeasure ℝ) := P '' Set.Ioo 0 1 with hSdef
  have hcarrier : ∀ m ∈ S, (m : Measure ℝ) (Set.Icc 0 (2 * π))ᶜ = 0 := by
    rintro m ⟨r, hr, rfl⟩
    have hd : (0 : ℝ) < r ∧ r < 1 := ⟨hr.1, hr.2⟩
    simp only [hPdef, dif_pos hd]
    show ((ENNReal.ofReal (u 0))⁻¹ • poissonBoundaryMeasure u 0 r) (Set.Icc 0 (2 * π))ᶜ = 0
    rw [Measure.smul_apply, smul_eq_mul, poissonBoundaryMeasure_compl_Icc_eq_zero, mul_zero]
  have htight : IsTightMeasureSet {((m : ProbabilityMeasure ℝ) : Measure ℝ) | m ∈ S} := by
    refine isTightMeasureSet_of_forall_compl_eq_zero (Set.Icc 0 (2 * π)) isCompact_Icc ?_
    rintro μ ⟨m, hm, rfl⟩
    exact hcarrier m hm
  have hcompact : IsCompact (closure S) := isCompact_closure_of_isTightMeasureSet htight
  have hmem : ∀ᶠ r in nhdsWithin (1 : ℝ) (Set.Iio 1), P r ∈ S := by
    filter_upwards [Filter.eventually_mem_set.mpr (Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1))]
      with r hr using ⟨r, hr, rfl⟩
  obtain ⟨μ, -, hcl⟩ := exists_clusterPt_closure_of_isCompact hcompact hmem
  refine ⟨ENNReal.ofReal (u 0) • (μ : Measure ℝ), ?_, fun w hw => ?_⟩
  · exact ⟨by
      rw [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
      exact ENNReal.ofReal_lt_top⟩
  · have hwn : ‖w‖ < 1 := by rwa [mem_ball_zero_iff] at hw
    have hΦ : Continuous fun m : ProbabilityMeasure ℝ =>
        ∫ θ, (unitPoissonTest hwn) θ ∂(m : Measure ℝ) :=
      MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction _
    have hy : Filter.Tendsto
        (fun r : ℝ => ∫ θ, (unitPoissonTest hwn) θ ∂((P r : ProbabilityMeasure ℝ) : Measure ℝ))
        (nhdsWithin 1 (Set.Iio 1)) (nhds ((u 0)⁻¹ * u w)) := by
      refine Filter.Tendsto.congr' ?_ (((tendsto_dilate hu hw)).const_mul ((u 0)⁻¹))
      filter_upwards [Filter.eventually_mem_set.mpr
        (Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1))] with r hr
      have hd : (0 : ℝ) < r ∧ r < 1 := ⟨hr.1, hr.2⟩
      simp only [hPdef, dif_pos hd, unitPoissonTest_apply]
      exact (integral_unitPoissonKernel_normalized hu hnn hc hr.1 hr.2 hw).symm
    have hkey := eq_of_clusterPt_of_tendsto hcl hΦ hy
    simp only [unitPoissonTest_apply] at hkey
    rw [integral_smul_measure, ENNReal.toReal_ofReal hc.le, smul_eq_mul, hkey,
      mul_inv_cancel_left₀ hc.ne']

/-! ## Harnack's inequality

The representation immediately bounds a nonnegative harmonic function above and below by its value
at the centre.  Both bounds are the corresponding bounds on the kernel, integrated: the kernel's
numerator is constant on the circle, so the only variation is the denominator, which the triangle
inequality pins between `(1 - ‖w‖)²` and `(1 + ‖w‖)²`. -/

/-- At the centre the Poisson kernel is one. -/
theorem poissonKernel_circleMap_one_center (θ : ℝ) : poissonKernel 0 0 (circleMap 0 1 θ) = 1 := by
  rw [poissonKernel_circleMap_one, sub_zero, norm_circleMap_zero, abs_one]
  norm_num

/-- A point of the unit circle is within `1 + ‖w‖` of an interior point. -/
theorem norm_circleMap_sub_le (w : ℂ) (θ : ℝ) : ‖circleMap 0 1 θ - w‖ ≤ 1 + ‖w‖ := by
  refine (norm_sub_le _ _).trans ?_
  rw [norm_circleMap_zero, abs_one]

/-- **The lower kernel bound.** -/
theorem le_poissonKernel_circleMap_one {w : ℂ} (hw : ‖w‖ < 1) (θ : ℝ) :
    (1 - ‖w‖) / (1 + ‖w‖) ≤ poissonKernel 0 w (circleMap 0 1 θ) := by
  rw [poissonKernel_circleMap_one]
  have h0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have h1 : (0 : ℝ) < 1 - ‖w‖ := by linarith
  have h2 : (0 : ℝ) < 1 + ‖w‖ := by linarith
  have hlow : (0 : ℝ) < ‖circleMap 0 1 θ - w‖ :=
    lt_of_lt_of_le h1 (one_sub_norm_le_norm_circleMap_sub w θ)
  rw [div_le_div_iff₀ h2 (pow_pos hlow 2)]
  have hup : ‖circleMap 0 1 θ - w‖ ^ 2 ≤ (1 + ‖w‖) ^ 2 :=
    pow_le_pow_left₀ hlow.le (norm_circleMap_sub_le w θ) 2
  nlinarith

/-- **Harnack's inequality on the disc.**  A nonnegative harmonic function on the unit disc is
pinned between two multiples of its value at the centre, the factors depending only on the distance
to the boundary. -/
theorem harnack {u : ℂ → ℝ} (hu : HarmonicOnNhd u (ball 0 1))
    (hnn : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ u z) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    (1 - ‖w‖) / (1 + ‖w‖) * u 0 ≤ u w ∧ u w ≤ (1 + ‖w‖) / (1 - ‖w‖) * u 0 := by
  obtain ⟨ν, hfin, hrep⟩ := exists_poissonRepresentation hu hnn
  have hwn : ‖w‖ < 1 := by rwa [mem_ball_zero_iff] at hw
  have hzero : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by simp
  have h0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have h1 : (1 : ℝ) - ‖w‖ ≠ 0 := by intro hc; nlinarith
  have hmass : u 0 = ν.real Set.univ := by
    rw [← hrep 0 hzero]
    simp only [poissonKernel_circleMap_one_center]
    rw [integral_const, smul_eq_mul, mul_one]
  have hint : Integrable (fun θ : ℝ => poissonKernel 0 w (circleMap 0 1 θ)) ν :=
    (unitPoissonTest hwn).integrable ν
  constructor
  · have hle := integral_mono (integrable_const _) hint
      (fun θ => le_poissonKernel_circleMap_one hwn θ)
    rw [integral_const, smul_eq_mul, hrep w hw] at hle
    rw [hmass, mul_comm]
    exact hle
  · have hle := integral_mono hint (integrable_const _)
      (fun θ => poissonKernel_circleMap_one_le hwn θ)
    rw [integral_const, smul_eq_mul, hrep w hw] at hle
    rw [hmass]
    refine hle.trans (le_of_eq ?_)
    field_simp
    ring

/-! ## Locating the measure: atoms and radial growth

The Poisson kernel evaluated on the radius through a boundary angle blows up like `(1+r)/(1-r)`.
So an atom of the representing measure forces the function to blow up along that radius, and
conversely a function bounded along a radius has no atom at its endpoint.  This is the first half of
localizing the measure: where the function stays bounded, the measure puts no point mass. -/

/-- The distance from a boundary point to the radius point beneath it. -/
theorem norm_circleMap_sub_smul {r : ℝ} (hr1 : r < 1) (θ₀ : ℝ) :
    ‖circleMap 0 1 θ₀ - (r : ℂ) * circleMap 0 1 θ₀‖ = 1 - r := by
  have hsub : circleMap 0 1 θ₀ - (r : ℂ) * circleMap 0 1 θ₀
      = ((1 - r : ℝ) : ℂ) * circleMap 0 1 θ₀ := by push_cast; ring
  rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith),
    norm_circleMap_zero, abs_one, mul_one]

/-- **The kernel on the radius.**  At the endpoint angle its value is exactly `(1+r)/(1-r)`. -/
theorem poissonKernel_radial {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (θ₀ : ℝ) :
    poissonKernel 0 ((r : ℂ) * circleMap 0 1 θ₀) (circleMap 0 1 θ₀) = (1 + r) / (1 - r) := by
  have hnw : ‖(r : ℂ) * circleMap 0 1 θ₀‖ = r := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr, norm_circleMap_zero,
      abs_one, mul_one]
  rw [poissonKernel_circleMap_one, hnw, norm_circleMap_sub_smul hr1 θ₀]
  have h1 : (1 : ℝ) - r ≠ 0 := by intro hc; nlinarith
  field_simp
  ring

/-- **An atom forces radial growth.**  The mass at a boundary angle, amplified by `(1+r)/(1-r)`, is
a lower bound for the function on the radius through that angle. -/
theorem measureReal_singleton_mul_le {ν : Measure ℝ} [IsFiniteMeasure ν] {u : ℂ → ℝ}
    (hrep : ∀ w ∈ ball (0 : ℂ) 1, ∫ θ, poissonKernel 0 w (circleMap 0 1 θ) ∂ν = u w)
    (θ₀ : ℝ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    ν.real {θ₀} * ((1 + r) / (1 - r)) ≤ u ((r : ℂ) * circleMap 0 1 θ₀) := by
  have hnw : ‖(r : ℂ) * circleMap 0 1 θ₀‖ = r := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
      norm_circleMap_zero, abs_one, mul_one]
  have hwmem : (r : ℂ) * circleMap 0 1 θ₀ ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, hnw]; exact hr1
  have hwn : ‖(r : ℂ) * circleMap 0 1 θ₀‖ < 1 := by rw [hnw]; exact hr1
  have hint : Integrable
      (fun θ : ℝ => poissonKernel 0 ((r : ℂ) * circleMap 0 1 θ₀) (circleMap 0 1 θ)) ν :=
    (unitPoissonTest hwn).integrable ν
  have hind : Integrable (Set.indicator {θ₀}
      fun _ : ℝ => poissonKernel 0 ((r : ℂ) * circleMap 0 1 θ₀) (circleMap 0 1 θ₀)) ν :=
    (integrable_const _).indicator (measurableSet_singleton θ₀)
  have hle : ∀ θ : ℝ,
      Set.indicator {θ₀}
          (fun _ : ℝ => poissonKernel 0 ((r : ℂ) * circleMap 0 1 θ₀) (circleMap 0 1 θ₀)) θ
        ≤ poissonKernel 0 ((r : ℂ) * circleMap 0 1 θ₀) (circleMap 0 1 θ) := by
    intro θ
    by_cases h : θ = θ₀
    · rw [Set.indicator_of_mem (by simp [h] : θ ∈ ({θ₀} : Set ℝ))]
      exact le_of_eq (by rw [h])
    · rw [Set.indicator_of_notMem (by simpa using h)]
      exact poissonKernel_circleMap_one_nonneg hwn θ
  have hmono := integral_mono hind hint hle
  rw [integral_indicator_const _ (measurableSet_singleton θ₀), hrep _ hwmem,
    poissonKernel_radial hr hr1 θ₀, smul_eq_mul] at hmono
  exact hmono

/-- **Bounded on a radius means no atom.**  If the function stays bounded along the radius through a
boundary angle, the representing measure has no mass at that angle. -/
theorem measureReal_singleton_eq_zero_of_bddAbove {ν : Measure ℝ} [IsFiniteMeasure ν] {u : ℂ → ℝ}
    (hrep : ∀ w ∈ ball (0 : ℂ) 1, ∫ θ, poissonKernel 0 w (circleMap 0 1 θ) ∂ν = u w)
    (θ₀ : ℝ) {M : ℝ} (hM : ∀ r : ℝ, 0 ≤ r → r < 1 → u ((r : ℂ) * circleMap 0 1 θ₀) ≤ M) :
    ν.real {θ₀} = 0 := by
  by_contra hne
  have hpos : 0 < ν.real {θ₀} := lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)
  have hbase := (measureReal_singleton_mul_le hrep θ₀ le_rfl (by norm_num)).trans
    (hM 0 le_rfl (by norm_num))
  norm_num at hbase
  have hMpos : 0 < M := lt_of_lt_of_le hpos hbase
  have hane : ν.real {θ₀} ≠ 0 := hpos.ne'
  have hMne : (2 : ℝ) * M ≠ 0 := by positivity
  have hfrac : 0 < ν.real {θ₀} / (2 * M) := div_pos hpos (by linarith)
  have hfrac1 : ν.real {θ₀} / (2 * M) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have hr0 : 0 ≤ 1 - ν.real {θ₀} / (2 * M) := by linarith
  have hr1 : 1 - ν.real {θ₀} / (2 * M) < 1 := by linarith
  have hkey := (measureReal_singleton_mul_le hrep θ₀ hr0 hr1).trans (hM _ hr0 hr1)
  have hone : (1 : ℝ) - (1 - ν.real {θ₀} / (2 * M)) = ν.real {θ₀} / (2 * M) := by ring
  rw [hone] at hkey
  have hprod : ν.real {θ₀} *
      ((1 + (1 - ν.real {θ₀} / (2 * M))) / (ν.real {θ₀} / (2 * M)))
      = (1 + (1 - ν.real {θ₀} / (2 * M))) * (2 * M) := by
    field_simp
  rw [hprod] at hkey
  nlinarith [hkey, hr0, hMpos]

/-- **The kernel stays large on a chordal ball.**  For boundary angles within `1 - r` of `θ₀`, the
kernel at the radius point is at least `(1+r)/(4(1-r))`: the numerator is fixed and the denominator
is at most twice the radial distance. -/
theorem le_poissonKernel_of_close {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (θ θ₀ : ℝ)
    (h : ‖circleMap 0 1 θ - circleMap 0 1 θ₀‖ ≤ 1 - r) :
    (1 + r) / (4 * (1 - r))
      ≤ poissonKernel 0 ((r : ℂ) * circleMap 0 1 θ₀) (circleMap 0 1 θ) := by
  have h1 : (0 : ℝ) < 1 - r := by linarith
  have hnw : ‖(r : ℂ) * circleMap 0 1 θ₀‖ = r := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
      norm_circleMap_zero, abs_one, mul_one]
  have hlow : 1 - r ≤ ‖circleMap 0 1 θ - (r : ℂ) * circleMap 0 1 θ₀‖ := by
    have := one_sub_norm_le_norm_circleMap_sub ((r : ℂ) * circleMap 0 1 θ₀) θ
    rwa [hnw] at this
  have hup : ‖circleMap 0 1 θ - (r : ℂ) * circleMap 0 1 θ₀‖ ≤ 2 * (1 - r) := by
    have htri : ‖circleMap 0 1 θ - (r : ℂ) * circleMap 0 1 θ₀‖
        ≤ ‖circleMap 0 1 θ - circleMap 0 1 θ₀‖
          + ‖circleMap 0 1 θ₀ - (r : ℂ) * circleMap 0 1 θ₀‖ := by
      have := norm_add_le (circleMap 0 1 θ - circleMap 0 1 θ₀)
        (circleMap 0 1 θ₀ - (r : ℂ) * circleMap 0 1 θ₀)
      rwa [sub_add_sub_cancel] at this
    rw [norm_circleMap_sub_smul hr1 θ₀] at htri
    linarith
  rw [poissonKernel_circleMap_one, hnw]
  have hnum : (0 : ℝ) ≤ 1 - r ^ 2 := by nlinarith
  have hden : ‖circleMap 0 1 θ - (r : ℂ) * circleMap 0 1 θ₀‖ ^ 2 ≤ (2 * (1 - r)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hup 2
  have hstep : (1 - r ^ 2) / (2 * (1 - r)) ^ 2
      ≤ (1 - r ^ 2) / ‖circleMap 0 1 θ - (r : ℂ) * circleMap 0 1 θ₀‖ ^ 2 :=
    div_le_div_of_nonneg_left hnum (pow_pos (by linarith) 2) hden
  refine le_trans (le_of_eq ?_) hstep
  have h1' : (1 : ℝ) - r ≠ 0 := ne_of_gt h1
  field_simp
  ring

/-- **The local mass bound.**  The mass carried by boundary angles within `1 - r` of `θ₀` is
controlled by the value of the function at the radius point. -/
theorem measureReal_le_of_close {ν : Measure ℝ} [IsFiniteMeasure ν] {u : ℂ → ℝ}
    (hrep : ∀ w ∈ ball (0 : ℂ) 1, ∫ θ, poissonKernel 0 w (circleMap 0 1 θ) ∂ν = u w)
    (θ₀ : ℝ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) {A : Set ℝ} (hA : MeasurableSet A)
    (hclose : ∀ θ ∈ A, ‖circleMap 0 1 θ - circleMap 0 1 θ₀‖ ≤ 1 - r) :
    ν.real A * ((1 + r) / (4 * (1 - r))) ≤ u ((r : ℂ) * circleMap 0 1 θ₀) := by
  have hnw : ‖(r : ℂ) * circleMap 0 1 θ₀‖ = r := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
      norm_circleMap_zero, abs_one, mul_one]
  have hwmem : (r : ℂ) * circleMap 0 1 θ₀ ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, hnw]; exact hr1
  have hwn : ‖(r : ℂ) * circleMap 0 1 θ₀‖ < 1 := by rw [hnw]; exact hr1
  have hint : Integrable
      (fun θ : ℝ => poissonKernel 0 ((r : ℂ) * circleMap 0 1 θ₀) (circleMap 0 1 θ)) ν :=
    (unitPoissonTest hwn).integrable ν
  have hind : Integrable (Set.indicator A fun _ : ℝ => (1 + r) / (4 * (1 - r))) ν :=
    (integrable_const _).indicator hA
  have hle : ∀ θ : ℝ,
      Set.indicator A (fun _ : ℝ => (1 + r) / (4 * (1 - r))) θ
        ≤ poissonKernel 0 ((r : ℂ) * circleMap 0 1 θ₀) (circleMap 0 1 θ) := by
    intro θ
    by_cases h : θ ∈ A
    · rw [Set.indicator_of_mem h]
      exact le_poissonKernel_of_close hr hr1 θ θ₀ (hclose θ h)
    · rw [Set.indicator_of_notMem h]
      exact poissonKernel_circleMap_one_nonneg hwn θ
  have hmono := integral_mono hind hint hle
  rw [integral_indicator_const _ hA, hrep _ hwmem, smul_eq_mul] at hmono
  exact hmono

/-! ## From chords to angles

The geometric hypothesis of the local mass bound is a chordal distance.  The circle map is
`1`-Lipschitz, so it is implied by the corresponding bound on angles, and the mass bound becomes a
statement about intervals of angles: the measure of an interval of half-width `1 - r` around `θ₀` is
controlled by the value of the function at the radius point. -/

/-- **Chord is at most arc.**  The unit circle map is `1`-Lipschitz. -/
theorem norm_circleMap_sub_circleMap_le (θ θ₀ : ℝ) :
    ‖circleMap 0 1 θ - circleMap 0 1 θ₀‖ ≤ |θ - θ₀| := by
  have h := (lipschitzWith_circleMap (0 : ℂ) 1).dist_le_mul θ θ₀
  rw [Complex.dist_eq, Real.dist_eq] at h
  simpa using h

/-- **The interval mass bound.**  The measure of the angle interval of half-width `1 - r` centred at
`θ₀` is controlled by the value of the function at the radius point. -/
theorem measureReal_Icc_le {ν : Measure ℝ} [IsFiniteMeasure ν] {u : ℂ → ℝ}
    (hrep : ∀ w ∈ ball (0 : ℂ) 1, ∫ θ, poissonKernel 0 w (circleMap 0 1 θ) ∂ν = u w)
    (θ₀ : ℝ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    ν.real (Set.Icc (θ₀ - (1 - r)) (θ₀ + (1 - r))) * ((1 + r) / (4 * (1 - r)))
      ≤ u ((r : ℂ) * circleMap 0 1 θ₀) := by
  refine measureReal_le_of_close hrep θ₀ hr hr1 measurableSet_Icc fun θ hθ => ?_
  refine (norm_circleMap_sub_circleMap_le θ θ₀).trans ?_
  rw [abs_le]
  constructor
  · linarith [hθ.1]
  · linarith [hθ.2]

/-- **Linear decay of local mass.**  If the function is bounded on the radius through `θ₀`, the
measure of the shrinking interval of half-width `1 - r` decays linearly in `1 - r`.  This is
strictly stronger than the absence of an atom at `θ₀`. -/
theorem measureReal_Icc_le_of_bddAbove {ν : Measure ℝ} [IsFiniteMeasure ν] {u : ℂ → ℝ}
    (hrep : ∀ w ∈ ball (0 : ℂ) 1, ∫ θ, poissonKernel 0 w (circleMap 0 1 θ) ∂ν = u w)
    (θ₀ : ℝ) {M : ℝ} (hM : ∀ r : ℝ, 0 ≤ r → r < 1 → u ((r : ℂ) * circleMap 0 1 θ₀) ≤ M)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    ν.real (Set.Icc (θ₀ - (1 - r)) (θ₀ + (1 - r))) ≤ 4 * M * (1 - r) := by
  have h1 : (0 : ℝ) < 1 - r := by linarith
  have hnn0 : 0 ≤ ν.real (Set.Icc (θ₀ - (1 - r)) (θ₀ + (1 - r))) := measureReal_nonneg
  have hkey := (measureReal_Icc_le hrep θ₀ hr hr1).trans (hM r hr hr1)
  have hM0 : 0 ≤ M := by
    have hnn1 : 0 ≤ ν.real (Set.Icc (θ₀ - 1) (θ₀ + 1)) := measureReal_nonneg
    have h0 := (measureReal_Icc_le hrep θ₀ le_rfl (by norm_num : (0 : ℝ) < 1)).trans
      (hM 0 le_rfl (by norm_num))
    norm_num at h0
    linarith
  have hkey' : ν.real (Set.Icc (θ₀ - (1 - r)) (θ₀ + (1 - r))) * (1 + r) ≤ M * (4 * (1 - r)) := by
    rw [mul_div_assoc'] at hkey
    rwa [div_le_iff₀ (by positivity)] at hkey
  nlinarith [hkey', hnn0, hr, h1, hM0]

/-! ## Toward the arc: the sharp local bound and a covering

The bound is sharper stated at each radius separately rather than against a uniform bound: the mass
of the interval of half-width `1 - r` is at most `4(1-r)` times the value of the function at that
one radius point.  Covering an arc by such intervals then converts the linear rate into a bound
proportional to the length of the arc. -/

/-- **The sharp local bound.**  At each radius separately, the mass of the interval of half-width
`1 - r` around `θ₀` is at most `4(1-r)` times the value at the radius point. -/
theorem measureReal_Icc_le_radial {ν : Measure ℝ} [IsFiniteMeasure ν] {u : ℂ → ℝ}
    (hrep : ∀ w ∈ ball (0 : ℂ) 1, ∫ θ, poissonKernel 0 w (circleMap 0 1 θ) ∂ν = u w)
    (θ₀ : ℝ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    ν.real (Set.Icc (θ₀ - (1 - r)) (θ₀ + (1 - r)))
      ≤ 4 * (1 - r) * u ((r : ℂ) * circleMap 0 1 θ₀) := by
  have h1 : (0 : ℝ) < 1 - r := by linarith
  have hnn0 : 0 ≤ ν.real (Set.Icc (θ₀ - (1 - r)) (θ₀ + (1 - r))) := measureReal_nonneg
  have hkey := measureReal_Icc_le hrep θ₀ hr hr1
  have hkey' : ν.real (Set.Icc (θ₀ - (1 - r)) (θ₀ + (1 - r))) * (1 + r)
      ≤ u ((r : ℂ) * circleMap 0 1 θ₀) * (4 * (1 - r)) := by
    rw [mul_div_assoc'] at hkey
    rwa [div_le_iff₀ (by positivity)] at hkey
  nlinarith [hkey', hnn0, hr, h1]

/-- **A covering of an arc by intervals of half-width `δ`.**  If `N` steps of length `2δ` overshoot
the arc, the `N` intervals centred at the step midpoints cover it. -/
theorem Icc_subset_biUnion_Icc {α β δ : ℝ} (hδ : 0 < δ) {N : ℕ} (hN : β - α < 2 * δ * N) :
    Set.Icc α β ⊆ ⋃ k ∈ Finset.range N,
      Set.Icc (α + 2 * k * δ) (α + 2 * (k + 1) * δ) := by
  intro θ hθ
  obtain ⟨hα, hβ⟩ := hθ
  have hq : 0 ≤ (θ - α) / (2 * δ) := by
    apply div_nonneg (by linarith)
    linarith
  have hklt : ((θ - α) / (2 * δ)) < N := by
    rw [div_lt_iff₀ (by linarith)]
    have : θ - α ≤ β - α := by linarith
    calc θ - α ≤ β - α := this
      _ < 2 * δ * N := hN
      _ = (N : ℝ) * (2 * δ) := by ring
  refine Set.mem_biUnion (Finset.mem_range.mpr ((Nat.floor_lt hq).mpr hklt)) ?_
  constructor
  · have hfl : (⌊(θ - α) / (2 * δ)⌋₊ : ℝ) ≤ (θ - α) / (2 * δ) := Nat.floor_le hq
    rw [le_div_iff₀ (by linarith)] at hfl
    linarith
  · have hfl : (θ - α) / (2 * δ) < (⌊(θ - α) / (2 * δ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [div_lt_iff₀ (by linarith)] at hfl
    linarith

/-- **The arc bound.**  If the function is bounded by `M` on the radius of level `1 - δ` through
every angle, the mass of an arc is at most `4 δ M N`, where `N` steps of length `2δ` overshoot the
arc.  Choosing `N` of order `(β-α)/δ` makes the right-hand side proportional to `M` times the length
of the arc, with no dependence on `δ`. -/
theorem measureReal_Icc_le_of_radial_bound {ν : Measure ℝ} [IsFiniteMeasure ν] {u : ℂ → ℝ}
    (hrep : ∀ w ∈ ball (0 : ℂ) 1, ∫ θ, poissonKernel 0 w (circleMap 0 1 θ) ∂ν = u w)
    {α β M δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {N : ℕ} (hN : β - α < 2 * δ * N)
    (hM : ∀ θ₀ ∈ Set.Icc α (α + 2 * δ * N), u (((1 - δ : ℝ) : ℂ) * circleMap 0 1 θ₀) ≤ M) :
    ν.real (Set.Icc α β) ≤ 4 * δ * M * N := by
  have hr : (0 : ℝ) ≤ 1 - δ := by linarith
  have hr1 : (1 : ℝ) - δ < 1 := by linarith
  have hone : (1 : ℝ) - (1 - δ) = δ := by ring
  have hcover := Icc_subset_biUnion_Icc (α := α) (β := β) hδ hN
  have hmono : ν.real (Set.Icc α β)
      ≤ ν.real (⋃ k ∈ Finset.range N, Set.Icc (α + 2 * k * δ) (α + 2 * (k + 1) * δ)) :=
    measureReal_mono hcover (measure_ne_top ν _)
  refine hmono.trans (((measureReal_biUnion_finset_le _ _).trans ?_))
  have hterm : ∀ k ∈ Finset.range N,
      ν.real (Set.Icc (α + 2 * k * δ) (α + 2 * (k + 1) * δ)) ≤ 4 * δ * M := by
    intro k hk
    have hkN : (k : ℝ) + 1 ≤ N := by
      have := Finset.mem_range.mp hk
      exact_mod_cast this
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hcentre : Set.Icc (α + 2 * k * δ) (α + 2 * (k + 1) * δ)
        = Set.Icc ((α + (2 * k + 1) * δ) - (1 - (1 - δ)))
            ((α + (2 * k + 1) * δ) + (1 - (1 - δ))) := by
      rw [hone]; congr 1 <;> ring
    rw [hcentre]
    refine (measureReal_Icc_le_radial hrep (α + (2 * k + 1) * δ) hr hr1).trans ?_
    rw [hone]
    have := hM (α + (2 * k + 1) * δ) ⟨by nlinarith, by nlinarith⟩
    nlinarith [hδ]
  calc ∑ _k ∈ Finset.range N, ν.real (Set.Icc (α + 2 * _k * δ) (α + 2 * (_k + 1) * δ))
      ≤ ∑ _k ∈ Finset.range N, 4 * δ * M := Finset.sum_le_sum hterm
    _ = 4 * δ * M * N := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- **The arc bound, free of the covering scale.**  Choosing the number of covering intervals of
order `(β-α)/δ` and letting `δ` shrink removes it: a uniform radial bound `M` gives
`nu(arc) <= 2 M |arc|`. -/
theorem measureReal_Icc_le_of_uniform_radial_bound {ν : Measure ℝ} [IsFiniteMeasure ν] {u : ℂ → ℝ}
    (hrep : ∀ w ∈ ball (0 : ℂ) 1, ∫ θ, poissonKernel 0 w (circleMap 0 1 θ) ∂ν = u w)
    {α β M : ℝ} (hαβ : α ≤ β) (hM0 : 0 ≤ M)
    (hM : ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ θ₀ ∈ Set.Icc α (β + 4),
      u (((1 - δ : ℝ) : ℂ) * circleMap 0 1 θ₀) ≤ M) :
    ν.real (Set.Icc α β) ≤ 2 * M * (β - α) := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ : ℝ := min (ε / (8 * M + 1)) (1 / 2) with hδdef
  have hδ : 0 < δ := lt_min (div_pos hε (by linarith)) (by norm_num)
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hq : 0 ≤ (β - α) / (2 * δ) := div_nonneg (by linarith) (by linarith)
  set N : ℕ := ⌈(β - α) / (2 * δ)⌉₊ + 1 with hNdef
  have hqN : (β - α) / (2 * δ) < N := by
    rw [hNdef]
    push_cast
    linarith [Nat.le_ceil ((β - α) / (2 * δ))]
  have hN : β - α < 2 * δ * N := by
    rw [div_lt_iff₀ (by linarith)] at hqN
    linarith
  have hNlt : (N : ℝ) < (β - α) / (2 * δ) + 2 := by
    rw [hNdef]
    push_cast
    linarith [Nat.ceil_lt_add_one hq]
  have hspan : 2 * δ * (N : ℝ) < (β - α) + 4 * δ := by
    have h2 : 2 * δ * (N : ℝ) < 2 * δ * ((β - α) / (2 * δ) + 2) :=
      mul_lt_mul_of_pos_left hNlt (by linarith)
    have hcalc : 2 * δ * ((β - α) / (2 * δ) + 2) = (β - α) + 4 * δ := by field_simp; ring
    linarith
  have hbound := measureReal_Icc_le_of_radial_bound hrep hδ hδ1 hN
    (fun θ₀ hθ₀ => hM δ hδ hδ1 θ₀ ⟨hθ₀.1, by
      have := hθ₀.2
      linarith⟩)
  have hstep : 4 * δ * M * N ≤ 2 * M * (β - α) + 8 * δ * M := by
    have hmul : 4 * δ * M * (N : ℝ) ≤ 4 * δ * M * ((β - α) / (2 * δ) + 2) :=
      mul_le_mul_of_nonneg_left hNlt.le (by positivity)
    have hcalc : 4 * δ * M * ((β - α) / (2 * δ) + 2) = 2 * M * (β - α) + 8 * δ * M := by
      field_simp
      ring
    linarith [hmul, hcalc.le, hcalc.ge]
  have hsmall : 8 * δ * M ≤ ε := by
    have hle : δ ≤ ε / (8 * M + 1) := min_le_left _ _
    have h8 : 8 * δ * M ≤ 8 * (ε / (8 * M + 1)) * M :=
      mul_le_mul_of_nonneg_right (by linarith) hM0
    have hd : (0 : ℝ) < 8 * M + 1 := by linarith
    have hfrac : 8 * (ε / (8 * M + 1)) * M ≤ ε := by
      rw [show 8 * (ε / (8 * M + 1)) * M = 8 * ε * M / (8 * M + 1) by field_simp,
        div_le_iff₀ hd]
      nlinarith [hε.le, hM0]
    linarith
  linarith [hbound, hstep, hsmall]

/-- **Vanishing on an arc.**  If the function admits arbitrarily small uniform radial bounds, the
measure of every arc vanishes.  This is the form the support statement takes: where the function
tends to zero at the boundary, the representing measure puts no mass. -/
theorem measureReal_Icc_eq_zero_of_radial_tendsto_zero {ν : Measure ℝ} [IsFiniteMeasure ν]
    {u : ℂ → ℝ}
    (hrep : ∀ w ∈ ball (0 : ℂ) 1, ∫ θ, poissonKernel 0 w (circleMap 0 1 θ) ∂ν = u w)
    {α β : ℝ} (hαβ : α ≤ β)
    (hsmall : ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ θ₀ ∈ Set.Icc α (β + 4),
      u (((1 - δ : ℝ) : ℂ) * circleMap 0 1 θ₀) ≤ M) :
    ν.real (Set.Icc α β) = 0 := by
  refine le_antisymm ?_ measureReal_nonneg
  rcases eq_or_lt_of_le hαβ with rfl | hlt
  · simpa using measureReal_Icc_le_of_uniform_radial_bound hrep hαβ zero_le_one
      (hsmall 1 one_pos)
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hM : 0 < ε / (2 * (β - α) + 1) := div_pos hε (by linarith)
    have hb := measureReal_Icc_le_of_uniform_radial_bound hrep hαβ hM.le
      (hsmall _ hM)
    have hd : (0 : ℝ) < 2 * (β - α) + 1 := by linarith
    have : 2 * (ε / (2 * (β - α) + 1)) * (β - α) ≤ ε := by
      rw [show 2 * (ε / (2 * (β - α) + 1)) * (β - α)
          = 2 * ε * (β - α) / (2 * (β - α) + 1) by field_simp,
        div_le_iff₀ hd]
      nlinarith [hε.le, hlt]
    linarith

/-! ## From arc vanishing to concentration

A measure that is null on every closed rational interval inside an open set is null on the whole set:
the set is the countable union of those intervals.  Combined with the arc-vanishing theorems this
turns "the function extends across the complement" into "the measure is concentrated on the
exceptional set" — which is how a meromorphic Herglotz function comes to have a purely atomic
representing measure. -/

/-- **Null on rational intervals gives null on the open set.**  Every point of an open set lies in a
closed interval with rational endpoints inside it, and there are only countably many such. -/
theorem measure_eq_zero_of_isOpen_of_rat_Icc {ν : Measure ℝ} {U : Set ℝ} (hU : IsOpen U)
    (h : ∀ p : ℚ × ℚ, Set.Icc (p.1 : ℝ) (p.2 : ℝ) ⊆ U → ν (Set.Icc (p.1 : ℝ) (p.2 : ℝ)) = 0) :
    ν U = 0 := by
  have hcover : U ⊆ ⋃ p : {p : ℚ × ℚ // Set.Icc (p.1 : ℝ) (p.2 : ℝ) ⊆ U},
      Set.Icc ((p.1.1 : ℝ)) ((p.1.2 : ℝ)) := by
    intro x hx
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hU x hx
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show x - ε < x by linarith)
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show x < x + ε by linarith)
    have hmem : Set.Icc ((q : ℝ)) ((r : ℝ)) ⊆ U := by
      intro y hy
      refine hsub ?_
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    exact Set.mem_iUnion.mpr ⟨⟨(q, r), hmem⟩, ⟨le_of_lt hq2, le_of_lt hr1⟩⟩
  refine measure_mono_null hcover (measure_iUnion_null fun p => ?_)
  exact h p.1 p.2

/-- **Concentration on the exceptional set.**  If the measure is null on every closed rational
interval avoiding a closed set, it is concentrated there. -/
theorem measure_compl_eq_zero_of_rat_Icc {ν : Measure ℝ} {S : Set ℝ} (hS : IsClosed S)
    (h : ∀ p : ℚ × ℚ, Set.Icc (p.1 : ℝ) (p.2 : ℝ) ⊆ Sᶜ → ν (Set.Icc (p.1 : ℝ) (p.2 : ℝ)) = 0) :
    ν Sᶜ = 0 :=
  measure_eq_zero_of_isOpen_of_rat_Icc hS.isOpen_compl h

end GaloisForLFunctions.HTGeometry
