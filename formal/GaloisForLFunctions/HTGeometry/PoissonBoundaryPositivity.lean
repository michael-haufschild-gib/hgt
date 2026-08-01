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

end GaloisForLFunctions.HTGeometry
