import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatConvexRigidity
import GaloisForLFunctions.HTGeometry.EuclideanCompactStokes

/-!
# Quasiconvexity of the flat loss under genuine gradient variations

Compactly supported C¹ perturbations have zero mean directional derivative.
The flat convex potential therefore has nonnegative excess action around
every affine background. The excess controls gradient displacement, and
its exact zero set records the potential's entire flat half-line.
-/

open MeasureTheory Filter
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
open HTGeometry
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Genuine compactly supported differentiable test functions. -/
abbrev CompactVariation (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  {u : E → ℝ // ContDiff ℝ 1 u ∧ HasCompactSupport u}

def variationSlope (u : CompactVariation E) (w : E) (x : E) : ℝ :=
  fderiv ℝ u.val x w

private theorem variationSlope_continuous (u : CompactVariation E) (w : E) :
    Continuous (variationSlope u w) :=
  (u.property.1.continuous_fderiv one_ne_zero).clm_apply continuous_const

private theorem variationSlope_compact (u : CompactVariation E) (w : E) :
    HasCompactSupport (variationSlope u w) :=
  (u.property.2.fderiv ℝ).comp_left (g := fun L : E →L[ℝ] ℝ => L w) rfl

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Excess action of an actual directional gradient perturbation of an affine background. -/
def flatVariationAction (a : ℝ) (u : CompactVariation E) (w : E) : ℝ :=
  ∫ x, potential (a + variationSlope u w x) - potential a ∂μ

/-- Compact support makes the excess integrable even when the affine background is nonzero. -/
theorem flatVariationAction_integrable (a : ℝ) (u : CompactVariation E) (w : E) :
    Integrable (fun x => potential (a + variationSlope u w x) - potential a) μ := by
  have hc : Continuous (fun x => potential (a + variationSlope u w x) - potential a) :=
    ((potential_contDiff 0).continuous.comp (continuous_const.add
      (variationSlope_continuous u w))).sub continuous_const
  exact hc.integrable_of_hasCompactSupport
    ((variationSlope_compact u w).comp_left
      (g := fun t => potential (a + t) - potential a) (by simp))

private theorem slope_integrable (u : CompactVariation E) (w : E) :
    Integrable (variationSlope u w) μ :=
  (variationSlope_continuous u w).integrable_of_hasCompactSupport (variationSlope_compact u w)

/-- Stokes cancels the affine tangent term exactly. -/
theorem flatVariationAction_tangent (a : ℝ) (u : CompactVariation E) (w : E) :
    flatVariationAction μ a u w =
      ∫ x, potential (a + variationSlope u w x) - potential a -
        gradient a * variationSlope u w x ∂μ := by
  rw [integral_sub (flatVariationAction_integrable μ a u w) ((slope_integrable μ u w).const_mul _),
    integral_const_mul]
  have hz : (∫ x, variationSlope u w x ∂μ) = 0 :=
    integral_fderiv_apply_eq_zero_of_hasCompactSupport μ u.property.1 u.property.2 w
  rw [hz, mul_zero, sub_zero]
  rfl

/-- The affine background minimizes the action under every compactly supported variation. -/
theorem flatVariationAction_nonneg (a : ℝ) (u : CompactVariation E) (w : E) :
    0 ≤ flatVariationAction μ a u w := by
  rw [flatVariationAction_tangent]
  apply integral_nonneg
  intro x
  change (0 : ℝ) ≤ potential (a + variationSlope u w x) - potential a -
    gradient a * variationSlope u w x
  have h := (tangent_error_bounds (a + variationSlope u w x) a).1
  have he : a + variationSlope u w x - a = variationSlope u w x := by ring
  simpa only [he] using h

/-- The quasiconvexity gap controls the full squared nonlinear gradient displacement. -/
theorem flatVariationAction_gradient_budget (a : ℝ) (u : CompactVariation E) (w : E) :
    (∫ x, (gradient (a + variationSlope u w x) - gradient a) ^ 2 ∂μ) / 2 ≤
      flatVariationAction μ a u w := by
  have hg : Integrable (fun x => (gradient (a + variationSlope u w x) - gradient a) ^ 2) μ := by
    have hc : Continuous (fun x => (gradient (a + variationSlope u w x) - gradient a) ^ 2) :=
      (((gradient_contDiff 0).continuous.comp (continuous_const.add
        (variationSlope_continuous u w))).sub continuous_const).pow 2
    exact hc.integrable_of_hasCompactSupport
      ((variationSlope_compact u w).comp_left
        (g := fun t => (gradient (a + t) - gradient a) ^ 2) (by simp))
  rw [flatVariationAction_tangent, ← integral_div]
  apply integral_mono (hg.div_const 2)
    ((flatVariationAction_integrable μ a u w).sub ((slope_integrable μ u w).const_mul _))
  intro x
  change (gradient (a + variationSlope u w x) - gradient a) ^ 2 / 2 ≤
    potential (a + variationSlope u w x) - potential a - gradient a * variationSlope u w x
  have h := gradient_displacement_le_tangent_error (a + variationSlope u w x) a
  have he : a + variationSlope u w x - a = variationSlope u w x := by ring
  simpa only [he] using h

/-- Zero excess occurs exactly when each slope is unchanged or stays inside the flat region. -/
theorem flatVariationAction_zero_iff (a : ℝ) (u : CompactVariation E) (w : E) :
    flatVariationAction μ a u w = 0 ↔
      ∀ᵐ x ∂μ, variationSlope u w x = 0 ∨
        (a + variationSlope u w x ≤ 0 ∧ a ≤ 0) := by
  have hi := (flatVariationAction_integrable μ a u w).sub ((slope_integrable μ u w).const_mul (gradient a))
  have hn : ∀ᵐ x ∂μ, 0 ≤ potential (a + variationSlope u w x) - potential a -
      gradient a * variationSlope u w x := by
    filter_upwards with x
    have h := (tangent_error_bounds (a + variationSlope u w x) a).1
    have he : a + variationSlope u w x - a = variationSlope u w x := by ring
    simpa only [he] using h
  rw [flatVariationAction_tangent, integral_eq_zero_iff_of_nonneg_ae hn hi]
  apply Filter.eventually_congr
  filter_upwards with x
  simp only [Pi.zero_apply]
  have he : a + variationSlope u w x - a = variationSlope u w x := by ring
  have h := tangent_error_zero_iff (a + variationSlope u w x) a
  rw [he] at h
  rw [h]
  constructor
  · rintro (hz | hz)
    · exact Or.inl (by linarith only [hz])
    · exact Or.inr hz
  · rintro (hz | hz)
    · exact Or.inl (by rw [hz, add_zero])
    · exact Or.inr hz

#print axioms flatVariationAction_tangent
#print axioms flatVariationAction_nonneg
#print axioms flatVariationAction_gradient_budget
#print axioms flatVariationAction_zero_iff
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
