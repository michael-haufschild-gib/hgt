import GaloisForLFunctions.HTGeometry.EinastoInformationCurvature

/-!
# Unconditional Einasto horizon existence and horizon identities

Applies sections 4.1 and 6 of arXiv:2608.23600v1 to the actual integrated
Einasto mass. For every positive length, shape, prescribed radius, and negative
lapse depth, an explicit positive central density gives two separated positive
lapse zeros. The proof uses continuity and the flat limits at the center and
infinity, without numerical root finding or a horizon-existence hypothesis.

Selected roots support closed enclosed-mass, curvature, actual derivative,
and signed-temperature identities. Their information curvature is strictly
below the central bound, connecting to arXiv:2608.06941v1. Existence of these
two roots does not by itself assert uniqueness or classify all lapse zeros.
The labels inner and outer refer to their order around the prescribed radius;
the temperature identity is a signed derivative expression.
-/

noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem einastoDensity_amplitude (d l a r : ℝ) :
    einastoDensity d l a r = exp d * einastoDensity 0 l a r := by
  simp [einastoDensity]

theorem einastoCore_amplitude (d l a r : ℝ) :
    einastoCore d l a r = exp d * einastoCore 0 l a r := by
  unfold einastoCore
  simp only [einastoDensity_amplitude d l a]
  have he : (fun u : ℝ => u ^ 2 * (exp d * einastoDensity 0 l a (r * u))) =
      (fun u => exp d * (u ^ 2 * einastoDensity 0 l a (r * u))) := by
    funext u
    ring
  rw [he, intervalIntegral.integral_const_mul]
  ring

theorem einastoMetric_asymptotically_flat (d l a : ℝ) :
    Tendsto (einastoMetric d l a) atTop (𝓝 1) := by
  unfold einastoMetric
  convert (tendsto_const_nhds (x := (1 : ℝ))).sub
    (((einastoMass_total d l a).const_mul 2).div_atTop tendsto_id) using 1 <;> simp

/-- The density placing the lapse at any prescribed negative depth and positive radius. -/
def einastoTwoHorizonDensity (l a t v : ℝ) : ℝ :=
  log ((1 + exp v) / (2 * exp t ^ 2 * einastoCore 0 l a (exp t)))

theorem einastoTwoHorizonDensity_negative_lapse (l a t v : ℝ) :
    einastoMetric (einastoTwoHorizonDensity l a t v) l a (exp t) = -exp v := by
  have hp : 0 < (1 + exp v) / (2 * exp t ^ 2 * einastoCore 0 l a (exp t)) :=
    div_pos (by positivity) (mul_pos (by positivity) (einastoCore_pos 0 l a t))
  rw [einastoMetric_core, einastoCore_amplitude, einastoTwoHorizonDensity, exp_log hp]
  have hn := (einastoCore_pos 0 l a t).ne'
  field_simp
  ring

/-- Every positive shape and length admits two distinct positive lapse zeros. -/
theorem einastoTwoHorizonDensity_two_horizons (l a t v : ℝ) :
    ∃ inner outer : ℝ, 0 < inner ∧ inner < exp t ∧ exp t < outer ∧
      einastoMetric (einastoTwoHorizonDensity l a t v) l a inner = 0 ∧
      einastoMetric (einastoTwoHorizonDensity l a t v) l a outer = 0 := by
  let d := einastoTwoHorizonDensity l a t v
  have hc := einastoMetric_continuous d l a
  have h0 := einastoMetric_zero d l a
  have hn : einastoMetric d l a (exp t) = -exp v := einastoTwoHorizonDensity_negative_lapse l a t v
  have hp : ∀ᶠ r in atTop, 0 < einastoMetric d l a r :=
    (einastoMetric_asymptotically_flat d l a).eventually (eventually_gt_nhds zero_lt_one)
  obtain ⟨R, hRp, hRt⟩ := (hp.and (eventually_gt_atTop (exp t))).exists
  obtain ⟨inner, hi, hif⟩ := intermediate_value_Icc' (exp_pos t).le hc.continuousOn
    (show (0 : ℝ) ∈ Icc (einastoMetric d l a (exp t)) (einastoMetric d l a 0) by
      rw [hn, h0]; exact ⟨(neg_neg_of_pos (exp_pos v)).le, zero_le_one⟩)
  obtain ⟨outer, ho, hof⟩ := intermediate_value_Icc hRt.le hc.continuousOn
    (show (0 : ℝ) ∈ Icc (einastoMetric d l a (exp t)) (einastoMetric d l a R) by
      rw [hn]; exact ⟨(neg_neg_of_pos (exp_pos v)).le, hRp.le⟩)
  have hi0 : 0 < inner := by
    by_contra h
    have he : inner = 0 := le_antisymm (le_of_not_gt h) hi.1
    rw [he, h0] at hif
    exact one_ne_zero hif
  have hit : inner < exp t := by
    by_contra h
    have he : inner = exp t := le_antisymm hi.2 (le_of_not_gt h)
    rw [he, hn] at hif
    linarith [exp_pos v]
  have hot : exp t < outer := by
    by_contra h
    have he : outer = exp t := le_antisymm (le_of_not_gt h) ho.1
    rw [he, hn] at hof
    linarith [exp_pos v]
  exact ⟨inner, outer, hi0, hit, hot, hif, hof⟩

/-- Two actual roots, selected from the unconditional existence theorem. -/
def einastoHorizonPair (l a t v : ℝ) : ℝ × ℝ :=
  (Classical.choose (einastoTwoHorizonDensity_two_horizons l a t v),
    Classical.choose (Classical.choose_spec (einastoTwoHorizonDensity_two_horizons l a t v)))

theorem einastoHorizonPair_spec (l a t v : ℝ) :
    0 < (einastoHorizonPair l a t v).1 ∧ (einastoHorizonPair l a t v).1 < exp t ∧
      exp t < (einastoHorizonPair l a t v).2 ∧
      einastoMetric (einastoTwoHorizonDensity l a t v) l a (einastoHorizonPair l a t v).1 = 0 ∧
      einastoMetric (einastoTwoHorizonDensity l a t v) l a (einastoHorizonPair l a t v).2 = 0 := by
  exact Classical.choose_spec (Classical.choose_spec (einastoTwoHorizonDensity_two_horizons l a t v))

/-- Select the root inside (`true`) or outside (`false`) the prescribed negative-lapse radius. -/
def einastoSelectedHorizon (l a t v : ℝ) (inner : Bool) : ℝ :=
  if inner then (einastoHorizonPair l a t v).1 else (einastoHorizonPair l a t v).2

theorem einastoSelectedHorizon_spec (l a t v : ℝ) (inner : Bool) :
    0 < einastoSelectedHorizon l a t v inner ∧
      einastoMetric (einastoTwoHorizonDensity l a t v) l a (einastoSelectedHorizon l a t v inner) = 0 := by
  have h := einastoHorizonPair_spec l a t v
  cases inner
  · exact ⟨(exp_pos t).trans h.2.2.1, h.2.2.2.2⟩
  · exact ⟨h.1, h.2.2.2.1⟩

/-- The integrated source has precisely half the radius as enclosed mass at either root. -/
theorem einastoSelectedHorizon_mass (l a t v : ℝ) (inner : Bool) :
    einastoMass (einastoTwoHorizonDensity l a t v) l a (einastoSelectedHorizon l a t v inner) =
      einastoSelectedHorizon l a t v inner / 2 := by
  obtain ⟨hp, hf⟩ := einastoSelectedHorizon_spec l a t v inner
  unfold einastoMetric at hf
  have hn := hp.ne'
  field_simp at hf ⊢
  linarith

/-- The information-curvature formula specializes at actual regular-source horizons. -/
theorem einastoSelectedHorizon_curvature (l a t v : ℝ) (inner : Bool) :
    einastoInformationCurvature (einastoTwoHorizonDensity l a t v) l a
      (einastoSelectedHorizon l a t v inner) = 1 / einastoSelectedHorizon l a t v inner ^ 2 := by
  obtain ⟨hp, hf⟩ := einastoSelectedHorizon_spec l a t v inner
  simpa only [exp_log hp, hf, sub_zero] using
    einastoInformationCurvature_metric (einastoTwoHorizonDensity l a t v) l a
      (log (einastoSelectedHorizon l a t v inner))

/-- Actual lapse derivative at each constructed horizon, including the density correction. -/
theorem einastoSelectedHorizon_derivative (l a t v : ℝ) (inner : Bool) :
    HasDerivAt (einastoMetric (einastoTwoHorizonDensity l a t v) l a)
      (1 / einastoSelectedHorizon l a t v inner -
        8 * Real.pi * einastoSelectedHorizon l a t v inner *
          einastoDensity (einastoTwoHorizonDensity l a t v) l a (einastoSelectedHorizon l a t v inner))
      (einastoSelectedHorizon l a t v inner) := by
  have hp := (einastoSelectedHorizon_spec l a t v inner).1
  have h := einastoMetric_derivative (einastoTwoHorizonDensity l a t v) l a
    (log (einastoSelectedHorizon l a t v inner))
  rw [exp_log hp, einastoSelectedHorizon_mass] at h
  apply h.congr_deriv
  have hn := hp.ne'
  field_simp

/-- The signed temperature expression in equation (16), evaluated at actual lapse zeros. -/
theorem einastoSelectedHorizon_temperature (l a t v : ℝ) (inner : Bool) :
    deriv (einastoMetric (einastoTwoHorizonDensity l a t v) l a)
      (einastoSelectedHorizon l a t v inner) / (4 * Real.pi) =
        1 / (4 * Real.pi * einastoSelectedHorizon l a t v inner) -
          2 * einastoSelectedHorizon l a t v inner *
            einastoDensity (einastoTwoHorizonDensity l a t v) l a (einastoSelectedHorizon l a t v inner) := by
  rw [(einastoSelectedHorizon_derivative l a t v inner).deriv]
  have hn := (einastoSelectedHorizon_spec l a t v inner).1.ne'
  field_simp
  ring

/-- Regular-source curvature at either horizon is strictly below the central ceiling. -/
theorem einastoSelectedHorizon_central_bound (l a t v : ℝ) (inner : Bool) :
    1 / einastoSelectedHorizon l a t v inner ^ 2 <
      8 * Real.pi * exp (einastoTwoHorizonDensity l a t v) / 3 := by
  have hp := (einastoSelectedHorizon_spec l a t v inner).1
  have h := (einastoInformationCurvature_global_bounds (einastoTwoHorizonDensity l a t v) l a
    (log (einastoSelectedHorizon l a t v inner))).2
  simpa only [exp_log hp, einastoSelectedHorizon_curvature] using h

end GaloisForLFunctions.HTGeometry
