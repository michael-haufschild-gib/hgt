import GaloisForLFunctions.HTGeometry.GomesHausdorffUniformSource
import GaloisForLFunctions.RHTower.GomesClarkCollapsedRange

/-!
# Diffuse endpoint powers and the sharp inverse-source threshold

The finite sources with density `(1 - y)^a`, for `a > -1`, have no atoms. Removing the collapsed
Clark weight shifts the exponent to `a - 1`, so its inverse is finite precisely for `a > 0`.
This gives a continuum of realizable and unrealizable diffuse observation sources for the
reconstruction experiments motivated by arXiv:2607.24901.
-/

noncomputable section
open MeasureTheory GaloisForLFunctions.HTGeometry
open scoped NNReal ENNReal

namespace RHTower

/-- A real endpoint-power density on the compact source interval. -/
def gomesClarkEndpointDensity (a : ℝ) (y : HausdorffSourceSpace) : ℝ := (1 - (y : ℝ)) ^ a

/-- Endpoint powers remain measurable even when they are unbounded near the endpoint. -/
theorem gomesClarkEndpointDensity_measurable (a : ℝ) : Measurable (gomesClarkEndpointDensity a) :=
  (measurable_const.sub measurable_subtype_coe).pow_const a

/-- Every endpoint-power density is nonnegative. -/
theorem gomesClarkEndpointDensity_nonneg (a : ℝ) (y : HausdorffSourceSpace) :
    0 ≤ gomesClarkEndpointDensity a y := Real.rpow_nonneg (sub_nonneg.mpr y.property.2) a

/-- Exact finite-integral threshold for the endpoint density. -/
theorem gomesClarkEndpointDensity_integrable_iff (a : ℝ) :
    Integrable (gomesClarkEndpointDensity a)
      (gomesHausdorffUniformSource : Measure HausdorffSourceSpace) ↔ -1 < a :=
  gomesHausdorffUniformSource_complement_rpow_integrable_iff a

/-- The entire finite diffuse family, with its admissible exponent packaged as data. -/
def gomesClarkEndpointPowerSource (a : Set.Ioi (-1 : ℝ)) : FiniteMeasure HausdorffSourceSpace :=
  ⟨(gomesHausdorffUniformSource : Measure HausdorffSourceSpace).withDensity
    (fun y => ENNReal.ofReal (gomesClarkEndpointDensity a y)),
    isFiniteMeasure_withDensity_ofReal
      ((gomesClarkEndpointDensity_integrable_iff a).mpr a.property).2⟩

/-- The zero exponent is exactly the uniform source. -/
theorem gomesClarkEndpointPowerSource_zero :
    gomesClarkEndpointPowerSource ⟨0, by simp⟩ = gomesHausdorffUniformSource := by
  apply FiniteMeasure.toMeasure_injective
  change (gomesHausdorffUniformSource : Measure HausdorffSourceSpace).withDensity
    (fun y => ENNReal.ofReal ((1 - (y : ℝ)) ^ (0 : ℝ))) = _
  simp only [Real.rpow_zero, ENNReal.ofReal_one]
  exact withDensity_one

/-- Every power source is atom-free, including at the singular endpoint. -/
theorem gomesClarkEndpointPowerSource_singleton (a : Set.Ioi (-1 : ℝ)) (y : HausdorffSourceSpace) :
    (gomesClarkEndpointPowerSource a : Measure HausdorffSourceSpace) {y} = 0 := by
  change ((gomesHausdorffUniformSource : Measure HausdorffSourceSpace).withDensity
    (fun y => ENNReal.ofReal (gomesClarkEndpointDensity a y))) {y} = 0
  rw [withDensity_apply _ (measurableSet_singleton _), lintegral_singleton]
  change _ * volume ({y} : Set HausdorffSourceSpace) = 0
  simp

/-- All real integrals transport to uniform volume with the literal power density. -/
theorem gomesClarkEndpointPowerSource_integral (a : Set.Ioi (-1 : ℝ))
    (f : HausdorffSourceSpace → ℝ) :
    (∫ y, f y ∂(gomesClarkEndpointPowerSource a : Measure HausdorffSourceSpace)) =
      ∫ y, gomesClarkEndpointDensity a y * f y
        ∂(gomesHausdorffUniformSource : Measure HausdorffSourceSpace) := by
  change (∫ y, f y ∂(gomesHausdorffUniformSource : Measure HausdorffSourceSpace).withDensity
    (fun y => ENNReal.ofReal (gomesClarkEndpointDensity a y))) = _
  rw [integral_withDensity_eq_integral_toReal_smul (gomesClarkEndpointDensity_measurable a).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (gomesClarkEndpointDensity_nonneg a _), smul_eq_mul]

/-- Integrability transports through the density without extra premises on the test. -/
theorem gomesClarkEndpointPowerSource_integrable_iff (a : Set.Ioi (-1 : ℝ))
    (f : HausdorffSourceSpace → ℝ) :
    Integrable f (gomesClarkEndpointPowerSource a : Measure HausdorffSourceSpace) ↔
      Integrable (fun y => gomesClarkEndpointDensity a y * f y)
        (gomesHausdorffUniformSource : Measure HausdorffSourceSpace) := by
  change Integrable f ((gomesHausdorffUniformSource : Measure HausdorffSourceSpace).withDensity
    (fun y => ENNReal.ofReal (gomesClarkEndpointDensity a y))) ↔ _
  rw [integrable_withDensity_iff_integrable_smul' (gomesClarkEndpointDensity_measurable a).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (gomesClarkEndpointDensity_nonneg a _), smul_eq_mul]

/-- Removing one collapsed weight shifts the power exponent by exactly one almost everywhere. -/
theorem gomesClarkEndpointDensity_inverse_product (a : ℝ) :
    (fun y => gomesClarkEndpointDensity a y * gomesClarkCollapsedInverseWeight y) =ᵐ[
      (gomesHausdorffUniformSource : Measure HausdorffSourceSpace)] gomesClarkEndpointDensity (a - 1) := by
  have hone : ∀ᵐ y ∂(gomesHausdorffUniformSource : Measure HausdorffSourceSpace),
      y ≠ gomesHausdorffOne := by
    change ∀ᵐ y ∂(volume : Measure HausdorffSourceSpace), y ≠ gomesHausdorffOne
    simp [ae_iff]
  filter_upwards [hone] with y hy
  have hy1 : (y : ℝ) ≠ 1 := fun h => hy (Subtype.ext h)
  have hp : 0 < 1 - (y : ℝ) := sub_pos.mpr (lt_of_le_of_ne y.property.2 hy1)
  rw [gomesClarkCollapsedInverseWeight_formula]
  dsimp [gomesClarkEndpointDensity]
  rw [Real.rpow_sub hp, Real.rpow_one]
  ring

/-- The reciprocal-moment threshold is one full exponent stronger than source finiteness. -/
theorem gomesClarkEndpointPowerSource_inverse_integrable_iff (a : Set.Ioi (-1 : ℝ)) :
    Integrable gomesClarkCollapsedInverseWeight
      (gomesClarkEndpointPowerSource a : Measure HausdorffSourceSpace) ↔ 0 < (a : ℝ) := by
  rw [gomesClarkEndpointPowerSource_integrable_iff]
  rw [integrable_congr (gomesClarkEndpointDensity_inverse_product a),
    gomesClarkEndpointDensity_integrable_iff]
  constructor <;> intro h <;> linarith

/-- The whole atom-free family crosses the collapsed-anchor image exactly at exponent zero. -/
theorem gomesClarkEndpointPowerSource_range_iff (a : Set.Ioi (-1 : ℝ)) :
    gomesClarkEndpointPowerSource a ∈ Set.range (gomesClarkWeightedSource 0) ↔ 0 < (a : ℝ) := by
  rw [gomesClarkCollapsed_range_iff, gomesClarkEndpointPowerSource_singleton,
    gomesClarkEndpointPowerSource_inverse_integrable_iff]
  simp

/-- Infinite inverse mass is the exact obstruction for all nonpositive admissible exponents. -/
theorem gomesClarkEndpointPowerSource_inverse_finite_iff (a : Set.Ioi (-1 : ℝ)) :
    IsFiniteMeasure (gomesClarkCollapsedUnweight
      (gomesClarkEndpointPowerSource a : Measure HausdorffSourceSpace)) ↔ 0 < (a : ℝ) := by
  rw [gomesClarkCollapsedUnweight_finite_iff, gomesClarkEndpointPowerSource_inverse_integrable_iff]

/-- The inverse source for a positive exponent is the preceding finite power source. -/
theorem gomesClarkEndpointPowerSource_unweight (a : Set.Ioi (0 : ℝ)) :
    gomesClarkCollapsedUnweight
      (gomesClarkEndpointPowerSource ⟨a, by change (-1 : ℝ) < (a : ℝ); have ha : (0 : ℝ) < a := a.property; linarith⟩ : Measure HausdorffSourceSpace) =
      (gomesClarkEndpointPowerSource ⟨(a : ℝ) - 1, by change (-1 : ℝ) < (a : ℝ) - 1; have ha : (0 : ℝ) < a := a.property; linarith⟩ :
        Measure HausdorffSourceSpace) := by
  change (((gomesHausdorffUniformSource : Measure HausdorffSourceSpace).withDensity
    (fun y => ENNReal.ofReal (gomesClarkEndpointDensity a y))).withDensity
    (fun y => ENNReal.ofReal (gomesClarkCollapsedInverseWeight y))) = _
  rw [← withDensity_mul _ (gomesClarkEndpointDensity_measurable a).ennreal_ofReal
    gomesClarkCollapsedInverseWeight_measurable.ennreal_ofReal]
  apply withDensity_congr_ae
  filter_upwards [gomesClarkEndpointDensity_inverse_product a] with y hy
  simp only [Pi.mul_apply, ← ENNReal.ofReal_mul (gomesClarkEndpointDensity_nonneg a y)]
  exact congrArg ENNReal.ofReal hy

end RHTower
