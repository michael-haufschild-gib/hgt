import GaloisForLFunctions.RHTower.GomesClarkAnchorCalibration

/-!
# Exact range of the collapsed Clark anchor

The invisible endpoint is only part of the reconstruction obstruction. The weighted finite
sources attainable at the zero anchor are precisely those with no endpoint-one atom and an
integrable reciprocal weight. Unweighting cancels the density off that endpoint, leaving the
literal restricted source. This extends the reconstruction / invisible-sector experiments
motivated by arXiv:2607.24901 without adding analytic hypotheses to the classification.
-/

noncomputable section
open MeasureTheory GaloisForLFunctions.HTGeometry
open scoped NNReal ENNReal

namespace RHTower

/-- Reciprocal collapsed density, with the field convention of value zero at the blind endpoint. -/
def gomesClarkCollapsedInverseWeight (y : HausdorffSourceSpace) : ℝ :=
  (gomesClarkSourceWeight 0 y)⁻¹

/-- The reciprocal density is measurable, although it need not be bounded. -/
theorem gomesClarkCollapsedInverseWeight_measurable : Measurable gomesClarkCollapsedInverseWeight :=
  (gomesClarkSourceWeight 0).continuous.measurable.inv

/-- The reciprocal collapsed density is everywhere nonnegative. -/
theorem gomesClarkCollapsedInverseWeight_nonneg (y : HausdorffSourceSpace) :
    0 ≤ gomesClarkCollapsedInverseWeight y := inv_nonneg.mpr (gomesClarkSourceWeight_nonneg 0 y)

/-- Weighting on arbitrary measures, needed to distinguish finite and infinite inverse sources. -/
def gomesClarkCollapsedWeight (μ : Measure HausdorffSourceSpace) : Measure HausdorffSourceSpace :=
  μ.withDensity (fun y => ENNReal.ofReal (gomesClarkSourceWeight 0 y))

/-- The canonical inverse source may have infinite mass, so its finiteness must be characterized. -/
def gomesClarkCollapsedUnweight (μ : Measure HausdorffSourceSpace) : Measure HausdorffSourceSpace :=
  μ.withDensity (fun y => ENNReal.ofReal (gomesClarkCollapsedInverseWeight y))

/-- The extended-density product is exactly the indicator of the visible complement. -/
theorem gomesClarkCollapsed_density_product :
    (fun y => ENNReal.ofReal (gomesClarkSourceWeight 0 y)) *
      (fun y => ENNReal.ofReal (gomesClarkCollapsedInverseWeight y)) =
      ({gomesHausdorffOne}ᶜ : Set HausdorffSourceSpace).indicator 1 := by
  classical
  funext y
  by_cases hy : y = gomesHausdorffOne
  · simp [hy, gomesClarkSourceWeight, gomesHausdorffOne]
  · have hw : gomesClarkSourceWeight 0 y ≠ 0 := by
      intro h
      exact hy ((gomesClarkSourceWeight_zero_iff 0 y).mp h).2
    rw [Set.indicator_of_mem (by simpa using hy)]
    simp only [Pi.mul_apply, Pi.one_apply, ← ENNReal.ofReal_mul (gomesClarkSourceWeight_nonneg 0 y)]
    change ENNReal.ofReal (gomesClarkSourceWeight 0 y * (gomesClarkSourceWeight 0 y)⁻¹) = 1
    rw [mul_inv_cancel₀ hw, ENNReal.ofReal_one]

/-- Unweighting a collapsed source recovers exactly the source off its invisible endpoint. -/
theorem gomesClarkCollapsedUnweight_weight (μ : Measure HausdorffSourceSpace) :
    gomesClarkCollapsedUnweight (gomesClarkCollapsedWeight μ) = μ.restrict {gomesHausdorffOne}ᶜ := by
  rw [gomesClarkCollapsedUnweight, gomesClarkCollapsedWeight,
    ← withDensity_mul _ (gomesClarkSourceWeight 0).continuous.measurable.ennreal_ofReal
      gomesClarkCollapsedInverseWeight_measurable.ennreal_ofReal,
    gomesClarkCollapsed_density_product, withDensity_indicator_one (measurableSet_singleton _).compl]

/-- The reverse cancellation removes the same endpoint, even for an infinite measure. -/
theorem gomesClarkCollapsedWeight_unweight (μ : Measure HausdorffSourceSpace) :
    gomesClarkCollapsedWeight (gomesClarkCollapsedUnweight μ) = μ.restrict {gomesHausdorffOne}ᶜ := by
  rw [gomesClarkCollapsedWeight, gomesClarkCollapsedUnweight,
    ← withDensity_mul _ gomesClarkCollapsedInverseWeight_measurable.ennreal_ofReal
      (gomesClarkSourceWeight 0).continuous.measurable.ennreal_ofReal,
    mul_comm, gomesClarkCollapsed_density_product,
    withDensity_indicator_one (measurableSet_singleton _).compl]

/-- Every collapsed weighted source has zero mass at the blind endpoint. -/
theorem gomesClarkCollapsedWeight_one (μ : Measure HausdorffSourceSpace) :
    gomesClarkCollapsedWeight μ {gomesHausdorffOne} = 0 := by
  rw [gomesClarkCollapsedWeight, withDensity_apply _ (measurableSet_singleton _), lintegral_singleton]
  simp [gomesClarkSourceWeight, gomesHausdorffOne]

/-- The canonical inverse also puts no mass at the blind endpoint. -/
theorem gomesClarkCollapsedUnweight_one (μ : Measure HausdorffSourceSpace) :
    gomesClarkCollapsedUnweight μ {gomesHausdorffOne} = 0 := by
  rw [gomesClarkCollapsedUnweight, withDensity_apply _ (measurableSet_singleton _), lintegral_singleton]
  simp [gomesClarkCollapsedInverseWeight, gomesClarkSourceWeight, gomesHausdorffOne]

/-- Finiteness of the inverse source is exactly the reciprocal-moment integrability condition. -/
theorem gomesClarkCollapsedUnweight_finite_iff (μ : Measure HausdorffSourceSpace) :
    IsFiniteMeasure (gomesClarkCollapsedUnweight μ) ↔ Integrable gomesClarkCollapsedInverseWeight μ := by
  have h : Integrable (fun _ : HausdorffSourceSpace => (1 : ℝ)) (gomesClarkCollapsedUnweight μ) ↔
      Integrable gomesClarkCollapsedInverseWeight μ := by
    change Integrable (fun _ : HausdorffSourceSpace => (1 : ℝ))
      (μ.withDensity (fun y => ENNReal.ofReal (gomesClarkCollapsedInverseWeight y))) ↔ _
    rw [integrable_withDensity_iff_integrable_smul'
      gomesClarkCollapsedInverseWeight_measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (gomesClarkCollapsedInverseWeight_nonneg _), smul_eq_mul, mul_one]
  exact (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : ℝ) ≠ 0)).symm.trans h

/-- The literal inverse weight on the interval is `1 / (1 - y)`. -/
theorem gomesClarkCollapsedInverseWeight_formula (y : HausdorffSourceSpace) :
    gomesClarkCollapsedInverseWeight y = 1 / (1 - (y : ℝ)) := by
  simp [gomesClarkCollapsedInverseWeight, gomesClarkSourceWeight, one_div, sub_eq_add_neg]

/-- A finite source's weighted image always has the finite reciprocal moment required to undo it. -/
theorem gomesClarkCollapsed_inverse_integrable (μ : FiniteMeasure HausdorffSourceSpace) :
    Integrable gomesClarkCollapsedInverseWeight
      (gomesClarkWeightedSource 0 μ : Measure HausdorffSourceSpace) := by
  apply (gomesClarkCollapsedUnweight_finite_iff _).mp
  change IsFiniteMeasure (gomesClarkCollapsedUnweight (gomesClarkCollapsedWeight (μ : Measure HausdorffSourceSpace)))
  rw [gomesClarkCollapsedUnweight_weight]
  infer_instance

/-- Exact attainable range: absence of the blind atom and finiteness of the inverse moment. -/
theorem gomesClarkCollapsed_range_iff (ν : FiniteMeasure HausdorffSourceSpace) :
    ν ∈ Set.range (gomesClarkWeightedSource 0) ↔
      (ν : Measure HausdorffSourceSpace) {gomesHausdorffOne} = 0 ∧
        Integrable gomesClarkCollapsedInverseWeight (ν : Measure HausdorffSourceSpace) := by
  constructor
  · rintro ⟨μ, rfl⟩
    exact ⟨gomesClarkCollapsedWeight_one _, gomesClarkCollapsed_inverse_integrable μ⟩
  · rintro ⟨hz, hi⟩
    let μ : FiniteMeasure HausdorffSourceSpace :=
      ⟨gomesClarkCollapsedUnweight (ν : Measure HausdorffSourceSpace),
        (gomesClarkCollapsedUnweight_finite_iff _).mpr hi⟩
    refine ⟨μ, FiniteMeasure.toMeasure_injective ?_⟩
    change gomesClarkCollapsedWeight (gomesClarkCollapsedUnweight (ν : Measure HausdorffSourceSpace)) = _
    rw [gomesClarkCollapsedWeight_unweight]
    have hr := Measure.restrict_add_restrict_compl (μ := (ν : Measure HausdorffSourceSpace))
      (measurableSet_singleton gomesHausdorffOne)
    rw [Measure.restrict_eq_zero.mpr hz, zero_add] at hr
    exact hr

/-- The range condition can be read as the literal reciprocal endpoint moment. -/
theorem gomesClarkCollapsed_range_iff_reciprocal (ν : FiniteMeasure HausdorffSourceSpace) :
    ν ∈ Set.range (gomesClarkWeightedSource 0) ↔
      (ν : Measure HausdorffSourceSpace) {gomesHausdorffOne} = 0 ∧
        Integrable (fun y : HausdorffSourceSpace => 1 / (1 - (y : ℝ)))
          (ν : Measure HausdorffSourceSpace) := by
  rw [gomesClarkCollapsed_range_iff]
  have hf : gomesClarkCollapsedInverseWeight =
      (fun y : HausdorffSourceSpace => 1 / (1 - (y : ℝ))) :=
    funext gomesClarkCollapsedInverseWeight_formula
  rw [hf]

/-- A reciprocal bank is realizable by a fixed Clark source exactly under the range criterion. -/
theorem gomesClarkFixed_reciprocal_realizable_iff (ν : FiniteMeasure HausdorffSourceSpace) :
    (∃ μ : FiniteMeasure HausdorffSourceSpace,
      gomesClarkFixedRecord μ = gomesClarkReciprocalRecord ν) ↔
      (ν : Measure HausdorffSourceSpace) {gomesHausdorffOne} = 0 ∧
        Integrable gomesClarkCollapsedInverseWeight (ν : Measure HausdorffSourceSpace) := by
  rw [← gomesClarkCollapsed_range_iff]
  constructor
  · rintro ⟨μ, hμ⟩
    refine ⟨μ, gomesClarkReciprocalRecord_injective ?_⟩
    rw [← gomesClarkAnchorRecord_weighted, gomesClarkAnchorRecord_zero]
    exact hμ
  · rintro ⟨μ, rfl⟩
    exact ⟨μ, by rw [← gomesClarkAnchorRecord_weighted, gomesClarkAnchorRecord_zero]⟩

end RHTower
