import GaloisForLFunctions.RHTower.GomesClarkCollapsedRange

/-!
# Canonical reconstruction and the complete collapsed-anchor fibre

The attainable weighted sources have a canonical finite inverse with zero blind-endpoint mass.
Every original source is exactly this inverse plus one free nonnegative endpoint mass. The
resulting equivalence separates reconstructible data from the discarded sector, as an
experimental corpus application of arXiv:2607.24901's reconstruction viewpoint.
-/

noncomputable section
open MeasureTheory GaloisForLFunctions.HTGeometry
open scoped NNReal ENNReal

namespace RHTower

/-- Attainable collapsed-anchor weighted sources. -/
abbrev GomesClarkCollapsedImage :=
  {ν : FiniteMeasure HausdorffSourceSpace // ν ∈ Set.range (gomesClarkWeightedSource 0)}

/-- The attainable datum carried by a finite source. -/
def gomesClarkCollapsedImageOf (μ : FiniteMeasure HausdorffSourceSpace) : GomesClarkCollapsedImage :=
  ⟨gomesClarkWeightedSource 0 μ, ⟨μ, rfl⟩⟩

/-- The canonical finite inverse of an attainable datum. -/
def gomesClarkCollapsedSource (ν : GomesClarkCollapsedImage) : FiniteMeasure HausdorffSourceSpace :=
  ⟨gomesClarkCollapsedUnweight (ν.val : Measure HausdorffSourceSpace),
    (gomesClarkCollapsedUnweight_finite_iff _).mpr ((gomesClarkCollapsed_range_iff ν.val).mp ν.property).2⟩

/-- The canonical inverse recovers exactly the visible restriction of every original source. -/
theorem gomesClarkCollapsedSource_imageOf (μ : FiniteMeasure HausdorffSourceSpace) :
    gomesClarkCollapsedSource (gomesClarkCollapsedImageOf μ) = μ.restrict {gomesHausdorffOne}ᶜ := by
  apply FiniteMeasure.toMeasure_injective
  exact gomesClarkCollapsedUnweight_weight (μ : Measure HausdorffSourceSpace)

/-- The inverse reconstructs every attainable weighted source exactly. -/
theorem gomesClarkCollapsedSource_weighted (ν : GomesClarkCollapsedImage) :
    gomesClarkWeightedSource 0 (gomesClarkCollapsedSource ν) = ν.val := by
  obtain ⟨μ, hμ⟩ := ν.property
  have hv : ν = gomesClarkCollapsedImageOf μ := Subtype.ext hμ.symm
  rw [hv]
  apply FiniteMeasure.toMeasure_injective
  change gomesClarkCollapsedWeight
    (gomesClarkCollapsedUnweight (gomesClarkCollapsedWeight (μ : Measure HausdorffSourceSpace))) = _
  rw [gomesClarkCollapsedWeight_unweight]
  have hr := Measure.restrict_add_restrict_compl
    (μ := gomesClarkCollapsedWeight (μ : Measure HausdorffSourceSpace))
    (measurableSet_singleton gomesHausdorffOne)
  rw [Measure.restrict_eq_zero.mpr (gomesClarkCollapsedWeight_one _), zero_add] at hr
  exact hr

/-- The canonical inverse has no arbitrary blind-endpoint contribution. -/
theorem gomesClarkCollapsedSource_one (ν : GomesClarkCollapsedImage) :
    gomesClarkCollapsedSource ν {gomesHausdorffOne} = 0 := by
  change (gomesClarkCollapsedUnweight (ν.val : Measure HausdorffSourceSpace)
    {gomesHausdorffOne}).toNNReal = 0
  rw [gomesClarkCollapsedUnweight_one]
  rfl

/-- Weighting the canonical inverse restores its attainable datum, including the range witness. -/
theorem gomesClarkCollapsedImageOf_source (ν : GomesClarkCollapsedImage) :
    gomesClarkCollapsedImageOf (gomesClarkCollapsedSource ν) = ν :=
  Subtype.ext (gomesClarkCollapsedSource_weighted ν)

/-- Every finite source splits into its canonical inverse and its exact missing endpoint mass. -/
theorem gomesClarkCollapsedSource_decomposition (μ : FiniteMeasure HausdorffSourceSpace) :
    μ = gomesClarkCollapsedSource (gomesClarkCollapsedImageOf μ) +
      μ {gomesHausdorffOne} • gomesHausdorffOneAtom := by
  rw [gomesClarkCollapsedSource_imageOf]
  apply FiniteMeasure.toMeasure_injective
  rw [FiniteMeasure.toMeasure_add, FiniteMeasure.restrict_measure_eq, FiniteMeasure.toMeasure_smul]
  change (μ : Measure HausdorffSourceSpace) = (μ : Measure HausdorffSourceSpace).restrict
    {gomesHausdorffOne}ᶜ + (μ {gomesHausdorffOne} : ℝ≥0∞) • Measure.dirac gomesHausdorffOne
  rw [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ← Measure.restrict_singleton]
  exact (Measure.restrict_compl_add_restrict (measurableSet_singleton _)).symm

/-- Adding any endpoint-one mass leaves the weighted datum unchanged. -/
theorem gomesClarkCollapsedWeighted_oneCompletion (μ : FiniteMeasure HausdorffSourceSpace)
    (w : ℝ≥0) :
    gomesClarkWeightedSource 0 (μ + w • gomesHausdorffOneAtom) = gomesClarkWeightedSource 0 μ := by
  apply (gomesClarkAnchorRecord_eq_iff_weighted 0 0 _ _).mp
  rw [gomesClarkAnchorRecord_zero, gomesClarkAnchorRecord_zero]
  exact gomesClarkFixedRecord_oneCompletion μ w

/-- The attainable datum is unchanged by every blind-endpoint completion. -/
theorem gomesClarkCollapsedImageOf_oneCompletion (μ : FiniteMeasure HausdorffSourceSpace)
    (w : ℝ≥0) :
    gomesClarkCollapsedImageOf (μ + w • gomesHausdorffOneAtom) = gomesClarkCollapsedImageOf μ :=
  Subtype.ext (gomesClarkCollapsedWeighted_oneCompletion μ w)

/-- Completing a canonical inverse introduces precisely the requested endpoint mass. -/
theorem gomesClarkCollapsedSource_completion_one (ν : GomesClarkCollapsedImage) (w : ℝ≥0) :
    (gomesClarkCollapsedSource ν + w • gomesHausdorffOneAtom) {gomesHausdorffOne} = w := by
  have ha : gomesHausdorffOneAtom {gomesHausdorffOne} = 1 := by
    change ((Measure.dirac gomesHausdorffOne) {gomesHausdorffOne}).toNNReal = 1
    simp
  simp only [FiniteMeasure.coeFn_add, Pi.add_apply, FiniteMeasure.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, gomesClarkCollapsedSource_one, ha, mul_one, zero_add]

/-- Full source space is exactly attainable observation data paired with one nonnegative blind mass. -/
def gomesClarkCollapsedEquiv :
    (GomesClarkCollapsedImage × ℝ≥0) ≃ FiniteMeasure HausdorffSourceSpace where
  toFun p := gomesClarkCollapsedSource p.1 + p.2 • gomesHausdorffOneAtom
  invFun μ := (gomesClarkCollapsedImageOf μ, μ {gomesHausdorffOne})
  left_inv p := by
    apply Prod.ext
    · exact (gomesClarkCollapsedImageOf_oneCompletion _ _).trans (gomesClarkCollapsedImageOf_source p.1)
    · exact gomesClarkCollapsedSource_completion_one p.1 p.2
  right_inv μ := (gomesClarkCollapsedSource_decomposition μ).symm

/-- Exact fibre classification using the original source's own endpoint mass. -/
theorem gomesClarkCollapsed_fibre (ν : GomesClarkCollapsedImage)
    (μ : FiniteMeasure HausdorffSourceSpace) :
    gomesClarkWeightedSource 0 μ = ν.val ↔
      μ = gomesClarkCollapsedSource ν + μ {gomesHausdorffOne} • gomesHausdorffOneAtom := by
  constructor
  · intro h
    have hi : gomesClarkCollapsedImageOf μ = ν := Subtype.ext h
    simpa only [hi] using gomesClarkCollapsedSource_decomposition μ
  · intro h
    conv_lhs => rw [h]
    rw [gomesClarkCollapsedWeighted_oneCompletion, gomesClarkCollapsedSource_weighted]

/-- A fixed Clark bank determines exactly the canonical source part. -/
theorem gomesClarkFixed_eq_iff_canonical (μ ν : FiniteMeasure HausdorffSourceSpace) :
    gomesClarkFixedRecord μ = gomesClarkFixedRecord ν ↔
      gomesClarkCollapsedSource (gomesClarkCollapsedImageOf μ) =
        gomesClarkCollapsedSource (gomesClarkCollapsedImageOf ν) := by
  constructor
  · intro h
    have hw := (gomesClarkAnchorRecord_eq_iff_weighted 0 0 μ ν).mp
      (by simpa only [gomesClarkAnchorRecord_zero] using h)
    exact congrArg gomesClarkCollapsedSource (Subtype.ext hw)
  · intro h
    have hw := congrArg (gomesClarkWeightedSource 0) h
    simp only [gomesClarkCollapsedSource_weighted] at hw
    simpa only [gomesClarkAnchorRecord_zero] using
      (gomesClarkAnchorRecord_eq_iff_weighted 0 0 μ ν).mpr hw

/-- A local fixed bank has the same canonical source classification. -/
theorem gomesClarkFixedGerm_eq_iff_canonical (r : Set.Ioc (0 : ℝ) 1)
    (μ ν : FiniteMeasure HausdorffSourceSpace) :
    gomesClarkGerm r (gomesClarkFixedRecord μ) = gomesClarkGerm r (gomesClarkFixedRecord ν) ↔
      gomesClarkCollapsedSource (gomesClarkCollapsedImageOf μ) =
        gomesClarkCollapsedSource (gomesClarkCollapsedImageOf ν) := by
  rw [gomesClarkFixedGerm_eq_iff_full, gomesClarkFixed_eq_iff_canonical]

/-- A local reciprocal bank has a fixed-Clark realization under precisely the same moment criterion. -/
theorem gomesClarkFixedGerm_reciprocal_realizable_iff (r : Set.Ioc (0 : ℝ) 1)
    (ν : FiniteMeasure HausdorffSourceSpace) :
    (∃ μ : FiniteMeasure HausdorffSourceSpace,
      gomesClarkGerm r (gomesClarkFixedRecord μ) =
        gomesClarkGerm r (gomesClarkReciprocalRecord ν)) ↔
      (ν : Measure HausdorffSourceSpace) {gomesHausdorffOne} = 0 ∧
        Integrable gomesClarkCollapsedInverseWeight (ν : Measure HausdorffSourceSpace) := by
  rw [← gomesClarkCollapsed_range_iff]
  constructor
  · rintro ⟨μ, hμ⟩
    refine ⟨μ, gomesClarkReciprocalGerm_injective r ?_⟩
    change gomesClarkGerm r (gomesClarkReciprocalRecord (gomesClarkWeightedSource 0 μ)) =
      gomesClarkGerm r (gomesClarkReciprocalRecord ν)
    rw [← gomesClarkAnchorRecord_weighted, gomesClarkAnchorRecord_zero]
    exact hμ
  · rintro ⟨μ, rfl⟩
    exact ⟨μ, by rw [← gomesClarkAnchorRecord_weighted, gomesClarkAnchorRecord_zero]⟩

end RHTower
