import GaloisForLFunctions.HTGeometry.GomesHausdorffObservationCompletion

/-!
# Faithful Stieltjes observations of sources away from the endpoint

The invisible-atom classification yields a concrete positive replacement for a failed
reconstruction: source data on `(0,1]` have no hidden endpoint mass. This extends the corpus's
Hausdorff moment and Stieltjes interfaces without requiring a separately supplied mass equality.
The conceptual link to arXiv:2607.24901 is recovery after identifying the invisible sector;
these are new measure-theoretic applications, not statements about gauge bundles.
-/

noncomputable section
open MeasureTheory
open scoped NNReal ENNReal

namespace GaloisForLFunctions.HTGeometry

/-- The positive part of the existing compact source coordinate, with zero removed. -/
abbrev GomesHausdorffVisibleSpace := {y : HausdorffSourceSpace // y ≠ gomesHausdorffZero}

/-- Include a finite positive-coordinate source in the corpus's compact source space. -/
def gomesHausdorffVisibleLift (μ : FiniteMeasure GomesHausdorffVisibleSpace) :
    FiniteMeasure HausdorffSourceSpace := μ.map Subtype.val

/-- Included visible sources have exactly zero mass at the compactification endpoint. -/
theorem gomesHausdorffVisibleLift_zeroAtom (μ : FiniteMeasure GomesHausdorffVisibleSpace) :
    gomesHausdorffVisibleLift μ {gomesHausdorffZero} = 0 := by
  rw [gomesHausdorffVisibleLift, FiniteMeasure.map_apply μ measurable_subtype_coe
    (MeasurableSet.singleton gomesHausdorffZero)]
  have hs : (Subtype.val : GomesHausdorffVisibleSpace → HausdorffSourceSpace) ⁻¹'
      {gomesHausdorffZero} = ∅ := by
    ext y
    simp [y.property]
  rw [hs]
  change ((μ : Measure GomesHausdorffVisibleSpace) ∅).toNNReal = 0
  simp

/-- Restricting an included visible source away from zero loses nothing. -/
theorem gomesHausdorffVisibleLift_restrict (μ : FiniteMeasure GomesHausdorffVisibleSpace) :
    (gomesHausdorffVisibleLift μ).restrict {gomesHausdorffZero}ᶜ =
      gomesHausdorffVisibleLift μ := by
  have h := gomesHausdorffSource_zeroDecomposition (gomesHausdorffVisibleLift μ)
  rw [gomesHausdorffVisibleLift_zeroAtom, zero_smul, add_zero] at h
  exact h.symm

/-- Inclusion of positive-coordinate sources is faithful at the measure level. -/
theorem gomesHausdorffVisibleLift_injective : Function.Injective gomesHausdorffVisibleLift := by
  have he : MeasurableEmbedding (Subtype.val : GomesHausdorffVisibleSpace → HausdorffSourceSpace) :=
    MeasurableEmbedding.subtype_coe ((MeasurableSet.singleton gomesHausdorffZero).compl)
  intro μ ν h
  apply FiniteMeasure.toMeasure_injective
  apply he.map_injective
  exact congrArg (fun ρ : FiniteMeasure HausdorffSourceSpace =>
    (ρ : Measure HausdorffSourceSpace)) h

/-- Stieltjes data alone reconstruct every positive-coordinate source, including its mass. -/
theorem gomesHausdorffVisibleStieltjes_injective :
    Function.Injective (fun μ : FiniteMeasure GomesHausdorffVisibleSpace =>
      gomesHausdorffStieltjesRecord (gomesHausdorffVisibleLift μ)) := by
  intro μ ν h
  apply gomesHausdorffVisibleLift_injective
  have hr := (gomesHausdorffStieltjesRecord_eq_iff_visible
    (gomesHausdorffVisibleLift μ) (gomesHausdorffVisibleLift ν)).mp h
  simpa only [gomesHausdorffVisibleLift_restrict] using hr

/-- Positive-order moments already reconstruct visible sources; the zeroth is redundant. -/
theorem gomesHausdorffVisibleMoments_injective :
    Function.Injective (fun μ : FiniteMeasure GomesHausdorffVisibleSpace =>
      fun m : ℕ => hausdorffMoment (↑(gomesHausdorffVisibleLift μ)) (m + 1)) := by
  intro μ ν h
  apply gomesHausdorffVisibleStieltjes_injective
  apply (gomesHausdorffStieltjesRecord_eq_iff_positive_moments _ _).mpr
  exact congrFun h

/-- With an explicit endpoint sector, equal observations identify exactly the visible source. -/
theorem gomesHausdorffVisibleStieltjes_withAtom_classification
    (μ ν : FiniteMeasure GomesHausdorffVisibleSpace) (w v : ℝ≥0) :
    gomesHausdorffStieltjesRecord (gomesHausdorffVisibleLift μ + w • gomesHausdorffZeroAtom) =
      gomesHausdorffStieltjesRecord (gomesHausdorffVisibleLift ν + v • gomesHausdorffZeroAtom) ↔
      μ = ν := by
  rw [gomesHausdorffStieltjesRecord_zeroCompletion,
    gomesHausdorffStieltjesRecord_zeroCompletion]
  exact ⟨fun h => gomesHausdorffVisibleStieltjes_injective h,
    fun h => congrArg (fun ρ => gomesHausdorffStieltjesRecord (gomesHausdorffVisibleLift ρ)) h⟩

/-- The explicit endpoint parameter is exactly the mass of the zero singleton. -/
theorem gomesHausdorffVisible_withAtom_singleton
    (μ : FiniteMeasure GomesHausdorffVisibleSpace) (w : ℝ≥0) :
    (gomesHausdorffVisibleLift μ + w • gomesHausdorffZeroAtom) {gomesHausdorffZero} = w := by
  simp only [FiniteMeasure.coeFn_add, Pi.add_apply, gomesHausdorffVisibleLift_zeroAtom,
    zero_add, FiniteMeasure.smul_apply, smul_eq_mul]
  change w * ((Measure.dirac gomesHausdorffZero) {gomesHausdorffZero}).toNNReal = w
  simp

/-- Visible source and endpoint mass are independent, uniquely encoded source coordinates. -/
theorem gomesHausdorffVisible_withAtom_injective :
    Function.Injective (fun p : FiniteMeasure GomesHausdorffVisibleSpace × ℝ≥0 =>
      gomesHausdorffVisibleLift p.1 + p.2 • gomesHausdorffZeroAtom) := by
  intro p q h
  apply Prod.ext
  · exact (gomesHausdorffVisibleStieltjes_withAtom_classification p.1 q.1 p.2 q.2).mp
      (congrArg gomesHausdorffStieltjesRecord h)
  · have hs := congrArg (fun ρ : FiniteMeasure HausdorffSourceSpace =>
      ρ {gomesHausdorffZero}) h
    simpa only [gomesHausdorffVisible_withAtom_singleton] using hs

/-- The canonical visible source, obtained by pulling back along the positive-coordinate inclusion. -/
def gomesHausdorffVisiblePart (μ : FiniteMeasure HausdorffSourceSpace) :
    FiniteMeasure GomesHausdorffVisibleSpace :=
  μ.comap (Subtype.val : GomesHausdorffVisibleSpace → HausdorffSourceSpace)

/-- The canonical visible part includes back to the exact restriction away from zero. -/
theorem gomesHausdorffVisiblePart_lift (μ : FiniteMeasure HausdorffSourceSpace) :
    gomesHausdorffVisibleLift (gomesHausdorffVisiblePart μ) =
      μ.restrict {gomesHausdorffZero}ᶜ := by
  apply FiniteMeasure.toMeasure_injective
  exact map_comap_subtype_coe ((MeasurableSet.singleton gomesHausdorffZero).compl) _

/-- Every compact source has a dependency-closed decomposition into visible source and zero mass. -/
theorem gomesHausdorffSource_visibleAtom_decomposition
    (μ : FiniteMeasure HausdorffSourceSpace) :
    gomesHausdorffVisibleLift (gomesHausdorffVisiblePart μ) +
      μ {gomesHausdorffZero} • gomesHausdorffZeroAtom = μ := by
  rw [gomesHausdorffVisiblePart_lift]
  exact (gomesHausdorffSource_zeroDecomposition μ).symm

/-- Exact product coordinates for every finite source: visible measure and nonnegative hidden mass. -/
def gomesHausdorffVisibleAtomEquiv :
    (FiniteMeasure GomesHausdorffVisibleSpace × ℝ≥0) ≃ FiniteMeasure HausdorffSourceSpace where
  toFun p := gomesHausdorffVisibleLift p.1 + p.2 • gomesHausdorffZeroAtom
  invFun μ := (gomesHausdorffVisiblePart μ, μ {gomesHausdorffZero})
  left_inv _ := gomesHausdorffVisible_withAtom_injective
    (gomesHausdorffSource_visibleAtom_decomposition _)
  right_inv := gomesHausdorffSource_visibleAtom_decomposition

/-- Stieltjes observations are exactly faithful to the visible factor of the product coordinates. -/
theorem gomesHausdorffStieltjesRecord_eq_iff_visiblePart
    (μ ν : FiniteMeasure HausdorffSourceSpace) :
    gomesHausdorffStieltjesRecord μ = gomesHausdorffStieltjesRecord ν ↔
      gomesHausdorffVisiblePart μ = gomesHausdorffVisiblePart ν := by
  rw [gomesHausdorffStieltjesRecord_eq_iff_visible]
  constructor
  · intro h
    apply gomesHausdorffVisibleLift_injective
    simpa only [gomesHausdorffVisiblePart_lift] using h
  · intro h
    have hm := congrArg gomesHausdorffVisibleLift h
    simpa only [gomesHausdorffVisiblePart_lift] using hm

end GaloisForLFunctions.HTGeometry
