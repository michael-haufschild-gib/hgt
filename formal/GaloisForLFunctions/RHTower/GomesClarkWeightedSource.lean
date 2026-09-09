import GaloisForLFunctions.RHTower.GomesClarkLocalObservation
import GaloisForLFunctions.RHTower.GomesClarkAnchorObservation
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The source reconstructed by Clark anchor observations

Experimental application of arXiv:2607.24901's reconstruction / invisible-sector distinction.
The compact Clark anchor bank reconstructs a canonical weighted source, even from a punctured
local interval. This identifies the exact object remembered when both anchor and source vary;
it is a corpus application, not a transcription of a gauge-category theorem.
-/

noncomputable section
open MeasureTheory GaloisForLFunctions.HTGeometry
open scoped NNReal ENNReal

namespace RHTower

/-- The continuous density hidden in the compactified Clark numerator. -/
def gomesClarkSourceWeight (c : ℝ) : C(HausdorffSourceSpace, ℝ) :=
  ⟨fun y => 1 + (c ^ 2 - 1) * (y : ℝ), by fun_prop⟩

/-- The density is an affine interpolation between the endpoint weights one and `c²`. -/
theorem gomesClarkSourceWeight_decomposition (c : ℝ) (y : HausdorffSourceSpace) :
    gomesClarkSourceWeight c y = (1 - (y : ℝ)) + c ^ 2 * (y : ℝ) := by
  dsimp [gomesClarkSourceWeight]
  ring

/-- Every real anchor gives a nonnegative density. -/
theorem gomesClarkSourceWeight_nonneg (c : ℝ) (y : HausdorffSourceSpace) :
    0 ≤ gomesClarkSourceWeight c y := by
  rw [gomesClarkSourceWeight_decomposition]
  exact add_nonneg (sub_nonneg.mpr y.property.2) (mul_nonneg (sq_nonneg c) y.property.1)

/-- The only zero density occurs at the invisible endpoint of the collapsed anchor. -/
theorem gomesClarkSourceWeight_zero_iff (c : ℝ) (y : HausdorffSourceSpace) :
    gomesClarkSourceWeight c y = 0 ↔ c = 0 ∧ y = gomesHausdorffOne := by
  rw [gomesClarkSourceWeight_decomposition]
  constructor
  · intro h
    have hm := mul_nonneg (sq_nonneg c) y.property.1
    have hy : (y : ℝ) = 1 := by linarith [y.property.2]
    have hc : c = 0 := by rw [hy] at h; nlinarith [sq_nonneg c]
    exact ⟨hc, Subtype.ext hy⟩
  · rintro ⟨rfl, rfl⟩
    simp [gomesHausdorffOne]

/-- Nonzero anchors have strictly positive density everywhere, including both endpoints. -/
theorem gomesClarkSourceWeight_pos (c : {c : ℝ // c ≠ 0}) (y : HausdorffSourceSpace) :
    0 < gomesClarkSourceWeight c y := by
  refine lt_of_le_of_ne (gomesClarkSourceWeight_nonneg c y) ?_
  intro h
  exact c.property ((gomesClarkSourceWeight_zero_iff c y).mp h.symm).1

/-- The finite source actually reconstructed by an anchor bank. -/
def gomesClarkWeightedSource (c : ℝ) (μ : FiniteMeasure HausdorffSourceSpace) :
    FiniteMeasure HausdorffSourceSpace :=
  ⟨(μ : Measure HausdorffSourceSpace).withDensity (fun y => ENNReal.ofReal (gomesClarkSourceWeight c y)),
    isFiniteMeasure_withDensity_ofReal
      (integrable_of_continuous _ (gomesClarkSourceWeight c).continuous).2⟩

/-- Transport any real integral to the original source using the canonical density. -/
theorem gomesClarkWeightedSource_integral (c : ℝ) (μ : FiniteMeasure HausdorffSourceSpace)
    (f : HausdorffSourceSpace → ℝ) :
    (∫ y, f y ∂(gomesClarkWeightedSource c μ : Measure HausdorffSourceSpace)) =
      ∫ y, gomesClarkSourceWeight c y * f y ∂(μ : Measure HausdorffSourceSpace) := by
  change (∫ y, f y ∂(μ : Measure HausdorffSourceSpace).withDensity
    (fun y => ENNReal.ofReal (gomesClarkSourceWeight c y))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (gomesClarkSourceWeight c).continuous.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (gomesClarkSourceWeight_nonneg c _), smul_eq_mul]

/-- Clark observations are exactly reciprocal observations of the weighted source. -/
theorem gomesClarkAnchorRecord_weighted (c : ℝ) (μ : FiniteMeasure HausdorffSourceSpace) :
    gomesClarkAnchorRecord c μ = gomesClarkReciprocalRecord (gomesClarkWeightedSource c μ) := by
  funext t
  rw [gomesClarkReciprocalRecord, gomesClarkWeightedSource_integral]
  apply integral_congr_ae
  filter_upwards with y
  change gomesClarkAnchorTest c t y = _
  rw [gomesClarkAnchorTest_fraction]
  dsimp [gomesClarkSourceWeight]
  ring

/-- The weighted source's mass is itself an observed anchor value. -/
theorem gomesClarkWeightedSource_mass (c : ℝ) (μ : FiniteMeasure HausdorffSourceSpace) :
    ((gomesClarkWeightedSource c μ).mass : ℝ) =
      gomesClarkAnchorRecord c μ ⟨0, by simp⟩ := by
  rw [gomesClarkAnchorRecord_weighted, gomesClarkReciprocalRecord_zero]

/-- Equality across different anchors has a canonical source-level classification. -/
theorem gomesClarkAnchorRecord_eq_iff_weighted (c d : ℝ)
    (μ ν : FiniteMeasure HausdorffSourceSpace) :
    gomesClarkAnchorRecord c μ = gomesClarkAnchorRecord d ν ↔
      gomesClarkWeightedSource c μ = gomesClarkWeightedSource d ν := by
  rw [gomesClarkAnchorRecord_weighted, gomesClarkAnchorRecord_weighted]
  exact gomesClarkReciprocalRecord_injective.eq_iff

/-- An arbitrarily small punctured local bank already reconstructs the weighted source. -/
theorem gomesClarkAnchorGerm_eq_iff_weighted (r : Set.Ioc (0 : ℝ) 1) (c d : ℝ)
    (μ ν : FiniteMeasure HausdorffSourceSpace) :
    gomesClarkGerm r (gomesClarkAnchorRecord c μ) =
      gomesClarkGerm r (gomesClarkAnchorRecord d ν) ↔
      gomesClarkWeightedSource c μ = gomesClarkWeightedSource d ν := by
  rw [gomesClarkAnchorRecord_weighted, gomesClarkAnchorRecord_weighted]
  exact (gomesClarkReciprocalGerm_injective r).eq_iff

/-- Local equality is exactly global equality, including when the anchors differ. -/
theorem gomesClarkAnchorGerm_eq_iff_full (r : Set.Ioc (0 : ℝ) 1) (c d : ℝ)
    (μ ν : FiniteMeasure HausdorffSourceSpace) :
    gomesClarkGerm r (gomesClarkAnchorRecord c μ) =
      gomesClarkGerm r (gomesClarkAnchorRecord d ν) ↔
      gomesClarkAnchorRecord c μ = gomesClarkAnchorRecord d ν := by
  rw [gomesClarkAnchorGerm_eq_iff_weighted, gomesClarkAnchorRecord_eq_iff_weighted]

/-- A local bank has exactly the same collapsed-anchor ambiguity as the global bank. -/
theorem gomesClarkAnchorGerm_classification (r : Set.Ioc (0 : ℝ) 1) (c : ℝ)
    (μ ν : FiniteMeasure HausdorffSourceSpace) :
    gomesClarkGerm r (gomesClarkAnchorRecord c μ) =
      gomesClarkGerm r (gomesClarkAnchorRecord c ν) ↔
      μ = ν ∨ (c = 0 ∧ gomesClarkFixedRecord μ = gomesClarkFixedRecord ν) := by
  rw [gomesClarkAnchorGerm_eq_iff_full, gomesClarkAnchorRecord_classification]

/-- The finite weighting operation is injective precisely away from anchor collapse. -/
theorem gomesClarkWeightedSource_injective_iff (c : ℝ) :
    Function.Injective (gomesClarkWeightedSource c) ↔ c ≠ 0 := by
  rw [← gomesClarkAnchorRecord_injective_iff]
  constructor <;> intro h μ ν he
  · exact h ((gomesClarkAnchorRecord_eq_iff_weighted c c μ ν).mp he)
  · exact h ((gomesClarkAnchorRecord_eq_iff_weighted c c μ ν).mpr he)

/-- Local observations recover the entire source exactly when the anchor is nonzero. -/
theorem gomesClarkAnchorGerm_injective_iff (r : Set.Ioc (0 : ℝ) 1) (c : ℝ) :
    Function.Injective (fun μ => gomesClarkGerm r (gomesClarkAnchorRecord c μ)) ↔ c ≠ 0 := by
  rw [← gomesClarkWeightedSource_injective_iff]
  constructor <;> intro h μ ν he
  · exact h ((gomesClarkAnchorGerm_eq_iff_weighted r c c μ ν).mpr he)
  · exact h ((gomesClarkAnchorGerm_eq_iff_weighted r c c μ ν).mp he)

end RHTower
