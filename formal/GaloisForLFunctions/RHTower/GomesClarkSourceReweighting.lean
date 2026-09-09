import GaloisForLFunctions.RHTower.GomesClarkWeightedSource

/-!
# Changing Clark anchors while preserving all observations

The weighted-source classification gives an explicit reconstruction ambiguity. Every nonzero
anchor admits a continuous reciprocal density, so weighting is an equivalence of finite sources.
Changing anchors transports the source by the ratio of the two densities. This is an experimental
corpus application of arXiv:2607.24901's distinction between observations and generating data.
-/

noncomputable section
open MeasureTheory GaloisForLFunctions.HTGeometry
open scoped NNReal ENNReal

namespace RHTower

/-- The inverse density exists continuously throughout the compact interval. -/
def gomesClarkInverseWeight (c : {c : ℝ // c ≠ 0}) : C(HausdorffSourceSpace, ℝ) :=
  ⟨fun y => (gomesClarkSourceWeight c y)⁻¹,
    (gomesClarkSourceWeight c).continuous.inv₀ (fun y => ne_of_gt (gomesClarkSourceWeight_pos c y))⟩

/-- The inverse density is strictly positive everywhere. -/
theorem gomesClarkInverseWeight_pos (c : {c : ℝ // c ≠ 0}) (y : HausdorffSourceSpace) :
    0 < gomesClarkInverseWeight c y := inv_pos.mpr (gomesClarkSourceWeight_pos c y)

/-- Removing the weight gives another finite source, with no separate integrability premise. -/
def gomesClarkUnweightedSource (c : {c : ℝ // c ≠ 0})
    (μ : FiniteMeasure HausdorffSourceSpace) : FiniteMeasure HausdorffSourceSpace :=
  ⟨(μ : Measure HausdorffSourceSpace).withDensity
    (fun y => ENNReal.ofReal (gomesClarkInverseWeight c y)),
    isFiniteMeasure_withDensity_ofReal
      (integrable_of_continuous _ (gomesClarkInverseWeight c).continuous).2⟩

/-- Transport real integrals through the inverse density. -/
theorem gomesClarkUnweightedSource_integral (c : {c : ℝ // c ≠ 0})
    (μ : FiniteMeasure HausdorffSourceSpace) (f : HausdorffSourceSpace → ℝ) :
    (∫ y, f y ∂(gomesClarkUnweightedSource c μ : Measure HausdorffSourceSpace)) =
      ∫ y, gomesClarkInverseWeight c y * f y ∂(μ : Measure HausdorffSourceSpace) := by
  change (∫ y, f y ∂(μ : Measure HausdorffSourceSpace).withDensity
    (fun y => ENNReal.ofReal (gomesClarkInverseWeight c y))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (gomesClarkInverseWeight c).continuous.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (le_of_lt (gomesClarkInverseWeight_pos c _)), smul_eq_mul]

/-- Weight removal recovers the original finite source. -/
theorem gomesClarkUnweightedSource_weighted (c : {c : ℝ // c ≠ 0})
    (μ : FiniteMeasure HausdorffSourceSpace) :
    gomesClarkUnweightedSource c (gomesClarkWeightedSource c μ) = μ := by
  apply FiniteMeasure.toMeasure_injective
  change ((μ : Measure HausdorffSourceSpace).withDensity
    (fun y => ENNReal.ofReal (gomesClarkSourceWeight c y))).withDensity
    (fun y => ENNReal.ofReal (gomesClarkInverseWeight c y)) = _
  rw [← withDensity_mul _ (gomesClarkSourceWeight c).continuous.measurable.ennreal_ofReal
    (gomesClarkInverseWeight c).continuous.measurable.ennreal_ofReal]
  have hd : (fun y => ENNReal.ofReal (gomesClarkSourceWeight c y)) *
      (fun y => ENNReal.ofReal (gomesClarkInverseWeight c y)) = 1 := by
    funext y
    simp only [Pi.mul_apply, Pi.one_apply, ← ENNReal.ofReal_mul (gomesClarkSourceWeight_nonneg c y)]
    change ENNReal.ofReal (gomesClarkSourceWeight c y * (gomesClarkSourceWeight c y)⁻¹) = 1
    rw [mul_inv_cancel₀ (ne_of_gt (gomesClarkSourceWeight_pos c y)), ENNReal.ofReal_one]
  rw [hd, withDensity_one]

/-- Applying the weight after removal also recovers the original source. -/
theorem gomesClarkWeightedSource_unweighted (c : {c : ℝ // c ≠ 0})
    (μ : FiniteMeasure HausdorffSourceSpace) :
    gomesClarkWeightedSource c (gomesClarkUnweightedSource c μ) = μ := by
  apply FiniteMeasure.toMeasure_injective
  change ((μ : Measure HausdorffSourceSpace).withDensity
    (fun y => ENNReal.ofReal (gomesClarkInverseWeight c y))).withDensity
    (fun y => ENNReal.ofReal (gomesClarkSourceWeight c y)) = _
  rw [← withDensity_mul _ (gomesClarkInverseWeight c).continuous.measurable.ennreal_ofReal
    (gomesClarkSourceWeight c).continuous.measurable.ennreal_ofReal]
  have hd : (fun y => ENNReal.ofReal (gomesClarkInverseWeight c y)) *
      (fun y => ENNReal.ofReal (gomesClarkSourceWeight c y)) = 1 := by
    funext y
    simp only [Pi.mul_apply, Pi.one_apply,
      ← ENNReal.ofReal_mul (le_of_lt (gomesClarkInverseWeight_pos c y))]
    change ENNReal.ofReal ((gomesClarkSourceWeight c y)⁻¹ * gomesClarkSourceWeight c y) = 1
    rw [inv_mul_cancel₀ (ne_of_gt (gomesClarkSourceWeight_pos c y)), ENNReal.ofReal_one]
  rw [hd, withDensity_one]

/-- Nonzero-anchor weighting is an explicit equivalence of finite sources. -/
def gomesClarkWeightEquiv (c : {c : ℝ // c ≠ 0}) :
    FiniteMeasure HausdorffSourceSpace ≃ FiniteMeasure HausdorffSourceSpace where
  toFun := gomesClarkWeightedSource c
  invFun := gomesClarkUnweightedSource c
  left_inv := gomesClarkUnweightedSource_weighted c
  right_inv := gomesClarkWeightedSource_unweighted c

/-- Every possible weighted source is realized at every nonzero anchor. -/
theorem gomesClarkWeightedSource_surjective (c : {c : ℝ // c ≠ 0}) :
    Function.Surjective (gomesClarkWeightedSource c) := (gomesClarkWeightEquiv c).surjective

/-- Canonical compensation for changing the anchor from `c` to `d`. -/
def gomesClarkReanchor (c d : {c : ℝ // c ≠ 0}) :
    FiniteMeasure HausdorffSourceSpace ≃ FiniteMeasure HausdorffSourceSpace :=
  (gomesClarkWeightEquiv c).trans (gomesClarkWeightEquiv d).symm

/-- The compensation is exactly the ratio of the old and new Clark densities. -/
theorem gomesClarkReanchor_integral (c d : {c : ℝ // c ≠ 0})
    (μ : FiniteMeasure HausdorffSourceSpace) (f : HausdorffSourceSpace → ℝ) :
    (∫ y, f y ∂(gomesClarkReanchor c d μ : Measure HausdorffSourceSpace)) =
      ∫ y, (gomesClarkSourceWeight c y / gomesClarkSourceWeight d y) * f y
        ∂(μ : Measure HausdorffSourceSpace) := by
  change (∫ y, f y ∂(gomesClarkUnweightedSource d (gomesClarkWeightedSource c μ) :
    Measure HausdorffSourceSpace)) = _
  rw [gomesClarkUnweightedSource_integral, gomesClarkWeightedSource_integral]
  apply integral_congr_ae
  filter_upwards with y
  dsimp [gomesClarkInverseWeight]
  ring

/-- Compensation leaves the canonical reconstructed source unchanged. -/
theorem gomesClarkReanchor_weighted (c d : {c : ℝ // c ≠ 0})
    (μ : FiniteMeasure HausdorffSourceSpace) :
    gomesClarkWeightedSource d (gomesClarkReanchor c d μ) = gomesClarkWeightedSource c μ :=
  gomesClarkWeightedSource_unweighted d _

/-- Every global observation is preserved after the compensating source change. -/
theorem gomesClarkReanchor_observation (c d : {c : ℝ // c ≠ 0})
    (μ : FiniteMeasure HausdorffSourceSpace) :
    gomesClarkAnchorRecord d (gomesClarkReanchor c d μ) = gomesClarkAnchorRecord c μ := by
  rw [gomesClarkAnchorRecord_eq_iff_weighted]
  exact gomesClarkReanchor_weighted c d μ

/-- The compensating source is the unique source with the same observations at the new anchor. -/
theorem gomesClarkReanchor_unique (c d : {c : ℝ // c ≠ 0})
    (μ ν : FiniteMeasure HausdorffSourceSpace) :
    gomesClarkAnchorRecord c μ = gomesClarkAnchorRecord d ν ↔ ν = gomesClarkReanchor c d μ := by
  rw [gomesClarkAnchorRecord_eq_iff_weighted]
  constructor
  · intro h
    apply (gomesClarkWeightEquiv d).injective
    exact h.symm.trans (gomesClarkReanchor_weighted c d μ).symm
  · rintro rfl
    exact (gomesClarkReanchor_weighted c d μ).symm

/-- Local observations already enforce the same unique compensation. -/
theorem gomesClarkReanchor_local_unique (r : Set.Ioc (0 : ℝ) 1)
    (c d : {c : ℝ // c ≠ 0}) (μ ν : FiniteMeasure HausdorffSourceSpace) :
    gomesClarkGerm r (gomesClarkAnchorRecord c μ) =
      gomesClarkGerm r (gomesClarkAnchorRecord d ν) ↔ ν = gomesClarkReanchor c d μ := by
  rw [gomesClarkAnchorGerm_eq_iff_full, gomesClarkReanchor_unique]

/-- No anchor change means no source change. -/
theorem gomesClarkReanchor_self (c : {c : ℝ // c ≠ 0})
    (μ : FiniteMeasure HausdorffSourceSpace) : gomesClarkReanchor c c μ = μ :=
  gomesClarkUnweightedSource_weighted c μ

/-- Successive anchor changes compose without any residual source distortion. -/
theorem gomesClarkReanchor_comp (c d e : {c : ℝ // c ≠ 0})
    (μ : FiniteMeasure HausdorffSourceSpace) :
    gomesClarkReanchor d e (gomesClarkReanchor c d μ) = gomesClarkReanchor c e μ := by
  change gomesClarkUnweightedSource e
    (gomesClarkWeightedSource d (gomesClarkUnweightedSource d (gomesClarkWeightedSource c μ))) = _
  rw [gomesClarkWeightedSource_unweighted]
  rfl

/-- Reversing an anchor change restores the source exactly. -/
theorem gomesClarkReanchor_reverse (c d : {c : ℝ // c ≠ 0})
    (μ : FiniteMeasure HausdorffSourceSpace) :
    gomesClarkReanchor d c (gomesClarkReanchor c d μ) = μ := by
  rw [gomesClarkReanchor_comp, gomesClarkReanchor_self]

end RHTower
