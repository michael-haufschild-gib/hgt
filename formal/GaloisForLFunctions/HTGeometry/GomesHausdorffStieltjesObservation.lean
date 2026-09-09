import GaloisForLFunctions.HTGeometry.StieltjesMomentDetermination
import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-!
# Exact invisible mass in compactified Stieltjes observations

Experimental corpus application of the reconstruction / invisible-kernel distinction in
arXiv:2607.24901, section 4. This is a theorem about the existing Hausdorff source and
Stieltjes kernel, not a transcription of the paper's gauge-bundle statements.

The kernel `y / (1 + t*y)` misses mass at zero. Equal records determine the entire source
away from zero; the sole ambiguity is exactly an atom there. All inputs are finite positive
measures as mathematical data. No determinacy or equality hypotheses are supplied to the
classification theorems.
-/

noncomputable section
open MeasureTheory
open scoped NNReal ENNReal

namespace GaloisForLFunctions.HTGeometry

/-- The compactification endpoint invisible to the Stieltjes kernel. -/
def gomesHausdorffZero : HausdorffSourceSpace := ⟨0, le_rfl, zero_le_one⟩

/-- A unit point source at the invisible endpoint. -/
def gomesHausdorffZeroAtom : FiniteMeasure HausdorffSourceSpace :=
  ⟨Measure.dirac gomesHausdorffZero, inferInstance⟩

/-- The denominator stays positive throughout the entire nonsingular observation domain. -/
theorem gomesHausdorffStieltjes_denominator_pos
    (t : Set.Ioi (-1 : ℝ)) (y : HausdorffSourceSpace) :
    0 < 1 + (t : ℝ) * (y : ℝ) := by
  by_cases ht : 0 ≤ (t : ℝ)
  · have hm := mul_nonneg ht y.property.1
    linarith
  · have hm := mul_le_mul_of_nonpos_left y.property.2 (le_of_not_ge ht)
    have hp : (-1 : ℝ) < t := t.property
    linarith

/-- Each admissible Stieltjes test is a continuous observable on the compact source space. -/
def gomesHausdorffStieltjesTest (t : Set.Ioi (-1 : ℝ)) : C(HausdorffSourceSpace, ℝ) :=
  ⟨stieltjesKernel t, continuous_subtype_val.div
    (continuous_const.add (continuous_const.mul continuous_subtype_val))
    (fun y => ne_of_gt (gomesHausdorffStieltjes_denominator_pos t y))⟩

/-- The existing Stieltjes integrals, indexed by all real parameters above minus one. -/
def gomesHausdorffStieltjesRecord (μ : FiniteMeasure HausdorffSourceSpace)
    (t : Set.Ioi (-1 : ℝ)) : ℝ :=
  ∫ y, stieltjesKernel t y ∂(μ : Measure HausdorffSourceSpace)

/-- Adding endpoint mass changes any continuous report by exactly its endpoint value. -/
theorem gomesHausdorffZeroCompletion_report (μ : FiniteMeasure HausdorffSourceSpace)
    (w : ℝ≥0) (f : C(HausdorffSourceSpace, ℝ)) :
    (∫ y, f y ∂((μ + w • gomesHausdorffZeroAtom : FiniteMeasure HausdorffSourceSpace) :
      Measure HausdorffSourceSpace)) =
      (∫ y, f y ∂(μ : Measure HausdorffSourceSpace)) + (w : ℝ) * f gomesHausdorffZero := by
  rw [FiniteMeasure.toMeasure_add, integral_add_measure
    (integrable_of_continuous _ f.continuous) (integrable_of_continuous _ f.continuous)]
  simp [gomesHausdorffZeroAtom, NNReal.smul_def, smul_eq_mul]

/-- Stieltjes observations ignore every amount of added endpoint mass. -/
theorem gomesHausdorffStieltjesRecord_zeroCompletion
    (μ : FiniteMeasure HausdorffSourceSpace) (w : ℝ≥0) :
    gomesHausdorffStieltjesRecord (μ + w • gomesHausdorffZeroAtom) =
      gomesHausdorffStieltjesRecord μ := by
  funext t
  have h := gomesHausdorffZeroCompletion_report μ w (gomesHausdorffStieltjesTest t)
  simpa [gomesHausdorffStieltjesRecord, gomesHausdorffStieltjesTest,
    stieltjesKernel, gomesHausdorffZero] using h

/-- The endpoint changes only the zeroth moment, with the usual zero-power convention. -/
theorem gomesHausdorffMoment_zeroCompletion (μ : FiniteMeasure HausdorffSourceSpace)
    (w : ℝ≥0) (m : ℕ) :
    hausdorffMoment (↑(μ + w • gomesHausdorffZeroAtom)) m =
      hausdorffMoment (μ : Measure HausdorffSourceSpace) m + (w : ℝ) * (0 : ℝ) ^ m := by
  exact gomesHausdorffZeroCompletion_report μ w
    ⟨fun y => (y : ℝ) ^ m, continuous_subtype_val.pow m⟩

/-- Equal Stieltjes records are exactly equal sources after balancing their endpoint masses. -/
theorem gomesHausdorffStieltjesRecord_eq_iff_balanced
    (μ ν : FiniteMeasure HausdorffSourceSpace) :
    gomesHausdorffStieltjesRecord μ = gomesHausdorffStieltjesRecord ν ↔
      μ + ν.mass • gomesHausdorffZeroAtom = ν + μ.mass • gomesHausdorffZeroAtom := by
  constructor
  · intro h
    apply FiniteMeasure.toMeasure_injective
    apply hausdorffSource_eq_of_stieltjes_eq (r := 1) zero_lt_one le_rfl
    · rw [gomesHausdorffMoment_zeroCompletion, gomesHausdorffMoment_zeroCompletion]
      simp [hausdorffMoment, add_comm]
    · intro t _ ht
      let p : Set.Ioi (-1 : ℝ) := ⟨t, (abs_lt.mp ht).1⟩
      change gomesHausdorffStieltjesRecord (μ + ν.mass • gomesHausdorffZeroAtom) p =
        gomesHausdorffStieltjesRecord (ν + μ.mass • gomesHausdorffZeroAtom) p
      rw [gomesHausdorffStieltjesRecord_zeroCompletion,
        gomesHausdorffStieltjesRecord_zeroCompletion, h]
  · intro h
    have h' := congrArg gomesHausdorffStieltjesRecord h
    simpa only [gomesHausdorffStieltjesRecord_zeroCompletion] using h'

/-- Every source splits canonically into visible mass and its endpoint atom. -/
theorem gomesHausdorffSource_zeroDecomposition (μ : FiniteMeasure HausdorffSourceSpace) :
    μ = μ.restrict {gomesHausdorffZero}ᶜ + μ {gomesHausdorffZero} • gomesHausdorffZeroAtom := by
  apply FiniteMeasure.toMeasure_injective
  rw [FiniteMeasure.toMeasure_add, FiniteMeasure.restrict_measure_eq,
    FiniteMeasure.toMeasure_smul]
  change (μ : Measure HausdorffSourceSpace) =
    (μ : Measure HausdorffSourceSpace).restrict {gomesHausdorffZero}ᶜ +
      μ {gomesHausdorffZero} • Measure.dirac gomesHausdorffZero
  change (μ : Measure HausdorffSourceSpace) =
    (μ : Measure HausdorffSourceSpace).restrict {gomesHausdorffZero}ᶜ +
      (μ {gomesHausdorffZero} : ℝ≥0∞) • Measure.dirac gomesHausdorffZero
  rw [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ← Measure.restrict_singleton]
  exact (Measure.restrict_compl_add_restrict
    (MeasurableSet.singleton gomesHausdorffZero)).symm


/-- The Stieltjes record recovers precisely the source restricted away from zero. -/
theorem gomesHausdorffStieltjesRecord_eq_iff_visible
    (μ ν : FiniteMeasure HausdorffSourceSpace) :
    gomesHausdorffStieltjesRecord μ = gomesHausdorffStieltjesRecord ν ↔
      μ.restrict {gomesHausdorffZero}ᶜ = ν.restrict {gomesHausdorffZero}ᶜ := by
  classical
  constructor
  · intro h
    have hb := (gomesHausdorffStieltjesRecord_eq_iff_balanced μ ν).mp h
    apply FiniteMeasure.toMeasure_injective
    have hr := congrArg
      (fun ρ : FiniteMeasure HausdorffSourceSpace =>
        (ρ : Measure HausdorffSourceSpace).restrict {gomesHausdorffZero}ᶜ) hb
    simpa [FiniteMeasure.toMeasure_add, FiniteMeasure.toMeasure_smul,
      gomesHausdorffZeroAtom, Measure.restrict_add, Measure.restrict_smul,
      restrict_dirac, FiniteMeasure.restrict_measure_eq] using hr
  · intro h
    calc
      gomesHausdorffStieltjesRecord μ =
          gomesHausdorffStieltjesRecord (μ.restrict {gomesHausdorffZero}ᶜ) := by
        conv_lhs => rw [gomesHausdorffSource_zeroDecomposition μ]
        exact gomesHausdorffStieltjesRecord_zeroCompletion _ _
      _ = gomesHausdorffStieltjesRecord (ν.restrict {gomesHausdorffZero}ᶜ) := congrArg _ h
      _ = gomesHausdorffStieltjesRecord ν := by
        conv_rhs => rw [gomesHausdorffSource_zeroDecomposition ν]
        exact (gomesHausdorffStieltjesRecord_zeroCompletion _ _).symm

/-- One total-mass measurement repairs exactly the lost endpoint information. -/
theorem gomesHausdorffStieltjes_mass_reconstruction
    (μ ν : FiniteMeasure HausdorffSourceSpace) :
    (gomesHausdorffStieltjesRecord μ = gomesHausdorffStieltjesRecord ν ∧
      μ.mass = ν.mass) ↔ μ = ν := by
  constructor
  · rintro ⟨h, hm⟩
    have hb := (gomesHausdorffStieltjesRecord_eq_iff_balanced μ ν).mp h
    rw [hm] at hb
    apply FiniteMeasure.eq_of_forall_apply_eq
    intro s _
    have hs := congrArg (fun ρ : FiniteMeasure HausdorffSourceSpace => ρ s) hb
    simp only [FiniteMeasure.coeFn_add, Pi.add_apply] at hs
    exact add_right_cancel hs
  · rintro rfl
    exact ⟨rfl, rfl⟩

end GaloisForLFunctions.HTGeometry
