import GaloisForLFunctions.HTGeometry.GomesHausdorffStieltjesObservation

/-!
# Which extra observations complete a Stieltjes record?

Experimental continuation of arXiv:2607.24901's reconstruction distinction in the existing
Hausdorff/CDD corpus. The preceding exact invisible-atom classification now identifies every
continuous report's remaining information and connects the Stieltjes record to positive moments
and the existing real CDD phase. No gauge-category equivalence is claimed.
-/

noncomputable section
open MeasureTheory
open scoped NNReal ENNReal

namespace GaloisForLFunctions.HTGeometry

/-- Equal Stieltjes records determine every continuous report up to its exact mass defect. -/
theorem gomesHausdorffStieltjesRecord_eq_iff_report_defect
    (μ ν : FiniteMeasure HausdorffSourceSpace) :
    gomesHausdorffStieltjesRecord μ = gomesHausdorffStieltjesRecord ν ↔
      ∀ f : C(HausdorffSourceSpace, ℝ),
        (∫ y, f y ∂(μ : Measure HausdorffSourceSpace)) -
          (∫ y, f y ∂(ν : Measure HausdorffSourceSpace)) =
          ((μ.mass : ℝ) - (ν.mass : ℝ)) * f gomesHausdorffZero := by
  constructor
  · intro h f
    have hb := (gomesHausdorffStieltjesRecord_eq_iff_balanced μ ν).mp h
    have hf := congrArg (fun ρ : FiniteMeasure HausdorffSourceSpace =>
      ∫ y, f y ∂(ρ : Measure HausdorffSourceSpace)) hb
    rw [gomesHausdorffZeroCompletion_report, gomesHausdorffZeroCompletion_report] at hf
    linear_combination hf
  · intro h
    funext t
    have hf := h (gomesHausdorffStieltjesTest t)
    simpa [gomesHausdorffStieltjesTest, gomesHausdorffStieltjesRecord,
      gomesHausdorffZero, stieltjesKernel, sub_eq_zero] using hf

/-- The observation equivalence is exactly equality of all positive-order moments. -/
theorem gomesHausdorffStieltjesRecord_eq_iff_positive_moments
    (μ ν : FiniteMeasure HausdorffSourceSpace) :
    gomesHausdorffStieltjesRecord μ = gomesHausdorffStieltjesRecord ν ↔
      ∀ m : ℕ, hausdorffMoment (μ : Measure HausdorffSourceSpace) (m + 1) =
        hausdorffMoment (ν : Measure HausdorffSourceSpace) (m + 1) := by
  constructor
  · intro h m
    have hf := (gomesHausdorffStieltjesRecord_eq_iff_report_defect μ ν).mp h
      ⟨fun y => (y : ℝ) ^ (m + 1), continuous_subtype_val.pow (m + 1)⟩
    simpa [gomesHausdorffZero, hausdorffMoment, sub_eq_zero] using hf
  · intro h
    apply (gomesHausdorffStieltjesRecord_eq_iff_balanced μ ν).mpr
    apply FiniteMeasure.toMeasure_injective
    apply hausdorffSource_eq_of_moments_eq
    intro m
    rw [gomesHausdorffMoment_zeroCompletion, gomesHausdorffMoment_zeroCompletion]
    cases m with
    | zero => simp [hausdorffMoment, add_comm]
    | succ m => simpa using h m

/-- Any one continuous report either detects the missing atom or adds no distinguishing power. -/
theorem gomesHausdorffStieltjes_singleReport_classification
    (μ ν : FiniteMeasure HausdorffSourceSpace) (f : C(HausdorffSourceSpace, ℝ)) :
    (gomesHausdorffStieltjesRecord μ = gomesHausdorffStieltjesRecord ν ∧
      (∫ y, f y ∂(μ : Measure HausdorffSourceSpace)) =
        (∫ y, f y ∂(ν : Measure HausdorffSourceSpace))) ↔
      μ = ν ∨ (gomesHausdorffStieltjesRecord μ = gomesHausdorffStieltjesRecord ν ∧
        f gomesHausdorffZero = 0) := by
  constructor
  · rintro ⟨h, hf⟩
    by_cases hz : f gomesHausdorffZero = 0
    · exact Or.inr ⟨h, hz⟩
    · left
      apply (gomesHausdorffStieltjes_mass_reconstruction μ ν).mp
      refine ⟨h, ?_⟩
      have hd := (gomesHausdorffStieltjesRecord_eq_iff_report_defect μ ν).mp h f
      rw [hf, sub_self] at hd
      have hm := (mul_eq_zero.mp hd.symm).resolve_right hz
      exact_mod_cast sub_eq_zero.mp hm
  · rintro (rfl | ⟨h, hz⟩)
    · exact ⟨rfl, rfl⟩
    · refine ⟨h, ?_⟩
      have hd := (gomesHausdorffStieltjesRecord_eq_iff_report_defect μ ν).mp h f
      rw [hz, mul_zero] at hd
      exact sub_eq_zero.mp hd

/-- The existing CDD phase supplies exactly the endpoint-sensitive report needed for recovery. -/
theorem gomesHausdorffStieltjes_CDDPhase_classification
    (μ ν : FiniteMeasure HausdorffSourceSpace) (θ : ℝ) :
    (gomesHausdorffStieltjesRecord μ = gomesHausdorffStieltjesRecord ν ∧
      hausdorffCDDPhase (μ : Measure HausdorffSourceSpace) θ =
        hausdorffCDDPhase (ν : Measure HausdorffSourceSpace) θ) ↔
      μ = ν ∨ (gomesHausdorffStieltjesRecord μ = gomesHausdorffStieltjesRecord ν ∧ θ = 0) := by
  have h := gomesHausdorffStieltjes_singleReport_classification μ ν
    ⟨fun y => cddPhaseKernel (y : ℝ) θ,
      (continuous_cddPhaseKernel θ).comp continuous_subtype_val⟩
  simpa [hausdorffCDDPhase, gomesHausdorffZero, cddPhaseKernel_zero,
    Real.sinh_eq_zero] using h

/-- A single extra continuous report reconstructs all sources exactly when it sees the endpoint. -/
theorem gomesHausdorffStieltjes_singleReport_injective_iff
    (f : C(HausdorffSourceSpace, ℝ)) :
    Function.Injective (fun μ : FiniteMeasure HausdorffSourceSpace =>
      (gomesHausdorffStieltjesRecord μ, ∫ y, f y ∂(μ : Measure HausdorffSourceSpace))) ↔
      f gomesHausdorffZero ≠ 0 := by
  constructor
  · intro hi hz
    have hr : gomesHausdorffStieltjesRecord (0 : FiniteMeasure HausdorffSourceSpace) =
        gomesHausdorffStieltjesRecord gomesHausdorffZeroAtom := by
      simpa using (gomesHausdorffStieltjesRecord_zeroCompletion
        (0 : FiniteMeasure HausdorffSourceSpace) 1).symm
    have ho := (gomesHausdorffStieltjes_singleReport_classification
      (0 : FiniteMeasure HausdorffSourceSpace) gomesHausdorffZeroAtom f).mpr
      (Or.inr ⟨hr, hz⟩)
    have he := hi (Prod.ext ho.1 ho.2)
    have hc := congrArg (fun μ : FiniteMeasure HausdorffSourceSpace =>
      (μ : Measure HausdorffSourceSpace) Set.univ) he
    simp [gomesHausdorffZeroAtom] at hc
  · intro hz μ ν h
    rcases (gomesHausdorffStieltjes_singleReport_classification μ ν f).mp
        ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩ with he | ⟨_, hf⟩
    · exact he
    · exact False.elim (hz hf)

/-- A single CDD phase completes Stieltjes reconstruction exactly at nonzero rapidity. -/
theorem gomesHausdorffStieltjes_CDDPhase_injective_iff (θ : ℝ) :
    Function.Injective (fun μ : FiniteMeasure HausdorffSourceSpace =>
      (gomesHausdorffStieltjesRecord μ,
        hausdorffCDDPhase (μ : Measure HausdorffSourceSpace) θ)) ↔ θ ≠ 0 := by
  have h := gomesHausdorffStieltjes_singleReport_injective_iff
    (⟨fun y => cddPhaseKernel (y : ℝ) θ,
      (continuous_cddPhaseKernel θ).comp continuous_subtype_val⟩ : C(HausdorffSourceSpace, ℝ))
  simpa [hausdorffCDDPhase, gomesHausdorffZero, cddPhaseKernel_zero,
    Real.sinh_eq_zero] using h

/-- A source is completely invisible exactly when it consists entirely of its zero atom. -/
theorem gomesHausdorffStieltjesRecord_zero_iff_atom
    (μ : FiniteMeasure HausdorffSourceSpace) :
    gomesHausdorffStieltjesRecord μ = 0 ↔ μ = μ.mass • gomesHausdorffZeroAtom := by
  have h := gomesHausdorffStieltjesRecord_eq_iff_balanced μ 0
  have hz : gomesHausdorffStieltjesRecord (0 : FiniteMeasure HausdorffSourceSpace) = 0 := by
    funext t
    simp [gomesHausdorffStieltjesRecord]
  rw [hz] at h
  simpa using h

end GaloisForLFunctions.HTGeometry
