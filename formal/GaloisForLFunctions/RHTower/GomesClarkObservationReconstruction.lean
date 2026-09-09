import GaloisForLFunctions.HTGeometry.GomesHausdorffReflection
import GaloisForLFunctions.RHTower.SuzukiClarkScrewRigidity

/-!
# Exact information retained by the existing Clark observation kernels

Experimental application of arXiv:2607.24901's reconstruction distinction to the literal
kernels in `SuzukiClarkScrewRigidity`. The fixed Clark bank loses exactly an atom at one,
whereas the compact Stieltjes bank loses exactly an atom at zero. The reciprocal bank retains
both. All source inputs are finite positive measures; no mass-equality premise is supplied.
-/

noncomputable section
open MeasureTheory GaloisForLFunctions.HTGeometry
open scoped NNReal ENNReal

namespace RHTower

/-- The existing fixed Clark integrand as a continuous compact-source test. -/
def gomesClarkFixedTest (t : Set.Ioi (-1 : ℝ)) : C(HausdorffSourceSpace, ℝ) :=
  ⟨fun y => 1 - ((t : ℝ) + 1) * stieltjesKernel t y,
    continuous_const.sub (continuous_const.mul (gomesHausdorffStieltjesTest t).continuous)⟩

/-- The full fixed Clark observation bank from the corpus's compactified interval law. -/
def gomesClarkFixedRecord (μ : FiniteMeasure HausdorffSourceSpace)
    (t : Set.Ioi (-1 : ℝ)) : ℝ :=
  ∫ y, (1 - ((t : ℝ) + 1) * stieltjesKernel t y) ∂(μ : Measure HausdorffSourceSpace)

/-- The reciprocal transform appearing in the corpus's Theorem T interface. -/
def gomesClarkReciprocalRecord (μ : FiniteMeasure HausdorffSourceSpace)
    (t : Set.Ioi (-1 : ℝ)) : ℝ :=
  ∫ y, (1 : ℝ) / (1 + (t : ℝ) * (y : ℝ)) ∂(μ : Measure HausdorffSourceSpace)

/-- A fixed Clark test sees the zero endpoint with unit strength. -/
theorem gomesClarkFixedTest_zero (t : Set.Ioi (-1 : ℝ)) :
    gomesClarkFixedTest t gomesHausdorffZero = 1 := by
  simp [gomesClarkFixedTest, stieltjesKernel, gomesHausdorffZero]

/-- A fixed Clark test is completely blind at the endpoint one. -/
theorem gomesClarkFixedTest_one (t : Set.Ioi (-1 : ℝ)) :
    gomesClarkFixedTest t gomesHausdorffOne = 0 := by
  have ht : (-1 : ℝ) < t := t.property
  have hd : 1 + (t : ℝ) ≠ 0 := by linarith
  dsimp [gomesClarkFixedTest, stieltjesKernel, gomesHausdorffOne]
  field_simp [hd]
  ring

/-- Reflection and the parameter involution transport the actual fixed Clark bank. -/
theorem gomesClarkFixedRecord_reflection (μ : FiniteMeasure HausdorffSourceSpace)
    (t : Set.Ioi (-1 : ℝ)) :
    (1 + (t : ℝ)) * gomesClarkFixedRecord μ t =
      gomesHausdorffStieltjesRecord (gomesHausdorffReflectSource μ)
        (gomesHausdorffDualParameter t) := by
  rw [gomesHausdorffStieltjesRecord, gomesHausdorffReflectSource_integral]
  simp_rw [gomesHausdorffStieltjes_reflection]
  rw [integral_const_mul]
  rfl

/-- Equal fixed Clark records are exactly equal Stieltjes records of the reflected sources. -/
theorem gomesClarkFixedRecord_eq_iff_reflected
    (μ ν : FiniteMeasure HausdorffSourceSpace) :
    gomesClarkFixedRecord μ = gomesClarkFixedRecord ν ↔
      gomesHausdorffStieltjesRecord (gomesHausdorffReflectSource μ) =
        gomesHausdorffStieltjesRecord (gomesHausdorffReflectSource ν) := by
  constructor
  · intro h
    funext t
    have hμ := gomesClarkFixedRecord_reflection μ (gomesHausdorffDualParameter t)
    have hν := gomesClarkFixedRecord_reflection ν (gomesHausdorffDualParameter t)
    rw [gomesHausdorffDualParameter_involutive] at hμ hν
    rw [← hμ, ← hν, h]
  · intro h
    funext t
    have ht : (-1 : ℝ) < t := t.property
    apply mul_left_cancel₀ (show 1 + (t : ℝ) ≠ 0 by linarith)
    rw [gomesClarkFixedRecord_reflection, gomesClarkFixedRecord_reflection, h]

/-- Endpoint-one mass is the sole ambiguity of the full fixed Clark observation bank. -/
theorem gomesClarkFixedRecord_eq_iff_balanced
    (μ ν : FiniteMeasure HausdorffSourceSpace) :
    gomesClarkFixedRecord μ = gomesClarkFixedRecord ν ↔
      μ + ν.mass • gomesHausdorffOneAtom = ν + μ.mass • gomesHausdorffOneAtom := by
  rw [gomesClarkFixedRecord_eq_iff_reflected,
    gomesHausdorffStieltjesRecord_eq_iff_balanced]
  simp only [gomesHausdorffReflectSource_mass]
  constructor
  · intro h
    have hr := congrArg gomesHausdorffReflectSource h
    simp only [gomesHausdorffReflectSource_add, gomesHausdorffReflectSource_smul,
      gomesHausdorffReflectSource_zeroAtom] at hr
    rw [gomesHausdorffReflectSource_involutive, gomesHausdorffReflectSource_involutive] at hr
    exact hr
  · intro h
    have hr := congrArg gomesHausdorffReflectSource h
    simpa only [gomesHausdorffReflectSource_add, gomesHausdorffReflectSource_smul,
      gomesHausdorffReflectSource_oneAtom] using hr

/-- Any continuous report changes under added endpoint-one mass by its endpoint value. -/
theorem gomesClarkOneCompletion_report (μ : FiniteMeasure HausdorffSourceSpace)
    (w : ℝ≥0) (f : C(HausdorffSourceSpace, ℝ)) :
    (∫ y, f y ∂((μ + w • gomesHausdorffOneAtom : FiniteMeasure HausdorffSourceSpace) :
      Measure HausdorffSourceSpace)) =
      (∫ y, f y ∂(μ : Measure HausdorffSourceSpace)) + (w : ℝ) * f gomesHausdorffOne := by
  rw [FiniteMeasure.toMeasure_add, integral_add_measure
    (integrable_of_continuous _ f.continuous) (integrable_of_continuous _ f.continuous)]
  simp [gomesHausdorffOneAtom, NNReal.smul_def, smul_eq_mul]

/-- Arbitrary additional endpoint-one mass leaves the fixed Clark record unchanged. -/
theorem gomesClarkFixedRecord_oneCompletion (μ : FiniteMeasure HausdorffSourceSpace) (w : ℝ≥0) :
    gomesClarkFixedRecord (μ + w • gomesHausdorffOneAtom) = gomesClarkFixedRecord μ := by
  funext t
  have h := gomesClarkOneCompletion_report μ w (gomesClarkFixedTest t)
  change (∫ y, gomesClarkFixedTest t y ∂(↑(μ + w • gomesHausdorffOneAtom))) =
    ∫ y, gomesClarkFixedTest t y ∂(μ : Measure HausdorffSourceSpace)
  simpa only [gomesClarkFixedTest_one, mul_zero, add_zero] using h

/-- Every remaining continuous report is determined up to the exact hidden mass difference. -/
theorem gomesClarkFixedRecord_eq_iff_report_defect
    (μ ν : FiniteMeasure HausdorffSourceSpace) :
    gomesClarkFixedRecord μ = gomesClarkFixedRecord ν ↔
      ∀ f : C(HausdorffSourceSpace, ℝ),
        (∫ y, f y ∂(μ : Measure HausdorffSourceSpace)) -
          (∫ y, f y ∂(ν : Measure HausdorffSourceSpace)) =
          ((μ.mass : ℝ) - (ν.mass : ℝ)) * f gomesHausdorffOne := by
  constructor
  · intro h f
    have hb := (gomesClarkFixedRecord_eq_iff_balanced μ ν).mp h
    have hf := congrArg (fun ρ : FiniteMeasure HausdorffSourceSpace =>
      ∫ y, f y ∂(ρ : Measure HausdorffSourceSpace)) hb
    rw [gomesClarkOneCompletion_report, gomesClarkOneCompletion_report] at hf
    linear_combination hf
  · intro h
    funext t
    have hf := h (gomesClarkFixedTest t)
    rw [gomesClarkFixedTest_one, mul_zero] at hf
    exact sub_eq_zero.mp hf

/-- Total mass and the fixed bank jointly reconstruct the source. -/
theorem gomesClarkFixedRecord_mass_reconstruction (μ ν : FiniteMeasure HausdorffSourceSpace) :
    (gomesClarkFixedRecord μ = gomesClarkFixedRecord ν ∧ μ.mass = ν.mass) ↔ μ = ν := by
  constructor
  · rintro ⟨h, hm⟩
    have hb := (gomesClarkFixedRecord_eq_iff_balanced μ ν).mp h
    rw [hm] at hb
    apply FiniteMeasure.eq_of_forall_apply_eq
    intro s _
    have hs := congrArg (fun ρ : FiniteMeasure HausdorffSourceSpace => ρ s) hb
    simp only [FiniteMeasure.coeFn_add, Pi.add_apply] at hs
    exact add_right_cancel hs
  · rintro rfl
    exact ⟨rfl, rfl⟩

/-- The fixed record's exact affine decomposition uses the actual source mass. -/
theorem gomesClarkFixedRecord_mass_split (μ : FiniteMeasure HausdorffSourceSpace)
    (t : Set.Ioi (-1 : ℝ)) :
    gomesClarkFixedRecord μ t = (μ.mass : ℝ) - ((t : ℝ) + 1) *
      gomesHausdorffStieltjesRecord μ t := by
  have hk : Integrable (stieltjesKernel (t : ℝ)) (μ : Measure HausdorffSourceSpace) :=
    integrable_of_continuous _ (gomesHausdorffStieltjesTest t).continuous
  rw [gomesClarkFixedRecord, integral_sub (integrable_const 1) (hk.const_mul _),
    integral_const_mul, integral_const]
  simp only [smul_eq_mul, mul_one]
  rfl

/-- A single fixed Clark value supplies precisely the information missing from a Stieltjes bank. -/
theorem gomesClarkFixed_completes_Stieltjes (t : Set.Ioi (-1 : ℝ)) :
    Function.Injective (fun μ : FiniteMeasure HausdorffSourceSpace =>
      (gomesHausdorffStieltjesRecord μ, gomesClarkFixedRecord μ t)) := by
  apply (gomesHausdorffStieltjes_singleReport_injective_iff (gomesClarkFixedTest t)).mpr
  rw [gomesClarkFixedTest_zero]
  exact one_ne_zero

/-- Conversely, one Stieltjes value completes the full fixed Clark bank. -/
theorem gomesStieltjes_completes_ClarkFixed (t : Set.Ioi (-1 : ℝ)) :
    Function.Injective (fun μ : FiniteMeasure HausdorffSourceSpace =>
      (gomesClarkFixedRecord μ, gomesHausdorffStieltjesRecord μ t)) := by
  intro μ ν h
  have hf : gomesClarkFixedRecord μ = gomesClarkFixedRecord ν := congrArg Prod.fst h
  have hs : gomesHausdorffStieltjesRecord μ t = gomesHausdorffStieltjesRecord ν t := congrArg Prod.snd h
  apply (gomesClarkFixedRecord_mass_reconstruction μ ν).mp
  refine ⟨hf, ?_⟩
  have hp := congrFun hf t
  rw [gomesClarkFixedRecord_mass_split, gomesClarkFixedRecord_mass_split, hs] at hp
  have hm : (μ.mass : ℝ) = (ν.mass : ℝ) := by linarith
  exact_mod_cast hm

/-- The reciprocal record separates mass from the Stieltjes record exactly. -/
theorem gomesClarkReciprocalRecord_mass_split (μ : FiniteMeasure HausdorffSourceSpace)
    (t : Set.Ioi (-1 : ℝ)) :
    gomesClarkReciprocalRecord μ t = (μ.mass : ℝ) - (t : ℝ) *
      gomesHausdorffStieltjesRecord μ t := by
  have hk : Integrable (stieltjesKernel (t : ℝ)) (μ : Measure HausdorffSourceSpace) :=
    integrable_of_continuous _ (gomesHausdorffStieltjesTest t).continuous
  rw [gomesClarkReciprocalRecord]
  have he : (fun y : HausdorffSourceSpace => (1 : ℝ) / (1 + (t : ℝ) * (y : ℝ))) =
      fun y => 1 - (t : ℝ) * stieltjesKernel t y :=
    funext (fun y => reciprocalKernel_eq (ne_of_gt (gomesHausdorffStieltjes_denominator_pos t y)))
  rw [he, integral_sub (integrable_const 1) (hk.const_mul _), integral_const_mul, integral_const]
  simp only [smul_eq_mul, mul_one]
  rfl

/-- The zero-parameter reciprocal measurement is exactly total mass. -/
theorem gomesClarkReciprocalRecord_zero (μ : FiniteMeasure HausdorffSourceSpace) :
    gomesClarkReciprocalRecord μ ⟨0, by change (-1 : ℝ) < 0; linarith⟩ = μ.mass := by
  rw [gomesClarkReciprocalRecord_mass_split]
  simp

/-- The reciprocal bank reconstructs every finite source without a supplied mass condition. -/
theorem gomesClarkReciprocalRecord_injective : Function.Injective gomesClarkReciprocalRecord := by
  intro μ ν h
  apply FiniteMeasure.toMeasure_injective
  apply clarkSource_eq_of_reciprocal_transform_eq (r := 1) zero_lt_one le_rfl
  · have hm := congrFun h (⟨0, by change (-1 : ℝ) < 0; linarith⟩ : Set.Ioi (-1 : ℝ))
    rw [gomesClarkReciprocalRecord_zero, gomesClarkReciprocalRecord_zero] at hm
    change (∫ _ : HausdorffSourceSpace, (1 : ℝ) ∂(μ : Measure HausdorffSourceSpace)) =
      ∫ _ : HausdorffSourceSpace, (1 : ℝ) ∂(ν : Measure HausdorffSourceSpace)
    rw [integral_const, integral_const]
    simp only [smul_eq_mul, mul_one]
    change (μ.mass : ℝ) = (ν.mass : ℝ)
    exact hm
  · intro t _ ht
    exact congrFun h ⟨t, (abs_lt.mp ht).1⟩

/-- Reciprocal records are continuous in their nonsingular parameter. -/
theorem gomesClarkReciprocalRecord_continuous (μ : FiniteMeasure HausdorffSourceSpace) :
    Continuous (gomesClarkReciprocalRecord μ) := by
  have he : gomesClarkReciprocalRecord μ =
      fun (t : Set.Ioi (-1 : ℝ)) => (μ.mass : ℝ) - (t : ℝ) * gomesHausdorffStieltjesRecord μ t :=
    funext (gomesClarkReciprocalRecord_mass_split μ)
  rw [he]
  exact continuous_const.sub (continuous_subtype_val.mul (gomesHausdorffStieltjesRecord_continuous μ))

/-- Omitting any single reciprocal sample still leaves an injective source record. -/
theorem gomesClarkReciprocalRecord_offPoint_injective (p : Set.Ioi (-1 : ℝ)) :
    Function.Injective (fun μ : FiniteMeasure HausdorffSourceSpace =>
      fun t : {t : Set.Ioi (-1 : ℝ) // t ≠ p} => gomesClarkReciprocalRecord μ t) := by
  intro μ ν h
  apply gomesClarkReciprocalRecord_injective
  apply Continuous.ext_on (dense_compl_singleton p)
    (gomesClarkReciprocalRecord_continuous μ) (gomesClarkReciprocalRecord_continuous ν)
  intro t ht
  exact congrFun h ⟨t, ht⟩

end RHTower
