import GaloisForLFunctions.RHTower.GomesClarkObservationReconstruction

/-!
# Exact reconstruction from the corpus's local punctured interval laws

The earlier record classifications extend to the literal `0 < |t| < r` sampling regime in
`SuzukiClarkScrewRigidity`. Stieltjes and fixed Clark germs retain their respective endpoint
ambiguities. Reciprocal germs determine total mass by continuity at the omitted base point,
so the original uniqueness interface's separately supplied mass equality is redundant here.
These are experimental source-reconstruction applications of arXiv:2607.24901, not gauge-category
claims.
-/

noncomputable section
open MeasureTheory GaloisForLFunctions.HTGeometry
open scoped NNReal ENNReal

namespace RHTower

/-- The corpus's punctured observation interval, packaged without a separate proof premise. -/
abbrev GomesClarkGermParameter (r : Set.Ioc (0 : ℝ) 1) :=
  {t : ℝ // 0 < |t| ∧ |t| < (r : ℝ)}

/-- Continuous inclusion of the unpunctured local interval into the nonsingular domain. -/
def gomesClarkLocalInclusion (r : Set.Ioc (0 : ℝ) 1) :
    C(Set.Ioo (-(r : ℝ)) r, Set.Ioi (-1 : ℝ)) where
  toFun t := ⟨t, lt_of_le_of_lt (neg_le_neg r.property.2) t.property.1⟩
  continuous_toFun := continuous_subtype_val.subtype_mk
    (fun t => lt_of_le_of_lt (neg_le_neg r.property.2) t.property.1)

/-- Include a punctured local sample into the full observation domain. -/
def gomesClarkGermInclusion (r : Set.Ioc (0 : ℝ) 1) (t : GomesClarkGermParameter r) :
    Set.Ioi (-1 : ℝ) := gomesClarkLocalInclusion r ⟨t, abs_lt.mp t.property.2⟩

/-- Restrict any observation bank to the exact local punctured data in the corpus. -/
def gomesClarkGerm (r : Set.Ioc (0 : ℝ) 1) (f : Set.Ioi (-1 : ℝ) → ℝ)
    (t : GomesClarkGermParameter r) : ℝ := f (gomesClarkGermInclusion r t)

/-- A Stieltjes germ has exactly the same source ambiguity as its full observation bank. -/
theorem gomesStieltjesGerm_eq_iff_full (r : Set.Ioc (0 : ℝ) 1)
    (μ ν : FiniteMeasure HausdorffSourceSpace) :
    gomesClarkGerm r (gomesHausdorffStieltjesRecord μ) =
        gomesClarkGerm r (gomesHausdorffStieltjesRecord ν) ↔
      gomesHausdorffStieltjesRecord μ = gomesHausdorffStieltjesRecord ν := by
  constructor
  · intro h
    apply (gomesHausdorffStieltjesRecord_eq_iff_balanced μ ν).mpr
    apply FiniteMeasure.toMeasure_injective
    apply hausdorffSource_eq_of_stieltjes_eq r.property.1 r.property.2
    · rw [gomesHausdorffMoment_zeroCompletion, gomesHausdorffMoment_zeroCompletion]
      simp [hausdorffMoment, add_comm]
    · intro t ht htr
      let p : GomesClarkGermParameter r := ⟨t, ht, htr⟩
      change gomesHausdorffStieltjesRecord (μ + ν.mass • gomesHausdorffZeroAtom)
          (gomesClarkGermInclusion r p) =
        gomesHausdorffStieltjesRecord (ν + μ.mass • gomesHausdorffZeroAtom)
          (gomesClarkGermInclusion r p)
      rw [gomesHausdorffStieltjesRecord_zeroCompletion,
        gomesHausdorffStieltjesRecord_zeroCompletion]
      exact congrFun h p
  · intro h
    exact congrArg (gomesClarkGerm r) h

/-- A fixed Clark germ has exactly the full bank's endpoint-one ambiguity. -/
theorem gomesClarkFixedGerm_eq_iff_full (r : Set.Ioc (0 : ℝ) 1)
    (μ ν : FiniteMeasure HausdorffSourceSpace) :
    gomesClarkGerm r (gomesClarkFixedRecord μ) = gomesClarkGerm r (gomesClarkFixedRecord ν) ↔
      gomesClarkFixedRecord μ = gomesClarkFixedRecord ν := by
  constructor
  · intro h
    apply (gomesClarkFixedRecord_eq_iff_balanced μ ν).mpr
    apply FiniteMeasure.toMeasure_injective
    have hm : hausdorffMoment (↑(μ + ν.mass • gomesHausdorffOneAtom)) 0 =
        hausdorffMoment (↑(ν + μ.mass • gomesHausdorffOneAtom)) 0 := by
      change (∫ _ : HausdorffSourceSpace, (1 : ℝ)
          ∂(↑(μ + ν.mass • gomesHausdorffOneAtom))) =
        ∫ _ : HausdorffSourceSpace, (1 : ℝ) ∂(↑(ν + μ.mass • gomesHausdorffOneAtom))
      let oneTest : C(HausdorffSourceSpace, ℝ) := ⟨fun _ => 1, continuous_const⟩
      change (∫ y, oneTest y ∂(↑(μ + ν.mass • gomesHausdorffOneAtom))) =
        ∫ y, oneTest y ∂(↑(ν + μ.mass • gomesHausdorffOneAtom))
      rw [gomesClarkOneCompletion_report, gomesClarkOneCompletion_report]
      dsimp [oneTest]
      simp only [integral_const, smul_eq_mul, mul_one]
      change (μ.mass : ℝ) + ν.mass = (ν.mass : ℝ) + μ.mass
      exact add_comm _ _
    apply hausdorffSource_eq_of_stieltjes_eq r.property.1 r.property.2 hm
    intro t ht htr
    let p : GomesClarkGermParameter r := ⟨t, ht, htr⟩
    have hp : (-1 : ℝ) < t := (gomesClarkGermInclusion r p).property
    apply stieltjes_eq_of_fixedKernel_eq (by linarith) hm
    change gomesClarkFixedRecord (μ + ν.mass • gomesHausdorffOneAtom)
        (gomesClarkGermInclusion r p) =
      gomesClarkFixedRecord (ν + μ.mass • gomesHausdorffOneAtom)
        (gomesClarkGermInclusion r p)
    rw [gomesClarkFixedRecord_oneCompletion, gomesClarkFixedRecord_oneCompletion]
    exact congrFun h p
  · intro h
    exact congrArg (gomesClarkGerm r) h

/-- The original punctured reciprocal interval law determines the source with no mass premise. -/
theorem gomesClarkReciprocalGerm_injective (r : Set.Ioc (0 : ℝ) 1) :
    Function.Injective (fun μ : FiniteMeasure HausdorffSourceSpace =>
      gomesClarkGerm r (gomesClarkReciprocalRecord μ)) := by
  intro μ ν h
  have hr : (0 : ℝ) < r := r.property.1
  letI : Nontrivial (Set.Ioo (-(r : ℝ)) r) := by
    refine ⟨⟨⟨0, by constructor <;> linarith⟩,
      ⟨(r : ℝ) / 2, by constructor <;> linarith⟩, ?_⟩⟩
    intro h
    have hv := congrArg Subtype.val h
    change (0 : ℝ) = (r : ℝ) / 2 at hv
    linarith
  let z : Set.Ioo (-(r : ℝ)) r := ⟨0, neg_lt_zero.mpr r.property.1, r.property.1⟩
  have he : (fun t => gomesClarkReciprocalRecord μ (gomesClarkLocalInclusion r t)) =
      fun t => gomesClarkReciprocalRecord ν (gomesClarkLocalInclusion r t) := by
    apply Continuous.ext_on (dense_compl_singleton z)
      ((gomesClarkReciprocalRecord_continuous μ).comp (gomesClarkLocalInclusion r).continuous)
      ((gomesClarkReciprocalRecord_continuous ν).comp (gomesClarkLocalInclusion r).continuous)
    intro t ht
    have hne : (t : ℝ) ≠ 0 := by
      intro hz
      exact ht (Subtype.ext hz)
    exact congrFun h ⟨t, abs_pos.mpr hne, abs_lt.mpr t.property⟩
  have hm : (μ.mass : ℝ) = (ν.mass : ℝ) := by
    have hz := congrFun he z
    change gomesClarkReciprocalRecord μ ⟨0, by change (-1 : ℝ) < 0; linarith⟩ =
      gomesClarkReciprocalRecord ν ⟨0, by change (-1 : ℝ) < 0; linarith⟩ at hz
    simpa only [gomesClarkReciprocalRecord_zero] using hz
  apply FiniteMeasure.toMeasure_injective
  apply clarkSource_eq_of_reciprocal_transform_eq r.property.1 r.property.2
  · change (∫ _ : HausdorffSourceSpace, (1 : ℝ) ∂(μ : Measure HausdorffSourceSpace)) =
      ∫ _ : HausdorffSourceSpace, (1 : ℝ) ∂(ν : Measure HausdorffSourceSpace)
    rw [integral_const, integral_const]
    simp only [smul_eq_mul, mul_one]
    change (μ.mass : ℝ) = (ν.mass : ℝ)
    exact hm
  · intro t ht htr
    exact congrFun h ⟨t, ht, htr⟩

/-- A local Stieltjes germ plus one fixed Clark value already reconstructs the entire source. -/
theorem gomesStieltjesGerm_ClarkFixed_injective (r : Set.Ioc (0 : ℝ) 1)
    (t : Set.Ioi (-1 : ℝ)) :
    Function.Injective (fun μ : FiniteMeasure HausdorffSourceSpace =>
      (gomesClarkGerm r (gomesHausdorffStieltjesRecord μ), gomesClarkFixedRecord μ t)) := by
  intro μ ν h
  have hs : gomesClarkFixedRecord μ t = gomesClarkFixedRecord ν t := congrArg Prod.snd h
  apply gomesClarkFixed_completes_Stieltjes t
  apply Prod.ext
  · exact (gomesStieltjesGerm_eq_iff_full r μ ν).mp (congrArg Prod.fst h)
  · exact hs

/-- A local fixed Clark germ plus one Stieltjes value also reconstructs the source. -/
theorem gomesClarkFixedGerm_Stieltjes_injective (r : Set.Ioc (0 : ℝ) 1)
    (t : Set.Ioi (-1 : ℝ)) :
    Function.Injective (fun μ : FiniteMeasure HausdorffSourceSpace =>
      (gomesClarkGerm r (gomesClarkFixedRecord μ), gomesHausdorffStieltjesRecord μ t)) := by
  intro μ ν h
  have hs : gomesHausdorffStieltjesRecord μ t = gomesHausdorffStieltjesRecord ν t :=
    congrArg Prod.snd h
  apply gomesStieltjes_completes_ClarkFixed t
  apply Prod.ext
  · exact (gomesClarkFixedGerm_eq_iff_full r μ ν).mp (congrArg Prod.fst h)
  · exact hs

end RHTower
