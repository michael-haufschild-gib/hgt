import GaloisForLFunctions.HTGeometry.NevanlinnaNormalizationTwist
import GaloisForLFunctions.HTGeometry.AnalyticNevanlinnaBoundaryRealAnalytic
import GaloisForLFunctions.HTGeometry.AnalyticNevanlinnaCarrierConstruction
import GaloisForLFunctions.HTGeometry.NevBauerUnconditional
import GaloisForLFunctions.HTGeometry.NevFiberCountable
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Spectral-type transport through the boundary barycenter

Barycentring the `N`-extremal leaves against a projective parameter law transports the spectral
type of the parameter law to the carrier.

*Pure point.*  Each leaf is carried by the level set of its own projective label, and those level
sets are countable for the Nevanlinna matrix data of an indeterminate moment sequence.  A parameter
law carried by a countable set therefore produces a carrier concentrated on a countable set.

*Absolutely continuous.*  A parameter law absolutely continuous with respect to Lebesgue measure on
the finite chart produces a carrier absolutely continuous with respect to Lebesgue measure.  The
mechanism is Luzin's property (N) for the real-analytic label `-d/c`: it maps Lebesgue-null sets to
Lebesgue-null sets, so a null carrier set can only be seen by a null set of parameters.

*Mixtures.*  Barycentring is additive and positively homogeneous and turns mutually singular
parameter laws into mutually singular carriers, so a mixture of parameter laws of the three pure
types produces a carrier whose spectral decomposition has exactly the mixing mass vector.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter MeasureTheory OnePoint Set Topology
open scoped OnePoint Topology ENNReal

noncomputable section

/-- **Luzin's property (N) on the line.**  A function differentiable on a set maps every
Lebesgue-null subset to a Lebesgue-null set. -/
theorem volume_image_eq_zero_of_differentiableOn {f : ℝ → ℝ} {s : Set ℝ}
    (hf : DifferentiableOn ℝ f s) (h0 : (volume : Measure ℝ) s = 0) :
    (volume : Measure ℝ) (f '' s) = 0 :=
  MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    (μ := (volume : Measure ℝ)) hf h0

namespace NevanlinnaBoundaryFamily

variable {s : ℕ → ℝ} (F : NevanlinnaBoundaryFamily s)

theorem measurable_projectiveLabel : Measurable F.matrix.projectiveLabel :=
  (F.matrix.continuous_projectiveLabel F.continuous_c F.continuous_d).measurable

/-- The leaf kernel of a boundary family, as a measure-valued map. -/
def leafMeasure (t : OnePoint ℝ) : Measure ℝ := (F.leaf t : Measure ℝ)

/-- The barycenter of an arbitrary projective parameter measure. -/
def measureBarycenter (eta : Measure (OnePoint ℝ)) : Measure ℝ :=
  boundaryBarycenter eta F.leafMeasure

theorem measureBarycenter_coe (eta : ProbabilityMeasure (OnePoint ℝ)) :
    F.measureBarycenter (eta : Measure (OnePoint ℝ)) = (F.barycenter eta : Measure ℝ) := rfl

/-- The barycenter of a parameter measure reads back exactly that measure along the projective
support label. -/
theorem map_projectiveLabel_measureBarycenter (eta : Measure (OnePoint ℝ)) :
    Measure.map F.matrix.projectiveLabel (F.measureBarycenter eta) = eta :=
  map_boundaryBarycenter_eq F.leafMeasure F.matrix.projectiveLabel
    F.measurable_leaf F.measurable_projectiveLabel F.map_projectiveLabel_leaf eta

/-- Mass of the barycenter as the parameter integral of the leaf masses. -/
theorem measureBarycenter_apply (eta : Measure (OnePoint ℝ)) {E : Set ℝ}
    (hE : MeasurableSet E) :
    F.measureBarycenter eta E = ∫⁻ t, F.leafMeasure t E ∂eta :=
  Measure.bind_apply hE F.measurable_leaf.aemeasurable

/-- Label preimages have exactly the parameter mass. -/
theorem measureBarycenter_preimage (eta : Measure (OnePoint ℝ)) {A : Set (OnePoint ℝ)}
    (hA : MeasurableSet A) :
    F.measureBarycenter eta (F.matrix.projectiveLabel ⁻¹' A) = eta A := by
  rw [← Measure.map_apply F.measurable_projectiveLabel hA,
    F.map_projectiveLabel_measureBarycenter eta]

/-- **Pure-point transport.**  If the projective parameter measure is carried by a countable set
and every label level set is countable, the barycenter is carried by a countable set. -/
theorem measureBarycenter_countableCarrier
    (hfib : ∀ t : OnePoint ℝ, {x : ℝ | F.matrix.projectiveLabel x = t}.Countable)
    (eta : Measure (OnePoint ℝ)) {S : Set (OnePoint ℝ)}
    (hS : S.Countable) (hSmeas : MeasurableSet S) (hcar : eta Sᶜ = 0) :
    ∃ C : Set ℝ, C.Countable ∧ F.measureBarycenter eta Cᶜ = 0 := by
  refine ⟨{x : ℝ | F.matrix.projectiveLabel x ∈ S}, ?_, ?_⟩
  · have hunion : {x : ℝ | F.matrix.projectiveLabel x ∈ S} =
        ⋃ t ∈ S, {x : ℝ | F.matrix.projectiveLabel x = t} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
      exact ⟨fun hx => ⟨_, hx, rfl⟩, fun ⟨t, ht, hx⟩ => hx ▸ ht⟩
    rw [hunion]
    exact hS.biUnion fun t _ => hfib t
  · have hpre : {x : ℝ | F.matrix.projectiveLabel x ∈ S}ᶜ =
        F.matrix.projectiveLabel ⁻¹' Sᶜ := by
      ext x
      simp [Set.mem_preimage]
    rw [hpre, F.measureBarycenter_preimage eta hSmeas.compl]
    exact hcar

/-- Only parameters in the label image of a set can charge that set. -/
theorem leafMeasure_eq_zero_of_notMem_image (t : OnePoint ℝ) {E : Set ℝ}
    (ht : t ∉ F.matrix.projectiveLabel '' E) : F.leafMeasure t E = 0 := by
  have hsub : E ⊆ {x : ℝ | F.matrix.projectiveLabel x = t}ᶜ := by
    intro x hx hxt
    exact ht ⟨x, hx, hxt⟩
  exact measure_mono_null hsub (F.carried_label t)

/-- **Absolute-continuity transport.**  If the lower row is differentiable off its zero set and the
projective parameter measure is absolutely continuous with respect to Lebesgue measure carried on
the finite chart, then the barycenter is absolutely continuous with respect to Lebesgue measure. -/
theorem measureBarycenter_absolutelyContinuous_volume
    (hdiff : DifferentiableOn ℝ (fun x => -F.matrix.d x / F.matrix.c x)
      {x : ℝ | F.matrix.c x ≠ 0})
    (eta : Measure (OnePoint ℝ))
    (heta : eta ≪ Measure.map ((↑) : ℝ → OnePoint ℝ) (volume : Measure ℝ)) :
    F.measureBarycenter eta ≪ (volume : Measure ℝ) := by
  refine Measure.AbsolutelyContinuous.mk fun E hE hEnull => ?_
  classical
  set q : ℝ → ℝ := fun x => -F.matrix.d x / F.matrix.c x with hq
  set s0 : Set ℝ := E ∩ {x : ℝ | F.matrix.c x ≠ 0} with hs0
  have hs0null : (volume : Measure ℝ) s0 = 0 :=
    measure_mono_null Set.inter_subset_left hEnull
  have himage : (volume : Measure ℝ) (q '' s0) = 0 :=
    volume_image_eq_zero_of_differentiableOn (hdiff.mono Set.inter_subset_right) hs0null
  obtain ⟨N, hNsub, hNmeas, hNnull⟩ := exists_measurable_superset_of_null himage
  set B : Set (OnePoint ℝ) := (((↑) : ℝ → OnePoint ℝ) '' N) ∪ {(∞ : OnePoint ℝ)} with hB
  have hcoeEmb : MeasurableEmbedding ((↑) : ℝ → OnePoint ℝ) :=
    OnePoint.isOpenEmbedding_coe.measurableEmbedding
  have hBmeas : MeasurableSet B := by
    refine MeasurableSet.union ?_ ?_
    · exact hcoeEmb.measurableSet_image.2 hNmeas
    · exact (OnePoint.isClosed_infty (X := ℝ)).measurableSet
  have hBpre : ((↑) : ℝ → OnePoint ℝ) ⁻¹' B = N := by
    ext x
    constructor
    · rintro (⟨y, hy, hxy⟩ | hx)
      · exact (OnePoint.coe_eq_coe.mp hxy) ▸ hy
      · exact absurd hx (OnePoint.coe_ne_infty x)
    · intro hx
      exact Or.inl ⟨x, hx, rfl⟩
  have hBnull : Measure.map ((↑) : ℝ → OnePoint ℝ) (volume : Measure ℝ) B = 0 := by
    rw [Measure.map_apply OnePoint.continuous_coe.measurable hBmeas, hBpre]
    exact hNnull
  have hetaB : eta B = 0 := heta hBnull
  have hsubB : F.matrix.projectiveLabel '' E ⊆ B := by
    rintro t ⟨x, hx, rfl⟩
    by_cases hcx : F.matrix.c x = 0
    · exact Or.inr (by simp [NevanlinnaMatrixData.projectiveLabel, hcx])
    · refine Or.inl ⟨q x, hNsub ⟨x, ⟨hx, hcx⟩, rfl⟩, ?_⟩
      simp [NevanlinnaMatrixData.projectiveLabel, hcx, hq]
  have himageNull : eta (F.matrix.projectiveLabel '' E) = 0 :=
    measure_mono_null hsubB hetaB
  rw [F.measureBarycenter_apply eta hE]
  have hmeasFun : Measurable fun t => F.leafMeasure t E :=
    (Measure.measurable_coe hE).comp F.measurable_leaf
  rw [lintegral_eq_zero_iff hmeasFun]
  have hzero : ∀ᵐ t ∂eta, F.leafMeasure t E = 0 := by
    refine (MeasureTheory.ae_iff).2 (measure_mono_null (fun t ht => ?_) himageNull)
    by_contra htmem
    exact ht (F.leafMeasure_eq_zero_of_notMem_image t htmem)
  exact hzero

/-- **Mutual singularity is transported.**  Mutually singular parameter measures have mutually
singular barycenters: label preimages separate them exactly. -/
theorem measureBarycenter_mutuallySingular
    {eta1 eta2 : Measure (OnePoint ℝ)} (hsing : eta1 ⟂ₘ eta2) :
    F.measureBarycenter eta1 ⟂ₘ F.measureBarycenter eta2 := by
  refine ⟨F.matrix.projectiveLabel ⁻¹' hsing.nullSet,
    hsing.measurableSet_nullSet.preimage F.measurable_projectiveLabel, ?_, ?_⟩
  · rw [F.measureBarycenter_preimage eta1 hsing.measurableSet_nullSet]
    exact hsing.measure_nullSet
  · rw [← Set.preimage_compl,
      F.measureBarycenter_preimage eta2 hsing.measurableSet_nullSet.compl]
    exact hsing.measure_compl_nullSet

/-- Barycentring a mixture of parameter measures is the mixture of the barycenters. -/
theorem measureBarycenter_mixture (a b c : ℝ≥0∞) (eta1 eta2 eta3 : Measure (OnePoint ℝ)) :
    F.measureBarycenter (a • eta1 + b • eta2 + c • eta3) =
      a • F.measureBarycenter eta1 + b • F.measureBarycenter eta2 +
        c • F.measureBarycenter eta3 := by
  have hleaf : Measurable F.leafMeasure := F.measurable_leaf
  unfold measureBarycenter
  rw [boundaryBarycenter_add _ _ _ hleaf, boundaryBarycenter_add _ _ _ hleaf,
    boundaryBarycenter_smul, boundaryBarycenter_smul, boundaryBarycenter_smul]

end NevanlinnaBoundaryFamily

end

end GaloisForLFunctions.HTGeometry

namespace HTGeometry

open MeasureTheory OnePoint Set
open GaloisForLFunctions.HTGeometry
open scoped OnePoint ENNReal

noncomputable section

variable {s : ℕ → ℝ}

/-- Every label level set of the constructed boundary family is countable: it is a denominator
fiber of the Nevanlinna matrix data. -/
theorem countable_projectiveLabel_fiber (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) (t : OnePoint ℝ) :
    {x : ℝ | (nevBoundaryFamily h h0b h0).matrix.projectiveLabel x = t}.Countable := by
  induction t using OnePoint.rec with
  | infty =>
      have hset : {x : ℝ | (nevBoundaryFamily h h0b h0).matrix.projectiveLabel x =
            (∞ : OnePoint ℝ)} = (nevMatrixDataInf h h0b).infinityDenominatorFiber := by
        ext x
        rw [Set.mem_setOf_eq,
          (nevBoundaryFamily h h0b h0).matrix.projectiveLabel_eq_infty_iff x]
        exact Iff.rfl
      rw [hset]
      exact countable_infinityDenominatorFiber h h0b
  | coe tau =>
      have hset : {x : ℝ | (nevBoundaryFamily h h0b h0).matrix.projectiveLabel x =
            (tau : OnePoint ℝ)} = (nevMatrixDataInf h h0b).finiteDenominatorFiber tau := by
        ext x
        rw [Set.mem_setOf_eq,
          (nevBoundaryFamily h h0b h0).matrix.projectiveLabel_eq_coe_iff x tau]
        exact Iff.rfl
      rw [hset]
      exact countable_finiteDenominatorFiber h h0b tau

/-- The real projective label of the constructed family is differentiable off the zero set of its
denominator entry: both lower-row entries are real analytic. -/
theorem differentiableOn_nevProjectiveQuotient (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) :
    DifferentiableOn ℝ
      (fun x => -(nevBoundaryFamily h h0b h0).matrix.d x /
        (nevBoundaryFamily h h0b h0).matrix.c x)
      {x : ℝ | (nevBoundaryFamily h h0b h0).matrix.c x ≠ 0} := by
  have hc : DifferentiableOn ℝ (nevBoundaryFamily h h0b h0).matrix.c
      {x : ℝ | (nevBoundaryFamily h h0b h0).matrix.c x ≠ 0} :=
    ((analyticNevCarrierFamily h h0b h0).analyticOnNhd_boundary_c).differentiableOn.mono
      (Set.subset_univ _)
  have hd : DifferentiableOn ℝ (nevBoundaryFamily h h0b h0).matrix.d
      {x : ℝ | (nevBoundaryFamily h h0b h0).matrix.c x ≠ 0} :=
    ((analyticNevCarrierFamily h h0b h0).analyticOnNhd_boundary_d).differentiableOn.mono
      (Set.subset_univ _)
  exact hd.neg.div hc fun x hx => hx

/-- **Pure-point transport, unconditionally.**  A projective parameter law carried by a countable
set produces a carrier of the indeterminate moment fiber concentrated on a countable set. -/
theorem nevBarycenter_countableCarrier (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) (eta : Measure (OnePoint ℝ)) {S : Set (OnePoint ℝ)}
    (hS : S.Countable) (hSmeas : MeasurableSet S) (hcar : eta Sᶜ = 0) :
    ∃ C : Set ℝ, C.Countable ∧ (nevBoundaryFamily h h0b h0).measureBarycenter eta Cᶜ = 0 :=
  (nevBoundaryFamily h h0b h0).measureBarycenter_countableCarrier
    (countable_projectiveLabel_fiber h h0b h0) eta hS hSmeas hcar

/-- **Absolute-continuity transport, unconditionally.**  A projective parameter law absolutely
continuous with respect to Lebesgue measure on the finite chart produces an absolutely continuous
carrier of the indeterminate moment fiber. -/
theorem nevBarycenter_absolutelyContinuous_volume (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) (eta : Measure (OnePoint ℝ))
    (heta : eta ≪ Measure.map ((↑) : ℝ → OnePoint ℝ) (volume : Measure ℝ)) :
    (nevBoundaryFamily h h0b h0).measureBarycenter eta ≪ (volume : Measure ℝ) :=
  (nevBoundaryFamily h h0b h0).measureBarycenter_absolutelyContinuous_volume
    (differentiableOn_nevProjectiveQuotient h h0b h0) eta heta

/-- **Singular-continuous transport, unconditionally.**  An atomless projective parameter law
singular with respect to projective Lebesgue measure produces an atomless carrier singular with
respect to Lebesgue measure. -/
theorem nevBarycenter_isSingularContinuous (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) (eta : Measure (OnePoint ℝ))
    [NullSingletonClass eta]
    (heta : eta ⟂ₘ (projectiveLebesgueProbability : Measure (OnePoint ℝ))) :
    NullSingletonClass ((nevBoundaryFamily h h0b h0).measureBarycenter eta) ∧
      (nevBoundaryFamily h h0b h0).measureBarycenter eta ⟂ₘ (volume : Measure ℝ) := by
  constructor
  · exact boundaryBarycenter_noAtoms eta (nevBoundaryFamily h h0b h0).leafMeasure
      (nevBoundaryFamily h h0b h0).matrix.projectiveLabel
      (nevBoundaryFamily h h0b h0).measurable_leaf
      (nevBoundaryFamily h h0b h0).measurable_projectiveLabel
      (nevBoundaryFamily h h0b h0).map_projectiveLabel_leaf
  · exact boundaryBarycenter_mutuallySingular eta
      (projectiveLebesgueProbability : Measure (OnePoint ℝ)) (volume : Measure ℝ)
      (nevBoundaryFamily h h0b h0).leafMeasure
      (nevBoundaryFamily h h0b h0).matrix.projectiveLabel
      (nevBoundaryFamily h h0b h0).measurable_leaf
      (nevBoundaryFamily h h0b h0).measurable_projectiveLabel
      (nevBoundaryFamily h h0b h0).map_projectiveLabel_leaf heta
      (fun E hE hnull => (nevBoundaryFamily h h0b h0).projectiveLabel_preimage_volume_eq_zero
        ((analyticNevCarrierFamily h h0b h0).analyticOnNhd_boundary_c)
        ((analyticNevCarrierFamily h h0b h0).analyticOnNhd_boundary_d) hE hnull)

/-- **The spectral mass vector is retained.**  Mixing parameter laws of the three pure types with
weights `a, b, c` produces exactly the mixture of a carrier concentrated on a countable set, an
atomless Lebesgue-singular carrier, and an absolutely continuous carrier, and the three components
remain pairwise mutually singular. -/
theorem nevBarycenter_mixture_spectralProfile (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) (a b c : ℝ≥0∞)
    (etaPP etaSC etaAC : Measure (OnePoint ℝ)) [NullSingletonClass etaSC]
    {S : Set (OnePoint ℝ)} (hS : S.Countable) (hSmeas : MeasurableSet S)
    (hPP : etaPP Sᶜ = 0)
    (hSC : etaSC ⟂ₘ (projectiveLebesgueProbability : Measure (OnePoint ℝ)))
    (hAC : etaAC ≪ Measure.map ((↑) : ℝ → OnePoint ℝ) (volume : Measure ℝ))
    (hPPSC : etaPP ⟂ₘ etaSC) (hPPAC : etaPP ⟂ₘ etaAC) (hSCAC : etaSC ⟂ₘ etaAC) :
    (nevBoundaryFamily h h0b h0).measureBarycenter (a • etaPP + b • etaSC + c • etaAC) =
        a • (nevBoundaryFamily h h0b h0).measureBarycenter etaPP +
          b • (nevBoundaryFamily h h0b h0).measureBarycenter etaSC +
          c • (nevBoundaryFamily h h0b h0).measureBarycenter etaAC ∧
      (∃ C : Set ℝ, C.Countable ∧
        (nevBoundaryFamily h h0b h0).measureBarycenter etaPP Cᶜ = 0) ∧
      (NullSingletonClass ((nevBoundaryFamily h h0b h0).measureBarycenter etaSC) ∧
        (nevBoundaryFamily h h0b h0).measureBarycenter etaSC ⟂ₘ (volume : Measure ℝ)) ∧
      (nevBoundaryFamily h h0b h0).measureBarycenter etaAC ≪ (volume : Measure ℝ) ∧
      (nevBoundaryFamily h h0b h0).measureBarycenter etaPP ⟂ₘ
          (nevBoundaryFamily h h0b h0).measureBarycenter etaSC ∧
      (nevBoundaryFamily h h0b h0).measureBarycenter etaPP ⟂ₘ
          (nevBoundaryFamily h h0b h0).measureBarycenter etaAC ∧
      (nevBoundaryFamily h h0b h0).measureBarycenter etaSC ⟂ₘ
          (nevBoundaryFamily h h0b h0).measureBarycenter etaAC :=
  ⟨(nevBoundaryFamily h h0b h0).measureBarycenter_mixture a b c etaPP etaSC etaAC,
    nevBarycenter_countableCarrier h h0b h0 etaPP hS hSmeas hPP,
    nevBarycenter_isSingularContinuous h h0b h0 etaSC hSC,
    nevBarycenter_absolutelyContinuous_volume h h0b h0 etaAC hAC,
    (nevBoundaryFamily h h0b h0).measureBarycenter_mutuallySingular hPPSC,
    (nevBoundaryFamily h h0b h0).measureBarycenter_mutuallySingular hPPAC,
    (nevBoundaryFamily h h0b h0).measureBarycenter_mutuallySingular hSCAC⟩

end

end HTGeometry
