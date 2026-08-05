import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Labeled measure kernels and boundary barycenters

This module formalizes the categorical core of the canonical Nevanlinna boundary simplex. A
measurable family of probability measures whose leaves are separated by a measurable label map
has a barycenter map with an exact pushforward left inverse. Consequently the barycenter map is
injective before any moment-problem-specific analytic input is used.

The later Nevanlinna module must construct this data from an indeterminate Hamburger moment
problem and prove the required continuity and moment preservation.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory
open scoped BoundedContinuousFunction ENNReal NNReal

noncomputable section

variable {T X : Type*} [MeasurableSpace T] [MeasurableSpace X]

/-- The barycenter of a measure `η` on a parameter space through a measurable measure kernel `ν`. -/
def boundaryBarycenter (η : Measure T) (ν : T → Measure X) : Measure X :=
  η.bind ν

/-- Exact label recovery: if every leaf pushes forward to the Dirac mass at its parameter, then
the barycenter pushes forward to the original parameter measure. -/
theorem map_boundaryBarycenter_eq
    (ν : T → Measure X) (π : X → T)
    (hν : Measurable ν) (hπ : Measurable π)
    (hlabel : ∀ t, Measure.map π (ν t) = Measure.dirac t)
    (η : Measure T) :
    Measure.map π (boundaryBarycenter η ν) = η := by
  rw [← Measure.bind_dirac_eq_map _ hπ]
  unfold boundaryBarycenter
  rw [Measure.bind_bind (m := η) (f := ν)
    (g := fun x => Measure.dirac (π x)) hν.aemeasurable
    ((Measure.measurable_dirac.comp hπ).aemeasurable)]
  simp_rw [Measure.bind_dirac_eq_map _ hπ, hlabel]
  exact Measure.bind_dirac

/-- The separated labeled barycenter map is injective. -/
theorem boundaryBarycenter_injective
    (ν : T → Measure X) (π : X → T)
    (hν : Measurable ν) (hπ : Measurable π)
    (hlabel : ∀ t, Measure.map π (ν t) = Measure.dirac t) :
    Function.Injective (fun η => boundaryBarycenter η ν) := by
  intro η₁ η₂ h
  have hmap := congrArg (Measure.map π) h
  rwa [map_boundaryBarycenter_eq ν π hν hπ hlabel,
    map_boundaryBarycenter_eq ν π hν hπ hlabel] at hmap

/-- The barycenter assigns to every measurable label preimage exactly the mass of the
corresponding parameter set. -/
theorem boundaryBarycenter_preimage_apply
    (ν : T → Measure X) (π : X → T)
    (hν : Measurable ν) (hπ : Measurable π)
    (hlabel : ∀ t, Measure.map π (ν t) = Measure.dirac t)
    (η : Measure T) {E : Set T} (hE : MeasurableSet E) :
    boundaryBarycenter η ν (π ⁻¹' E) = η E := by
  have hmap := congrArg (fun m : Measure T => m E)
    (map_boundaryBarycenter_eq ν π hν hπ hlabel η)
  change (Measure.map π (boundaryBarycenter η ν)) E = η E at hmap
  rw [Measure.map_apply hπ hE] at hmap
  exact hmap

/-- Barycentring probability leaves against a probability parameter measure again gives a
probability measure. -/
theorem boundaryBarycenter_isProbabilityMeasure
    (η : Measure T) [IsProbabilityMeasure η]
    (ν : T → Measure X) (hν : Measurable ν)
    (hprob : ∀ t, IsProbabilityMeasure (ν t)) :
    IsProbabilityMeasure (boundaryBarycenter η ν) := by
  unfold boundaryBarycenter
  exact isProbabilityMeasure_bind hν.aemeasurable
    (Filter.Eventually.of_forall hprob)

/-- A measurable probability kernel preserves finiteness of its parameter measure.  Equivalently,
the total mass of its barycenter is the total mass of the parameter measure. -/
theorem boundaryBarycenter_isFiniteMeasure
    (η : Measure T) [IsFiniteMeasure η]
    (ν : T → Measure X) (hν : Measurable ν)
    (hprob : ∀ t, IsProbabilityMeasure (ν t)) :
    IsFiniteMeasure (boundaryBarycenter η ν) := by
  constructor
  rw [boundaryBarycenter, Measure.bind_apply MeasurableSet.univ hν.aemeasurable]
  simp_rw [show ∀ t, ν t Set.univ = 1 from fun t => (hprob t).measure_univ]
  simpa using IsFiniteMeasure.measure_univ_lt_top (μ := η)

/-- Barycentring is additive in the parameter measure. -/
theorem boundaryBarycenter_add
    (η₁ η₂ : Measure T) (ν : T → Measure X) (hν : Measurable ν) :
    boundaryBarycenter (η₁ + η₂) ν =
      boundaryBarycenter η₁ ν + boundaryBarycenter η₂ ν := by
  unfold boundaryBarycenter
  simpa using Measure.bind_sum (fun b : Bool => cond b η₁ η₂) ν
    (by simpa using And.intro hν.aemeasurable hν.aemeasurable)

/-- Barycentring commutes with nonnegative scalar multiplication. -/
theorem boundaryBarycenter_smul
    (c : ENNReal) (η : Measure T) (ν : T → Measure X) :
    boundaryBarycenter (c • η) ν = c • boundaryBarycenter η ν := by
  exact Measure.bind_smul c η ν

/-- Exact leaf labeling holds almost everywhere on every leaf. -/
theorem boundaryLabel_ae_eq
    [MeasurableSingletonClass T]
    (ν : T → Measure X) (π : X → T) (hπ : Measurable π)
    (hlabel : ∀ t, Measure.map π (ν t) = Measure.dirac t) (t : T) :
    π =ᵐ[ν t] fun _ => t := by
  show ∀ᵐ x ∂ν t, π x = t
  rw [← ae_map_iff (p := fun y : T => y = t) hπ.aemeasurable
    (by simpa only [Set.setOf_eq_eq_singleton] using measurableSet_singleton t)]
  rw [hlabel]
  exact (ae_dirac_iff (measurableSet_singleton t)).2 rfl

/-- Exact density transport through a separated labeled kernel. Reweighting the parameter measure
by `w` is the same as reweighting the barycenter by `w ∘ π`. -/
theorem boundaryBarycenter_withDensity
    [MeasurableSingletonClass T]
    (η : Measure T) (ν : T → Measure X) (π : X → T) (w : T → ENNReal)
    (hν : Measurable ν) (hπ : Measurable π) (hw : Measurable w)
    (hlabel : ∀ t, Measure.map π (ν t) = Measure.dirac t) :
    boundaryBarycenter (η.withDensity w) ν =
      (boundaryBarycenter η ν).withDensity (w ∘ π) := by
  ext E hE
  rw [boundaryBarycenter, Measure.bind_apply hE hν.aemeasurable]
  rw [lintegral_withDensity_eq_lintegral_mul (f := w) (g := fun t => ν t E) η hw
    ((Measure.measurable_coe hE).comp hν)]
  rw [withDensity_apply _ hE]
  rw [← lintegral_indicator hE]
  unfold boundaryBarycenter
  rw [Measure.lintegral_bind hν.aemeasurable]
  · apply lintegral_congr
    intro t
    simp only [Pi.mul_apply]
    symm
    have hae := boundaryLabel_ae_eq ν π hπ hlabel t
    calc
      ∫⁻ x, E.indicator (w ∘ π) x ∂ν t =
          ∫⁻ x, E.indicator (fun _ => w t) x ∂ν t := by
            apply lintegral_congr_ae
            filter_upwards [hae] with x hx
            by_cases hxE : x ∈ E
            · simp [Set.indicator_of_mem hxE, Function.comp_apply, hx]
            · simp [Set.indicator_of_notMem hxE]
      _ = w t * ν t E := by
        rw [lintegral_indicator hE]
        simp
  · exact ((hw.comp hπ).indicator hE).aemeasurable

/-- A pointwise positive parameter density preserves the measure class of the barycenter. -/
theorem boundaryBarycenter_withDensity_mutuallyAbsolutelyContinuous
    [MeasurableSingletonClass T]
    (η : Measure T) (ν : T → Measure X) (π : X → T) (w : T → ENNReal)
    (hν : Measurable ν) (hπ : Measurable π) (hw : Measurable w)
    (hw0 : ∀ t, w t ≠ 0)
    (hlabel : ∀ t, Measure.map π (ν t) = Measure.dirac t) :
    boundaryBarycenter (η.withDensity w) ν ≪ boundaryBarycenter η ν ∧
      boundaryBarycenter η ν ≪ boundaryBarycenter (η.withDensity w) ν := by
  rw [boundaryBarycenter_withDensity η ν π w hν hπ hw hlabel]
  constructor
  · exact withDensity_absolutelyContinuous _ _
  · exact withDensity_absolutelyContinuous' (hw.comp hπ).aemeasurable
      (Filter.Eventually.of_forall fun x => hw0 (π x))

/-- An atomless parameter law has an atomless barycenter when the leaves are exactly separated by
the label map. -/
theorem boundaryBarycenter_noAtoms
    [MeasurableSingletonClass T] [MeasurableSingletonClass X]
    (η : Measure T) [NullSingletonClass η]
    (ν : T → Measure X) (π : X → T)
    (hν : Measurable ν) (hπ : Measurable π)
    (hlabel : ∀ t, Measure.map π (ν t) = Measure.dirac t) :
    NullSingletonClass (boundaryBarycenter η ν) := by
  constructor
  intro x
  rw [boundaryBarycenter, Measure.bind_apply (measurableSet_singleton x) hν.aemeasurable]
  apply (lintegral_eq_zero_iff
    ((Measure.measurable_coe (measurableSet_singleton x)).comp hν)).2
  rw [Filter.EventuallyEq, ae_iff]
  have hsingle : η {π x} = 0 := measure_singleton (π x)
  apply measure_mono_null (t := {π x})
  · intro t ht
    simp only [Set.mem_setOf_eq, Pi.zero_apply] at ht
    by_contra htmem
    have htne : t ≠ π x := by simpa using htmem
    have hmass := congrArg (fun m : Measure T => m {π x}) (hlabel t)
    change (Measure.map π (ν t)) {π x} = (Measure.dirac t) {π x} at hmass
    rw [Measure.map_apply hπ (measurableSet_singleton (π x))] at hmass
    have hpre : ν t (π ⁻¹' {π x}) = 0 := by simpa [htne] using hmass
    apply ht
    exact measure_mono_null (by intro y hy; simpa using congrArg π hy) hpre
  · exact hsingle

/-- The probability-measure-valued barycenter induced by a measurable probability kernel. -/
noncomputable def probabilityBoundaryBarycenter
    (eta : ProbabilityMeasure T) (nu : T → ProbabilityMeasure X)
    (hnu : Measurable fun t => ((nu t : ProbabilityMeasure X) : Measure X)) :
    ProbabilityMeasure X := by
  refine ⟨boundaryBarycenter (eta : Measure T)
    (fun t => ((nu t : ProbabilityMeasure X) : Measure X)), ?_⟩
  exact boundaryBarycenter_isProbabilityMeasure (eta : Measure T)
    (fun t => ((nu t : ProbabilityMeasure X) : Measure X)) hnu (fun t => (nu t).prop)

@[simp]
theorem probabilityBoundaryBarycenter_coe
    (eta : ProbabilityMeasure T) (nu : T → ProbabilityMeasure X)
    (hnu : Measurable fun t => ((nu t : ProbabilityMeasure X) : Measure X)) :
    ((probabilityBoundaryBarycenter eta nu hnu : ProbabilityMeasure X) : Measure X) =
      boundaryBarycenter (eta : Measure T)
        (fun t => ((nu t : ProbabilityMeasure X) : Measure X)) := rfl

/-- Barycentring through a weakly continuous measurable probability kernel is continuous for the
weak topologies on probability measures. This is the abstract topological core of the Bauer
boundary-simplex construction. -/
theorem continuous_probabilityBoundaryBarycenter
    [TopologicalSpace T] [OpensMeasurableSpace T] [CompactSpace T]
    [TopologicalSpace X] [OpensMeasurableSpace X]
    (nu : T → ProbabilityMeasure X) (hcont : Continuous nu)
    (hnu : Measurable fun t => ((nu t : ProbabilityMeasure X) : Measure X)) :
    Continuous (fun eta : ProbabilityMeasure T => probabilityBoundaryBarycenter eta nu hnu) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_lintegral]
  intro f
  have hinner : Continuous (fun t => ∫⁻ x, f x ∂(nu t : Measure X)) :=
    (ProbabilityMeasure.continuous_lintegral_boundedContinuousFunction f).comp hcont
  have hfinite (t : T) : (∫⁻ x, f x ∂(nu t : Measure X)) ≠ ∞ :=
    ne_of_lt (BoundedContinuousFunction.lintegral_lt_top_of_nnreal (nu t : Measure X) f)
  let g0 : C(T, ℝ≥0) :=
    ⟨fun t => (∫⁻ x, f x ∂(nu t : Measure X)).toNNReal, by
      change Continuous (ENNReal.toNNReal ∘ fun t => ∫⁻ x, f x ∂(nu t : Measure X))
      exact ENNReal.continuousOn_toNNReal.comp_continuous hinner (fun t => hfinite t)⟩
  let g : T →ᵇ ℝ≥0 := BoundedContinuousFunction.mkOfCompact g0
  have heq (eta : ProbabilityMeasure T) :
      (∫⁻ x, f x ∂(probabilityBoundaryBarycenter eta nu hnu : Measure X)) =
        ∫⁻ t, g t ∂(eta : Measure T) := by
    change (∫⁻ x, f x ∂boundaryBarycenter (eta : Measure T)
      (fun t => ((nu t : ProbabilityMeasure X) : Measure X))) = _
    unfold boundaryBarycenter
    rw [Measure.lintegral_bind hnu.aemeasurable
      (BoundedContinuousFunction.measurable_coe_ennreal_comp f).aemeasurable]
    apply lintegral_congr
    intro t
    change (∫⁻ x, f x ∂(nu t : Measure X)) =
      (((∫⁻ x, f x ∂(nu t : Measure X)).toNNReal : ℝ≥0) : ℝ≥0∞)
    exact (ENNReal.coe_toNNReal (hfinite t)).symm
  simpa only [heq] using
    (ProbabilityMeasure.continuous_lintegral_boundedContinuousFunction g)

/-- Exact label recovery makes the probability barycenter map injective. -/
theorem probabilityBoundaryBarycenter_injective
    (nu : T → ProbabilityMeasure X)
    (hnu : Measurable fun t => ((nu t : ProbabilityMeasure X) : Measure X))
    (pi : X → T) (hpi : Measurable pi)
    (hlabel : ∀ t, Measure.map pi (nu t : Measure X) = Measure.dirac t) :
    Function.Injective (fun eta : ProbabilityMeasure T =>
      probabilityBoundaryBarycenter eta nu hnu) := by
  intro eta₁ eta₂ h
  apply ProbabilityMeasure.toMeasure_injective
  apply boundaryBarycenter_injective
    (fun t => ((nu t : ProbabilityMeasure X) : Measure X)) pi hnu hpi hlabel
  exact congrArg ProbabilityMeasure.toMeasure h

/-- A weakly continuous separated probability kernel identifies the compact parameter-law space
with a closed subspace of the carrier-law space. This is the exact topological embedding statement
used by the canonical boundary-simplex proposition. -/
theorem probabilityBoundaryBarycenter_isClosedEmbedding
    [TopologicalSpace T] [OpensMeasurableSpace T] [CompactSpace T] [T2Space T]
    [BorelSpace T] [TopologicalSpace X] [OpensMeasurableSpace X]
    [HasOuterApproxClosed X] [BorelSpace X]
    (nu : T → ProbabilityMeasure X) (hcont : Continuous nu)
    (hnu : Measurable fun t => ((nu t : ProbabilityMeasure X) : Measure X))
    (pi : X → T) (hpi : Measurable pi)
    (hlabel : ∀ t, Measure.map pi (nu t : Measure X) = Measure.dirac t) :
    Topology.IsClosedEmbedding (fun eta : ProbabilityMeasure T =>
      probabilityBoundaryBarycenter eta nu hnu) :=
  (continuous_probabilityBoundaryBarycenter nu hcont hnu).isClosedEmbedding
    (probabilityBoundaryBarycenter_injective nu hnu pi hpi hlabel)

/-- Singularity transport through a separated labeled kernel. If the parameter law is singular
to a reference measure and every reference-null parameter set has a null label preimage for the
target reference measure, then the barycenter is singular to that target reference measure. -/
theorem boundaryBarycenter_mutuallySingular
    (eta lambda : Measure T) (rho : Measure X)
    (nu : T → Measure X) (pi : X → T)
    (hnu : Measurable nu) (hpi : Measurable pi)
    (hlabel : ∀ t, Measure.map pi (nu t) = Measure.dirac t)
    (hsing : eta ⟂ₘ lambda)
    (hnull : ∀ E : Set T, MeasurableSet E → lambda E = 0 → rho (pi ⁻¹' E) = 0) :
    boundaryBarycenter eta nu ⟂ₘ rho := by
  refine ⟨pi ⁻¹' hsing.nullSet, hsing.measurableSet_nullSet.preimage hpi,
    boundaryBarycenter_preimage_apply nu pi hnu hpi hlabel eta
      hsing.measurableSet_nullSet |>.trans hsing.measure_nullSet, ?_⟩
  rw [← Set.preimage_compl]
  exact hnull hsing.nullSetᶜ hsing.measurableSet_nullSet.compl hsing.measure_compl_nullSet

end

end GaloisForLFunctions.HTGeometry
