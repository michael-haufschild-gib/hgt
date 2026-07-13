import GaloisForLFunctions.HTGeometry.NevanlinnaBoundaryKernel
import GaloisForLFunctions.HTGeometry.InfiniteSupportFrameTowerTopology

/-!
# Infinite-support Nevanlinna carriers and their complete frame towers

Exact recovery of a parameter law by a continuous support label transports infinite support
backward: a carrier with finite support could push forward only to a law with finite support.
Applied to the labeled Nevanlinna boundary kernel, this proves that an infinite-support projective
law has an infinite-support barycenter.  Its complete inverse-Cholesky tower is therefore defined,
continuous, and faithful without any extra positivity assumption.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory OnePoint
open Topology
open scoped OnePoint

noncomputable section

/-- If a continuous pushforward has infinite support, then the source measure has infinite
support.  The contrapositive uses conullity of the source support and the fact that a finite image
is closed in a Hausdorff target. -/
theorem infinite_support_of_map_eq_of_infinite_support
    {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [HereditarilyLindelofSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y]
    [T2Space Y] [BorelSpace Y]
    (mu : Measure X) (nu : Measure Y) (f : X → Y)
    (hf : Continuous f) (hmap : Measure.map f mu = nu)
    (hnu : nu.support.Infinite) : mu.support.Infinite := by
  by_contra hmu
  have hmuFinite : mu.support.Finite := Set.not_infinite.mp hmu
  let T : Set Y := f '' mu.support
  have hTfinite : T.Finite := hmuFinite.image f
  have hTclosed : IsClosed T := hTfinite.isClosed
  have hTmeas : MeasurableSet T := hTclosed.measurableSet
  have hnuT : nu Tᶜ = 0 := by
    rw [← hmap, Measure.map_apply_of_aemeasurable hf.aemeasurable hTmeas.compl]
    apply measure_mono_null _ Measure.measure_compl_support
    intro x hx hxsupp
    exact hx ⟨x, hxsupp, rfl⟩
  have hsuppSubset : nu.support ⊆ T := by
    intro y hy
    by_contra hyT
    have hnhds : Tᶜ ∈ 𝓝 y := hTclosed.isOpen_compl.mem_nhds hyT
    have hpos := (Measure.mem_support_iff_forall (μ := nu) y).mp hy Tᶜ hnhds
    exact hpos.ne' hnuT
  exact hnu (hTfinite.subset hsuppSubset)

/-- Projective probability laws with infinite topological support. -/
abbrev InfiniteSupportProjectiveProbability :=
  {eta : ProbabilityMeasure (OnePoint ℝ) //
    ((eta : ProbabilityMeasure (OnePoint ℝ)) : Measure (OnePoint ℝ)).support.Infinite}

namespace NevanlinnaBoundaryFamily

variable {s : ℕ → ℝ} (F : NevanlinnaBoundaryFamily s)

/-- Exact projective-label recovery forces the Nevanlinna barycenter of an infinite-support
parameter law to have infinite real support. -/
theorem barycenter_support_infinite (eta : ProbabilityMeasure (OnePoint ℝ))
    (heta : ((eta : ProbabilityMeasure (OnePoint ℝ)) :
      Measure (OnePoint ℝ)).support.Infinite) :
    ((F.barycenter eta : ProbabilityMeasure ℝ) : Measure ℝ).support.Infinite := by
  apply infinite_support_of_map_eq_of_infinite_support
    ((F.barycenter eta : ProbabilityMeasure ℝ) : Measure ℝ)
    ((eta : ProbabilityMeasure (OnePoint ℝ)) : Measure (OnePoint ℝ))
    F.matrix.projectiveLabel
    (F.matrix.continuous_projectiveLabel F.continuous_c F.continuous_d)
  simpa [NevanlinnaBoundaryFamily.barycenter, probabilityBoundaryBarycenter] using
    (map_boundaryBarycenter_eq (fun t => (F.leaf t : Measure ℝ))
      F.matrix.projectiveLabel F.measurable_leaf
      (F.matrix.continuous_projectiveLabel F.continuous_c F.continuous_d).measurable
      F.map_projectiveLabel_leaf
      ((eta : ProbabilityMeasure (OnePoint ℝ)) : Measure (OnePoint ℝ)))
  exact heta

/-- The Nevanlinna barycenter as an infinite-support real probability measure. -/
noncomputable def infiniteSupportBarycenter
    (eta : InfiniteSupportProjectiveProbability) : InfiniteSupportProbability :=
  ⟨F.barycenter eta.1, F.barycenter_support_infinite eta.1 eta.2⟩

/-- Infinite-support Nevanlinna barycentring is continuous. -/
theorem continuous_infiniteSupportBarycenter :
    Continuous F.infiniteSupportBarycenter := by
  apply Continuous.subtype_mk
  exact F.barycenter_isClosedEmbedding.continuous.comp continuous_subtype_val

/-- Infinite-support Nevanlinna barycentring is injective. -/
theorem injective_infiniteSupportBarycenter :
    Function.Injective F.infiniteSupportBarycenter := by
  intro eta theta h
  apply Subtype.ext
  apply F.barycenter_isClosedEmbedding.injective
  exact congrArg Subtype.val h

/-- The complete canonical inverse-Cholesky tower attached directly to an infinite-support
projective boundary law. -/
noncomputable def completeBoundaryCanonicalFrameTower
    (eta : InfiniteSupportProjectiveProbability) :
    ∀ N : ℕ, Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  completeInfiniteSupportCanonicalFrameTower (F.infiniteSupportBarycenter eta)

/-- The boundary-law complete frame tower is continuous. -/
theorem continuous_completeBoundaryCanonicalFrameTower :
    Continuous F.completeBoundaryCanonicalFrameTower :=
  continuous_completeInfiniteSupportCanonicalFrameTower.comp
    F.continuous_infiniteSupportBarycenter

/-- The boundary-law complete frame tower selects its projective parameter law uniquely. -/
theorem injective_completeBoundaryCanonicalFrameTower :
    Function.Injective F.completeBoundaryCanonicalFrameTower :=
  injective_completeInfiniteSupportCanonicalFrameTower.comp
    F.injective_infiniteSupportBarycenter

/-- **Boundary-simplex complete-frame selector.** On every compact family of infinite-support
projective laws, the complete carrier frame tower is a closed topological embedding. -/
theorem isClosedEmbedding_completeBoundaryCanonicalFrameTower_restrict
    (K : Set InfiniteSupportProjectiveProbability) (hK : IsCompact K) :
    Topology.IsClosedEmbedding
      (fun eta : K => F.completeBoundaryCanonicalFrameTower
        (eta : InfiniteSupportProjectiveProbability)) := by
  letI : CompactSpace K := ⟨by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    simpa using hK⟩
  apply Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
  · exact F.continuous_completeBoundaryCanonicalFrameTower.comp continuous_subtype_val
  · exact F.injective_completeBoundaryCanonicalFrameTower.comp Subtype.val_injective
  · exact (F.continuous_completeBoundaryCanonicalFrameTower.comp
      continuous_subtype_val).isClosedMap

end NevanlinnaBoundaryFamily
end
end GaloisForLFunctions.HTGeometry
