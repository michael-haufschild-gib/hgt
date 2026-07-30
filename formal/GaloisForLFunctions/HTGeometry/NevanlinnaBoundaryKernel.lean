import GaloisForLFunctions.HTGeometry.HamburgerBoundaryKernel
import GaloisForLFunctions.HTGeometry.NevanlinnaBoundaryAlgebra
import GaloisForLFunctions.HTGeometry.AtomlessProbabilityLaws

/-!
# The labeled Nevanlinna boundary kernel

This module assembles the measure-theoretic output of a classical N-extremal Nevanlinna family.
It does not assume the boundary-simplex conclusion: exact denominator-fiber support proves exact
projective labeling, and that label proves the closed embedding of parameter laws into carrier
laws. Complete Hamburger-moment preservation is obtained separately by unbounded integration.

The remaining classical construction problem is to build this structure from an arbitrary
indeterminate Hamburger moment sequence.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory OnePoint
open scoped OnePoint Topology

noncomputable section

/-- A weakly continuous probability kernel over a Borel parameter space is automatically a
measurable measure kernel.  The proof is an exact Portmanteau-to-Giry bridge: closed-set masses
have open strict sublevel sets in the weak topology, and closed sets generate the Borel sigma
algebra. -/
theorem continuous_probabilityMeasureKernel_toMeasure_measurable
    {T X : Type*}
    [MeasurableSpace T] [TopologicalSpace T] [OpensMeasurableSpace T]
    [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
    (nu : T → ProbabilityMeasure X) (hnu : Continuous nu) :
    Measurable fun t => ((nu t : ProbabilityMeasure X) : Measure X) := by
  letI (t : T) : IsProbabilityMeasure (nu t : Measure X) := (nu t).prop
  refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    ?_ isPiSystem_isClosed ?_
  · calc
      _ = borel X := BorelSpace.measurable_eq
      _ = _ := borel_eq_generateFrom_isClosed
  · intro K hK
    apply measurable_of_Iio
    intro a
    change MeasurableSet (nu ⁻¹' closedMassBelow K a)
    exact ((closedMassBelow_isOpen K hK a).preimage hnu).measurableSet

/-- The concrete output data of an N-extremal Nevanlinna parametrization. The fields contain the
Nevanlinna matrix, its probability leaves, their exact denominator-fiber support, and their common
Hamburger moments. The boundary-simplex consequences are theorems below, not structure fields. -/
structure NevanlinnaBoundaryFamily (s : ℕ → ℝ) where
  matrix : NevanlinnaMatrixData ℝ
  continuous_c : Continuous matrix.c
  continuous_d : Continuous matrix.d
  leaf : OnePoint ℝ → ProbabilityMeasure ℝ
  continuous_leaf : Continuous leaf
  finite_carried : ∀ tau : ℝ,
    (leaf tau : Measure ℝ) (matrix.finiteDenominatorFiber tau)ᶜ = 0
  infinity_carried :
    (leaf ∞ : Measure ℝ) matrix.infinityDenominatorFiberᶜ = 0
  leaf_moments : ∀ t, HasHamburgerMoments s (leaf t : Measure ℝ)

namespace NevanlinnaBoundaryFamily

variable {s : ℕ → ℝ} (F : NevanlinnaBoundaryFamily s)

/-- Weak continuity of the probability leaves already gives the Giry measurability required for
measure-valued integration.  Thus measurability is a theorem, not an independent classical input. -/
theorem measurable_leaf :
    Measurable fun t => ((F.leaf t : ProbabilityMeasure ℝ) : Measure ℝ) :=
  continuous_probabilityMeasureKernel_toMeasure_measurable F.leaf F.continuous_leaf

/-- Denominator-fiber support forces every N-extremal leaf to have its exact projective label. -/
theorem map_projectiveLabel_leaf (t : OnePoint ℝ) :
    Measure.map F.matrix.projectiveLabel (F.leaf t : Measure ℝ) = Measure.dirac t := by
  induction t using OnePoint.rec with
  | coe tau =>
      letI : IsProbabilityMeasure (F.leaf tau : Measure ℝ) := (F.leaf tau).prop
      exact F.matrix.map_projectiveLabel_eq_dirac_of_carried_finite
        (F.leaf tau : Measure ℝ) tau F.continuous_c F.continuous_d (F.finite_carried tau)
  | infty =>
      letI : IsProbabilityMeasure (F.leaf ∞ : Measure ℝ) := (F.leaf ∞).prop
      exact F.matrix.map_projectiveLabel_eq_dirac_of_carried_infinity
        (F.leaf ∞ : Measure ℝ) F.continuous_c F.continuous_d F.infinity_carried

/-- The probability carrier obtained by barycentring N-extremal leaves against a projective
parameter law. -/
noncomputable def barycenter (eta : ProbabilityMeasure (OnePoint ℝ)) : ProbabilityMeasure ℝ :=
  probabilityBoundaryBarycenter eta F.leaf F.measurable_leaf

/-- Every boundary barycenter has exactly the complete Hamburger moment sequence of its leaves. -/
theorem barycenter_hasHamburgerMoments (eta : ProbabilityMeasure (OnePoint ℝ)) :
    HasHamburgerMoments s (F.barycenter eta : Measure ℝ) := by
  letI : IsProbabilityMeasure (eta : Measure (OnePoint ℝ)) := eta.prop
  letI (t : OnePoint ℝ) : IsProbabilityMeasure (F.leaf t : Measure ℝ) := (F.leaf t).prop
  exact boundaryBarycenter_hasHamburgerMoments
    (eta : Measure (OnePoint ℝ)) (fun t => (F.leaf t : Measure ℝ))
      F.measurable_leaf s F.leaf_moments

/-- The Nevanlinna boundary barycenter is a closed topological embedding. This is the formal
topological core of the paper's canonical Bauer-simplex proposition. -/
theorem barycenter_isClosedEmbedding :
    Topology.IsClosedEmbedding F.barycenter := by
  exact probabilityBoundaryBarycenter_isClosedEmbedding F.leaf F.continuous_leaf
    F.measurable_leaf F.matrix.projectiveLabel
    (F.matrix.continuous_projectiveLabel F.continuous_c F.continuous_d).measurable
    F.map_projectiveLabel_leaf

/-- Exact spectral-density transport for the concrete projective label. Reweighting a parameter
law is exactly reweighting its carrier by the pulled-back projective density. -/
theorem boundaryBarycenter_withDensity_projective
    (eta : Measure (OnePoint ℝ)) (w : OnePoint ℝ → ENNReal)
    (hw : Measurable w) :
    boundaryBarycenter (eta.withDensity w) (fun t => (F.leaf t : Measure ℝ)) =
      (boundaryBarycenter eta (fun t => (F.leaf t : Measure ℝ))).withDensity
        (w ∘ F.matrix.projectiveLabel) := by
  exact boundaryBarycenter_withDensity eta (fun t => (F.leaf t : Measure ℝ))
    F.matrix.projectiveLabel w F.measurable_leaf
    (F.matrix.continuous_projectiveLabel F.continuous_c F.continuous_d).measurable
    hw F.map_projectiveLabel_leaf

/-- An atomless projective parameter law produces an atomless real carrier. -/
theorem barycenter_noAtoms (eta : ProbabilityMeasure (OnePoint ℝ))
    [NullSingletonClass (eta : Measure (OnePoint ℝ))] :
    NullSingletonClass (F.barycenter eta : Measure ℝ) := by
  exact boundaryBarycenter_noAtoms (eta : Measure (OnePoint ℝ))
    (fun t => (F.leaf t : Measure ℝ)) F.matrix.projectiveLabel F.measurable_leaf
    (F.matrix.continuous_projectiveLabel F.continuous_c F.continuous_d).measurable
    F.map_projectiveLabel_leaf

end NevanlinnaBoundaryFamily

end

end GaloisForLFunctions.HTGeometry
