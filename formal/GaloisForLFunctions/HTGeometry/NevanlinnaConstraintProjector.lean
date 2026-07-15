import GaloisForLFunctions.HTGeometry.NevanlinnaBoundaryKernel
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# The Nevanlinna constraint projector

A separated Nevanlinna boundary family supplies two equivalent idempotent objects.  On
probability measures, push forward by the projective support label and then barycentre the
boundary leaves.  Pointwise, use the Markov kernel which replaces `x` by the boundary leaf
carrying `x`.  This file proves the exact equality of those constructions, their idempotence,
the stationary-law characterization, and the one-step Hamburger-moment law.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory OnePoint ProbabilityTheory Set
open scoped OnePoint BoundedContinuousFunction

noncomputable section

namespace NevanlinnaBoundaryFamily

variable {s : ℕ → ℝ} (F : NevanlinnaBoundaryFamily s)

/-- The distribution of the exact projective support label of a real probability measure. -/
noncomputable def projectiveLaw
    (nu : ProbabilityMeasure ℝ) : ProbabilityMeasure (OnePoint ℝ) :=
  nu.map
    (F.matrix.continuous_projectiveLabel F.continuous_c F.continuous_d).measurable.aemeasurable

/-- Projective labeling is continuous in the weak probability topologies. -/
theorem continuous_projectiveLaw : Continuous F.projectiveLaw := by
  exact ProbabilityMeasure.continuous_map
    (F.matrix.continuous_projectiveLabel F.continuous_c F.continuous_d)

/-- Barycentring separated leaves and then reading their label recovers the parameter law. -/
@[simp]
theorem projectiveLaw_barycenter (eta : ProbabilityMeasure (OnePoint ℝ)) :
    F.projectiveLaw (F.barycenter eta) = eta := by
  apply ProbabilityMeasure.toMeasure_injective
  simpa only [projectiveLaw, ProbabilityMeasure.toMeasure_map,
    ProbabilityMeasure.coe_mk, NevanlinnaBoundaryFamily.barycenter,
    probabilityBoundaryBarycenter_coe] using
    (map_boundaryBarycenter_eq
      (fun t => (F.leaf t : Measure ℝ)) F.matrix.projectiveLabel
      F.measurable_leaf
      (F.matrix.continuous_projectiveLabel F.continuous_c F.continuous_d).measurable
      F.map_projectiveLabel_leaf (eta : Measure (OnePoint ℝ)))

/-- The canonical measure-side constraint projector. -/
noncomputable def carrierProjector
    (nu : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ :=
  F.barycenter (F.projectiveLaw nu)

/-- The carrier projector is continuous for weak convergence. -/
theorem continuous_carrierProjector : Continuous F.carrierProjector :=
  F.barycenter_isClosedEmbedding.continuous.comp F.continuous_projectiveLaw

/-- The projector fixes every boundary barycenter. -/
@[simp]
theorem carrierProjector_barycenter (eta : ProbabilityMeasure (OnePoint ℝ)) :
    F.carrierProjector (F.barycenter eta) = F.barycenter eta := by
  simp [carrierProjector]

/-- The carrier projector is literally idempotent. -/
@[simp]
theorem carrierProjector_idempotent (nu : ProbabilityMeasure ℝ) :
    F.carrierProjector (F.carrierProjector nu) = F.carrierProjector nu := by
  simp [carrierProjector]

/-- The image of the projector is exactly the Nevanlinna boundary carrier range. -/
theorem range_carrierProjector :
    range F.carrierProjector = range F.barycenter := by
  apply Subset.antisymm
  · rintro _ ⟨nu, rfl⟩
    exact ⟨F.projectiveLaw nu, rfl⟩
  · rintro _ ⟨eta, rfl⟩
    exact ⟨F.barycenter eta, F.carrierProjector_barycenter eta⟩

/-- A probability law is fixed by the constraint projector exactly when it is a boundary
barycenter. -/
theorem carrierProjector_eq_self_iff (nu : ProbabilityMeasure ℝ) :
    F.carrierProjector nu = nu ↔ nu ∈ range F.barycenter := by
  constructor
  · intro h
    exact ⟨F.projectiveLaw nu, h⟩
  · rintro ⟨eta, rfl⟩
    exact F.carrierProjector_barycenter eta

/-- One application of the constraint projector lands in the exact complete Hamburger-moment
fiber, with no moment assumption on the initial probability law. -/
theorem carrierProjector_hasHamburgerMoments (nu : ProbabilityMeasure ℝ) :
    HasHamburgerMoments s (F.carrierProjector nu : Measure ℝ) :=
  F.barycenter_hasHamburgerMoments (F.projectiveLaw nu)

/-- The pointwise Markov kernel which replaces a real point by the unique Nevanlinna boundary
leaf carrying its projective label. -/
noncomputable def constraintKernel : Kernel ℝ ℝ where
  toFun x := (F.leaf (F.matrix.projectiveLabel x) : Measure ℝ)
  measurable' := F.measurable_leaf.comp
    (F.matrix.continuous_projectiveLabel F.continuous_c F.continuous_d).measurable

@[simp]
theorem constraintKernel_apply (x : ℝ) :
    F.constraintKernel x = (F.leaf (F.matrix.projectiveLabel x) : Measure ℝ) := rfl

instance constraintKernel_isMarkov : IsMarkovKernel F.constraintKernel where
  isProbabilityMeasure x := (F.leaf (F.matrix.projectiveLabel x)).prop

/-- Composing the pointwise kernel with a measure is the same as first pushing the measure to its
projective label law and then barycentring the boundary leaves. -/
theorem constraintKernel_comp_eq_boundaryBarycenter (nu : Measure ℝ) :
    F.constraintKernel ∘ₘ nu =
      boundaryBarycenter (Measure.map F.matrix.projectiveLabel nu)
        (fun t => (F.leaf t : Measure ℝ)) := by
  rw [← Measure.bind_dirac_eq_map nu
    (F.matrix.continuous_projectiveLabel F.continuous_c F.continuous_d).measurable]
  unfold boundaryBarycenter
  rw [Measure.bind_bind]
  · apply Measure.bind_congr_right
    filter_upwards with x
    exact (Measure.dirac_bind F.measurable_leaf (F.matrix.projectiveLabel x)).symm
  · exact ((Measure.measurable_dirac.comp
      (F.matrix.continuous_projectiveLabel F.continuous_c F.continuous_d).measurable).aemeasurable)
  · exact F.measurable_leaf.aemeasurable

/-- The Mathlib kernel action on probability measures is exactly the canonical carrier
projector. -/
theorem constraintKernel_comp_probability (nu : ProbabilityMeasure ℝ) :
    F.constraintKernel ∘ₘ (nu : Measure ℝ) =
      (F.carrierProjector nu : Measure ℝ) := by
  rw [constraintKernel_comp_eq_boundaryBarycenter]
  rfl

/-- The Nevanlinna constraint kernel is idempotent under kernel composition. -/
theorem constraintKernel_comp_self :
    F.constraintKernel ∘ₖ F.constraintKernel = F.constraintKernel := by
  ext x E hE
  rw [Kernel.comp_apply, constraintKernel_apply,
    constraintKernel_comp_eq_boundaryBarycenter, F.map_projectiveLabel_leaf]
  rw [show boundaryBarycenter (Measure.dirac (F.matrix.projectiveLabel x))
      (fun t => (F.leaf t : Measure ℝ)) =
        (F.leaf (F.matrix.projectiveLabel x) : Measure ℝ) by
    exact Measure.dirac_bind F.measurable_leaf (F.matrix.projectiveLabel x)]

/-- Stationary probability laws of the Markov kernel are exactly the boundary barycenters. -/
theorem constraintKernel_stationary_iff (nu : ProbabilityMeasure ℝ) :
    F.constraintKernel ∘ₘ (nu : Measure ℝ) = (nu : Measure ℝ) ↔
      nu ∈ range F.barycenter := by
  rw [F.constraintKernel_comp_probability]
  exact ProbabilityMeasure.toMeasure_injective.eq_iff.trans
    (F.carrierProjector_eq_self_iff nu)

/-- Every monomial is flattened in one step to its prescribed Hamburger moment. -/
theorem integral_pow_constraintKernel (n : ℕ) (x : ℝ) :
    ∫ y, y ^ n ∂(F.constraintKernel x) = s n := by
  simpa [constraintKernel_apply] using (F.leaf_moments (F.matrix.projectiveLabel x) n).2

end NevanlinnaBoundaryFamily

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory OnePoint ProbabilityTheory
open scoped OnePoint BoundedContinuousFunction

noncomputable section

/-- A Markov kernel is weak Feller when it sends every bounded continuous real observable to a
continuous expectation function.  Boundedness of the expectation follows separately from the
Markov property. -/
def IsWeakFellerKernel {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (kappa : Kernel X X) : Prop :=
  forall f : X →ᵇ ℝ, Continuous fun x => ∫ y, f y ∂(kappa x)

namespace NevanlinnaBoundaryFamily

variable {s : ℕ → ℝ} (F : NevanlinnaBoundaryFamily s)

/-- Weak continuity of the Nevanlinna leaves and continuity of the projective label make the
constraint kernel weak Feller. -/
theorem constraintKernel_isWeakFeller : IsWeakFellerKernel F.constraintKernel := by
  intro f
  exact (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).comp
    (F.continuous_leaf.comp
      (F.matrix.continuous_projectiveLabel F.continuous_c F.continuous_d))

/-- The bounded-continuous Markov operator dual to the constraint kernel. -/
noncomputable def constraintMarkovOperator (f : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => ∫ y, f y ∂(F.constraintKernel x))
    (F.constraintKernel_isWeakFeller f) ‖f‖
    (fun x => f.norm_integral_le_norm (F.constraintKernel x))

@[simp]
theorem constraintMarkovOperator_apply (f : ℝ →ᵇ ℝ) (x : ℝ) :
    F.constraintMarkovOperator f x = ∫ y, f y ∂(F.constraintKernel x) := rfl

/-- The constraint Markov operator preserves the constant one. -/
@[simp]
theorem constraintMarkovOperator_one :
    F.constraintMarkovOperator (1 : ℝ →ᵇ ℝ) = 1 := by
  ext x
  simp [constraintMarkovOperator_apply]

/-- The constraint Markov operator is positive. -/
theorem constraintMarkovOperator_nonneg {f : ℝ →ᵇ ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∀ x, 0 ≤ F.constraintMarkovOperator f x := by
  intro x
  rw [constraintMarkovOperator_apply]
  exact integral_nonneg hf

/-- The constraint Markov operator contracts the supremum norm. -/
theorem norm_constraintMarkovOperator_le (f : ℝ →ᵇ ℝ) :
    ‖F.constraintMarkovOperator f‖ ≤ ‖f‖ := by
  rw [BoundedContinuousFunction.norm_le_of_nonempty]
  intro x
  exact f.norm_integral_le_norm (F.constraintKernel x)

/-- Coordinate covariance of leaves and labels makes the canonical projector independent of the
chosen projective Nevanlinna normalization. -/
theorem carrierProjector_eq_of_leaf_label_covariance
    (G : NevanlinnaBoundaryFamily s) (e : OnePoint ℝ → OnePoint ℝ)
    (hleaf : ∀ t, G.leaf (e t) = F.leaf t)
    (hlabel : ∀ x, G.matrix.projectiveLabel x = e (F.matrix.projectiveLabel x))
    (nu : ProbabilityMeasure ℝ) :
    G.carrierProjector nu = F.carrierProjector nu := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [← G.constraintKernel_comp_probability nu,
    ← F.constraintKernel_comp_probability nu]
  apply Measure.bind_congr_right
  filter_upwards with x
  simp only [constraintKernel_apply, hlabel, hleaf]

end NevanlinnaBoundaryFamily

end

end GaloisForLFunctions.HTGeometry
