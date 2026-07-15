import GaloisForLFunctions.HTGeometry.NevanlinnaStationaryBauer

/-!
# Invariant-set ergodicity of the Nevanlinna constraint kernel

The convex extreme-point description of stationary laws is upgraded here to the literal
invariant-set definition of Markov-kernel ergodicity.  Exact projective-label recovery makes the
argument finite: invariant label preimages detect every non-Dirac parameter law, while a single
leaf makes every invariant event have probability zero or one.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory OnePoint ProbabilityTheory Set
open scoped OnePoint ENNReal

noncomputable section

local instance kernelErgodicityOnePointRealPolishSpace : PolishSpace (OnePoint ℝ) :=
  onePointRealSphereHomeomorph.isClosedEmbedding.polishSpace

local instance kernelErgodicityOnePointRealStandardBorelSpace :
    StandardBorelSpace (OnePoint ℝ) :=
  standardBorel_of_polish

namespace NevanlinnaBoundaryFamily

variable {s : ℕ → ℝ} (F : NevanlinnaBoundaryFamily s)

/-- A measurable event is invariant for the constraint kernel modulo a probability law when its
one-step transition probability agrees almost everywhere with its indicator. -/
def IsConstraintKernelInvariantSet
    (nu : ProbabilityMeasure ℝ) (A : Set ℝ) : Prop :=
  MeasurableSet A ∧
    ∀ᵐ x ∂(nu : Measure ℝ),
      F.constraintKernel x A = A.indicator (fun _ => (1 : ENNReal)) x

/-- Literal invariant-set ergodicity, including stationarity as part of the predicate. -/
def IsErgodicConstraintStationaryLaw (nu : ProbabilityMeasure ℝ) : Prop :=
  nu ∈ F.stationaryProbabilityLaws ∧
    ∀ A : Set ℝ, F.IsConstraintKernelInvariantSet nu A →
      (nu : Measure ℝ) A = 0 ∨ (nu : Measure ℝ) A = 1

/-- Every measurable projective-label event is pointwise invariant for the constraint kernel. -/
theorem projectiveLabel_preimage_isConstraintKernelInvariantSet
    (nu : ProbabilityMeasure ℝ) (B : Set (OnePoint ℝ)) (hB : MeasurableSet B) :
    F.IsConstraintKernelInvariantSet nu (F.matrix.projectiveLabel ⁻¹' B) := by
  have hlabel : Measurable F.matrix.projectiveLabel :=
    F.matrix.continuous_projectiveLabel F.continuous_c F.continuous_d |>.measurable
  refine ⟨hB.preimage hlabel, ae_of_all _ fun x => ?_⟩
  rw [constraintKernel_apply]
  have hmap := congrArg (fun mu : Measure (OnePoint ℝ) => mu B)
    (F.map_projectiveLabel_leaf (F.matrix.projectiveLabel x))
  change Measure.map F.matrix.projectiveLabel
      (F.leaf (F.matrix.projectiveLabel x) : Measure ℝ) B =
    Measure.dirac (F.matrix.projectiveLabel x) B at hmap
  rw [Measure.map_apply hlabel hB, Measure.dirac_apply' _ hB] at hmap
  by_cases hx : F.matrix.projectiveLabel x ∈ B
  · have hx' : x ∈ F.matrix.projectiveLabel ⁻¹' B := hx
    rw [Set.indicator_of_mem hx']
    simpa [Set.indicator_of_mem hx] using hmap
  · have hx' : x ∉ F.matrix.projectiveLabel ⁻¹' B := hx
    rw [Set.indicator_of_notMem hx']
    simpa [Set.indicator_of_notMem hx] using hmap

/-- Reading a measurable projective event under a boundary barycenter recovers its parameter
probability exactly. -/
theorem barycenter_projectiveLabel_preimage
    (eta : ProbabilityMeasure (OnePoint ℝ))
    (B : Set (OnePoint ℝ)) (hB : MeasurableSet B) :
    (F.barycenter eta : Measure ℝ) (F.matrix.projectiveLabel ⁻¹' B) =
      (eta : Measure (OnePoint ℝ)) B := by
  have hlabel : Measurable F.matrix.projectiveLabel :=
    F.matrix.continuous_projectiveLabel F.continuous_c F.continuous_d |>.measurable
  have hmap := congrArg ProbabilityMeasure.toMeasure (F.projectiveLaw_barycenter eta)
  change Measure.map F.matrix.projectiveLabel (F.barycenter eta : Measure ℝ) =
    (eta : Measure (OnePoint ℝ)) at hmap
  rw [← hmap, Measure.map_apply hlabel hB]

/-- A single N-extremal leaf is ergodic for the constraint kernel in the literal invariant-event
sense. -/
theorem leaf_isErgodicConstraintStationaryLaw (t : OnePoint ℝ) :
    F.IsErgodicConstraintStationaryLaw (F.leaf t) := by
  constructor
  · rw [F.stationaryProbabilityLaws_eq_carrierRange]
    exact ⟨⟨Measure.dirac t, Measure.dirac.isProbabilityMeasure⟩,
      F.barycenter_dirac t⟩
  · intro A hA
    let mu : Measure ℝ := (F.leaf t : Measure ℝ)
    have hlabel : F.matrix.projectiveLabel =ᵐ[mu] fun _ => t :=
      boundaryLabel_ae_eq (fun u => (F.leaf u : Measure ℝ))
        F.matrix.projectiveLabel
        (F.matrix.continuous_projectiveLabel F.continuous_c F.continuous_d).measurable
        F.map_projectiveLabel_leaf t
    have heq : ∀ᵐ x ∂mu,
        mu A = A.indicator (fun _ => (1 : ENNReal)) x := by
      filter_upwards [hA.2, hlabel] with x hx hxt
      rw [constraintKernel_apply, hxt] at hx
      exact hx
    by_cases hzero : mu A = 0
    · exact Or.inl hzero
    · right
      by_contra hone
      have hnotMem : ∀ᵐ x ∂mu, x ∉ A := by
        filter_upwards [heq] with x hx
        intro hxA
        apply hone
        simpa [Set.indicator_of_mem hxA] using hx
      exact hzero (measure_eq_zero_iff_ae_notMem.mpr hnotMem)

/-- A boundary barycenter is invariant-set ergodic exactly when its recovered parameter law is a
Dirac mass. -/
theorem barycenter_isErgodicConstraintStationaryLaw_iff_dirac
    (eta : ProbabilityMeasure (OnePoint ℝ)) :
    F.IsErgodicConstraintStationaryLaw (F.barycenter eta) ↔
      ∃ t, eta =
        (⟨Measure.dirac t, Measure.dirac.isProbabilityMeasure⟩ :
          ProbabilityMeasure (OnePoint ℝ)) := by
  constructor
  · intro hergodic
    by_contra hdirac
    push Not at hdirac
    obtain ⟨B, hB, hB0, hB1⟩ :=
      exists_measurableSet_measure_ne_zero_ne_one_of_not_dirac eta hdirac
    have hinvariant :=
      F.projectiveLabel_preimage_isConstraintKernelInvariantSet (F.barycenter eta) B hB
    have hzeroOne := hergodic.2 (F.matrix.projectiveLabel ⁻¹' B) hinvariant
    rw [F.barycenter_projectiveLabel_preimage eta B hB] at hzeroOne
    exact hzeroOne.elim hB0 hB1
  · rintro ⟨t, rfl⟩
    rw [F.barycenter_dirac]
    exact F.leaf_isErgodicConstraintStationaryLaw t

/-- The invariant-set ergodic stationary boundary is exactly the N-extremal leaf family. -/
theorem ergodicConstraintStationaryBoundary :
    {nu : ProbabilityMeasure ℝ | F.IsErgodicConstraintStationaryLaw nu} = range F.leaf := by
  ext nu
  constructor
  · intro hnu
    have hstationary : nu ∈ range F.barycenter := by
      rw [← F.stationaryProbabilityLaws_eq_carrierRange]
      exact hnu.1
    rcases hstationary with ⟨eta, heta⟩
    have hergodicEta : F.IsErgodicConstraintStationaryLaw (F.barycenter eta) := by
      simpa [heta] using hnu
    rcases (F.barycenter_isErgodicConstraintStationaryLaw_iff_dirac eta).mp hergodicEta with
      ⟨t, rfl⟩
    exact ⟨t, (F.barycenter_dirac t).symm.trans heta⟩
  · rintro ⟨t, rfl⟩
    exact F.leaf_isErgodicConstraintStationaryLaw t

/-- For the Nevanlinna constraint projector, invariant-set ergodicity and convex extremality of a
stationary probability law are equivalent. -/
theorem ergodicConstraintStationaryLaw_iff_extremalStationaryLaw
    (nu : ProbabilityMeasure ℝ) :
    F.IsErgodicConstraintStationaryLaw nu ↔ F.IsExtremalStationaryLaw nu := by
  change nu ∈ {rho : ProbabilityMeasure ℝ |
      F.IsErgodicConstraintStationaryLaw rho} ↔
    nu ∈ {rho : ProbabilityMeasure ℝ | F.IsExtremalStationaryLaw rho}
  rw [F.ergodicConstraintStationaryBoundary, F.extremalStationaryBoundary]

end NevanlinnaBoundaryFamily

end

end GaloisForLFunctions.HTGeometry
