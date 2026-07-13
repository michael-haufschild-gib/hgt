import GaloisForLFunctions.HTGeometry.AtomlessProbabilityLaws
import GaloisForLFunctions.HTGeometry.CircleAtomlessProbabilityLaws
import GaloisForLFunctions.HTGeometry.NevanlinnaBoundaryKernel
import GaloisForLFunctions.HTGeometry.SingularProbabilityLaws
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Metrizable.Uniformity

/-!
# Residual singular-continuous laws on the projective parameter line

The Nevanlinna parameter line is represented by `OnePoint ℝ`.  Its projective
Lebesgue probability is the standard Cauchy law in the finite chart, with zero
mass at infinity.  This file proves that atomless laws singular to that
reference form a dense `G_delta`, and transports the phase topologically through
the closed Nevanlinna barycenter embedding.

The final conversion of projective-reference null sets to real-Lebesgue null
preimages under a concrete Nevanlinna label is exposed as an explicit
hypothesis.  It is not hidden in the residual transport theorem.
-/

open MeasureTheory Set Filter Metric Topology OnePoint
open TopologicalSpace
open scoped ENNReal NNReal Topology OnePoint

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A concrete metrization witness for the real projective line. -/
def onePointRealSphereHomeomorph :
    OnePoint ℝ ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
  onePointEquivSphereOfFinrankEq (ι := Fin 2) (V := ℝ) (by simp)

/-- The Euclidean unit circle and the complex unit circle are the same normed
space through the canonical real orthonormal coordinates of `ℂ`. -/
def euclideanSphereComplexCircleHomeomorph :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ Circle where
  toFun x := ⟨Complex.orthonormalBasisOneI.repr.symm x, by
    change Complex.orthonormalBasisOneI.repr.symm x ∈
      Metric.sphere (0 : ℂ) 1
    have hx : ‖(x : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
      rw [← dist_zero_right]
      exact x.prop
    rw [mem_sphere, dist_zero_right, LinearIsometryEquiv.norm_map]
    exact hx⟩
  invFun z := ⟨Complex.orthonormalBasisOneI.repr z, by
    change dist (Complex.orthonormalBasisOneI.repr z) 0 = 1
    have hz : ‖(z : ℂ)‖ = 1 := Circle.norm_coe z
    simp [dist_eq_norm, hz]⟩
  left_inv x := by
    apply Subtype.ext
    exact Complex.orthonormalBasisOneI.repr.apply_symm_apply x
  right_inv z := by
    apply Subtype.ext
    exact Complex.orthonormalBasisOneI.repr.symm_apply_apply z
  continuous_toFun := by
    exact (Complex.orthonormalBasisOneI.repr.symm.continuous.comp
      continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    exact (Complex.orthonormalBasisOneI.repr.continuous.comp
      continuous_subtype_val).subtype_mk _

/-- Concrete identification of the real projective line with the unit
additive circle. -/
def onePointRealUnitAddCircleHomeomorph : OnePoint ℝ ≃ₜ UnitAddCircle :=
  (onePointRealSphereHomeomorph.trans
    euclideanSphereComplexCircleHomeomorph).trans
      (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm

local instance onePointRealMetrizableSpace : MetrizableSpace (OnePoint ℝ) :=
  onePointRealSphereHomeomorph.isEmbedding.metrizableSpace

local instance onePointRealMetricSpace : MetricSpace (OnePoint ℝ) :=
  TopologicalSpace.metrizableSpaceMetric (OnePoint ℝ)

/-- Pushforward by a homeomorphism is a homeomorphism of probability-law
spaces in the weak topology. -/
def probabilityMeasureHomeomorph
    {A B : Type*} [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
    (e : A ≃ₜ B) : ProbabilityMeasure A ≃ₜ ProbabilityMeasure B where
  toFun mu := mu.map e.continuous.measurable.aemeasurable
  invFun nu := nu.map e.symm.continuous.measurable.aemeasurable
  left_inv mu := by
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.toMeasure_map]
    rw [Measure.map_map]
    · simp [Function.comp_def]
    · exact e.symm.continuous.measurable
    · exact e.continuous.measurable
  right_inv nu := by
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.toMeasure_map]
    rw [Measure.map_map]
    · simp [Function.comp_def]
    · exact e.continuous.measurable
    · exact e.symm.continuous.measurable
  continuous_toFun := ProbabilityMeasure.continuous_map e.continuous
  continuous_invFun := ProbabilityMeasure.continuous_map e.symm.continuous

/-- A homeomorphic pushforward preserves atomlessness. -/
theorem probabilityMeasure_map_noAtoms
    {A B : Type*} [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
    [MeasurableSingletonClass B]
    (e : A ≃ₜ B) (mu : ProbabilityMeasure A)
    (hmu : NoAtoms (mu : Measure A)) :
    NoAtoms ((mu.map e.continuous.measurable.aemeasurable :
      ProbabilityMeasure B) : Measure B) := by
  constructor
  intro y
  rw [ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply e.continuous.measurable (measurableSet_singleton y)]
  have hpre : e ⁻¹' {y} = {e.symm y} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff]
    constructor
    · intro hxy
      apply e.injective
      simpa using hxy
    · rintro rfl
      exact e.apply_symm_apply y
  rw [hpre, hmu.measure_singleton]

local instance standardCauchyNoAtoms :
    NoAtoms (ProbabilityTheory.cauchyMeasure 0 1) := by
  rw [ProbabilityTheory.cauchyMeasure_of_scale_ne_zero 0 (γ := 1) (by norm_num)]
  infer_instance

/-- Standard Cauchy probability in the finite projective chart. -/
def standardCauchyProbability : ProbabilityMeasure ℝ :=
  ⟨ProbabilityTheory.cauchyMeasure 0 1, inferInstance⟩

/-- Projective Lebesgue probability on `OnePoint ℝ`: standard Cauchy measure in
the finite chart and zero mass at infinity. -/
def projectiveLebesgueProbability : ProbabilityMeasure (OnePoint ℝ) :=
  standardCauchyProbability.map OnePoint.continuous_coe.measurable.aemeasurable

theorem projectiveLebesgueProbability_toMeasure :
    (projectiveLebesgueProbability : Measure (OnePoint ℝ)) =
      Measure.map ((↑) : ℝ → OnePoint ℝ)
        (ProbabilityTheory.cauchyMeasure 0 1) := rfl

local instance projectiveLebesgueProbability_noAtoms :
    NoAtoms (projectiveLebesgueProbability : Measure (OnePoint ℝ)) := by
  constructor
  intro x
  change (Measure.map ((↑) : ℝ → OnePoint ℝ)
    (ProbabilityTheory.cauchyMeasure 0 1)) {x} = 0
  rw [Measure.map_apply OnePoint.continuous_coe.measurable
    (measurableSet_singleton x)]
  cases x with
  | infty =>
      have hpre : ((fun y : ℝ => (y : OnePoint ℝ)) ⁻¹'
          {(∞ : OnePoint ℝ)}) = ∅ := by
        ext y
        simp
      rw [hpre, measure_empty]
  | coe x =>
      have hpre : ((fun y : ℝ => (y : OnePoint ℝ)) ⁻¹'
          {(x : OnePoint ℝ)}) = {x} := by
        ext y
        simp
      rw [hpre, measure_singleton]

/-- Atomless projective laws singular to projective Lebesgue probability. -/
def projectiveSingularContinuousProbabilityLaws :
    Set (ProbabilityMeasure (OnePoint ℝ)) :=
  atomlessProbabilityLaws (X := OnePoint ℝ) ∩
    singularProbabilityLaws projectiveLebesgueProbability

theorem projective_atomlessProbabilityLaws_dense :
    Dense (atomlessProbabilityLaws (X := OnePoint ℝ)) := by
  let E := probabilityMeasureHomeomorph onePointRealUnitAddCircleHomeomorph
  have hDense : Dense (E ⁻¹' atomlessProbabilityLaws) :=
    circle_atomlessProbabilityLaws_dense.preimage E.isOpenMap
  apply hDense.mono
  intro mu hmu
  change NoAtoms ((E mu : ProbabilityMeasure UnitAddCircle) :
    Measure UnitAddCircle) at hmu
  change NoAtoms (mu : Measure (OnePoint ℝ))
  have hBack := probabilityMeasure_map_noAtoms
    onePointRealUnitAddCircleHomeomorph.symm (E mu) hmu
  have hInv : E.symm (E mu) = mu := E.left_inv mu
  rw [← hInv]
  exact hBack

theorem projective_singularProbabilityLaws_dense :
    Dense (singularProbabilityLaws projectiveLebesgueProbability) :=
  singularProbabilityLaws_dense projectiveLebesgueProbability

theorem projective_singularProbabilityLaws_isGdelta :
    IsGδ (singularProbabilityLaws projectiveLebesgueProbability) :=
  singularProbabilityLaws_isGdelta projectiveLebesgueProbability

theorem projectiveSingularContinuousProbabilityLaws_isGdelta :
    IsGδ projectiveSingularContinuousProbabilityLaws := by
  exact atomlessProbabilityLaws_isGdelta.inter
    projective_singularProbabilityLaws_isGdelta

theorem projectiveSingularContinuousProbabilityLaws_dense :
    Dense projectiveSingularContinuousProbabilityLaws := by
  exact Dense.inter_of_Gδ atomlessProbabilityLaws_isGdelta
    projective_singularProbabilityLaws_isGdelta
    projective_atomlessProbabilityLaws_dense
    projective_singularProbabilityLaws_dense

/-- Atomless projective laws singular to projective Lebesgue probability form
a dense `G_delta`. -/
theorem projectiveSingularContinuousProbabilityLaws_dense_gdelta :
    Dense projectiveSingularContinuousProbabilityLaws ∧
      IsGδ projectiveSingularContinuousProbabilityLaws :=
  ⟨projectiveSingularContinuousProbabilityLaws_dense,
    projectiveSingularContinuousProbabilityLaws_isGdelta⟩

/-- A homeomorphism sends a `G_delta` to a `G_delta`. -/
theorem Homeomorph.isGdelta_image
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) {S : Set A} (hS : IsGδ S) :
    IsGδ (e '' S) := by
  have himage : e '' S = e.symm ⁻¹' S := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨e.symm y, hy, e.apply_symm_apply y⟩
  rw [himage]
  exact isGδ_induced e.symm.continuous hS

/-- A homeomorphism sends a dense set to a dense set. -/
theorem Homeomorph.dense_image
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) {S : Set A} (hS : Dense S) :
    Dense (e '' S) := by
  have himage : e '' S = e.symm ⁻¹' S := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨e.symm y, hy, e.apply_symm_apply y⟩
  rw [himage]
  exact hS.preimage e.symm.isOpenMap

namespace NevanlinnaBoundaryFamily

variable {s : ℕ → ℝ} (F : NevanlinnaBoundaryFamily s)

/-- The canonical Nevanlinna carrier simplex as the range of the barycenter
embedding. -/
abbrev carrierRange := Set.range F.barycenter

/-- The image in the exact Nevanlinna carrier simplex of the residual
singular-continuous parameter phase. -/
def singularContinuousParameterCarrierPhase : Set F.carrierRange :=
  F.barycenter_isClosedEmbedding.toIsEmbedding.toHomeomorph ''
    projectiveSingularContinuousProbabilityLaws

theorem singularContinuousParameterCarrierPhase_isGdelta :
    IsGδ F.singularContinuousParameterCarrierPhase := by
  exact Homeomorph.isGdelta_image
    F.barycenter_isClosedEmbedding.toIsEmbedding.toHomeomorph
    projectiveSingularContinuousProbabilityLaws_isGdelta

theorem singularContinuousParameterCarrierPhase_dense :
    Dense F.singularContinuousParameterCarrierPhase := by
  exact Homeomorph.dense_image
    F.barycenter_isClosedEmbedding.toIsEmbedding.toHomeomorph
    projectiveSingularContinuousProbabilityLaws_dense

/-- The projective singular-continuous parameter phase is residual in the
exact Nevanlinna carrier simplex. -/
theorem singularContinuousParameterCarrierPhase_dense_gdelta :
    Dense F.singularContinuousParameterCarrierPhase ∧
      IsGδ F.singularContinuousParameterCarrierPhase :=
  ⟨F.singularContinuousParameterCarrierPhase_dense,
    F.singularContinuousParameterCarrierPhase_isGdelta⟩

/-- Every carrier in the transported phase is atomless, unconditionally. -/
theorem singularContinuousParameterCarrierPhase_noAtoms
    (nu : F.carrierRange)
    (hnu : nu ∈ F.singularContinuousParameterCarrierPhase) :
    NoAtoms (nu.1 : Measure ℝ) := by
  rcases hnu with ⟨eta, heta, hEq⟩
  have hetaNoAtoms : NoAtoms (eta : Measure (OnePoint ℝ)) := heta.1
  letI := hetaNoAtoms
  have hcarrier := F.barycenter_noAtoms eta
  have hval : F.barycenter eta = nu.1 := congrArg Subtype.val hEq
  rw [← hval]
  exact hcarrier

/-- Under the exact null-preimage statement for the concrete projective label,
every carrier in the transported phase is singular to real Lebesgue measure. -/
theorem singularContinuousParameterCarrierPhase_mutuallySingular_volume
    (hnull : ∀ E : Set (OnePoint ℝ), MeasurableSet E →
      (projectiveLebesgueProbability : Measure (OnePoint ℝ)) E = 0 →
      (volume : Measure ℝ) (F.matrix.projectiveLabel ⁻¹' E) = 0)
    (nu : F.carrierRange)
    (hnu : nu ∈ F.singularContinuousParameterCarrierPhase) :
    (nu.1 : Measure ℝ) ⟂ₘ (volume : Measure ℝ) := by
  rcases hnu with ⟨eta, heta, hEq⟩
  have hsing := boundaryBarycenter_mutuallySingular
    (eta : Measure (OnePoint ℝ))
    (projectiveLebesgueProbability : Measure (OnePoint ℝ))
    (volume : Measure ℝ)
    (fun t => (F.leaf t : Measure ℝ)) F.matrix.projectiveLabel
    F.measurable_leaf
    (F.matrix.continuous_projectiveLabel F.continuous_c F.continuous_d).measurable
    F.map_projectiveLabel_leaf heta.2 hnull
  have hval : F.barycenter eta = nu.1 := congrArg Subtype.val hEq
  rw [← hval]
  exact hsing

end NevanlinnaBoundaryFamily

end


end GaloisForLFunctions.HTGeometry
