import GaloisForLFunctions.HTGeometry.ShapeResidualAvoidance
import GaloisForLFunctions.HTGeometry.ShapeDeterminantPolynomial

/-!
# Residual coefficient rigidity

Putting the two halves together: a continuous, locally surjective jet observation avoids every
shape's determinant hypersurface on a residual set of parameters, and off that hypersurface the only
coefficient vector annihilated by the expanded evaluation matrix is zero.

So on a dense residual set of parameters no relation of any shape holds -- which is the parameter
statement a transversality argument is supposed to deliver.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The jet variables of a shape: one packet of jets per row of its evaluation matrix. -/
abbrev ShapeJetIndex (S : RelationShape) : Type :=
  (Fin S.monomialCount × Fin (S.spectralDegree + 1)) × Fin S.jetDepth

/-- **Residual coefficient rigidity.**  For a continuous, locally surjective jet observation there is
a residual set of parameters at which, for every relation shape, the only coefficient vector
annihilated by the expanded evaluation matrix at the shape's node packet is zero. -/
theorem residual_forall_shape_coeff_eq_zero {P : Type*} [TopologicalSpace P] [BaireSpace P]
    {Sh : Type} [Countable Sh] (sh : Sh → RelationShape)
    (nodeOf : ∀ S : Sh, Fin (sh S).monomialCount × Fin ((sh S).spectralDegree + 1) → ℂ)
    (jetOf : ∀ S : Sh, P → (ShapeJetIndex (sh S) → ℂ))
    (hcont : ∀ S, Continuous (jetOf S))
    (hsurj : ∀ S, LocallySurjectiveObservation (jetOf S))
    (hD : ∀ S, shapeDeterminant (sh S).spectralDegree (sh S).jetDepth (sh S).exponent
      (nodeOf S) ≠ 0) :
    {p : P | ∀ (S : Sh) (c : Fin (sh S).monomialCount × Fin ((sh S).spectralDegree + 1) → ℂ),
        (expandedDifferentialEvaluationMatrix (sh S).spectralDegree (sh S).jetDepth (nodeOf S)
          (sh S).exponent (jetOf S p)).mulVec c = 0 → c = 0} ∈ residual P := by
  refine Filter.mem_of_superset
    (residual_forall_shape_avoidance jetOf hcont hsurj
      (fun S => shapeDeterminant (sh S).spectralDegree (sh S).jetDepth (sh S).exponent
        (nodeOf S)) hD) ?_
  intro p hp S c hc
  exact coeff_eq_zero_of_shapeDeterminant_ne_zero (sh S).spectralDegree (sh S).jetDepth
    (sh S).exponent (nodeOf S) (jetOf S p) (hp S) c hc

/-- **The rigid parameters are dense.** -/
theorem dense_forall_shape_coeff_eq_zero {P : Type*} [TopologicalSpace P] [BaireSpace P]
    {Sh : Type} [Countable Sh] (sh : Sh → RelationShape)
    (nodeOf : ∀ S : Sh, Fin (sh S).monomialCount × Fin ((sh S).spectralDegree + 1) → ℂ)
    (jetOf : ∀ S : Sh, P → (ShapeJetIndex (sh S) → ℂ))
    (hcont : ∀ S, Continuous (jetOf S))
    (hsurj : ∀ S, LocallySurjectiveObservation (jetOf S))
    (hD : ∀ S, shapeDeterminant (sh S).spectralDegree (sh S).jetDepth (sh S).exponent
      (nodeOf S) ≠ 0) :
    Dense {p : P | ∀ (S : Sh) (c : Fin (sh S).monomialCount × Fin ((sh S).spectralDegree + 1) → ℂ),
        (expandedDifferentialEvaluationMatrix (sh S).spectralDegree (sh S).jetDepth (nodeOf S)
          (sh S).exponent (jetOf S p)).mulVec c = 0 → c = 0} :=
  dense_of_mem_residual (residual_forall_shape_coeff_eq_zero sh nodeOf jetOf hcont hsurj hD)

/-- **Every shape with distinct monomials admits an admissible node packet.**  Choosing one for each
shape supplies the `nodeOf` and `hD` data of the rigidity theorem. -/
theorem exists_nodeOf_of_injective_exponent
    (hexp : ∀ S : RelationShape, Function.Injective S.exponent) :
    ∃ nodeOf : ∀ S : RelationShape, Fin S.monomialCount × Fin (S.spectralDegree + 1) → ℂ,
      (∀ S, Function.Injective (nodeOf S)) ∧
      ∀ S, shapeDeterminant S.spectralDegree S.jetDepth S.exponent (nodeOf S) ≠ 0 := by
  classical
  choose nodeOf hinj hne using fun S : RelationShape =>
    exists_injective_nodes_shapeDeterminant_ne_zero S.spectralDegree S.jetDepth S.exponent (hexp S)
  exact ⟨nodeOf, hinj, hne⟩

end

end GaloisForLFunctions.HTGeometry
