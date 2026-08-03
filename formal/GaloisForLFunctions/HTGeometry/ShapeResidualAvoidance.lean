import GaloisForLFunctions.HTGeometry.RelationShapeCountable
import GaloisForLFunctions.HTGeometry.JetObservationGenericity

/-!
# Avoiding every shape's hypersurface on a residual set

Each relation shape contributes one nonzero polynomial in the observed jet coordinates -- the
determinant of its expanded evaluation matrix at a fixed node packet.  A locally surjective
observation avoids the zero set of any one of them on a residual set, and the shapes are countable,
so it avoids all of them simultaneously on a residual set.

This is the parameter-space conclusion of a transversality argument, with the shape data as the only
index.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Simultaneous avoidance of one hypersurface per shape.**  Note that the observed coordinate
system is allowed to depend on the shape, since deeper relations need deeper jets. -/
theorem residual_forall_shape_avoidance {P : Type*} [TopologicalSpace P] [BaireSpace P]
    {σ : RelationShape → Type} [∀ S, Fintype (σ S)]
    (J : ∀ S : RelationShape, P → (σ S → ℂ))
    (hcont : ∀ S, Continuous (J S)) (hJ : ∀ S, LocallySurjectiveObservation (J S))
    (D : ∀ S, MvPolynomial (σ S) ℂ) (hD : ∀ S, D S ≠ 0) :
    {p : P | ∀ S, MvPolynomial.eval (J S p) (D S) ≠ 0} ∈ residual P := by
  have hset : {p : P | ∀ S, MvPolynomial.eval (J S p) (D S) ≠ 0}
      = ⋂ S, {p : P | MvPolynomial.eval (J S p) (D S) ≠ 0} := by
    ext p
    simp
  rw [hset]
  refine residual_iInter fun S => ?_
  have hone := residual_setOf_forall_eval_observation_ne_zero (hcont S) (hJ S)
    (fun _ : Unit => D S) (fun _ => hD S)
  simpa using hone

/-- **The avoiding parameters are dense.** -/
theorem dense_forall_shape_avoidance {P : Type*} [TopologicalSpace P] [BaireSpace P]
    {σ : RelationShape → Type} [∀ S, Fintype (σ S)]
    (J : ∀ S : RelationShape, P → (σ S → ℂ))
    (hcont : ∀ S, Continuous (J S)) (hJ : ∀ S, LocallySurjectiveObservation (J S))
    (D : ∀ S, MvPolynomial (σ S) ℂ) (hD : ∀ S, D S ≠ 0) :
    Dense {p : P | ∀ S, MvPolynomial.eval (J S p) (D S) ≠ 0} :=
  dense_of_mem_residual (residual_forall_shape_avoidance J hcont hJ D hD)

end

end GaloisForLFunctions.HTGeometry
