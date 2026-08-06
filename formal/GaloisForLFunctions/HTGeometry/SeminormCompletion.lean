import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Seminorm

/-!
# The Hausdorff completion of a space with respect to a seminorm

A seminorm on a real vector space makes it a seminormed group, and the uniform completion of a
seminormed group is a normed group: the completion identifies vectors at distance zero, which is
exactly the Hausdorff quotient by the null space of the seminorm.  The completion is a Banach
space, the canonical map into it is linear and preserves the seminorm as a norm, and its image is
dense.

A graph seminorm — the sum of the norms of the images under two linear maps — is a seminorm, so a
space of forms measured simultaneously by two norms has a Banach completion in which the two
measurements are recorded together.

* `GaloisForLFunctions.HTGeometry.exists_banach_completion_of_seminorm` : the completion of a
  seminormed space.
* `GaloisForLFunctions.HTGeometry.graphSeminorm` : the graph seminorm of a pair of linear maps.
* `GaloisForLFunctions.HTGeometry.exists_banach_completion_graphSeminorm` : the completion with
  respect to a graph seminorm.
-/

universe u

namespace GaloisForLFunctions.HTGeometry

section Completion

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-- The seminormed group structure attached to a seminorm. -/
@[reducible] def seminormedOfSeminorm (q : Seminorm ℝ V) : SeminormedAddCommGroup V :=
  q.toAddGroupSeminorm.toSeminormedAddCommGroup

/-- **The Hausdorff completion of a space with respect to a seminorm is a Banach space**, with a
linear map from the space that turns the seminorm into the norm and has dense image. -/
theorem exists_banach_completion_of_seminorm (q : Seminorm ℝ V) :
    ∃ (B : Type u) (_ : NormedAddCommGroup B) (_ : NormedSpace ℝ B) (_ : CompleteSpace B)
      (ι : V →ₗ[ℝ] B), (∀ v, ‖ι v‖ = q v) ∧ DenseRange ι := by
  letI : SeminormedAddCommGroup V := seminormedOfSeminorm q
  have hnorm : ∀ v : V, ‖v‖ = q v := fun _ => rfl
  letI : NormedSpace ℝ V :=
    { (inferInstance : Module ℝ V) with
      norm_smul_le := fun c v => by
        rw [hnorm, hnorm, map_smul_eq_mul q c v] }
  haveI : UniformContinuousConstSMul ℝ V := inferInstance
  refine ⟨UniformSpace.Completion V, inferInstance, inferInstance, inferInstance,
    (UniformSpace.Completion.toComplL (𝕜 := ℝ) (E := V)).toLinearMap, fun v => ?_, ?_⟩
  · show ‖((v : V) : UniformSpace.Completion V)‖ = q v
    rw [UniformSpace.Completion.norm_coe, hnorm]
  · exact UniformSpace.Completion.denseRange_coe

end Completion

section GraphSeminorm

variable {V : Type u} {W₁ W₂ : Type*} [AddCommGroup V] [Module ℝ V]
  [SeminormedAddCommGroup W₁] [NormedSpace ℝ W₁]
  [SeminormedAddCommGroup W₂] [NormedSpace ℝ W₂]

/-- **The graph seminorm of a pair of linear maps**: the sum of the norms of the two images. -/
noncomputable def graphSeminorm (f : V →ₗ[ℝ] W₁) (g : V →ₗ[ℝ] W₂) : Seminorm ℝ V :=
  (normSeminorm ℝ W₁).comp f + (normSeminorm ℝ W₂).comp g

@[simp] theorem graphSeminorm_apply (f : V →ₗ[ℝ] W₁) (g : V →ₗ[ℝ] W₂) (v : V) :
    graphSeminorm f g v = ‖f v‖ + ‖g v‖ := rfl

/-- **The graph completion is a Banach space**: a space measured simultaneously by two linear
images has a Banach completion recording both, with dense image. -/
theorem exists_banach_completion_graphSeminorm (f : V →ₗ[ℝ] W₁) (g : V →ₗ[ℝ] W₂) :
    ∃ (B : Type u) (_ : NormedAddCommGroup B) (_ : NormedSpace ℝ B) (_ : CompleteSpace B)
      (ι : V →ₗ[ℝ] B), (∀ v, ‖ι v‖ = ‖f v‖ + ‖g v‖) ∧ DenseRange ι :=
  exists_banach_completion_of_seminorm (graphSeminorm f g)

end GraphSeminorm

end GaloisForLFunctions.HTGeometry
