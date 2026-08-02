import GaloisForLFunctions.RHTower.DeningerNuclearSubspaceCompleted

/-!
# The `ℓ²` embedding of a Hilbertian seminorm quotient

A Hilbertian seminorm is the norm of a linear map into an `ℓ²` space, so that map kills the
kernel of the seminorm and induces an isometric embedding of the seminorm quotient into `ℓ²`.
The embedding extends to the completion, still isometrically, and the extension has closed range
because a complete space maps onto a complete, hence closed, subset.

A closed subspace of `ℓ²` is complemented by orthogonal projection, which is what supplies the
bounded left inverse required for permanence of nuclearity under closed subspaces.

* `deningerHilbertianEmbedding`, `_norm`, `_isometry` : the isometric embedding into `ℓ²`.
* `deningerHilbertianEmbeddingC`, `_norm`, `_isometry` : its extension to the completion.
* `deningerHilbertianEmbeddingC_isClosed_range` : the extension has closed range.
-/

namespace RHTower

open UniformSpace ContinuousLinearMap

section HilbertianEmbedding

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable {κ : Type} {p : Seminorm 𝕜 E} {A : E →ₗ[𝕜] lp (fun _ : κ => 𝕜) 2}

theorem deningerSeminormKer_le_ker_of_hilbertian (hA : ∀ x, p x = ‖A x‖) :
    deningerSeminormKer p ≤ LinearMap.ker A := by
  intro x hx
  have hnorm : ‖A x‖ = 0 := by
    rw [← hA x]
    exact hx
  exact norm_eq_zero.mp hnorm

/-- **The isometric embedding of a Hilbertian seminorm quotient into `ℓ²`.** -/
noncomputable def deningerHilbertianEmbedding (hA : ∀ x, p x = ‖A x‖) :
    DeningerSeminormSpace p →L[𝕜] lp (fun _ : κ => 𝕜) 2 :=
  LinearMap.mkContinuous
    (Submodule.liftQ (deningerSeminormKer p) A (deningerSeminormKer_le_ker_of_hilbertian hA))
    1 (by
      rintro ⟨a⟩
      show ‖A a‖ ≤ 1 * p a
      rw [one_mul, hA a])

@[simp]
theorem deningerHilbertianEmbedding_mk (hA : ∀ x, p x = ‖A x‖) (x : E) :
    deningerHilbertianEmbedding hA (deningerSeminormMk p x) = A x := rfl

theorem deningerHilbertianEmbedding_norm (hA : ∀ x, p x = ‖A x‖)
    (z : DeningerSeminormSpace p) : ‖deningerHilbertianEmbedding hA z‖ = ‖z‖ := by
  obtain ⟨x, rfl⟩ := deningerSeminormMk_surjective p z
  rw [deningerHilbertianEmbedding_mk, deningerSeminormMk_norm, hA x]

theorem deningerHilbertianEmbedding_isometry (hA : ∀ x, p x = ‖A x‖) :
    Isometry (deningerHilbertianEmbedding hA) :=
  AddMonoidHomClass.isometry_of_norm _ (deningerHilbertianEmbedding_norm hA)

/-- **The extension of the embedding to the completion.** -/
noncomputable def deningerHilbertianEmbeddingC (hA : ∀ x, p x = ‖A x‖) :
    DeningerSeminormCompletion p →L[𝕜] lp (fun _ : κ => 𝕜) 2 :=
  (deningerHilbertianEmbedding hA).extend
    (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p))

theorem deningerHilbertianEmbeddingC_coe (hA : ∀ x, p x = ‖A x‖)
    (z : DeningerSeminormSpace p) :
    deningerHilbertianEmbeddingC hA
        (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p) z)
      = deningerHilbertianEmbedding hA z :=
  ContinuousLinearMap.extend_eq (f := deningerHilbertianEmbedding hA)
    (e := Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p))
    (deningerDenseRange_toComplL p) (deningerIsUniformInducing_toComplL p) z

theorem deningerHilbertianEmbeddingC_norm (hA : ∀ x, p x = ‖A x‖)
    (w : DeningerSeminormCompletion p) : ‖deningerHilbertianEmbeddingC hA w‖ = ‖w‖ := by
  have hfun : (fun w : DeningerSeminormCompletion p => ‖deningerHilbertianEmbeddingC hA w‖)
      = fun w : DeningerSeminormCompletion p => ‖w‖ := by
    refine (deningerDenseRange_toComplL p).equalizer
      (continuous_norm.comp (deningerHilbertianEmbeddingC hA).continuous) continuous_norm ?_
    funext z
    show ‖deningerHilbertianEmbeddingC hA
      (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p) z)‖
      = ‖Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p) z‖
    rw [deningerHilbertianEmbeddingC_coe, deningerHilbertianEmbedding_norm,
      Completion.coe_toComplL, Completion.norm_coe]
  exact congrFun hfun w

theorem deningerHilbertianEmbeddingC_isometry (hA : ∀ x, p x = ‖A x‖) :
    Isometry (deningerHilbertianEmbeddingC hA) :=
  AddMonoidHomClass.isometry_of_norm _ (deningerHilbertianEmbeddingC_norm hA)

/-- **The extended embedding has closed range**, since a complete space maps isometrically onto a
complete, hence closed, subset. -/
theorem deningerHilbertianEmbeddingC_isClosed_range (hA : ∀ x, p x = ‖A x‖) :
    IsClosed (Set.range (deningerHilbertianEmbeddingC hA)) :=
  ((deningerHilbertianEmbeddingC_isometry hA).isUniformInducing.isComplete_range).isClosed

end HilbertianEmbedding

end RHTower

