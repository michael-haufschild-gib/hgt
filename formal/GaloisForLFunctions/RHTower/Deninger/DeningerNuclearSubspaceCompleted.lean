import GaloisForLFunctions.RHTower.Deninger.DeningerNuclearSpaceCompleted

/-!
# Subspaces in the completed formulation

The embedding of the seminorm quotient of a subspace extends to the completions, and the square
relating it to the comparison maps still commutes there, since both composites agree on the dense
image of the uncompleted quotient.  So the completed comparison map of the subspace is nuclear as
soon as the completed embedding admits a bounded left inverse.

At the completed level that hypothesis is the honest one: for a Hilbertian seminorm the completed
quotients are Hilbert spaces and the image of a completed subspace quotient is a closed subspace,
hence complemented by orthogonal projection — whereas before completion only the closure of the
image is complemented.

* `deningerSubspaceEmbeddingC` : the completed embedding of a subspace quotient.
* `deningerSubspaceEmbedding_square` : the comparison square before completion.
* `deningerIsNuclearSpaceC_subspace_of_leftInverse` : completed nuclearity of a subspace with
  complemented completed embeddings.
-/

namespace RHTower

open UniformSpace ContinuousLinearMap

section SubspaceCompleted

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]

omit [CompleteSpace 𝕜] in
/-- **The comparison square of a subspace**, before completion. -/
theorem deningerSubspaceEmbedding_square {p q : Seminorm 𝕜 E} {C : ℝ} (F : Submodule 𝕜 E)
    (h : ∀ x, p x ≤ C * q x)
    (hF : ∀ v : F, deningerRestrictSeminorm F p v ≤ C * deningerRestrictSeminorm F q v) :
    (deningerSubspaceEmbedding F p).comp (deningerSeminormComparison hF)
      = (deningerSeminormComparison h).comp (deningerSubspaceEmbedding F q) := by
  refine ContinuousLinearMap.ext fun w => ?_
  obtain ⟨v, rfl⟩ := deningerSeminormMk_surjective (deningerRestrictSeminorm F q) w
  rfl

/-- **The completed embedding of a subspace quotient.** -/
noncomputable def deningerSubspaceEmbeddingC (F : Submodule 𝕜 E) (p : Seminorm 𝕜 E) :
    DeningerSeminormCompletion (deningerRestrictSeminorm F p) →L[𝕜]
      DeningerSeminormCompletion p :=
  ((Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p)).comp
    (deningerSubspaceEmbedding F p)).extend
      (Completion.toComplL (𝕜 := 𝕜)
        (E := DeningerSeminormSpace (deningerRestrictSeminorm F p)))

omit [CompleteSpace 𝕜] in
theorem deningerSubspaceEmbeddingC_coe (F : Submodule 𝕜 E) (p : Seminorm 𝕜 E)
    (w : DeningerSeminormSpace (deningerRestrictSeminorm F p)) :
    deningerSubspaceEmbeddingC F p
        (Completion.toComplL (𝕜 := 𝕜)
          (E := DeningerSeminormSpace (deningerRestrictSeminorm F p)) w)
      = Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p)
        (deningerSubspaceEmbedding F p w) :=
  ContinuousLinearMap.extend_eq
    (f := (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p)).comp
      (deningerSubspaceEmbedding F p))
    (e := Completion.toComplL (𝕜 := 𝕜)
      (E := DeningerSeminormSpace (deningerRestrictSeminorm F p)))
    (deningerDenseRange_toComplL _) (deningerIsUniformInducing_toComplL _) w

omit [CompleteSpace 𝕜] in
/-- **The comparison square of a subspace, after completion.**  Both composites agree on the
dense image of the uncompleted quotient. -/
theorem deningerSubspaceEmbeddingC_square {p q : Seminorm 𝕜 E} {C : ℝ} (F : Submodule 𝕜 E)
    (h : ∀ x, p x ≤ C * q x)
    (hF : ∀ v : F, deningerRestrictSeminorm F p v ≤ C * deningerRestrictSeminorm F q v) :
    (deningerSubspaceEmbeddingC F p).comp (deningerSeminormComparisonC hF)
      = (deningerSeminormComparisonC h).comp (deningerSubspaceEmbeddingC F q) := by
  refine DFunLike.coe_injective ?_
  refine (deningerDenseRange_toComplL (deningerRestrictSeminorm F q)).equalizer
    ((deningerSubspaceEmbeddingC F p).comp (deningerSeminormComparisonC hF)).continuous
    ((deningerSeminormComparisonC h).comp (deningerSubspaceEmbeddingC F q)).continuous ?_
  funext w
  show deningerSubspaceEmbeddingC F p (deningerSeminormComparisonC hF (Completion.toComplL w))
    = deningerSeminormComparisonC h (deningerSubspaceEmbeddingC F q (Completion.toComplL w))
  rw [deningerSeminormComparisonC_coe, deningerSubspaceEmbeddingC_coe,
    deningerSubspaceEmbeddingC_coe, deningerSeminormComparisonC_coe]
  exact congrArg (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p))
    (ContinuousLinearMap.ext_iff.mp (deningerSubspaceEmbedding_square F h hF) w)

omit [CompleteSpace 𝕜] in
/-- **A subspace with complemented completed embeddings is nuclear in the completed sense.** -/
theorem deningerIsNuclearSpaceC_subspace_of_leftInverse {ι : Type*} (P : SeminormFamily 𝕜 E ι)
    (F : Submodule 𝕜 E) (hP : DeningerIsNuclearSpaceC P)
    (hinv : ∀ i : ι, ∃ r : DeningerSeminormCompletion (P i) →L[𝕜]
        DeningerSeminormCompletion (deningerRestrictSeminorm F (P i)),
      ∀ v, r (deningerSubspaceEmbeddingC F (P i) v) = v) :
    DeningerIsNuclearSpaceC (fun i => deningerRestrictSeminorm F (P i)) := by
  intro i
  obtain ⟨j, C, h, hnuc⟩ := hP i
  obtain ⟨r, hr⟩ := hinv i
  have hcF : ∀ v : F, deningerRestrictSeminorm F (P i) v
      ≤ C * deningerRestrictSeminorm F (P j) v := fun v => h (v : E)
  refine ⟨j, C, hcF, ?_⟩
  refine DeningerIsNuclear.of_comp_left_inverse r hr ?_
  rw [deningerSubspaceEmbeddingC_square F h hcF]
  exact hnuc.compR (deningerSubspaceEmbeddingC F (P j))

end SubspaceCompleted

end RHTower

