import GaloisForLFunctions.RHTower.DeningerHilbertianEmbedding

/-!
# The subspace quotient embeds isometrically, with closed image

The seminorm of a subspace is the restriction of the ambient seminorm, so the induced embedding of
seminorm quotients preserves norms.  The extension to the completions preserves them too, being
continuous and agreeing with the embedding on a dense set, and therefore has closed range: an
isometry out of a complete space has complete, hence closed, image.

For a Hilbertian ambient seminorm the restriction is Hilbertian as well, and the two `ℓ²`
embeddings are compatible with the embedding of the subspace quotient.  Together these say the
completed subspace quotient sits inside the ambient one as a closed isometric copy, which is what
makes it complemented.

* `deningerSubspaceEmbedding_norm`, `deningerSubspaceEmbeddingC_norm` : the embedding is
  isometric, before and after completion.
* `deningerSubspaceEmbeddingC_isClosed_range` : its image is closed.
* `deningerRestrict_hilbertian`, `deningerHilbertianEmbeddingC_subspace` : the restriction of a
  Hilbertian seminorm is Hilbertian, compatibly with the embedding.
-/

namespace RHTower

open UniformSpace ContinuousLinearMap

section SubspaceIsometry

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]

omit [CompleteSpace 𝕜] in
/-- **The embedding of a subspace quotient is isometric.** -/
theorem deningerSubspaceEmbedding_norm (F : Submodule 𝕜 E) (p : Seminorm 𝕜 E)
    (w : DeningerSeminormSpace (deningerRestrictSeminorm F p)) :
    ‖deningerSubspaceEmbedding F p w‖ = ‖w‖ := by
  obtain ⟨v, rfl⟩ := deningerSeminormMk_surjective (deningerRestrictSeminorm F p) w
  rw [deningerSubspaceEmbedding_mk, deningerSeminormMk_norm, deningerSeminormMk_norm]
  rfl

omit [CompleteSpace 𝕜] in
/-- **The completed embedding of a subspace quotient is isometric.** -/
theorem deningerSubspaceEmbeddingC_norm (F : Submodule 𝕜 E) (p : Seminorm 𝕜 E)
    (w : DeningerSeminormCompletion (deningerRestrictSeminorm F p)) :
    ‖deningerSubspaceEmbeddingC F p w‖ = ‖w‖ := by
  have hfun : (fun w : DeningerSeminormCompletion (deningerRestrictSeminorm F p) =>
        ‖deningerSubspaceEmbeddingC F p w‖)
      = fun w : DeningerSeminormCompletion (deningerRestrictSeminorm F p) => ‖w‖ := by
    refine (deningerDenseRange_toComplL (deningerRestrictSeminorm F p)).equalizer
      (continuous_norm.comp (deningerSubspaceEmbeddingC F p).continuous) continuous_norm ?_
    funext z
    show ‖deningerSubspaceEmbeddingC F p (Completion.toComplL z)‖
      = ‖Completion.toComplL (𝕜 := 𝕜)
        (E := DeningerSeminormSpace (deningerRestrictSeminorm F p)) z‖
    rw [deningerSubspaceEmbeddingC_coe]
    simp only [Completion.coe_toComplL, Completion.norm_coe]
    exact deningerSubspaceEmbedding_norm F p z
  exact congrFun hfun w

omit [CompleteSpace 𝕜] in
theorem deningerSubspaceEmbeddingC_isometry (F : Submodule 𝕜 E) (p : Seminorm 𝕜 E) :
    Isometry (deningerSubspaceEmbeddingC F p) :=
  AddMonoidHomClass.isometry_of_norm _ (deningerSubspaceEmbeddingC_norm F p)

omit [CompleteSpace 𝕜] in
/-- **The completed embedding has closed image.** -/
theorem deningerSubspaceEmbeddingC_isClosed_range (F : Submodule 𝕜 E) (p : Seminorm 𝕜 E) :
    IsClosed (Set.range (deningerSubspaceEmbeddingC F p)) :=
  ((deningerSubspaceEmbeddingC_isometry F p).isUniformInducing.isComplete_range).isClosed

omit [CompleteSpace 𝕜] in
theorem deningerSubspaceEmbeddingC_injective (F : Submodule 𝕜 E) (p : Seminorm 𝕜 E) :
    Function.Injective (deningerSubspaceEmbeddingC F p) :=
  (deningerSubspaceEmbeddingC_isometry F p).injective

end SubspaceIsometry

section SubspaceHilbertian

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable {κ : Type} {p : Seminorm 𝕜 E} {A : E →ₗ[𝕜] lp (fun _ : κ => 𝕜) 2}

/-- **A Hilbertian seminorm restricts to a Hilbertian seminorm.** -/
theorem deningerRestrict_hilbertian (F : Submodule 𝕜 E) (hA : ∀ x, p x = ‖A x‖) :
    ∀ v : F, deningerRestrictSeminorm F p v = ‖(A ∘ₗ F.subtype) v‖ := fun v => hA (v : E)

/-- **The two `ℓ²` embeddings are compatible** with the embedding of the subspace quotient. -/
theorem deningerHilbertianEmbeddingC_subspace (F : Submodule 𝕜 E) (hA : ∀ x, p x = ‖A x‖)
    (v : DeningerSeminormCompletion (deningerRestrictSeminorm F p)) :
    deningerHilbertianEmbeddingC hA (deningerSubspaceEmbeddingC F p v)
      = deningerHilbertianEmbeddingC (deningerRestrict_hilbertian F hA) v := by
  have hfun : (fun v : DeningerSeminormCompletion (deningerRestrictSeminorm F p) =>
        deningerHilbertianEmbeddingC hA (deningerSubspaceEmbeddingC F p v))
      = fun v => deningerHilbertianEmbeddingC (deningerRestrict_hilbertian F hA) v := by
    refine (deningerDenseRange_toComplL (deningerRestrictSeminorm F p)).equalizer
      ((deningerHilbertianEmbeddingC hA).continuous.comp
        (deningerSubspaceEmbeddingC F p).continuous)
      (deningerHilbertianEmbeddingC (deningerRestrict_hilbertian F hA)).continuous ?_
    funext w
    show deningerHilbertianEmbeddingC hA
        (deningerSubspaceEmbeddingC F p (Completion.toComplL w))
      = deningerHilbertianEmbeddingC (deningerRestrict_hilbertian F hA)
        (Completion.toComplL w)
    rw [deningerSubspaceEmbeddingC_coe, deningerHilbertianEmbeddingC_coe,
      deningerHilbertianEmbeddingC_coe]
    obtain ⟨u, rfl⟩ := deningerSeminormMk_surjective (deningerRestrictSeminorm F p) w
    rfl
  exact congrFun hfun v

/-- The image in `ℓ²` of the completed quotient of the subspace. -/
noncomputable def deningerSubspaceRange (F : Submodule 𝕜 E) (hA : ∀ x, p x = ‖A x‖) :
    Submodule 𝕜 (lp (fun _ : κ => 𝕜) 2) :=
  LinearMap.range
    (deningerHilbertianEmbeddingC (deningerRestrict_hilbertian F hA)).toLinearMap

theorem deningerSubspaceRange_coe (F : Submodule 𝕜 E) (hA : ∀ x, p x = ‖A x‖) :
    (deningerSubspaceRange F hA : Set (lp (fun _ : κ => 𝕜) 2))
      = Set.range (deningerHilbertianEmbeddingC (deningerRestrict_hilbertian F hA)) := by
  ext z
  exact ⟨fun ⟨v, hv⟩ => ⟨v, hv⟩, fun ⟨v, hv⟩ => ⟨v, hv⟩⟩

/-- **The image of the completed subspace quotient is a closed subspace of `ℓ²`**, hence
complete. -/
theorem deningerSubspaceRange_completeSpace (F : Submodule 𝕜 E) (hA : ∀ x, p x = ‖A x‖) :
    CompleteSpace (deningerSubspaceRange F hA) := by
  haveI : IsClosed ((deningerSubspaceRange F hA : Set (lp (fun _ : κ => 𝕜) 2))) := by
    rw [deningerSubspaceRange_coe]
    exact deningerHilbertianEmbeddingC_isClosed_range (deningerRestrict_hilbertian F hA)
  exact IsClosed.completeSpace_coe

/-- The completed subspace quotient is isometrically isomorphic to its image in `ℓ²`. -/
noncomputable def deningerSubspaceRangeEquiv (F : Submodule 𝕜 E) (hA : ∀ x, p x = ‖A x‖) :
    DeningerSeminormCompletion (deningerRestrictSeminorm F p) ≃ₗᵢ[𝕜]
      deningerSubspaceRange F hA :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap :=
        (deningerHilbertianEmbeddingC
          (deningerRestrict_hilbertian F hA)).toLinearMap.codRestrict
            (deningerSubspaceRange F hA) fun v => ⟨v, rfl⟩
      norm_map' := fun v =>
        deningerHilbertianEmbeddingC_norm (deningerRestrict_hilbertian F hA) v }
    fun w => by
      obtain ⟨v, hv⟩ := w.2
      exact ⟨v, Subtype.ext hv⟩

theorem deningerSubspaceRangeEquiv_coe (F : Submodule 𝕜 E) (hA : ∀ x, p x = ‖A x‖)
    (v : DeningerSeminormCompletion (deningerRestrictSeminorm F p)) :
    ((deningerSubspaceRangeEquiv F hA v : deningerSubspaceRange F hA) : lp (fun _ : κ => 𝕜) 2)
      = deningerHilbertianEmbeddingC (deningerRestrict_hilbertian F hA) v := rfl

/-- **The bounded left inverse of the completed subspace embedding**: send the ambient class into
`ℓ²`, project orthogonally onto the closed image of the subspace quotient, and undo the isometry
onto that image. -/
noncomputable def deningerSubspaceLeftInverse (F : Submodule 𝕜 E) (hA : ∀ x, p x = ‖A x‖)
    [(deningerSubspaceRange F hA).HasOrthogonalProjection] :
    DeningerSeminormCompletion p →L[𝕜]
      DeningerSeminormCompletion (deningerRestrictSeminorm F p) :=
  ((deningerSubspaceRangeEquiv F hA).symm.toLinearIsometry.toContinuousLinearMap).comp
    (((deningerSubspaceRange F hA).orthogonalProjectionOnto).comp
      (deningerHilbertianEmbeddingC hA))

/-- **The left inverse identity.**  The ambient image of a subspace class already lies in the
image of the subspace quotient, so the projection leaves it fixed. -/
theorem deningerSubspaceLeftInverse_comp (F : Submodule 𝕜 E) (hA : ∀ x, p x = ‖A x‖)
    [(deningerSubspaceRange F hA).HasOrthogonalProjection]
    (v : DeningerSeminormCompletion (deningerRestrictSeminorm F p)) :
    deningerSubspaceLeftInverse F hA (deningerSubspaceEmbeddingC F p v) = v := by
  show (deningerSubspaceRangeEquiv F hA).symm
      ((deningerSubspaceRange F hA).orthogonalProjectionOnto
        (deningerHilbertianEmbeddingC hA (deningerSubspaceEmbeddingC F p v))) = v
  rw [deningerHilbertianEmbeddingC_subspace, ← deningerSubspaceRangeEquiv_coe F hA v,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    LinearIsometryEquiv.symm_apply_apply]

end SubspaceHilbertian

section SubspacePermanence

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- **Subspaces of a nuclear space with a Hilbertian presentation are nuclear.**  Each seminorm is
the norm of a map into `ℓ²`, so the completed subspace quotient sits in the completed ambient
quotient as a closed isometric copy; orthogonal projection in `ℓ²` supplies the bounded left
inverse required for permanence. -/
theorem deningerIsNuclearSpaceC_subspace_of_hilbertian {ι : Type*} (P : SeminormFamily 𝕜 E ι)
    (F : Submodule 𝕜 E) (hP : DeningerIsNuclearSpaceC P)
    (hhilb : ∀ i, DeningerIsHilbertianSeminorm (P i)) :
    DeningerIsNuclearSpaceC (fun i => deningerRestrictSeminorm F (P i)) := by
  refine deningerIsNuclearSpaceC_subspace_of_leftInverse P F hP fun i => ?_
  obtain ⟨κ, A, hA⟩ := hhilb i
  haveI : CompleteSpace (deningerSubspaceRange F hA) :=
    deningerSubspaceRange_completeSpace F hA
  exact ⟨deningerSubspaceLeftInverse F hA, deningerSubspaceLeftInverse_comp F hA⟩

/-- **Permanence of nuclearity under subspaces**, from an uncompleted Hilbertian presentation. -/
theorem deningerIsNuclearSpace_subspace_of_hilbertian {ι : Type*} (P : SeminormFamily 𝕜 E ι)
    (F : Submodule 𝕜 E) (hP : DeningerIsNuclearSpace P)
    (hhilb : ∀ i, DeningerIsHilbertianSeminorm (P i)) :
    DeningerIsNuclearSpaceC (fun i => deningerRestrictSeminorm F (P i)) :=
  deningerIsNuclearSpaceC_subspace_of_hilbertian P F (DeningerIsNuclearSpace.toC P hP) hhilb

end SubspacePermanence

end RHTower
