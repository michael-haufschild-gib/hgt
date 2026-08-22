import GaloisForLFunctions.RHTower.DeningerQuotientHilbertian
import GaloisForLFunctions.RHTower.DeningerNuclearCompletedInvariance
import GaloisForLFunctions.RHTower.DeningerHilbertianRefinement

/-!
# Nuclearity passes to quotients

For a Hilbertian seminorm the completed quotient is realized in `ℓ²` by the complementary
orthogonal projection.  Its range lies inside the range of the ambient realization — the projection
moves a vector by an element of the closed image of the submodule, which the ambient range already
contains — and inside the orthogonal complement of that image.  Inverting the ambient realization
on its range therefore produces a bounded section of the completed projection, and the quotient
criterion turns the section into nuclearity of the quotient family.

For a general nuclear family the Hilbertian refinement supplies an equivalent Hilbertian family,
and dominations pass to quotients, so nuclearity of a quotient holds in general.

* `deningerQuotientEmbeddingC_range_le` : the quotient realization lands in the ambient range.
* `deningerQuotientSection` : **the bounded section of the completed projection.**
* `deningerIsNuclearSpaceC_quotient` : **quotients of nuclear spaces are nuclear.**
-/

namespace RHTower

open UniformSpace ContinuousLinearMap

section QuotientSection

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable {κ : Type} {p : Seminorm 𝕜 E} {A : E →ₗ[𝕜] lp (fun _ : κ => 𝕜) 2}

theorem deningerQuotientSeminorm_eq_norm_hilbertianMap (N : Submodule 𝕜 E)
    (hA : ∀ x, p x = ‖A x‖) (z : E ⧸ N) :
    deningerQuotientSeminorm N p z = ‖deningerQuotientHilbertianMap N A z‖ := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N z
  rw [deningerQuotientSeminorm_eq_norm_sub_starProjection N hA x,
    deningerQuotientHilbertianMap_mk]

/-- The ambient realization of the completed seminorm space. -/
noncomputable abbrev deningerAmbientEmbeddingC (hA : ∀ x, p x = ‖A x‖) :
    DeningerSeminormCompletion p →L[𝕜] lp (fun _ : κ => 𝕜) 2 :=
  deningerHilbertianEmbeddingC hA

/-- The realization of the completed quotient. -/
noncomputable abbrev deningerQuotientEmbeddingC (N : Submodule 𝕜 E) (hA : ∀ x, p x = ‖A x‖) :
    DeningerSeminormCompletion (deningerQuotientSeminorm N p) →L[𝕜] lp (fun _ : κ => 𝕜) 2 :=
  deningerHilbertianEmbeddingC (deningerQuotientSeminorm_eq_norm_hilbertianMap N hA)

/-! ## The two range inclusions -/

theorem deningerQuotientImage_le_ambient_range (N : Submodule 𝕜 E) (hA : ∀ x, p x = ‖A x‖) :
    (deningerQuotientImage N A : Set (lp (fun _ : κ => 𝕜) 2))
      ⊆ Set.range (deningerAmbientEmbeddingC hA) := by
  refine closure_minimal ?_ (deningerHilbertianEmbeddingC_isClosed_range hA)
  rintro w ⟨n, _, rfl⟩
  exact ⟨Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p)
    (deningerSeminormMk p n), by rw [deningerHilbertianEmbeddingC_coe]; rfl⟩

theorem deningerQuotientEmbeddingC_range_le (N : Submodule 𝕜 E) (hA : ∀ x, p x = ‖A x‖)
    (w : DeningerSeminormCompletion (deningerQuotientSeminorm N p)) :
    deningerQuotientEmbeddingC N hA w ∈ Set.range (deningerAmbientEmbeddingC hA) := by
  set S : Set (DeningerSeminormCompletion (deningerQuotientSeminorm N p)) :=
    {v | deningerQuotientEmbeddingC N hA v ∈ Set.range (deningerAmbientEmbeddingC hA)} with hS
  have hclosed : IsClosed S :=
    IsClosed.preimage (deningerQuotientEmbeddingC N hA).continuous
      (deningerHilbertianEmbeddingC_isClosed_range hA)
  have hsub : Set.range (Completion.toComplL (𝕜 := 𝕜)
      (E := DeningerSeminormSpace (deningerQuotientSeminorm N p))) ⊆ S := by
    rintro v ⟨z, rfl⟩
    obtain ⟨y, rfl⟩ := deningerSeminormMk_surjective (deningerQuotientSeminorm N p) z
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N y
    show deningerQuotientEmbeddingC N hA (Completion.toComplL _)
      ∈ Set.range (deningerAmbientEmbeddingC hA)
    rw [deningerHilbertianEmbeddingC_coe, deningerHilbertianEmbedding_mk,
      deningerQuotientHilbertianMap_mk]
    have hAx : A x ∈ Set.range (deningerAmbientEmbeddingC hA) :=
      ⟨Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p) (deningerSeminormMk p x), by
        rw [deningerHilbertianEmbeddingC_coe]; rfl⟩
    have hproj : (deningerQuotientImage N A).starProjection (A x)
        ∈ Set.range (deningerAmbientEmbeddingC hA) :=
      deningerQuotientImage_le_ambient_range N hA
        ((deningerQuotientImage N A).starProjection_apply_mem (A x))
    obtain ⟨v₁, hv₁⟩ := hAx
    obtain ⟨v₂, hv₂⟩ := hproj
    exact ⟨v₁ - v₂, by rw [map_sub, hv₁, hv₂]⟩
  have hdense := deningerDenseRange_toComplL (deningerQuotientSeminorm N p)
  have huniv : (Set.univ : Set (DeningerSeminormCompletion (deningerQuotientSeminorm N p)))
      ⊆ S := by
    rw [← hdense.closure_eq]
    exact hclosed.closure_subset_iff.mpr hsub
  exact huniv (Set.mem_univ w)

theorem deningerQuotientEmbeddingC_mem_orthogonal (N : Submodule 𝕜 E) (hA : ∀ x, p x = ‖A x‖)
    (w : DeningerSeminormCompletion (deningerQuotientSeminorm N p)) :
    deningerQuotientEmbeddingC N hA w ∈ (deningerQuotientImage N A)ᗮ := by
  have hclosed : IsClosed {v : DeningerSeminormCompletion (deningerQuotientSeminorm N p) |
      deningerQuotientEmbeddingC N hA v ∈ (deningerQuotientImage N A)ᗮ} :=
    IsClosed.preimage (deningerQuotientEmbeddingC N hA).continuous
      (deningerQuotientImage N A).isClosed_orthogonal
  have hmem : ∀ z : DeningerSeminormSpace (deningerQuotientSeminorm N p),
      deningerQuotientEmbeddingC N hA
          (Completion.toComplL (𝕜 := 𝕜)
            (E := DeningerSeminormSpace (deningerQuotientSeminorm N p)) z)
        ∈ (deningerQuotientImage N A)ᗮ := by
    intro z
    obtain ⟨y, rfl⟩ := deningerSeminormMk_surjective (deningerQuotientSeminorm N p) z
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N y
    rw [deningerHilbertianEmbeddingC_coe, deningerHilbertianEmbedding_mk,
      deningerQuotientHilbertianMap_mk]
    exact (deningerQuotientImage N A).sub_starProjection_mem_orthogonal (A x)
  have hsub : Set.range (Completion.toComplL (𝕜 := 𝕜)
      (E := DeningerSeminormSpace (deningerQuotientSeminorm N p)))
      ⊆ {v | deningerQuotientEmbeddingC N hA v ∈ (deningerQuotientImage N A)ᗮ} := by
    rintro v ⟨z, rfl⟩
    exact hmem z
  have hdense := deningerDenseRange_toComplL (deningerQuotientSeminorm N p)
  have huniv : (Set.univ : Set (DeningerSeminormCompletion (deningerQuotientSeminorm N p)))
      ⊆ {v | deningerQuotientEmbeddingC N hA v ∈ (deningerQuotientImage N A)ᗮ} := by
    rw [← hdense.closure_eq]
    exact hclosed.closure_subset_iff.mpr hsub
  exact huniv (Set.mem_univ w)

/-! ## The section -/

/-- The ambient realization as an isometric equivalence onto its range. -/
noncomputable def deningerAmbientRangeEquiv (hA : ∀ x, p x = ‖A x‖) :
    DeningerSeminormCompletion p ≃ₗᵢ[𝕜]
      (LinearMap.range (deningerAmbientEmbeddingC hA).toLinearMap) :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap :=
        (deningerAmbientEmbeddingC hA).toLinearMap.codRestrict
          (LinearMap.range (deningerAmbientEmbeddingC hA).toLinearMap) fun v => ⟨v, rfl⟩
      norm_map' := fun v => deningerHilbertianEmbeddingC_norm hA v }
    fun w => by
      obtain ⟨v, hv⟩ := w.2
      exact ⟨v, Subtype.ext hv⟩

theorem deningerAmbientRangeEquiv_coe (hA : ∀ x, p x = ‖A x‖)
    (v : DeningerSeminormCompletion p) :
    ((deningerAmbientRangeEquiv hA v :
        LinearMap.range (deningerAmbientEmbeddingC hA).toLinearMap) : lp (fun _ : κ => 𝕜) 2)
      = deningerAmbientEmbeddingC hA v := rfl

/-- **The bounded section of the completed quotient projection.** -/
private noncomputable def deningerQuotientSection (N : Submodule 𝕜 E) (hA : ∀ x, p x = ‖A x‖) :
    DeningerSeminormCompletion (deningerQuotientSeminorm N p) →L[𝕜]
      DeningerSeminormCompletion p :=
  ((deningerAmbientRangeEquiv hA).symm.toLinearIsometry.toContinuousLinearMap).comp
    ((deningerQuotientEmbeddingC N hA).codRestrict
      (LinearMap.range (deningerAmbientEmbeddingC hA).toLinearMap)
      fun w => deningerQuotientEmbeddingC_range_le N hA w)

theorem deningerQuotientSection_embedding (N : Submodule 𝕜 E) (hA : ∀ x, p x = ‖A x‖)
    (w : DeningerSeminormCompletion (deningerQuotientSeminorm N p)) :
    deningerAmbientEmbeddingC hA (deningerQuotientSection N hA w)
      = deningerQuotientEmbeddingC N hA w := by
  show deningerAmbientEmbeddingC hA
      ((deningerAmbientRangeEquiv hA).symm
        ⟨deningerQuotientEmbeddingC N hA w, deningerQuotientEmbeddingC_range_le N hA w⟩) = _
  have h := deningerAmbientRangeEquiv_coe hA
    ((deningerAmbientRangeEquiv hA).symm
      ⟨deningerQuotientEmbeddingC N hA w, deningerQuotientEmbeddingC_range_le N hA w⟩)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h.symm

/-- The realization intertwines the projection with the complementary orthogonal projection. -/
theorem deningerQuotientEmbeddingC_projection (N : Submodule 𝕜 E) (hA : ∀ x, p x = ‖A x‖)
    (v : DeningerSeminormCompletion p) :
    deningerQuotientEmbeddingC N hA (deningerQuotientProjectionC N p v)
      = deningerAmbientEmbeddingC hA v
        - (deningerQuotientImage N A).starProjection (deningerAmbientEmbeddingC hA v) := by
  have hfun : (fun v : DeningerSeminormCompletion p =>
        deningerQuotientEmbeddingC N hA (deningerQuotientProjectionC N p v))
      = fun v : DeningerSeminormCompletion p => deningerAmbientEmbeddingC hA v
        - (deningerQuotientImage N A).starProjection (deningerAmbientEmbeddingC hA v) := by
    refine (deningerDenseRange_toComplL p).equalizer
      ((deningerQuotientEmbeddingC N hA).continuous.comp
        (deningerQuotientProjectionC N p).continuous)
      (((deningerAmbientEmbeddingC hA).continuous).sub
        (((deningerQuotientImage N A).starProjection).continuous.comp
          (deningerAmbientEmbeddingC hA).continuous)) ?_
    funext z
    obtain ⟨x, rfl⟩ := deningerSeminormMk_surjective p z
    show deningerQuotientEmbeddingC N hA
        (deningerQuotientProjectionC N p (Completion.toComplL _))
      = deningerAmbientEmbeddingC hA (Completion.toComplL _)
        - (deningerQuotientImage N A).starProjection
          (deningerAmbientEmbeddingC hA (Completion.toComplL _))
    rw [deningerQuotientProjectionC_coe, deningerHilbertianEmbeddingC_coe,
      deningerHilbertianEmbeddingC_coe, deningerQuotientProjection_mk,
      deningerHilbertianEmbedding_mk, deningerHilbertianEmbedding_mk,
      deningerQuotientHilbertianMap_mk]
  exact congrFun hfun v

/-- **The section identity.** -/
theorem deningerQuotientSection_projection (N : Submodule 𝕜 E) (hA : ∀ x, p x = ‖A x‖)
    (w : DeningerSeminormCompletion (deningerQuotientSeminorm N p)) :
    deningerQuotientProjectionC N p (deningerQuotientSection N hA w) = w := by
  have hinj : Function.Injective (deningerQuotientEmbeddingC N hA) :=
    (deningerHilbertianEmbeddingC_isometry
      (deningerQuotientSeminorm_eq_norm_hilbertianMap N hA)).injective
  refine hinj ?_
  rw [deningerQuotientEmbeddingC_projection N hA (deningerQuotientSection N hA w),
    deningerQuotientSection_embedding N hA w]
  have hzero : (deningerQuotientImage N A).starProjection
      (deningerQuotientEmbeddingC N hA w) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff (K := deningerQuotientImage N A)).mpr
      (deningerQuotientEmbeddingC_mem_orthogonal N hA w)
  rw [hzero, sub_zero]

end QuotientSection

section QuotientPermanence

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- **Quotients of a nuclear space with a Hilbertian presentation are nuclear.** -/
theorem deningerIsNuclearSpaceC_quotient_of_hilbertian {ι : Type*} (P : SeminormFamily 𝕜 E ι)
    (N : Submodule 𝕜 E) (hP : DeningerIsNuclearSpaceC P)
    (hhilb : ∀ i, DeningerIsHilbertianSeminorm (P i)) :
    DeningerIsNuclearSpaceC (fun i => deningerQuotientSeminorm N (P i)) := by
  refine deningerIsNuclearSpaceC_quotient_of_rightInverse P N hP fun i => ?_
  obtain ⟨κ, A, hA⟩ := hhilb i
  exact ⟨deningerQuotientSection N hA, deningerQuotientSection_projection N hA⟩

/-- **Quotients of nuclear spaces are nuclear.**  The Hilbertian refinement of a nuclear family is
a nuclear Hilbertian family, its quotient family is nuclear by the section construction, and
dominations pass to quotients, so the quotient of the original family is nuclear as well. -/
theorem deningerIsNuclearSpaceC_quotient {ι : Type*} (P : SeminormFamily 𝕜 E ι)
    (N : Submodule 𝕜 E) (hP : DeningerIsNuclearSpace P) :
    DeningerIsNuclearSpaceC (fun i => deningerQuotientSeminorm N (P i)) := by
  obtain ⟨Q, hhilb, hQnuc, hPQ, hQP⟩ := deningerNuclear_exists_hilbertian_family P hP
  have hQquot : DeningerIsNuclearSpaceC (fun k => deningerQuotientSeminorm N (Q k)) :=
    deningerIsNuclearSpaceC_quotient_of_hilbertian Q N (DeningerIsNuclearSpace.toC Q hQnuc) hhilb
  refine deningerIsNuclearSpaceC_of_dominating (fun k => deningerQuotientSeminorm N (Q k))
    (fun i => deningerQuotientSeminorm N (P i)) ?_ ?_ hQquot
  · intro i
    obtain ⟨k, C, hC⟩ := hPQ i
    exact ⟨k, |C|, fun z => deningerQuotientSeminorm_le_of_le N (abs_nonneg C)
      (deningerSeminorm_le_abs hC) z⟩
  · intro k
    obtain ⟨i, C, hC⟩ := hQP k
    exact ⟨i, |C|, fun z => deningerQuotientSeminorm_le_of_le N (abs_nonneg C)
      (deningerSeminorm_le_abs hC) z⟩

end QuotientPermanence

end RHTower
