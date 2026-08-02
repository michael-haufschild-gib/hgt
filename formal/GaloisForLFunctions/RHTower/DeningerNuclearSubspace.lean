import GaloisForLFunctions.RHTower.DeningerNuclearCompletion

/-!
# Subspaces of nuclear spaces

The seminorm quotient of a subspace embeds isometrically into the seminorm quotient of the whole
space, and the comparison maps of the subspace and of the whole space commute with those
embeddings.  Composing with the whole-space comparison map therefore gives a nuclear map, and the
subspace comparison map is nuclear as soon as the embedding admits a bounded left inverse.

That last hypothesis is exactly the point where nuclearity of a subspace is not formal: a nuclear
representation of the composite has its vectors in the ambient quotient, not in the subspace one.
It is supplied classically by making the seminorms Hilbertian, where a closed subspace is
complemented by orthogonal projection.

* `DeningerIsNuclear.of_comp_left_inverse` : a retracted composite of a nuclear map is nuclear.
* `deningerRestrictSeminorm`, `deningerSubspaceEmbedding` : the restricted seminorm and the
  induced embedding of quotients.
* `deningerIsNuclearSpace_subspace_of_leftInverse` : a subspace with complemented embeddings is
  nuclear.
-/

namespace RHTower

section Retract

variable {𝕜 V Z W : Type*} [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [SeminormedAddCommGroup Z] [NormedSpace 𝕜 Z]
variable [SeminormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- **A retracted composite of a nuclear map is nuclear.**  If the left factor has a bounded left
inverse, nuclearity of the composite descends to the right factor. -/
theorem DeningerIsNuclear.of_comp_left_inverse {j : Z →L[𝕜] W} {S : V →L[𝕜] Z}
    (r : W →L[𝕜] Z) (hr : ∀ z, r (j z) = z) (h : DeningerIsNuclear (j.comp S)) :
    DeningerIsNuclear S := by
  have hcomp : r.comp (j.comp S) = S := by
    refine ContinuousLinearMap.ext fun v => ?_
    exact hr (S v)
  exact hcomp ▸ h.compL r

end Retract

section Subspace

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- The restriction of a seminorm to a subspace. -/
def deningerRestrictSeminorm (F : Submodule 𝕜 E) (p : Seminorm 𝕜 E) : Seminorm 𝕜 F :=
  p.comp F.subtype

@[simp]
theorem deningerRestrictSeminorm_apply (F : Submodule 𝕜 E) (p : Seminorm 𝕜 E) (v : F) :
    deningerRestrictSeminorm F p v = p (v : E) := rfl

/-- **The embedding of the seminorm quotient of a subspace into that of the whole space.**  It is
isometric, since the seminorm of the subspace is the restriction. -/
noncomputable def deningerSubspaceEmbedding (F : Submodule 𝕜 E) (p : Seminorm 𝕜 E) :
    DeningerSeminormSpace (deningerRestrictSeminorm F p) →L[𝕜] DeningerSeminormSpace p :=
  deningerSeminormInduced (F.subtype) (C := 1) fun _ => le_of_eq (one_mul _).symm

@[simp]
theorem deningerSubspaceEmbedding_mk (F : Submodule 𝕜 E) (p : Seminorm 𝕜 E) (v : F) :
    deningerSubspaceEmbedding F p (deningerSeminormMk (deningerRestrictSeminorm F p) v)
      = deningerSeminormMk p (v : E) := rfl

/-- **A subspace with complemented quotient embeddings is nuclear.**  The comparison map of the
subspace, followed by the embedding, is the whole-space comparison map restricted, hence nuclear;
a bounded left inverse of the embedding brings it back. -/
theorem deningerIsNuclearSpace_subspace_of_leftInverse {ι : Type*} (P : SeminormFamily 𝕜 E ι)
    (F : Submodule 𝕜 E) (hP : DeningerIsNuclearSpace P)
    (hinv : ∀ i : ι, ∃ r : DeningerSeminormSpace (P i) →L[𝕜]
        DeningerSeminormSpace (deningerRestrictSeminorm F (P i)),
      ∀ v, r (deningerSubspaceEmbedding F (P i) v) = v) :
    DeningerIsNuclearSpace (fun i => deningerRestrictSeminorm F (P i)) := by
  intro i
  obtain ⟨j, C, hc, hnuc⟩ := hP i
  obtain ⟨r, hr⟩ := hinv i
  have hcF : ∀ v : F, deningerRestrictSeminorm F (P i) v
      ≤ C * deningerRestrictSeminorm F (P j) v := fun v => hc (v : E)
  refine ⟨j, C, hcF, ?_⟩
  refine DeningerIsNuclear.of_comp_left_inverse r hr ?_
  have hfactor : (deningerSubspaceEmbedding F (P i)).comp (deningerSeminormComparison hcF)
      = (deningerSeminormComparison hc).comp (deningerSubspaceEmbedding F (P j)) := by
    refine ContinuousLinearMap.ext fun w => ?_
    obtain ⟨v, rfl⟩ := deningerSeminormMk_surjective (deningerRestrictSeminorm F (P j)) w
    rfl
  rw [hfactor]
  exact hnuc.compR (deningerSubspaceEmbedding F (P j))

end Subspace

end RHTower

