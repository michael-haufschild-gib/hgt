import GaloisForLFunctions.RHTower.DeningerNuclearHilbertFactor

/-!
# A nuclear space is presented by Hilbertian seminorms

Each comparison map of a nuclear space is dominated by a Hilbertian seminorm which is itself
dominated by the dominating member of the family.  Choosing one such seminorm for every index
gives a second family, consisting of Hilbertian seminorms, which dominates the original family and
is dominated by it.  Since nuclearity does not depend on the presenting family, the Hilbertian
family is nuclear as well.

A Hilbertian presentation is what the permanence theory for closed subspaces requires: the
seminorm quotients are then pre-Hilbert spaces, in which the image of a subspace quotient is
complemented.

* `DeningerIsHilbertianSeminorm` : a seminorm given by the norm of a map into an `ℓ²` space.
* `deningerNuclear_hilbertian_refinement` : every seminorm of a nuclear space is squeezed by a
  Hilbertian one.
* `deningerNuclear_exists_hilbertian_family` : a nuclear space has a nuclear Hilbertian
  presentation.
-/

namespace RHTower

section Hilbertian

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- **A Hilbertian seminorm**: one given by the norm of a linear map into an `ℓ²` space. -/
def DeningerIsHilbertianSeminorm (h : Seminorm 𝕜 E) : Prop :=
  ∃ (ι : Type) (A : E →ₗ[𝕜] lp (fun _ : ι => 𝕜) 2), ∀ x, h x = ‖A x‖

/-- **Every seminorm of a nuclear space is squeezed by a Hilbertian one.**  The comparison map is
dominated by the norm of its coefficient map into `ℓ²`, which in turn is dominated by the
dominating seminorm. -/
theorem deningerNuclear_hilbertian_refinement {ι : Type*} (P : SeminormFamily 𝕜 E ι)
    (hP : DeningerIsNuclearSpace P) (i : ι) :
    ∃ (h : Seminorm 𝕜 E) (j : ι) (C : ℝ), 0 ≤ C ∧ DeningerIsHilbertianSeminorm h ∧
      (∀ x, P i x ≤ C * h x) ∧ (∀ x, h x ≤ C * P j x) := by
  obtain ⟨j, D, hD, hnuc⟩ := hP i
  obtain ⟨κ, A, C, hC, hAle, hTle⟩ := hnuc.exists_hilbert_factor
  set B : E →ₗ[𝕜] lp (fun _ : κ => 𝕜) 2 := A ∘ₗ deningerSeminormMk (P j) with hB
  refine ⟨(normSeminorm 𝕜 (lp (fun _ : κ => 𝕜) 2)).comp B, j, C, hC,
    ⟨κ, B, fun _ => rfl⟩, ?_, ?_⟩
  · intro x
    have hval : deningerSeminormComparison hD (deningerSeminormMk (P j) x)
        = deningerSeminormMk (P i) x := rfl
    have h1 : P i x = ‖deningerSeminormComparison hD (deningerSeminormMk (P j) x)‖ := by
      rw [hval]
      exact (deningerSeminormMk_norm (P i) x).symm
    rw [h1]
    exact hTle (deningerSeminormMk (P j) x)
  · intro x
    have h2 : ‖A (deningerSeminormMk (P j) x)‖ ≤ C * ‖deningerSeminormMk (P j) x‖ :=
      hAle (deningerSeminormMk (P j) x)
    rw [deningerSeminormMk_norm (P j) x] at h2
    exact h2

/-- **A nuclear space has a nuclear Hilbertian presentation.**  Choosing a Hilbertian squeeze for
every index gives a family mutually dominating the original one, hence nuclear. -/
theorem deningerNuclear_exists_hilbertian_family {ι : Type*} (P : SeminormFamily 𝕜 E ι)
    (hP : DeningerIsNuclearSpace P) :
    ∃ Q : SeminormFamily 𝕜 E ι, (∀ i, DeningerIsHilbertianSeminorm (Q i)) ∧
      DeningerIsNuclearSpace Q ∧
      (∀ i, ∃ (k : ι) (C : ℝ), ∀ x, P i x ≤ C * Q k x) ∧
      (∀ i, ∃ (k : ι) (C : ℝ), ∀ x, Q i x ≤ C * P k x) := by
  choose Q j C hC hhilb hPQ hQP using fun i => deningerNuclear_hilbertian_refinement P hP i
  refine ⟨Q, hhilb, ?_, ?_, ?_⟩
  · refine deningerIsNuclearSpace_of_dominating P Q ?_ ?_ hP
    · exact fun k => ⟨j k, C k, hQP k⟩
    · exact fun i => ⟨i, C i, hPQ i⟩
  · exact fun i => ⟨i, C i, hPQ i⟩
  · exact fun i => ⟨j i, C i, hQP i⟩

end Hilbertian

end RHTower

