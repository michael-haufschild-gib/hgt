import GaloisForLFunctions.RHTower.Deninger.DeningerHilbertianRefinement

/-!
# Nuclearity of the completed seminorm quotients

The normed quotient attached to a seminorm has a completion, a Banach space, and a comparison of
seminorms extends to a map of the completions.  Nuclearity of a locally convex space is classically
stated for those completed comparison maps, and that statement follows from the one for the
uncompleted quotients, because a nuclear map extends to a nuclear map of completions and the
extension is unique by density.

* `DeningerSeminormCompletion`, `deningerSeminormMkC` : the Banach space of a seminorm.
* `deningerSeminormComparisonC` : the completed comparison map.
* `DeningerIsNuclearSpaceC`, `DeningerIsNuclearSpace.toC` : nuclearity in the completed sense, and
  that it follows from the uncompleted one.
-/

namespace RHTower

open UniformSpace ContinuousLinearMap

section CompletedQuotient

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]

/-- **The Banach space attached to a seminorm**: the completion of its normed quotient. -/
abbrev DeningerSeminormCompletion (p : Seminorm 𝕜 E) : Type _ :=
  Completion (DeningerSeminormSpace p)

/-- The canonical map into the completed seminorm quotient. -/
noncomputable def deningerSeminormMkC (p : Seminorm 𝕜 E) :
    E →ₗ[𝕜] DeningerSeminormCompletion p :=
  (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p)).toLinearMap.comp
    (deningerSeminormMk p)

omit [CompleteSpace 𝕜] in
theorem deningerSeminormMkC_norm (p : Seminorm 𝕜 E) (x : E) :
    ‖deningerSeminormMkC p x‖ = p x := by
  show ‖Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p)
    (deningerSeminormMk p x)‖ = p x
  rw [Completion.coe_toComplL, Completion.norm_coe, deningerSeminormMk_norm]

omit [CompleteSpace 𝕜] in
theorem deningerDenseRange_toComplL (p : Seminorm 𝕜 E) :
    DenseRange (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p)) := by
  rw [Completion.coe_toComplL]
  exact Completion.denseRange_coe

omit [CompleteSpace 𝕜] in
theorem deningerIsUniformInducing_toComplL (p : Seminorm 𝕜 E) :
    IsUniformInducing (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p)) := by
  rw [Completion.coe_toComplL]
  exact Completion.isUniformInducing_coe _

/-- **The completed comparison map** of two seminorms. -/
noncomputable def deningerSeminormComparisonC {p q : Seminorm 𝕜 E} {C : ℝ}
    (h : ∀ x, p x ≤ C * q x) :
    DeningerSeminormCompletion q →L[𝕜] DeningerSeminormCompletion p :=
  ((Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p)).comp
    (deningerSeminormComparison h)).extend
      (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace q))

omit [CompleteSpace 𝕜] in
theorem deningerSeminormComparisonC_coe {p q : Seminorm 𝕜 E} {C : ℝ}
    (h : ∀ x, p x ≤ C * q x) (z : DeningerSeminormSpace q) :
    deningerSeminormComparisonC h
        (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace q) z)
      = Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p)
        (deningerSeminormComparison h z) :=
  ContinuousLinearMap.extend_eq
    (f := (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p)).comp
      (deningerSeminormComparison h))
    (e := Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace q))
    (deningerDenseRange_toComplL q) (deningerIsUniformInducing_toComplL q) z

end CompletedQuotient

section CompletedNuclear

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]

/-- **Nuclearity in the completed sense**: every seminorm is dominated by one whose completed
comparison map is nuclear. -/
def DeningerIsNuclearSpaceC {ι : Type*} (P : SeminormFamily 𝕜 E ι) : Prop :=
  ∀ i : ι, ∃ (j : ι) (C : ℝ) (h : ∀ x, P i x ≤ C * P j x),
    DeningerIsNuclear (deningerSeminormComparisonC h)

/-- **Nuclearity passes to the completed quotients.** -/
theorem DeningerIsNuclearSpace.toC {ι : Type*} (P : SeminormFamily 𝕜 E ι)
    (hP : DeningerIsNuclearSpace P) : DeningerIsNuclearSpaceC P := by
  intro i
  obtain ⟨j, C, h, hnuc⟩ := hP i
  obtain ⟨S, hSnuc, hS⟩ := hnuc.exists_completion
  refine ⟨j, C, h, ?_⟩
  have heq : S = deningerSeminormComparisonC h := by
    refine DFunLike.coe_injective ?_
    refine (deningerDenseRange_toComplL (P j)).equalizer S.continuous
      (deningerSeminormComparisonC h).continuous ?_
    funext z
    show S (Completion.toComplL z) = deningerSeminormComparisonC h (Completion.toComplL z)
    rw [hS z, deningerSeminormComparisonC_coe]
  rwa [heq] at hSnuc

end CompletedNuclear

end RHTower

