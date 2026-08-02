import GaloisForLFunctions.RHTower.DeningerNuclearSubspaceHilbertian

/-!
# Completed nuclearity is independent of the seminorm family, and passes to subspaces

A map out of a completed seminorm quotient is determined by its values on the dense image of the
vectors of the space, so the completed comparison maps obey the same calculus as the uncompleted
ones: the constant is irrelevant and a chain of dominations composes.  Completed nuclearity is
therefore an invariant of the topology rather than of the chosen family.

Every nuclear space admits a Hilbertian presentation, and for a Hilbertian presentation the
completed subspace quotients are complemented, so nuclearity passes to subspaces of any nuclear
space, with no hypothesis on the given family.

* `deningerSeminormComparisonC_ext`, `_congr`, `_trans` : the calculus of completed comparisons.
* `deningerIsNuclearSpaceC_of_dominating`, `_comp` : invariance under change of family.
* `deningerIsNuclearSpaceC_subspace` : **subspaces of a nuclear space are nuclear.**
-/

namespace RHTower

open UniformSpace ContinuousLinearMap

section CompletedComparison

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]

omit [CompleteSpace 𝕜] in
/-- **A map out of a completed seminorm quotient is determined on classes of vectors**, these
being dense in the completion. -/
theorem deningerSeminormComparisonC_ext {p q : Seminorm 𝕜 E}
    (f g : DeningerSeminormCompletion q →L[𝕜] DeningerSeminormCompletion p)
    (h : ∀ x : E, f (deningerSeminormMkC q x) = g (deningerSeminormMkC q x)) : f = g := by
  refine DFunLike.coe_injective ?_
  refine (deningerDenseRange_toComplL q).equalizer f.continuous g.continuous ?_
  funext z
  obtain ⟨x, rfl⟩ := deningerSeminormMk_surjective q z
  exact h x

omit [CompleteSpace 𝕜] in
/-- **The completed comparison map does not depend on the constant.** -/
theorem deningerSeminormComparisonC_congr {p q : Seminorm 𝕜 E} {C C' : ℝ}
    (h : ∀ x, p x ≤ C * q x) (h' : ∀ x, p x ≤ C' * q x) :
    deningerSeminormComparisonC h = deningerSeminormComparisonC h' := by
  refine deningerSeminormComparisonC_ext _ _ fun x => ?_
  show deningerSeminormComparisonC h
      (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace q) (deningerSeminormMk q x))
    = deningerSeminormComparisonC h'
      (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace q) (deningerSeminormMk q x))
  rw [deningerSeminormComparisonC_coe, deningerSeminormComparisonC_coe]
  rfl

omit [CompleteSpace 𝕜] in
/-- **A chain of dominations composes at the completed level.** -/
theorem deningerSeminormComparisonC_trans {p q r : Seminorm 𝕜 E} {C C' D : ℝ}
    (h₁ : ∀ x, p x ≤ C * q x) (h₂ : ∀ x, q x ≤ C' * r x) (h₃ : ∀ x, p x ≤ D * r x) :
    deningerSeminormComparisonC h₃
      = (deningerSeminormComparisonC h₁).comp (deningerSeminormComparisonC h₂) := by
  refine deningerSeminormComparisonC_ext _ _ fun x => ?_
  show deningerSeminormComparisonC h₃
      (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace r) (deningerSeminormMk r x))
    = deningerSeminormComparisonC h₁ (deningerSeminormComparisonC h₂
      (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace r) (deningerSeminormMk r x)))
  rw [deningerSeminormComparisonC_coe, deningerSeminormComparisonC_coe,
    deningerSeminormComparisonC_coe]
  rfl

end CompletedComparison

section CompletedInvariance

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]

omit [CompleteSpace 𝕜] in
/-- **Completed nuclearity transfers between mutually dominating seminorm families.**  A
comparison map of the second family factors through a nuclear comparison map of the first. -/
theorem deningerIsNuclearSpaceC_of_dominating {ι κ : Type*} (P : SeminormFamily 𝕜 E ι)
    (Q : SeminormFamily 𝕜 E κ)
    (hPQ : ∀ k, ∃ (i : ι) (C : ℝ), ∀ x, Q k x ≤ C * P i x)
    (hQP : ∀ i, ∃ (k : κ) (C : ℝ), ∀ x, P i x ≤ C * Q k x)
    (hP : DeningerIsNuclearSpaceC P) : DeningerIsNuclearSpaceC Q := by
  intro k
  obtain ⟨i, C₁, h₁⟩ := hPQ k
  obtain ⟨i', C, h₂, hnuc⟩ := hP i
  obtain ⟨j, C₂, h₃⟩ := hQP i'
  have h₁' : ∀ x, Q k x ≤ |C₁| * P i x := deningerSeminorm_le_abs h₁
  have h₂' : ∀ x, P i x ≤ |C| * P i' x := deningerSeminorm_le_abs h₂
  have h₃' : ∀ x, P i' x ≤ |C₂| * Q j x := deningerSeminorm_le_abs h₃
  have hchain : ∀ x, Q k x ≤ (|C₁| * |C| * |C₂|) * Q j x := by
    intro x
    calc Q k x ≤ |C₁| * P i x := h₁' x
      _ ≤ |C₁| * (|C| * P i' x) := mul_le_mul_of_nonneg_left (h₂' x) (abs_nonneg C₁)
      _ ≤ |C₁| * (|C| * (|C₂| * Q j x)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (h₃' x) (abs_nonneg C)) (abs_nonneg C₁)
      _ = (|C₁| * |C| * |C₂|) * Q j x := by ring
  refine ⟨j, |C₁| * |C| * |C₂|, hchain, ?_⟩
  have hcomp : DeningerIsNuclear
      ((deningerSeminormComparisonC h₁').comp
        ((deningerSeminormComparisonC h₂).comp (deningerSeminormComparisonC h₃'))) :=
    ((hnuc.compR (deningerSeminormComparisonC h₃')).compL (deningerSeminormComparisonC h₁'))
  refine hcomp.of_eq ?_
  refine deningerSeminormComparisonC_ext _ _ fun x => ?_
  show deningerSeminormComparisonC hchain (Completion.toComplL (𝕜 := 𝕜)
      (E := DeningerSeminormSpace (Q j)) (deningerSeminormMk (Q j) x))
    = deningerSeminormComparisonC h₁' (deningerSeminormComparisonC h₂
      (deningerSeminormComparisonC h₃' (Completion.toComplL (𝕜 := 𝕜)
        (E := DeningerSeminormSpace (Q j)) (deningerSeminormMk (Q j) x))))
  rw [deningerSeminormComparisonC_coe, deningerSeminormComparisonC_coe,
    deningerSeminormComparisonC_coe, deningerSeminormComparisonC_coe]
  rfl

omit [CompleteSpace 𝕜] in
/-- **Completed nuclearity may be tested on a cofinal subfamily.** -/
theorem deningerIsNuclearSpaceC_comp {ι κ : Type*} (P : SeminormFamily 𝕜 E ι) (f : κ → ι)
    (hcof : ∀ i, ∃ (k : κ) (C : ℝ), ∀ x, P i x ≤ C * P (f k) x)
    (hP : DeningerIsNuclearSpaceC P) : DeningerIsNuclearSpaceC (fun k => P (f k)) := by
  refine deningerIsNuclearSpaceC_of_dominating P (fun k => P (f k)) ?_ ?_ hP
  · exact fun k => ⟨f k, 1, fun x => by rw [one_mul]⟩
  · exact hcof

end CompletedInvariance

section SubspacePermanence

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- **Permanence of nuclearity under subspaces.**  Every nuclear space has a Hilbertian
presentation, for which the completed subspace quotients embed as closed, hence complemented,
subspaces of an `ℓ²` space; nuclearity of the restricted Hilbertian family then transfers to the
restriction of the given family, the two restrictions dominating each other. -/
theorem deningerIsNuclearSpaceC_subspace {ι : Type*} (P : SeminormFamily 𝕜 E ι)
    (F : Submodule 𝕜 E) (hP : DeningerIsNuclearSpace P) :
    DeningerIsNuclearSpaceC (fun i => deningerRestrictSeminorm F (P i)) := by
  obtain ⟨Q, hhilb, hQnuc, hPQ, hQP⟩ := deningerNuclear_exists_hilbertian_family P hP
  have hQres : DeningerIsNuclearSpaceC (fun i => deningerRestrictSeminorm F (Q i)) :=
    deningerIsNuclearSpace_subspace_of_hilbertian Q F hQnuc hhilb
  refine deningerIsNuclearSpaceC_of_dominating (fun i => deningerRestrictSeminorm F (Q i))
    (fun i => deningerRestrictSeminorm F (P i)) ?_ ?_ hQres
  · intro k
    obtain ⟨i, C, hC⟩ := hPQ k
    exact ⟨i, C, fun v => hC (v : E)⟩
  · intro i
    obtain ⟨k, C, hC⟩ := hQP i
    exact ⟨k, C, fun v => hC (v : E)⟩

end SubspacePermanence

end RHTower
