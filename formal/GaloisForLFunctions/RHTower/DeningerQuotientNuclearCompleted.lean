import GaloisForLFunctions.RHTower.DeningerQuotientNuclear

/-!
# Quotients of completed-nuclear spaces

The Hilbertian refinement works just as well for the completed formulation of nuclearity: the
factorization of the completed comparison map through `ℓ²` pulls back along the canonical map of a
vector into its completed seminorm quotient, and produces a Hilbertian seminorm squeezed between
the two given ones.

So a completed-nuclear family has a Hilbertian completed-nuclear presentation, and the quotient
permanence proved for Hilbertian families applies to it.  This is the form the Poisson complex
needs, since the radial space is itself a subspace and subspace permanence lands in the completed
formulation.

* `deningerNuclear_hilbertian_refinementC`, `_familyC` : the Hilbertian refinement, completed
  version.
* `deningerIsNuclearSpaceC_quotient_of_C` : **quotients of completed-nuclear spaces are
  completed-nuclear.**
-/

namespace RHTower

open UniformSpace ContinuousLinearMap

section HilbertianRefinementC

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- **Every seminorm of a completed-nuclear space is squeezed by a Hilbertian one.** -/
theorem deningerNuclear_hilbertian_refinementC {ι : Type*} (P : SeminormFamily 𝕜 E ι)
    (hP : DeningerIsNuclearSpaceC P) (i : ι) :
    ∃ (h : Seminorm 𝕜 E) (j : ι) (C : ℝ), 0 ≤ C ∧ DeningerIsHilbertianSeminorm h ∧
      (∀ x, P i x ≤ C * h x) ∧ (∀ x, h x ≤ C * P j x) := by
  obtain ⟨j, D, hD, hnuc⟩ := hP i
  obtain ⟨κ, A, C, hC, hAle, hTle⟩ := hnuc.exists_hilbert_factor
  set ι₀ : E →ₗ[𝕜] DeningerSeminormCompletion (P j) :=
    (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace (P j))).toLinearMap.comp
      (deningerSeminormMk (P j)) with hι₀
  set B : E →ₗ[𝕜] lp (fun _ : κ => 𝕜) 2 := A ∘ₗ ι₀ with hB
  have hnorm : ∀ x : E, ‖ι₀ x‖ = P j x := by
    intro x
    show ‖Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace (P j))
      (deningerSeminormMk (P j) x)‖ = P j x
    rw [Completion.coe_toComplL, Completion.norm_coe, deningerSeminormMk_norm]
  refine ⟨(normSeminorm 𝕜 (lp (fun _ : κ => 𝕜) 2)).comp B, j, C, hC,
    ⟨κ, B, fun _ => rfl⟩, ?_, ?_⟩
  · intro x
    have hval : deningerSeminormComparisonC hD (ι₀ x)
        = Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace (P i))
          (deningerSeminormMk (P i) x) := by
      show deningerSeminormComparisonC hD (Completion.toComplL (𝕜 := 𝕜)
          (E := DeningerSeminormSpace (P j)) (deningerSeminormMk (P j) x)) = _
      rw [deningerSeminormComparisonC_coe]
      rfl
    have h1 : P i x = ‖deningerSeminormComparisonC hD (ι₀ x)‖ := by
      rw [hval, Completion.coe_toComplL, Completion.norm_coe, deningerSeminormMk_norm]
    rw [h1]
    exact hTle (ι₀ x)
  · intro x
    have h2 : ‖A (ι₀ x)‖ ≤ C * ‖ι₀ x‖ := hAle (ι₀ x)
    rw [hnorm x] at h2
    exact h2

/-- **A completed-nuclear space has a Hilbertian completed-nuclear presentation.** -/
theorem deningerNuclear_exists_hilbertian_familyC {ι : Type*} (P : SeminormFamily 𝕜 E ι)
    (hP : DeningerIsNuclearSpaceC P) :
    ∃ Q : SeminormFamily 𝕜 E ι, (∀ i, DeningerIsHilbertianSeminorm (Q i)) ∧
      DeningerIsNuclearSpaceC Q ∧
      (∀ i, ∃ (k : ι) (C : ℝ), ∀ x, P i x ≤ C * Q k x) ∧
      (∀ i, ∃ (k : ι) (C : ℝ), ∀ x, Q i x ≤ C * P k x) := by
  choose Q j C hC hhilb hPQ hQP using fun i => deningerNuclear_hilbertian_refinementC P hP i
  refine ⟨Q, hhilb, ?_, ?_, ?_⟩
  · refine deningerIsNuclearSpaceC_of_dominating P Q ?_ ?_ hP
    · exact fun k => ⟨j k, C k, hQP k⟩
    · exact fun i => ⟨i, C i, hPQ i⟩
  · exact fun i => ⟨i, C i, hPQ i⟩
  · exact fun i => ⟨j i, C i, hQP i⟩

end HilbertianRefinementC

section QuotientPermanenceC

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- **Quotients of completed-nuclear spaces are completed-nuclear.** -/
theorem deningerIsNuclearSpaceC_quotient_of_C {ι : Type*} (P : SeminormFamily 𝕜 E ι)
    (N : Submodule 𝕜 E) (hP : DeningerIsNuclearSpaceC P) :
    DeningerIsNuclearSpaceC (fun i => deningerQuotientSeminorm N (P i)) := by
  obtain ⟨Q, hhilb, hQnuc, hPQ, hQP⟩ := deningerNuclear_exists_hilbertian_familyC P hP
  have hQquot : DeningerIsNuclearSpaceC (fun k => deningerQuotientSeminorm N (Q k)) :=
    deningerIsNuclearSpaceC_quotient_of_hilbertian Q N hQnuc hhilb
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

end QuotientPermanenceC

end RHTower
