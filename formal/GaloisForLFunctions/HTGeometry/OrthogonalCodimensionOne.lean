import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Splitting off one direction inside a closed subspace

Let `A` be a closed subspace of a Hilbert space and `w ∈ A`.  The subspace
`W = A ⊓ (𝕜 ∙ w)ᗮ` is the orthogonal complement of the line `𝕜 ∙ w` *inside* `A`, so `A` splits as
`𝕜 ∙ w ⊕ W`.  Consequently a vector of the ambient space is orthogonal to `W` exactly when its
orthogonal projection onto `A` lies on the line.

Burnol, *Two complete and minimal systems associated with the zeros of the Riemann zeta function*
(arXiv:math/0203120), uses exactly this in the second proof of Prop. 4.5: the extended Sonine space
`L_a` is the perpendicular complement of `(L²(0,a) ∩ 1⊥) + F₊(L²(0,a) ∩ 1⊥)`, and membership in
that complement is precisely the statement that the vector is *constant* on `(0,a)` — i.e. that its
truncation lies on the line spanned by the indicator.

## Main results

* `Submodule.sup_span_singleton_inf_orthogonal` — the splitting `A = 𝕜 ∙ w ⊔ (A ⊓ (𝕜 ∙ w)ᗮ)`.
* `Submodule.mem_orthogonal_inf_orthogonal_span_singleton_iff` — the orthogonality criterion.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Inside a closed subspace `A`, a vector `w ∈ A` splits off an orthogonal line. -/
theorem sup_span_singleton_inf_orthogonal (A : Submodule 𝕜 E) {w : E} (hw : w ∈ A) :
    (𝕜 ∙ w) ⊔ (A ⊓ (𝕜 ∙ w)ᗮ) = A := by
  refine le_antisymm (sup_le ?_ inf_le_left) ?_
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hw
  · intro x hx
    rcases eq_or_ne w 0 with rfl | hw0
    · refine Submodule.mem_sup.2 ⟨0, Submodule.zero_mem _, x, ⟨hx, ?_⟩, by simp⟩
      simp only [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
      simp
    · set c : 𝕜 := ⟪w, x⟫_𝕜 / ((‖w‖ : 𝕜) ^ (2 : ℕ)) with hc
      have hwsq : ((‖w‖ : 𝕜)) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 (by simpa using hw0)
      refine Submodule.mem_sup.2 ⟨c • w, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w),
        x - c • w, ⟨Submodule.sub_mem _ hx (Submodule.smul_mem _ _ hw), ?_⟩, by abel⟩
      simp only [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
      rw [inner_sub_right, inner_smul_right, hc, div_mul_eq_mul_div, inner_self_eq_norm_sq_to_K,
        mul_div_assoc, div_self hwsq, mul_one, sub_self]

/-- A vector is orthogonal to `A ⊓ (𝕜 ∙ w)ᗮ` exactly when its projection to `A` lies on the line
spanned by `w`. -/
theorem mem_orthogonal_inf_orthogonal_span_singleton_iff (A : Submodule 𝕜 E)
    [A.HasOrthogonalProjection] {w : E} (hw : w ∈ A) (f : E) :
    f ∈ (A ⊓ (𝕜 ∙ w)ᗮ)ᗮ ↔ A.starProjection f ∈ (𝕜 ∙ w) := by
  have hproj : ∀ g ∈ A, ⟪g, f⟫_𝕜 = ⟪g, A.starProjection f⟫_𝕜 := by
    intro g hg
    have := A.inner_starProjection_left_eq_right g f
    rwa [Submodule.starProjection_eq_self_iff.2 hg] at this
  constructor
  · intro hf
    rcases eq_or_ne w 0 with rfl | hw0
    · have hA : A ⊓ ((𝕜 ∙ (0 : E))ᗮ) = A := by
        refine le_antisymm inf_le_left (le_inf le_rfl ?_)
        intro x _
        simp only [Submodule.mem_orthogonal_singleton_iff_inner_right]
        simp
      rw [hA] at hf
      have : A.starProjection f = 0 := by
        have h0 : ⟪A.starProjection f, f⟫_𝕜 = 0 :=
          (Submodule.mem_orthogonal _ _).1 hf _ (A.starProjection_apply_mem f)
        rw [hproj _ (A.starProjection_apply_mem f)] at h0
        simpa using inner_self_eq_zero.1 h0
      simp [this]
    · set x : E := A.starProjection f with hx
      set c : 𝕜 := ⟪w, x⟫_𝕜 / ((‖w‖ : 𝕜) ^ (2 : ℕ)) with hc
      have hwsq : ((‖w‖ : 𝕜)) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 (by simpa using hw0)
      have hy : x - c • w ∈ A ⊓ (𝕜 ∙ w)ᗮ := by
        refine ⟨Submodule.sub_mem _ (A.starProjection_apply_mem f) (Submodule.smul_mem _ _ hw), ?_⟩
        simp only [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
        rw [inner_sub_right, inner_smul_right, hc, div_mul_eq_mul_div, inner_self_eq_norm_sq_to_K,
          mul_div_assoc, div_self hwsq, mul_one, sub_self]
      have h0 : ⟪x - c • w, f⟫_𝕜 = 0 := (Submodule.mem_orthogonal _ _).1 hf _ hy
      rw [hproj _ hy.1] at h0
      have hsplit : ⟪x - c • w, x⟫_𝕜 = ⟪x - c • w, x - c • w⟫_𝕜 := by
        have hzero : ⟪x - c • w, c • w⟫_𝕜 = 0 := by
          rw [inner_smul_right]
          have hflip := inner_eq_zero_symm.1
            ((Submodule.mem_orthogonal_singleton_iff_inner_right).1 hy.2)
          rw [hflip, mul_zero]
        have : x = (x - c • w) + c • w := by abel
        nth_rewrite 2 [this]
        rw [inner_add_right, hzero, add_zero]
      rw [hsplit] at h0
      have : x - c • w = 0 := inner_self_eq_zero.1 h0
      have hxc : x = c • w := by
        have := sub_eq_zero.1 this
        exact this
      rw [hxc]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
  · intro hf
    rw [Submodule.mem_orthogonal]
    intro g hg
    rw [hproj g hg.1]
    obtain ⟨c, hcw⟩ := Submodule.mem_span_singleton.1 hf
    rw [← hcw, inner_smul_right]
    have hflip := inner_eq_zero_symm.1
      ((Submodule.mem_orthogonal_singleton_iff_inner_right).1 hg.2)
    rw [hflip, mul_zero]

end GaloisForLFunctions.HTGeometry
