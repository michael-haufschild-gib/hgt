import GaloisForLFunctions.RHTower.DeningerNuclearCompletedInvariance

/-!
# Nuclearity transports along a linear equivalence of seminormed spaces

A linear equivalence matching two seminorm families carries the kernel of one seminorm onto the
kernel of the other, so it induces an isometric isomorphism of the seminorm quotients, and the
comparison maps of the two families are conjugate.  Nuclearity, being invariant under composition
with bounded maps, therefore transports.

This is what identifies a space of functions with a space of coefficient sequences: nuclearity of
the sequence model is nuclearity of the function space.

* `deningerSeminormEquivMap`, `_mk`, `_norm_le` : the induced map of seminorm quotients.
* `deningerSeminormComparison_conj` : the comparison maps are conjugate.
* `deningerIsNuclearSpace_of_linearEquiv` : **nuclearity transports.**
-/

namespace RHTower

section Transport

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [AddCommGroup F] [Module 𝕜 F]

/-- **The map of seminorm quotients induced by a linear equivalence matching the seminorms.** -/
noncomputable def deningerSeminormEquivMap {p : Seminorm 𝕜 E} {q : Seminorm 𝕜 F}
    (e : E ≃ₗ[𝕜] F) (h : ∀ x, p x = q (e x)) :
    DeningerSeminormSpace p →L[𝕜] DeningerSeminormSpace q :=
  LinearMap.mkContinuous
    (Submodule.liftQ (deningerSeminormKer p)
      ((deningerSeminormMk q).comp (e : E →ₗ[𝕜] F)) (by
        intro x hx
        have hp : p x = 0 := hx
        have hq : q (e x) = 0 := by rw [← h x, hp]
        have hnorm : ‖deningerSeminormMk q (e x)‖ = 0 := by
          rw [deningerSeminormMk_norm, hq]
        exact norm_eq_zero.mp hnorm))
    1 (by
      rintro ⟨a⟩
      show ‖deningerSeminormMk q (e a)‖ ≤ 1 * ‖deningerSeminormMk p a‖
      rw [one_mul, deningerSeminormMk_norm, deningerSeminormMk_norm, h a])

@[simp]
theorem deningerSeminormEquivMap_mk {p : Seminorm 𝕜 E} {q : Seminorm 𝕜 F}
    (e : E ≃ₗ[𝕜] F) (h : ∀ x, p x = q (e x)) (x : E) :
    deningerSeminormEquivMap e h (deningerSeminormMk p x) = deningerSeminormMk q (e x) := rfl

/-- **The comparison maps of two matched families are conjugate.** -/
theorem deningerSeminormComparison_conj {p₁ p₂ : Seminorm 𝕜 E} {q₁ q₂ : Seminorm 𝕜 F} {C : ℝ}
    (e : E ≃ₗ[𝕜] F) (h₁ : ∀ x, p₁ x = q₁ (e x)) (h₂ : ∀ x, p₂ x = q₂ (e x))
    (hp : ∀ x, p₁ x ≤ C * p₂ x) (hq : ∀ y, q₁ y ≤ C * q₂ y) :
    deningerSeminormComparison hp
      = (deningerSeminormEquivMap (p := q₁) (q := p₁) e.symm
          (fun y => by rw [h₁ (e.symm y), LinearEquiv.apply_symm_apply])).comp
        ((deningerSeminormComparison hq).comp
          (deningerSeminormEquivMap (p := p₂) (q := q₂) e h₂)) := by
  refine deningerSeminormComparison_ext _ _ fun x => ?_
  simp only [ContinuousLinearMap.comp_apply, deningerSeminormEquivMap_mk,
    deningerSeminormComparison_mk, LinearEquiv.symm_apply_apply]

/-- **Nuclearity transports along a linear equivalence matching the seminorm families.** -/
theorem deningerIsNuclearSpace_of_linearEquiv {ι : Type*} (P : SeminormFamily 𝕜 E ι)
    (Q : SeminormFamily 𝕜 F ι) (e : E ≃ₗ[𝕜] F) (h : ∀ i x, P i x = Q i (e x))
    (hQ : DeningerIsNuclearSpace Q) : DeningerIsNuclearSpace P := by
  intro i
  obtain ⟨j, C, hq, hnuc⟩ := hQ i
  have hp : ∀ x, P i x ≤ C * P j x := by
    intro x
    rw [h i x, h j x]
    exact hq (e x)
  refine ⟨j, C, hp, ?_⟩
  have hconj := deningerSeminormComparison_conj e (h i) (h j) hp hq
  refine DeningerIsNuclear.of_eq ?_ hconj
  exact (hnuc.compR (deningerSeminormEquivMap (p := P j) (q := Q j) e (h j))).compL
    (deningerSeminormEquivMap (p := Q i) (q := P i) e.symm
      (fun y => by rw [h i (e.symm y), LinearEquiv.apply_symm_apply]))

end Transport

end RHTower
