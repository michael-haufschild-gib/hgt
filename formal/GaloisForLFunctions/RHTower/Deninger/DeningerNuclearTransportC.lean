import GaloisForLFunctions.RHTower.Deninger.DeningerNuclearTransport

/-!
# Nuclearity of the completed quotients transports along a linear equivalence

The isometric isomorphism of seminorm quotients induced by a linear equivalence matching two
seminorm families extends to the completions, and the completed comparison maps are conjugate
there as well, because both composites agree on the dense image of the uncompleted quotients.

* `deningerSeminormEquivMapC`, `_coe` : the induced map of completed quotients.
* `deningerSeminormComparisonC_conj` : the completed comparison maps are conjugate.
* `deningerIsNuclearSpaceC_of_linearEquiv` : **completed nuclearity transports.**
-/

namespace RHTower

open UniformSpace ContinuousLinearMap

section TransportC

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

/-- **The map of completed seminorm quotients induced by a linear equivalence.** -/
noncomputable def deningerSeminormEquivMapC {p : Seminorm 𝕜 E} {q : Seminorm 𝕜 F}
    (e : E ≃ₗ[𝕜] F) (h : ∀ x, p x = q (e x)) :
    DeningerSeminormCompletion p →L[𝕜] DeningerSeminormCompletion q :=
  ((Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace q)).comp
    (deningerSeminormEquivMap e h)).extend
      (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p))

omit [CompleteSpace 𝕜] in
theorem deningerSeminormEquivMapC_coe {p : Seminorm 𝕜 E} {q : Seminorm 𝕜 F}
    (e : E ≃ₗ[𝕜] F) (h : ∀ x, p x = q (e x)) (z : DeningerSeminormSpace p) :
    deningerSeminormEquivMapC e h
        (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p) z)
      = Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace q)
        (deningerSeminormEquivMap e h z) :=
  ContinuousLinearMap.extend_eq
    (f := (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace q)).comp
      (deningerSeminormEquivMap e h))
    (e := Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p))
    (deningerDenseRange_toComplL p) (deningerIsUniformInducing_toComplL p) z

omit [CompleteSpace 𝕜] in
/-- **The completed comparison maps of two matched families are conjugate.** -/
theorem deningerSeminormComparisonC_conj {p₁ p₂ : Seminorm 𝕜 E} {q₁ q₂ : Seminorm 𝕜 F} {C : ℝ}
    (e : E ≃ₗ[𝕜] F) (h₁ : ∀ x, p₁ x = q₁ (e x)) (h₂ : ∀ x, p₂ x = q₂ (e x))
    (hp : ∀ x, p₁ x ≤ C * p₂ x) (hq : ∀ y, q₁ y ≤ C * q₂ y) :
    deningerSeminormComparisonC hp
      = (deningerSeminormEquivMapC (p := q₁) (q := p₁) e.symm
          (fun y => by rw [h₁ (e.symm y), LinearEquiv.apply_symm_apply])).comp
        ((deningerSeminormComparisonC hq).comp
          (deningerSeminormEquivMapC (p := p₂) (q := q₂) e h₂)) := by
  refine deningerSeminormComparisonC_ext _ _ fun x => ?_
  show deningerSeminormComparisonC hp
      (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p₂)
        (deningerSeminormMk p₂ x)) = _
  rw [deningerSeminormComparisonC_coe]
  show _ = deningerSeminormEquivMapC (p := q₁) (q := p₁) e.symm _
    (deningerSeminormComparisonC hq (deningerSeminormEquivMapC (p := p₂) (q := q₂) e h₂
      (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p₂)
        (deningerSeminormMk p₂ x))))
  simp only [deningerSeminormEquivMapC_coe, deningerSeminormEquivMap_mk,
    deningerSeminormComparisonC_coe, deningerSeminormComparison_mk,
    LinearEquiv.symm_apply_apply]

omit [CompleteSpace 𝕜] in
/-- **Completed nuclearity transports along a linear equivalence matching the families.** -/
theorem deningerIsNuclearSpaceC_of_linearEquiv {ι : Type*} (P : SeminormFamily 𝕜 E ι)
    (Q : SeminormFamily 𝕜 F ι) (e : E ≃ₗ[𝕜] F) (h : ∀ i x, P i x = Q i (e x))
    (hQ : DeningerIsNuclearSpaceC Q) : DeningerIsNuclearSpaceC P := by
  intro i
  obtain ⟨j, C, hq, hnuc⟩ := hQ i
  have hp : ∀ x, P i x ≤ C * P j x := by
    intro x
    rw [h i x, h j x]
    exact hq (e x)
  refine ⟨j, C, hp, ?_⟩
  have hconj := deningerSeminormComparisonC_conj e (h i) (h j) hp hq
  refine DeningerIsNuclear.of_eq ?_ hconj
  exact (hnuc.compR (deningerSeminormEquivMapC (p := P j) (q := Q j) e (h j))).compL
    (deningerSeminormEquivMapC (p := Q i) (q := P i) e.symm
      (fun y => by rw [h i (e.symm y), LinearEquiv.apply_symm_apply]))

end TransportC

end RHTower
