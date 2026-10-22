import GaloisForLFunctions.RHTower.Deninger.DeningerNuclearSpaceInvariance
import GaloisForLFunctions.RHTower.Deninger.DeningerNuclearSpaceCompleted

/-!
# Nuclearity pulls back along a surjection

If `f` is surjective, the seminorm space of `q ∘ f` is isometrically the seminorm space of `q`:
both are quotients of the same normed space, and the comparison maps correspond.  So a nuclear
family pulls back to a nuclear family.

* `deningerCompSeminormEquiv` : `Ê(q ∘ f) ≃ Ê(q)` for surjective `f`.
* `deningerIsNuclearSpace_comp_surjective` : **nuclearity pulls back along a surjection.**
-/

namespace RHTower

open Function UniformSpace

variable {𝕜 E G : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup G] [Module 𝕜 G]

noncomputable section

theorem deningerSeminormKer_comp (q : Seminorm 𝕜 G) (f : E →ₗ[𝕜] G) :
    deningerSeminormKer (q.comp f) = Submodule.comap f (deningerSeminormKer q) := by
  ext x
  simp [deningerSeminormKer, Seminorm.comp_apply]

/-- For a surjective `f`, the seminorm space of `q ∘ f` is the seminorm space of `q`. -/
def deningerCompSeminormEquiv (q : Seminorm 𝕜 G) (f : E →ₗ[𝕜] G) (hf : Surjective f) :
    DeningerSeminormSpace (q.comp f) ≃ₗ[𝕜] DeningerSeminormSpace q :=
  let g : E →ₗ[𝕜] DeningerSeminormSpace q := (deningerSeminormMk q).comp f
  have hgsurj : Surjective g := (deningerSeminormMk_surjective q).comp hf
  have hker : LinearMap.ker g = deningerSeminormKer (q.comp f) := by
    ext x
    constructor
    · intro hx
      have : deningerSeminormMk q (f x) = 0 := hx
      have hnorm : ‖deningerSeminormMk q (f x)‖ = 0 := by rw [this, norm_zero]
      rw [deningerSeminormMk_norm] at hnorm
      simpa [deningerSeminormKer, Seminorm.comp_apply] using hnorm
    · intro hx
      have hq : q (f x) = 0 := by
        simpa [deningerSeminormKer, Seminorm.comp_apply] using hx
      have : ‖deningerSeminormMk q (f x)‖ = 0 := by rw [deningerSeminormMk_norm]; exact hq
      exact norm_eq_zero.1 this
  (Submodule.quotEquivOfEq _ _ hker.symm).trans (g.quotKerEquivOfSurjective hgsurj)

theorem deningerCompSeminormEquiv_mk (q : Seminorm 𝕜 G) (f : E →ₗ[𝕜] G) (hf : Surjective f)
    (x : E) :
    deningerCompSeminormEquiv q f hf (deningerSeminormMk (q.comp f) x)
      = deningerSeminormMk q (f x) := rfl

theorem deningerCompSeminormEquiv_norm (q : Seminorm 𝕜 G) (f : E →ₗ[𝕜] G) (hf : Surjective f)
    (z : DeningerSeminormSpace (q.comp f)) :
    ‖deningerCompSeminormEquiv q f hf z‖ = ‖z‖ := by
  obtain ⟨x, rfl⟩ := deningerSeminormMk_surjective (q.comp f) z
  rw [deningerCompSeminormEquiv_mk, deningerSeminormMk_norm, deningerSeminormMk_norm]
  rfl

/-- The equivalence as a bounded map. -/
def deningerCompSeminormCLM (q : Seminorm 𝕜 G) (f : E →ₗ[𝕜] G) (hf : Surjective f) :
    DeningerSeminormSpace (q.comp f) →L[𝕜] DeningerSeminormSpace q :=
  LinearMap.mkContinuous (deningerCompSeminormEquiv q f hf).toLinearMap 1 fun z => by
    rw [one_mul]
    exact le_of_eq (deningerCompSeminormEquiv_norm q f hf z)

/-- Its inverse as a bounded map. -/
def deningerCompSeminormCLMInv (q : Seminorm 𝕜 G) (f : E →ₗ[𝕜] G) (hf : Surjective f) :
    DeningerSeminormSpace q →L[𝕜] DeningerSeminormSpace (q.comp f) :=
  LinearMap.mkContinuous (deningerCompSeminormEquiv q f hf).symm.toLinearMap 1 fun z => by
    rw [one_mul]
    have := deningerCompSeminormEquiv_norm q f hf ((deningerCompSeminormEquiv q f hf).symm z)
    rw [LinearEquiv.apply_symm_apply] at this
    exact le_of_eq this.symm

/-- The uncompleted comparison map factors through the seminorm space of `q`. -/
theorem deningerSeminormComparison_comp_factor {q q' : Seminorm 𝕜 G} {C : ℝ}
    (hle : ∀ y, q y ≤ C * q' y) (f : E →ₗ[𝕜] G) (hf : Surjective f)
    (z : DeningerSeminormSpace (q'.comp f)) :
    deningerSeminormComparison (p := q.comp f) (q := q'.comp f) (fun x => hle (f x)) z
      = deningerCompSeminormCLMInv q f hf
        (deningerSeminormComparison hle (deningerCompSeminormCLM q' f hf z)) := by
  obtain ⟨x, rfl⟩ := deningerSeminormMk_surjective (q'.comp f) z
  show deningerSeminormMk (q.comp f) x
    = (deningerCompSeminormEquiv q f hf).symm
      (deningerSeminormComparison hle (deningerCompSeminormEquiv q' f hf
        (deningerSeminormMk (q'.comp f) x)))
  rw [deningerCompSeminormEquiv_mk]
  have hcmp : deningerSeminormComparison hle (deningerSeminormMk q' (f x))
      = deningerSeminormMk q (f x) := rfl
  rw [hcmp, ← deningerCompSeminormEquiv_mk q f hf x, LinearEquiv.symm_apply_apply]

/-- **Nuclearity pulls back along a surjection.** -/
theorem deningerIsNuclearSpace_comp_surjective {ι : Type*} (Q : SeminormFamily 𝕜 G ι)
    (f : E →ₗ[𝕜] G) (hf : Surjective f) (hQ : DeningerIsNuclearSpace Q) :
    DeningerIsNuclearSpace (fun i => (Q i).comp f) := by
  intro i
  obtain ⟨j, C, hle, hnuc⟩ := hQ i
  refine ⟨j, C, fun x => hle (f x), ?_⟩
  have hfactor : deningerSeminormComparison (p := (Q i).comp f) (q := (Q j).comp f)
      (fun x => hle (f x))
      = (deningerCompSeminormCLMInv (Q i) f hf).comp
        ((deningerSeminormComparison hle).comp (deningerCompSeminormCLM (Q j) f hf)) := by
    refine ContinuousLinearMap.ext fun z => ?_
    obtain ⟨x, rfl⟩ := deningerSeminormMk_surjective ((Q j).comp f) z
    have hleft : deningerSeminormComparison (p := (Q i).comp f) (q := (Q j).comp f)
        (fun y => hle (f y)) (deningerSeminormMk ((Q j).comp f) x)
        = deningerSeminormMk ((Q i).comp f) x := rfl
    rw [hleft]
    show _ = (deningerCompSeminormEquiv (Q i) f hf).symm
      (deningerSeminormComparison hle (deningerSeminormMk (Q j) (f x)))
    have hcmp : deningerSeminormComparison hle (deningerSeminormMk (Q j) (f x))
        = deningerSeminormMk (Q i) (f x) := rfl
    rw [hcmp, ← deningerCompSeminormEquiv_mk (Q i) f hf x, LinearEquiv.symm_apply_apply]
  rw [hfactor]
  exact ((hnuc.compR _).compL _)

/-! ## The completed version -/

/-- The completed identification `Ê_C(q ∘ f) → Ê_C(q)`. -/
def deningerCompSeminormCLMC (q : Seminorm 𝕜 G) (f : E →ₗ[𝕜] G) (hf : Surjective f) :
    DeningerSeminormCompletion (q.comp f) →L[𝕜] DeningerSeminormCompletion q :=
  ((Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace q)).comp
    (deningerCompSeminormCLM q f hf)).extend
      (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace (q.comp f)))

theorem deningerCompSeminormCLMC_coe (q : Seminorm 𝕜 G) (f : E →ₗ[𝕜] G) (hf : Surjective f)
    (z : DeningerSeminormSpace (q.comp f)) :
    deningerCompSeminormCLMC q f hf
        (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace (q.comp f)) z)
      = Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace q)
        (deningerCompSeminormCLM q f hf z) :=
  ContinuousLinearMap.extend_eq
    (f := (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace q)).comp
      (deningerCompSeminormCLM q f hf))
    (e := Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace (q.comp f)))
    (deningerDenseRange_toComplL (q.comp f)) (deningerIsUniformInducing_toComplL (q.comp f)) z

/-- The completed inverse identification. -/
def deningerCompSeminormCLMInvC (q : Seminorm 𝕜 G) (f : E →ₗ[𝕜] G) (hf : Surjective f) :
    DeningerSeminormCompletion q →L[𝕜] DeningerSeminormCompletion (q.comp f) :=
  ((Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace (q.comp f))).comp
    (deningerCompSeminormCLMInv q f hf)).extend
      (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace q))

theorem deningerCompSeminormCLMInvC_coe (q : Seminorm 𝕜 G) (f : E →ₗ[𝕜] G) (hf : Surjective f)
    (z : DeningerSeminormSpace q) :
    deningerCompSeminormCLMInvC q f hf
        (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace q) z)
      = Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace (q.comp f))
        (deningerCompSeminormCLMInv q f hf z) :=
  ContinuousLinearMap.extend_eq
    (f := (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace (q.comp f))).comp
      (deningerCompSeminormCLMInv q f hf))
    (e := Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace q))
    (deningerDenseRange_toComplL q) (deningerIsUniformInducing_toComplL q) z

/-- **Nuclearity in the completed sense pulls back along a surjection.** -/
theorem deningerIsNuclearSpaceC_comp_surjective {ι : Type*} (Q : SeminormFamily 𝕜 G ι)
    (f : E →ₗ[𝕜] G) (hf : Surjective f) (hQ : DeningerIsNuclearSpaceC Q) :
    DeningerIsNuclearSpaceC (fun i => (Q i).comp f) := by
  intro i
  obtain ⟨j, C, hle, hnuc⟩ := hQ i
  refine ⟨j, C, fun x => hle (f x), ?_⟩
  have hfactor : deningerSeminormComparisonC (p := (Q i).comp f) (q := (Q j).comp f)
      (fun x => hle (f x))
      = (deningerCompSeminormCLMInvC (Q i) f hf).comp
        ((deningerSeminormComparisonC hle).comp (deningerCompSeminormCLMC (Q j) f hf)) := by
    refine DFunLike.coe_injective ?_
    refine (deningerDenseRange_toComplL ((Q j).comp f)).equalizer
      (deningerSeminormComparisonC (p := (Q i).comp f) (q := (Q j).comp f)
        (fun x => hle (f x))).continuous
      ((deningerCompSeminormCLMInvC (Q i) f hf).comp
        ((deningerSeminormComparisonC hle).comp
          (deningerCompSeminormCLMC (Q j) f hf))).continuous ?_
    funext z
    show deningerSeminormComparisonC (p := (Q i).comp f) (q := (Q j).comp f)
        (fun x => hle (f x))
        (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace ((Q j).comp f)) z)
      = deningerCompSeminormCLMInvC (Q i) f hf (deningerSeminormComparisonC hle
          (deningerCompSeminormCLMC (Q j) f hf
            (Completion.toComplL (𝕜 := 𝕜)
              (E := DeningerSeminormSpace ((Q j).comp f)) z)))
    rw [deningerSeminormComparisonC_coe, deningerCompSeminormCLMC_coe,
      deningerSeminormComparisonC_coe, deningerCompSeminormCLMInvC_coe,
      deningerSeminormComparison_comp_factor hle f hf z]
  rw [hfactor]
  exact ((hnuc.compR _).compL _)

end

end RHTower
