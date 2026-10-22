import GaloisForLFunctions.RHTower.Deninger.DeningerHolomorphicDescent

/-!
# The cohomology of a character stage as a module

The closed holomorphic forms of a given degree on a character stage form a module, the ones that are
exterior derivatives of holomorphic forms form a submodule, and the quotient is the holomorphic de
Rham cohomology of the stage.  Sending a constant alternating form to the class of the stage form it
defines is an isomorphism onto that quotient: it is surjective because every closed holomorphic form
is a constant form plus an exact one, and injective because a constant form that is exact vanishes.

* `deningerClosedForms`, `deningerExactForms`, `deningerCohomology` : the cohomology module.
* `deningerCohomologyEquiv` : the cohomology of a stage is the space of constant alternating forms.
-/

set_option maxSynthPendingDepth 3

namespace RHTower

open Complex

section ClosedForms

variable {r n : ℕ}

/-- A constant stage form is closed. -/
theorem deningerConstantStageForm_closed (α : (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ) {z : Fin r → ℂ}
    (hz : z ∈ deningerStageTorus r) : extDeriv (deningerConstantStageForm α) z = 0 := by
  refine deningerExpPullback_injective (B := (0 : DeningerStageForm r (n + 1))) (fun w => ?_) hz
  have hpull : deningerExpPullbackForm (deningerConstantStageForm α) = fun _ => α := by
    funext y
    exact deningerConstantStageForm_pullback α y
  have hzero : deningerPullbackForm (deningerExpMap r) (0 : DeningerStageForm r (n + 1)) w = 0 := by
    ext v
    rfl
  rw [hzero]
  show deningerPullbackForm (deningerExpMap r) (extDeriv (deningerConstantStageForm α)) w = 0
  rw [← deningerPullbackForm_extDeriv
    ((deningerConstantStageForm_holomorphic α _ (deningerExpMap_mem w)).differentiableAt)
    (deningerExpMap_analyticAt w).contDiffAt]
  show extDeriv (deningerExpPullbackForm (deningerConstantStageForm α)) w = 0
  rw [hpull]
  exact deningerExtDeriv_const α w

/-- **The closed holomorphic forms of a given degree on a character stage.** -/
def deningerClosedForms (r n : ℕ) : Submodule ℂ (DeningerStageForm r n) where
  carrier := {ω | DeningerIsHolomorphicForm ω ∧ ∀ z ∈ deningerStageTorus r, extDeriv ω z = 0}
  zero_mem' := by
    refine ⟨fun z _ => analyticAt_const, fun z _ => ?_⟩
    exact deningerExtDeriv_const (0 : (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ) z
  add_mem' := by
    rintro ω₁ ω₂ ⟨h₁, hc₁⟩ ⟨h₂, hc₂⟩
    refine ⟨fun z hz => (h₁ z hz).add (h₂ z hz), fun z hz => ?_⟩
    show extDeriv (fun y => ω₁ y + ω₂ y) z = 0
    rw [extDeriv_fun_add (h₁ z hz).differentiableAt (h₂ z hz).differentiableAt, hc₁ z hz,
      hc₂ z hz, add_zero]
  smul_mem' := by
    rintro c ω ⟨h, hc⟩
    refine ⟨fun z hz => AnalyticAt.const_smul (h z hz), fun z hz => ?_⟩
    show extDeriv (c • ω) z = 0
    rw [extDeriv_smul, hc z hz, smul_zero]

theorem deningerMem_closedForms {ω : DeningerStageForm r n} :
    ω ∈ deningerClosedForms r n ↔
      DeningerIsHolomorphicForm ω ∧ ∀ z ∈ deningerStageTorus r, extDeriv ω z = 0 :=
  Iff.rfl

/-- **The exact forms among the closed holomorphic forms.** -/
def deningerExactForms (r n : ℕ) : Submodule ℂ (deningerClosedForms r (n + 1)) where
  carrier := {ω | ∃ θ : DeningerStageForm r n, DeningerIsHolomorphicForm θ ∧
    ∀ z ∈ deningerStageTorus r, (ω : DeningerStageForm r (n + 1)) z = extDeriv θ z}
  zero_mem' := by
    refine ⟨0, fun z _ => analyticAt_const, fun z _ => ?_⟩
    show (0 : (Fin r → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ) = extDeriv (0 : DeningerStageForm r n) z
    exact (deningerExtDeriv_const (0 : (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ) z).symm
  add_mem' := by
    rintro ω₁ ω₂ ⟨θ₁, hθ₁, h₁⟩ ⟨θ₂, hθ₂, h₂⟩
    refine ⟨θ₁ + θ₂, fun z hz => (hθ₁ z hz).add (hθ₂ z hz), fun z hz => ?_⟩
    show (ω₁ : DeningerStageForm r (n + 1)) z + (ω₂ : DeningerStageForm r (n + 1)) z =
      extDeriv (fun y => θ₁ y + θ₂ y) z
    rw [extDeriv_fun_add (hθ₁ z hz).differentiableAt (hθ₂ z hz).differentiableAt, h₁ z hz,
      h₂ z hz]
  smul_mem' := by
    rintro c ω ⟨θ, hθ, h⟩
    refine ⟨c • θ, fun z hz => AnalyticAt.const_smul (hθ z hz), fun z hz => ?_⟩
    show c • ((ω : DeningerStageForm r (n + 1)) z) = extDeriv (c • θ) z
    rw [extDeriv_smul, h z hz]

/-- **The holomorphic de Rham cohomology of a character stage.** -/
abbrev deningerCohomology (r n : ℕ) :=
  (↥(deningerClosedForms r (n + 1))) ⧸ (deningerExactForms r n)

end ClosedForms

end RHTower

namespace RHTower

open Complex

section CohomologyEquiv

variable {r n : ℕ}

/-- A constant stage form is a closed holomorphic form. -/
theorem deningerConstantStageForm_mem (α : (Fin r → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ) :
    deningerConstantStageForm α ∈ deningerClosedForms r (n + 1) :=
  ⟨deningerConstantStageForm_holomorphic α, fun _ hz => deningerConstantStageForm_closed α hz⟩

/-- **The class of the constant stage form of an alternating form.** -/
noncomputable def deningerConstantClass (r n : ℕ) :
    ((Fin r → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ) →ₗ[ℂ] deningerCohomology r n where
  toFun α := Submodule.Quotient.mk ⟨deningerConstantStageForm α, deningerConstantStageForm_mem α⟩
  map_add' α β := by
    refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
    funext z
    exact deningerConstantStageForm_add α β z
  map_smul' c α := by
    refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
    funext z
    exact deningerConstantStageForm_smul c α z

/-- **The cohomology of a character stage is the space of constant alternating forms.**  Every class
contains exactly one constant form: one by the decomposition of a closed holomorphic form, at most
one because a constant form that is the exterior derivative of a holomorphic form vanishes. -/
noncomputable def deningerCohomologyEquiv (r n : ℕ) :
    ((Fin r → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ) ≃ₗ[ℂ] deningerCohomology r n := by
  refine LinearEquiv.ofBijective (deningerConstantClass r n) ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_zero (deningerConstantClass r n)).2 fun α hα => ?_
    have hexact : (⟨deningerConstantStageForm α, deningerConstantStageForm_mem α⟩ :
        deningerClosedForms r (n + 1)) ∈ deningerExactForms r n := by
      rwa [← Submodule.Quotient.mk_eq_zero]
    obtain ⟨θ, hθ, hθeq⟩ := hexact
    refine deningerConstantStageForm_unique (α := α) (α' := 0) hθ fun z hz => ?_
    rw [deningerConstantStageForm_zero, zero_add]
    exact hθeq z hz
  · intro ξ
    refine Quotient.inductionOn' ξ fun ω => ?_
    obtain ⟨α, θ, hθ, hdecomp⟩ :=
      deningerStage_closed_form_decomposition_hol ω.2.1 ω.2.2
    refine ⟨α, ?_⟩
    refine (Submodule.Quotient.eq _).2 ?_
    refine ⟨fun y => -θ y, fun z hz => (hθ z hz).neg, fun z hz => ?_⟩
    show deningerConstantStageForm α z - (ω : DeningerStageForm r (n + 1)) z =
      extDeriv (fun y => -θ y) z
    have hneg : extDeriv (fun y => -θ y) z = -extDeriv θ z := by
      have hfun : (fun y : Fin r → ℂ => -θ y) = (-1 : ℂ) • θ := by
        funext y
        rw [Pi.smul_apply, deningerNegOneSmul]
      rw [hfun, extDeriv_smul, deningerNegOneSmul]
    rw [hneg, hdecomp z hz]
    abel

end CohomologyEquiv

end RHTower
