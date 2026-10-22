import GaloisForLFunctions.RHTower.Deninger.DeningerPoincareOneForm

/-!
# Closed one-forms and their primitives

A differential one-form is the same thing as a family of functionals, and its closedness is the
symmetry of the derivative of that family.  Combined with the Poincaré lemma this says that a closed
holomorphic one-form on a finite-dimensional complex space is the exterior derivative of a
holomorphic function.

* `deningerFormFunctional` : the functional attached to a one-form.
* `deningerSymm_of_closed` : closedness is the symmetry of the derivative.
* `deningerExists_primitive_of_closed` : a closed holomorphic one-form is exact.
-/

namespace RHTower

section Bridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The functional attached to a one-form. -/
noncomputable def deningerFormFunctional (ω : E → E [⋀^Fin 1]→L[ℂ] ℂ) (x : E) : E →L[ℂ] ℂ :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℂ) (E := E) (F := ℂ) (ι := Fin 1)
    (0 : Fin 1)).symm (ω x)

theorem deningerFormFunctional_apply (ω : E → E [⋀^Fin 1]→L[ℂ] ℂ) (x u : E) :
    deningerFormFunctional ω x u = ω x (fun _ => u) := rfl

theorem deningerFormFunctional_analyticAt {ω : E → E [⋀^Fin 1]→L[ℂ] ℂ} {x : E}
    (hana : AnalyticAt ℂ ω x) : AnalyticAt ℂ (deningerFormFunctional ω) x := by
  have hclm := ContinuousLinearMap.analyticAt
    ((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℂ) (E := E) (F := ℂ) (ι := Fin 1)
      (0 : Fin 1)).symm.toContinuousLinearEquiv.toContinuousLinearMap) (ω x)
  exact hclm.comp hana

/-- Differentiating a one-form in a fixed direction is differentiating its functional. -/
theorem deningerFderiv_functional_apply {ω : E → E [⋀^Fin 1]→L[ℂ] ℂ} {x : E}
    (hana : AnalyticAt ℂ ω x) (u v : E) :
    fderiv ℂ (fun y => ω y (fun _ => u)) x v = fderiv ℂ (deningerFormFunctional ω) x v u := by
  have hc : HasFDerivAt (deningerFormFunctional ω)
      (fderiv ℂ (deningerFormFunctional ω) x) x :=
    (deningerFormFunctional_analyticAt hana).differentiableAt.hasFDerivAt
  have h := ((ContinuousLinearMap.apply ℂ ℂ u).hasFDerivAt).comp x hc
  have heq : (fun y : E => ω y (fun _ => u)) =
      ⇑((ContinuousLinearMap.apply ℂ ℂ) u) ∘ deningerFormFunctional ω := rfl
  rw [heq, h.fderiv]
  rfl

/-- **Closedness of a one-form is the symmetry of the derivative of its functional.** -/
theorem deningerSymm_of_closed {ω : E → E [⋀^Fin 1]→L[ℂ] ℂ} {x : E} (hana : AnalyticAt ℂ ω x)
    (hclosed : extDeriv ω x = 0) (u v : E) :
    fderiv ℂ (deningerFormFunctional ω) x u v = fderiv ℂ (deningerFormFunctional ω) x v u := by
  have hdiff : DifferentiableAt ℂ ω x := hana.differentiableAt
  have hval : extDeriv ω x ![u, v] = (0 : ℂ) := by
    rw [hclosed]
    rfl
  rw [extDeriv_apply hdiff ![u, v]] at hval
  have h0 : (Fin.removeNth (0 : Fin 2) ![u, v]) = fun _ : Fin 1 => v := by
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rfl
  have h1 : (Fin.removeNth (1 : Fin 2) ![u, v]) = fun _ : Fin 1 => u := by
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rfl
  rw [Fin.sum_univ_two, h0, h1] at hval
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hval
  rw [deningerFderiv_functional_apply hana v u, deningerFderiv_functional_apply hana u v] at hval
  exact sub_eq_zero.1 hval

end Bridge

section Primitive

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- **A closed holomorphic one-form is exact**: the Poincaré lemma in the language of alternating
forms. -/
theorem deningerExists_primitive_of_closed {ω : E → E [⋀^Fin 1]→L[ℂ] ℂ}
    (hana : AnalyticOnNhd ℂ ω Set.univ) (hclosed : ∀ x, extDeriv ω x = 0) :
    ∃ F : E → ℂ, (∀ x, HasFDerivAt F (deningerFormFunctional ω x) x) ∧
      ∀ x, extDeriv (fun y => ContinuousAlternatingMap.constOfIsEmpty ℂ E (Fin 0) (F y)) x =
        ω x := by
  have hanac : AnalyticOnNhd ℂ (deningerFormFunctional ω) Set.univ := fun x _ =>
    deningerFormFunctional_analyticAt (hana x (Set.mem_univ x))
  have hsymm : ∀ x u v : E, fderiv ℂ (deningerFormFunctional ω) x u v =
      fderiv ℂ (deningerFormFunctional ω) x v u := fun x u v =>
    deningerSymm_of_closed (hana x (Set.mem_univ x)) (hclosed x) u v
  refine ⟨deningerHomotopyPrimitive (deningerFormFunctional ω), fun x =>
    deningerHomotopyPrimitive_hasFDerivAt hanac hsymm x, fun x => ?_⟩
  rw [extDeriv_constOfIsEmpty]
  rw [(deningerHomotopyPrimitive_hasFDerivAt hanac hsymm x).fderiv]
  exact (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℂ) (E := E) (F := ℂ) (ι := Fin 1)
    (0 : Fin 1)).apply_symm_apply (ω x)

end Primitive

end RHTower
