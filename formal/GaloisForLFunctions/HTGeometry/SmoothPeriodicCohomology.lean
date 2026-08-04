import GaloisForLFunctions.HTGeometry.PeriodicSmoothness
import GaloisForLFunctions.HTGeometry.PeriodicCohomology

/-!
# The smooth periodic de Rham complex and its cohomology

Averaging over the periods preserves smoothness, so the decomposition of a closed periodic form into
a constant form plus an exact one can be carried out inside the smooth forms: every closed smooth
periodic form is a constant form plus the exterior derivative of a smooth periodic form, and a
constant form with a smooth periodic primitive still vanishes.  Hence the cohomology of the smooth
periodic de Rham complex — the de Rham complex of the torus — is again the space of constant
alternating forms.

* `periodicAveragedData_contDiff` : the averaged form and its primitive are smooth.
* `periodic_closed_eq_const_add_exact_smooth` : the smooth decomposition.
* `smoothPeriodicCohomology`, `smoothPeriodicCohomologyEquiv` : the cohomology of the smooth
  complex is the space of constant alternating forms.
-/

set_option maxSynthPendingDepth 3

namespace GaloisForLFunctions.HTGeometry

open ContinuousAlternatingMap
open scoped ContDiff

section SmoothAveraging

variable {𝕜 : Type u} [RCLike 𝕜] {r n : ℕ}

/-- **Both the averaged form and its primitive are smooth** when the given form is. -/
theorem periodicAveragedData_contDiff {p : 𝕜}
    {β : (Fin r → 𝕜) → (Fin r → 𝕜) [⋀^Fin (n + 1)]→L[𝕜] 𝕜} (hdiff : Differentiable 𝕜 β)
    (hcont' : Continuous (fderiv 𝕜 β))
    (hper : ∀ (l : Fin r) (w : Fin r → 𝕜),
      β (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = β w)
    (hclosed : ∀ w : Fin r → 𝕜, extDeriv β w = 0) (hsm : ContDiff 𝕜 ∞ β) :
    ∀ L : List (Fin r),
      ContDiff 𝕜 ∞ (periodicAveragedData hdiff hcont' hper hclosed L).form ∧
        ContDiff 𝕜 ∞ (periodicAveragedData hdiff hcont' hper hclosed L).prim := by
  intro L
  induction L with
  | nil => exact ⟨hsm, contDiff_const⟩
  | cons j L ih =>
      refine ⟨?_, ?_⟩
      · show ContDiff 𝕜 ∞
          (averageOp p (periodicAveragedData hdiff hcont' hper hclosed L).form j)
        exact averageOp_contDiff_infty j ih.1
      · show ContDiff 𝕜 ∞ (fun w =>
          (periodicAveragedData hdiff hcont' hper hclosed L).prim w +
            weightHomotopy p (fun y => contractCLM (𝕜 := 𝕜)
              (p • (Pi.single j (1 : 𝕜) : Fin r → 𝕜))
              ((periodicAveragedData hdiff hcont' hper hclosed L).form y)) j w)
        refine ih.2.add (weightHomotopy_contDiff_infty j ?_)
        exact (contractCLM (𝕜 := 𝕜) (p • (Pi.single j (1 : 𝕜) : Fin r → 𝕜))).contDiff.comp ih.1

/-- **A closed smooth periodic form is a constant form plus the exterior derivative of a smooth
periodic form.** -/
theorem periodic_closed_eq_const_add_exact_smooth {p : 𝕜} (hp : p ≠ 0)
    {β : (Fin r → 𝕜) → (Fin r → 𝕜) [⋀^Fin (n + 1)]→L[𝕜] 𝕜} (hsm : ContDiff 𝕜 ∞ β)
    (hper : ∀ (l : Fin r) (w : Fin r → 𝕜),
      β (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = β w)
    (hclosed : ∀ w : Fin r → 𝕜, extDeriv β w = 0) :
    ∃ (α : (Fin r → 𝕜) [⋀^Fin (n + 1)]→L[𝕜] 𝕜)
      (η : (Fin r → 𝕜) → (Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜),
      ContDiff 𝕜 ∞ η ∧
      (∀ (l : Fin r) (w : Fin r → 𝕜), η (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = η w) ∧
      ∀ w : Fin r → 𝕜, β w = α + extDeriv η w := by
  classical
  have hdiff : Differentiable 𝕜 β := hsm.differentiable (by simp)
  have hcont' : Continuous (fderiv 𝕜 β) := hsm.continuous_fderiv (by simp)
  set d := periodicAveragedData hdiff hcont' hper hclosed (List.finRange r) with hd
  have hsmooth := periodicAveragedData_contDiff hdiff hcont' hper hclosed hsm (List.finRange r)
  have hinv : ∀ j : Fin r, FlowInvariant p d.form j :=
    fun j => d.invariant j (List.mem_finRange j)
  have hconst : ∀ w : Fin r → 𝕜, d.form w = d.form 0 :=
    fun w => const_of_flowInvariant hp d.diff hinv w 0
  refine ⟨d.form 0, fun w => (-1 : 𝕜) • d.prim w, ?_, ?_, ?_⟩
  · exact hsmooth.2.const_smul (-1 : 𝕜)
  · intro l w
    show (-1 : 𝕜) • d.prim (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = (-1 : 𝕜) • d.prim w
    rw [d.primPeriodic l w]
  · intro w
    show β w = d.form 0 + extDeriv ((-1 : 𝕜) • d.prim) w
    rw [extDeriv_smul, d.primDeriv w, hconst w, negOne_smul_alternating]
    abel

end SmoothAveraging

section SmoothComplex

variable {𝕜 : Type u} [RCLike 𝕜] {r n : ℕ}

/-- **The closed smooth periodic forms of a given degree.** -/
def smoothPeriodicClosedForms (p : 𝕜) (r n : ℕ) : Submodule 𝕜 (PeriodicFormSpace 𝕜 r n) where
  carrier := {u | ContDiff 𝕜 ∞ u ∧
    (∀ (l : Fin r) (w : Fin r → 𝕜), u (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = u w) ∧
    ∀ w : Fin r → 𝕜, extDeriv u w = 0}
  zero_mem' := ⟨contDiff_const, fun _ _ => rfl, fun w => extDeriv_const 0 w⟩
  add_mem' := by
    rintro ω₁ ω₂ ⟨h₁, hp₁, hz₁⟩ ⟨h₂, hp₂, hz₂⟩
    refine ⟨h₁.add h₂, fun l w => ?_, fun w => ?_⟩
    · show ω₁ (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) +
        ω₂ (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = ω₁ w + ω₂ w
      rw [hp₁ l w, hp₂ l w]
    · show extDeriv (fun y => ω₁ y + ω₂ y) w = 0
      rw [extDeriv_fun_add ((h₁.differentiable (by simp)) w) ((h₂.differentiable (by simp)) w),
        hz₁ w, hz₂ w, add_zero]
  smul_mem' := by
    rintro c u ⟨h, hpp, hz⟩
    refine ⟨h.const_smul c, fun l w => ?_, fun w => ?_⟩
    · show c • u (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = c • u w
      rw [hpp l w]
    · show extDeriv (c • u) w = 0
      rw [extDeriv_smul, hz w, smul_zero]

/-- **The exact forms among the closed smooth periodic forms.** -/
def smoothPeriodicExactForms (p : 𝕜) (r n : ℕ) :
    Submodule 𝕜 (smoothPeriodicClosedForms p r (n + 1)) where
  carrier := {u | ∃ θ : PeriodicFormSpace 𝕜 r n, ContDiff 𝕜 ∞ θ ∧
    (∀ (l : Fin r) (w : Fin r → 𝕜), θ (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = θ w) ∧
    ∀ w : Fin r → 𝕜, (u : PeriodicFormSpace 𝕜 r (n + 1)) w = extDeriv θ w}
  zero_mem' := ⟨0, contDiff_const, fun _ _ => rfl, fun w => (extDeriv_const 0 w).symm⟩
  add_mem' := by
    rintro ω₁ ω₂ ⟨θ₁, h₁, hp₁, he₁⟩ ⟨θ₂, h₂, hp₂, he₂⟩
    refine ⟨θ₁ + θ₂, h₁.add h₂, fun l w => ?_, fun w => ?_⟩
    · show θ₁ (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) +
        θ₂ (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = θ₁ w + θ₂ w
      rw [hp₁ l w, hp₂ l w]
    · show (ω₁ : PeriodicFormSpace 𝕜 r (n + 1)) w + (ω₂ : PeriodicFormSpace 𝕜 r (n + 1)) w =
        extDeriv (fun y => θ₁ y + θ₂ y) w
      rw [extDeriv_fun_add ((h₁.differentiable (by simp)) w) ((h₂.differentiable (by simp)) w),
        he₁ w, he₂ w]
  smul_mem' := by
    rintro c u ⟨θ, h, hpp, he⟩
    refine ⟨c • θ, h.const_smul c, fun l w => ?_, fun w => ?_⟩
    · show c • θ (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = c • θ w
      rw [hpp l w]
    · show c • ((u : PeriodicFormSpace 𝕜 r (n + 1)) w) = extDeriv (c • θ) w
      rw [extDeriv_smul, he w]

/-- **The de Rham cohomology of the torus**, computed by smooth periodic forms on the covering
space. -/
abbrev smoothPeriodicCohomology (p : 𝕜) (r n : ℕ) :=
  (↥(smoothPeriodicClosedForms p r (n + 1))) ⧸ (smoothPeriodicExactForms p r n)

/-- A constant form is a closed smooth periodic form. -/
theorem constantForm_mem_smooth (p : 𝕜) (α : (Fin r → 𝕜) [⋀^Fin (n + 1)]→L[𝕜] 𝕜) :
    (fun _ : Fin r → 𝕜 => α) ∈ smoothPeriodicClosedForms p r (n + 1) :=
  ⟨contDiff_const, fun _ _ => rfl, fun w => extDeriv_const α w⟩

/-- **The class of a constant alternating form** in the cohomology of the smooth complex. -/
noncomputable def smoothConstantClass (p : 𝕜) (r n : ℕ) :
    ((Fin r → 𝕜) [⋀^Fin (n + 1)]→L[𝕜] 𝕜) →ₗ[𝕜] smoothPeriodicCohomology p r n where
  toFun α := Submodule.Quotient.mk ⟨fun _ => α, constantForm_mem_smooth p α⟩
  map_add' α β := by
    refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
    funext w
    rfl
  map_smul' c α := by
    refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
    funext w
    rfl

/-- **The cohomology of the smooth periodic de Rham complex is the space of constant alternating
forms**: the inclusion of the translation-invariant forms into the de Rham complex of the torus is a
quasi-isomorphism. -/
noncomputable def smoothPeriodicCohomologyEquiv {p : 𝕜} (hp : p ≠ 0) (r n : ℕ) :
    ((Fin r → 𝕜) [⋀^Fin (n + 1)]→L[𝕜] 𝕜) ≃ₗ[𝕜] smoothPeriodicCohomology p r n := by
  refine LinearEquiv.ofBijective (smoothConstantClass p r n) ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_zero (smoothConstantClass p r n)).2 fun α hα => ?_
    have hexact : (⟨fun _ => α, constantForm_mem_smooth p α⟩ :
        smoothPeriodicClosedForms p r (n + 1)) ∈ smoothPeriodicExactForms p r n := by
      rwa [← Submodule.Quotient.mk_eq_zero]
    obtain ⟨θ, hθ, hθp, hθeq⟩ := hexact
    exact periodic_const_add_exact_unique (α' := 0) hp (hθ.differentiable (by simp))
      (hθ.continuous_fderiv (by simp)) hθp fun w => by rw [zero_add]; exact hθeq w
  · intro ξ
    refine Quotient.inductionOn' ξ fun u => ?_
    obtain ⟨hsm, hper, hclosed⟩ := u.2
    obtain ⟨α, η, hηsm, hηper, hdecomp⟩ :=
      periodic_closed_eq_const_add_exact_smooth hp hsm hper hclosed
    refine ⟨α, ?_⟩
    refine (Submodule.Quotient.eq _).2 ?_
    refine ⟨fun y => -η y, ?_, fun l w => ?_, fun w => ?_⟩
    · have hfun : (fun y : Fin r → 𝕜 => -η y) = (-1 : 𝕜) • η := by
        funext y
        rw [Pi.smul_apply, negOne_smul_alternating]
      rw [hfun]
      exact hηsm.const_smul (-1 : 𝕜)
    · show -η (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = -η w
      rw [hηper l w]
    · show α - (u : PeriodicFormSpace 𝕜 r (n + 1)) w = extDeriv (fun y => -η y) w
      have hneg : extDeriv (fun y => -η y) w = -extDeriv η w := by
        have hfun : (fun y : Fin r → 𝕜 => -η y) = (-1 : 𝕜) • η := by
          funext y
          rw [Pi.smul_apply, negOne_smul_alternating]
        rw [hfun, extDeriv_smul, negOne_smul_alternating]
      rw [hneg, hdecomp w]
      abel

end SmoothComplex

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open ContinuousAlternatingMap
open scoped ContDiff

section Complex

variable {𝕜 : Type u} [RCLike 𝕜] {r n : ℕ}

/-- The derivative of a periodic map is periodic. -/
theorem fderiv_periodic {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {u : (Fin r → 𝕜) → X} (hd : Differentiable 𝕜 u) {c : Fin r → 𝕜}
    (hper : ∀ w, u (w + c) = u w) (w : Fin r → 𝕜) : fderiv 𝕜 u (w + c) = fderiv 𝕜 u w := by
  have hshift : HasFDerivAt (fun y => u (y + c)) (fderiv 𝕜 u (w + c)) w := by
    have h := ((hd (w + c)).hasFDerivAt).comp w ((hasFDerivAt_id w).add_const c)
    rwa [ContinuousLinearMap.comp_id] at h
  rw [show (fun y => u (y + c)) = u from funext hper] at hshift
  exact hshift.fderiv.symm

/-- **The smooth periodic forms of a given degree**: the forms on the torus. -/
def smoothPeriodicForms (p : 𝕜) (r n : ℕ) : Submodule 𝕜 (PeriodicFormSpace 𝕜 r n) where
  carrier := {v | ContDiff 𝕜 ∞ v ∧
    ∀ (l : Fin r) (w : Fin r → 𝕜), v (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = v w}
  zero_mem' := ⟨contDiff_const, fun _ _ => rfl⟩
  add_mem' := by
    rintro v₁ v₂ ⟨h₁, hp₁⟩ ⟨h₂, hp₂⟩
    refine ⟨h₁.add h₂, fun l w => ?_⟩
    show v₁ (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) +
      v₂ (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = v₁ w + v₂ w
    rw [hp₁ l w, hp₂ l w]
  smul_mem' := by
    rintro c v ⟨h, hpp⟩
    refine ⟨h.const_smul c, fun l w => ?_⟩
    show c • v (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = c • v w
    rw [hpp l w]

/-- The exterior derivative of a smooth periodic form is a smooth periodic form. -/
theorem extDeriv_mem_smoothPeriodicForms {p : 𝕜} {v : PeriodicFormSpace 𝕜 r n}
    (hv : v ∈ smoothPeriodicForms p r n) : extDeriv v ∈ smoothPeriodicForms p r (n + 1) := by
  obtain ⟨hsm, hper⟩ := hv
  have hfd : ContDiff 𝕜 ∞ (fderiv 𝕜 v) := (contDiff_infty_iff_fderiv.1 hsm).2
  refine ⟨?_, fun l w => ?_⟩
  · have hfun : extDeriv v =
        fun x => (alternatizeUncurryFinCLM 𝕜 (Fin r → 𝕜) 𝕜 (n := n)) (fderiv 𝕜 v x) := rfl
    rw [hfun]
    exact (alternatizeUncurryFinCLM 𝕜 (Fin r → 𝕜) 𝕜 (n := n)).contDiff.comp hfd
  · show alternatizeUncurryFin (fderiv 𝕜 v (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜))) =
      alternatizeUncurryFin (fderiv 𝕜 v w)
    rw [fderiv_periodic (hsm.differentiable (by simp)) (hper l) w]

/-- **The differential of the de Rham complex of the torus.** -/
noncomputable def smoothExtDerivMap (p : 𝕜) (r n : ℕ) :
    smoothPeriodicForms p r n →ₗ[𝕜] smoothPeriodicForms p r (n + 1) where
  toFun v := ⟨extDeriv (v : PeriodicFormSpace 𝕜 r n), extDeriv_mem_smoothPeriodicForms v.2⟩
  map_add' v₁ v₂ := by
    refine Subtype.ext ?_
    funext w
    exact extDeriv_fun_add ((v₁.2.1.differentiable (by simp)) w)
      ((v₂.2.1.differentiable (by simp)) w)
  map_smul' c v := by
    refine Subtype.ext ?_
    funext w
    exact extDeriv_smul c _

/-- **The differential squares to zero**, so the smooth periodic forms are a cochain complex. -/
theorem smoothExtDerivMap_comp (p : 𝕜) (r n : ℕ) :
    (smoothExtDerivMap p r (n + 1)).comp (smoothExtDerivMap p r n) = 0 := by
  refine LinearMap.ext fun v => ?_
  refine Subtype.ext ?_
  show extDeriv (extDeriv (v : PeriodicFormSpace 𝕜 r n)) = 0
  exact extDeriv_extDeriv (r := ∞) v.2.1
    (by simp only [minSmoothness_of_isRCLikeNormedField]; decide)

/-- The kernel of the differential is the closed smooth periodic forms. -/
theorem mem_ker_smoothExtDerivMap {p : 𝕜} (v : smoothPeriodicForms p r n) :
    v ∈ LinearMap.ker (smoothExtDerivMap p r n) ↔
      (v : PeriodicFormSpace 𝕜 r n) ∈ smoothPeriodicClosedForms p r n := by
  constructor
  · intro hv
    refine ⟨v.2.1, v.2.2, fun w => ?_⟩
    have h := congrArg (fun z : smoothPeriodicForms p r (n + 1) =>
      (z : PeriodicFormSpace 𝕜 r (n + 1)) w) hv
    exact h
  · rintro ⟨-, -, hz⟩
    refine Subtype.ext ?_
    funext w
    exact hz w

/-- The image of the differential is the exact smooth periodic forms. -/
theorem mem_range_smoothExtDerivMap {p : 𝕜} (v : smoothPeriodicForms p r (n + 1)) :
    v ∈ LinearMap.range (smoothExtDerivMap p r n) ↔
      ∃ θ : PeriodicFormSpace 𝕜 r n, ContDiff 𝕜 ∞ θ ∧
        (∀ (l : Fin r) (w : Fin r → 𝕜),
          θ (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = θ w) ∧
        ∀ w : Fin r → 𝕜, (v : PeriodicFormSpace 𝕜 r (n + 1)) w = extDeriv θ w := by
  constructor
  · rintro ⟨θ, rfl⟩
    exact ⟨(θ : PeriodicFormSpace 𝕜 r n), θ.2.1, θ.2.2, fun w => rfl⟩
  · rintro ⟨θ, hsm, hper, heq⟩
    refine ⟨⟨θ, hsm, hper⟩, ?_⟩
    refine Subtype.ext ?_
    funext w
    exact (heq w).symm

end Complex

end GaloisForLFunctions.HTGeometry
