import Mathlib

/-!
# Relative-law observer-descent duality

Over a field, the observers on source cohomology modulo those that factor through resolved
cohomology are canonically the dual of the kernel of the comparison map.  The relative-law space of
a mapping cone — cone cohomology modulo the image of the resolved complex — is canonically that
same kernel.  Hence observers that fail to descend and laws created by exactification are dual, and
an observer descends exactly when it annihilates every relative law.
-/

namespace HTGeometry.ConstraintRelativity

open LinearMap

/-! ## The observer-descent quotient -/

section ObserverDescent

variable {k HC HX V : Type*} [Field k]
  [AddCommGroup HC] [Module k HC] [AddCommGroup HX] [Module k HX]
  [AddCommGroup V] [Module k V]

/-- **Card `(ROD.3)`.**  Precomposition with the comparison map. -/
noncomputable def pullback (f : HC →ₗ[k] HX) : (HX →ₗ[k] V) →ₗ[k] (HC →ₗ[k] V) :=
  LinearMap.lcomp k V f

@[simp] theorem pullback_apply (f : HC →ₗ[k] HX) (χ : HX →ₗ[k] V) (x : HC) :
    pullback (V := V) f χ x = χ (f x) := rfl

/-- Restriction of an observer to the kernel of the comparison map. -/
noncomputable def restrictKer (f : HC →ₗ[k] HX) : (HC →ₗ[k] V) →ₗ[k] (LinearMap.ker f →ₗ[k] V) :=
  (LinearMap.ker f).subtype.lcomp k V

@[simp] theorem restrictKer_apply (f : HC →ₗ[k] HX) (χ : HC →ₗ[k] V) (x : LinearMap.ker f) :
    restrictKer (V := V) f χ x = χ (x : HC) := rfl

/-- **Card `(ROD.6)`, exactness at `Hom(H_C,V)`.**  An observer restricts to zero on the kernel
exactly when it is pulled back from resolved cohomology. -/
theorem range_pullback_eq_ker_restrictKer (f : HC →ₗ[k] HX) :
    LinearMap.range (pullback (V := V) f) = LinearMap.ker (restrictKer (V := V) f) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨χ, rfl⟩
    ext x
    have hx : f (x : HC) = 0 := x.2
    simp [hx]
  · intro χ hχ
    have hker : LinearMap.ker f ≤ LinearMap.ker χ := by
      intro x hx
      have := congrArg (fun g => g (⟨x, hx⟩ : LinearMap.ker f)) hχ
      simpa using this
    set χ' : (HC ⧸ LinearMap.ker f) →ₗ[k] V := (LinearMap.ker f).liftQ χ hker with hχ'
    set χ'' : LinearMap.range f →ₗ[k] V := χ'.comp f.quotKerEquivRange.symm.toLinearMap with hχ''
    obtain ⟨ψ, hψ⟩ := χ''.exists_extend
    refine ⟨ψ, ?_⟩
    ext x
    have hmem : f x ∈ LinearMap.range f := ⟨x, rfl⟩
    have h1 : ψ (f x) = χ'' ⟨f x, hmem⟩ := congrArg (fun g => g (⟨f x, hmem⟩ :
      LinearMap.range f)) hψ
    have h2 : f.quotKerEquivRange.symm ⟨f x, hmem⟩
        = (Submodule.Quotient.mk x : HC ⧸ LinearMap.ker f) := by
      apply f.quotKerEquivRange.injective
      rw [LinearEquiv.apply_symm_apply]
      exact Subtype.ext (f.quotKerEquivRange_apply_mk x).symm
    simp only [pullback_apply, h1, hχ'', LinearMap.comp_apply, LinearEquiv.coe_coe, h2, hχ',
      Submodule.liftQ_apply]

/-- **Card `(ROD.6)`, surjectivity.**  Every observer on the kernel extends. -/
theorem restrictKer_surjective (f : HC →ₗ[k] HX) :
    Function.Surjective (restrictKer (V := V) f) := by
  intro τ
  obtain ⟨χ, hχ⟩ := τ.exists_extend
  exact ⟨χ, by ext x; exact congrArg (fun g => g x) hχ⟩

/-- **Card `(ROD.7)`, boxed.**  The observer-descent quotient is canonically the dual of the
kernel: observers that fail to descend are exactly covectors on the created laws. -/
noncomputable def observerDescentEquiv (f : HC →ₗ[k] HX) :
    ((HC →ₗ[k] V) ⧸ LinearMap.range (pullback (V := V) f)) ≃ₗ[k] (LinearMap.ker f →ₗ[k] V) :=
  (Submodule.quotEquivOfEq _ _ (range_pullback_eq_ker_restrictKer f)).trans
    (LinearMap.quotKerEquivOfSurjective _ (restrictKer_surjective f))

@[simp] theorem observerDescentEquiv_mk (f : HC →ₗ[k] HX) (χ : HC →ₗ[k] V) (x : LinearMap.ker f) :
    observerDescentEquiv (V := V) f (Submodule.Quotient.mk χ) x = χ (x : HC) := rfl

/-- **Descent–detection complementarity.**  An observer descends through the exactification exactly
when it annihilates every class created by it. -/
theorem descends_iff_vanishes (f : HC →ₗ[k] HX) (χ : HC →ₗ[k] V) :
    (∃ ψ : HX →ₗ[k] V, ∀ x, χ x = ψ (f x)) ↔ ∀ x : HC, f x = 0 → χ x = 0 := by
  constructor
  · rintro ⟨ψ, hψ⟩ x hx
    rw [hψ x, hx, map_zero]
  · intro h
    have hmem : χ ∈ LinearMap.ker (restrictKer (V := V) f) := by
      ext x
      exact h (x : HC) x.2
    rw [← range_pullback_eq_ker_restrictKer] at hmem
    obtain ⟨ψ, hψ⟩ := hmem
    exact ⟨ψ, fun x => by rw [← hψ]; rfl⟩

end ObserverDescent

/-! ## The relative-law space of an exact segment -/

section RelativeLaw

variable {k A B M N : Type*} [Field k]
  [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- **Card `(ROD.10)`, boxed.**  For the exact segment coming from the mapping cone, the
relative-law space — cone cohomology modulo the image of the resolved complex — is canonically the
kernel of the comparison map. -/
noncomputable def relativeLawEquiv (g : A →ₗ[k] B) (π : B →ₗ[k] M) (f : M →ₗ[k] N)
    (h₁ : LinearMap.range g = LinearMap.ker π) (h₂ : LinearMap.range π = LinearMap.ker f) :
    (B ⧸ LinearMap.range g) ≃ₗ[k] LinearMap.ker f :=
  (Submodule.quotEquivOfEq _ _ h₁).trans
    (π.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ h₂))

@[simp] theorem relativeLawEquiv_mk (g : A →ₗ[k] B) (π : B →ₗ[k] M) (f : M →ₗ[k] N)
    (h₁ : LinearMap.range g = LinearMap.ker π) (h₂ : LinearMap.range π = LinearMap.ker f)
    (b : B) : (relativeLawEquiv g π f h₁ h₂ (Submodule.Quotient.mk b) : M) = π b := rfl

/-- **Card `(ROD.11)`, boxed.**  Combining the two identifications: the observer-descent quotient
is the dual of the relative-law space. -/
noncomputable def relativeObserverDuality {V : Type*} [AddCommGroup V] [Module k V]
    (g : A →ₗ[k] B) (π : B →ₗ[k] M) (f : M →ₗ[k] N)
    (h₁ : LinearMap.range g = LinearMap.ker π) (h₂ : LinearMap.range π = LinearMap.ker f) :
    ((M →ₗ[k] V) ⧸ LinearMap.range (pullback (V := V) f))
      ≃ₗ[k] ((B ⧸ LinearMap.range g) →ₗ[k] V) :=
  (observerDescentEquiv f).trans
    (LinearEquiv.congrLeft V k (relativeLawEquiv g π f h₁ h₂)).symm

/-- **Card `(ROD.12)`.**  The canonical relative-observer pairing. -/
noncomputable def relativePairing {V : Type*} [AddCommGroup V] [Module k V]
    (π : B →ₗ[k] M) (χ : M →ₗ[k] V) (b : B) : V := χ (π b)

/-- The pairing is well defined: a descending observer annihilates every relative law, and a cone
class coming from the resolved complex has zero projection. -/
theorem relativePairing_well_defined {V : Type*} [AddCommGroup V] [Module k V]
    (g : A →ₗ[k] B) (π : B →ₗ[k] M) (f : M →ₗ[k] N)
    (h₁ : LinearMap.range g = LinearMap.ker π) (χ : M →ₗ[k] V)
    (hχ : ∃ ψ : N →ₗ[k] V, ∀ x, χ x = ψ (f x)) (a : A) :
    relativePairing (V := V) π χ (g a) = 0 := by
  obtain ⟨ψ, hψ⟩ := hχ
  have hga : g a ∈ LinearMap.ker π := h₁ ▸ ⟨a, rfl⟩
  simp only [relativePairing]
  rw [show π (g a) = 0 from hga, map_zero]

end RelativeLaw

/-! ## Simultaneous nonvanishing occurs exactly at the centre -/

section Simultaneous

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- **Card §6.**  If the forward evaluation vanishes exactly on one open half-line and the
reflected evaluation on the opposite one, both are nonzero exactly at the centre. -/
theorem simultaneous_nonvanishing {F : ℝ → V} (hF : ∀ u : ℝ, F u = 0 ↔ u < 0) {c : k}
    (hc : c ≠ 0) (t : ℝ) :
    (c • F (-t) ≠ 0 ∧ c • F t ≠ 0) ↔ t = 0 := by
  have hsm : ∀ u : ℝ, c • F u = 0 ↔ u < 0 := by
    intro u
    rw [smul_eq_zero]
    exact ⟨fun h => h.elim (fun hz => absurd hz hc) fun hz => (hF u).1 hz,
      fun h => Or.inr ((hF u).2 h)⟩
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with ht | ht
    · exact h2 ((hsm t).2 ht)
    · exact h1 ((hsm (-t)).2 (by linarith))
  · rintro rfl
    exact ⟨fun h => absurd ((hsm 0).1 (by simpa using h)) (lt_irrefl 0),
      fun h => absurd ((hsm 0).1 h) (lt_irrefl 0)⟩

end Simultaneous

end HTGeometry.ConstraintRelativity
