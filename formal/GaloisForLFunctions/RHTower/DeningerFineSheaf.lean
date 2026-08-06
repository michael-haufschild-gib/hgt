import GaloisForLFunctions.RHTower.DeningerGodement

/-!
# Fine sheaves

A sheaf of abelian groups is fine when its sections can be multiplied by continuous real functions,
compatibly with restriction, in such a way that the unit function acts as the identity and a
function vanishing on an open set kills the sections there.  The last condition is what makes a
partition of unity usable: multiplying a section by a bump function produces a section that
vanishes off the bump, hence extends by zero.

Fineness is inherited by the two constructions the Godement resolution is made of.  The sheaf of
arbitrary sections of the stalks inherits it because the multiplication acts on stalks, and the
quotient by the original sheaf inherits it because the multiplication commutes with the embedding
and therefore descends to the cokernel.  So every kernel of the Godement resolution of a fine sheaf
is again fine, which is what makes the dimension shift terminate.

* `RHTower.DeningerFineAction` : the multiplication by continuous functions.
* `RHTower.DeningerFineAction.godement` : the sheaf of arbitrary sections of the stalks is fine.
* `RHTower.DeningerFineAction.godementQuotient` : the Godement quotient of a fine sheaf is fine.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat

universe u

variable {X : TopCat.{u}}

section Definition

/-- Restriction of a section along an inclusion of open sets. -/
abbrev deningerRes (F : TopCat.Sheaf AddCommGrpCat.{u} X) {U W : Opens X} (h : W ≤ U)
    (s : ToType (F.1.obj (op U))) : ToType (F.1.obj (op W)) :=
  ConcreteCategory.hom (F.1.map (homOfLE h).op) s

/-- **A fine structure on a sheaf**: a multiplication of sections by continuous real functions,
additive in both arguments, compatible with restriction, unital, and vanishing on any open set
where the function vanishes. -/
structure DeningerFineAction (F : TopCat.Sheaf AddCommGrpCat.{u} X) where
  /-- Multiplication of a section by a continuous real function. -/
  smul : C(X, ℝ) → ∀ U : Opens X, ToType (F.1.obj (op U)) → ToType (F.1.obj (op U))
  smul_add : ∀ (ρ : C(X, ℝ)) (U : Opens X) (s t : ToType (F.1.obj (op U))),
    smul ρ U (s + t) = smul ρ U s + smul ρ U t
  add_smul : ∀ (ρ σ : C(X, ℝ)) (U : Opens X) (s : ToType (F.1.obj (op U))),
    smul (ρ + σ) U s = smul ρ U s + smul σ U s
  one_smul : ∀ (U : Opens X) (s : ToType (F.1.obj (op U))), smul 1 U s = s
  smul_res : ∀ (ρ : C(X, ℝ)) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (s : ToType (F.1.obj U)),
    ConcreteCategory.hom (F.1.map i) (smul ρ (unop U) s)
      = smul ρ (unop V) (ConcreteCategory.hom (F.1.map i) s)
  smul_eq_zero : ∀ (ρ : C(X, ℝ)) (U : Opens X) (s : ToType (F.1.obj (op U))),
    (∀ x ∈ U, ρ x = 0) → smul ρ U s = 0

variable {F : TopCat.Sheaf AddCommGrpCat.{u} X}

theorem DeningerFineAction.zero_smul (A : DeningerFineAction F) (U : Opens X)
    (s : ToType (F.1.obj (op U))) : A.smul 0 U s = 0 :=
  A.smul_eq_zero 0 U s fun _ _ => rfl

theorem DeningerFineAction.sub_smul (A : DeningerFineAction F) (ρ σ : C(X, ℝ)) (U : Opens X)
    (s : ToType (F.1.obj (op U))) : A.smul (ρ - σ) U s = A.smul ρ U s - A.smul σ U s := by
  have h := A.add_smul (ρ - σ) σ U s
  rw [sub_add_cancel] at h
  rw [h]
  abel

/-- Two functions agreeing on an open set act the same way on its sections. -/
theorem DeningerFineAction.smul_congr (A : DeningerFineAction F) {ρ σ : C(X, ℝ)} {U : Opens X}
    (h : ∀ x ∈ U, ρ x = σ x) (s : ToType (F.1.obj (op U))) : A.smul ρ U s = A.smul σ U s := by
  have h0 : A.smul (ρ - σ) U s = 0 := by
    refine A.smul_eq_zero _ U s fun x hx => ?_
    show ρ x - σ x = 0
    rw [h x hx, sub_self]
  rw [A.sub_smul, sub_eq_zero] at h0
  exact h0

theorem DeningerFineAction.smul_zero (A : DeningerFineAction F) (ρ : C(X, ℝ)) (U : Opens X) :
    A.smul ρ U 0 = 0 := by
  have h := A.smul_add ρ U 0 0
  rw [add_zero] at h
  simpa using h.symm

/-- Multiplication by a function, as an endomorphism of the underlying presheaf. -/
def DeningerFineAction.hom (A : DeningerFineAction F) (ρ : C(X, ℝ)) : F.1 ⟶ F.1 where
  app U := AddCommGrpCat.ofHom
    { toFun := A.smul ρ (unop U)
      map_zero' := A.smul_zero ρ (unop U)
      map_add' := A.smul_add ρ (unop U) }
  naturality _ _ i := by
    ext s
    exact (A.smul_res ρ i s).symm

@[simp] theorem DeningerFineAction.hom_app_apply (A : DeningerFineAction F) (ρ : C(X, ℝ))
    (U : (Opens X)ᵒᵖ) (s : ToType (F.1.obj U)) :
    ConcreteCategory.hom ((A.hom ρ).app U) s = A.smul ρ (unop U) s := rfl

theorem DeningerFineAction.hom_add (A : DeningerFineAction F) (ρ σ : C(X, ℝ)) :
    A.hom (ρ + σ) = A.hom ρ + A.hom σ := by
  ext U s
  exact A.add_smul ρ σ (unop U) s

theorem DeningerFineAction.hom_one (A : DeningerFineAction F) : A.hom 1 = 𝟙 F.1 := by
  ext U s
  exact A.one_smul (unop U) s

/-- Multiplication by a function, as an endomorphism of the sheaf. -/
def DeningerFineAction.homSheaf (A : DeningerFineAction F) (ρ : C(X, ℝ)) : F ⟶ F :=
  ⟨A.hom ρ⟩

theorem DeningerFineAction.homSheaf_add (A : DeningerFineAction F) (ρ σ : C(X, ℝ)) :
    A.homSheaf (ρ + σ) = A.homSheaf ρ + A.homSheaf σ :=
  CategoryTheory.ObjectProperty.hom_ext _ (A.hom_add ρ σ)

theorem DeningerFineAction.homSheaf_one (A : DeningerFineAction F) : A.homSheaf 1 = 𝟙 F :=
  CategoryTheory.ObjectProperty.hom_ext _ A.hom_one

end Definition

section Godement

variable {F : TopCat.Sheaf AddCommGrpCat.{u} X}

/-- Multiplication by a function on the stalks. -/
noncomputable def DeningerFineAction.stalkHom (A : DeningerFineAction F) (ρ : C(X, ℝ)) (x : X) :
    F.presheaf.stalk x ⟶ F.presheaf.stalk x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (A.hom ρ)

theorem DeningerFineAction.stalkHom_germ (A : DeningerFineAction F) (ρ : C(X, ℝ)) (U : Opens X)
    (x : X) (hx : x ∈ U) (s : ToType (F.1.obj (op U))) :
    ConcreteCategory.hom (A.stalkHom ρ x) (ConcreteCategory.hom (F.presheaf.germ U x hx) s)
      = ConcreteCategory.hom (F.presheaf.germ U x hx) (A.smul ρ U s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx (A.hom ρ) s

theorem DeningerFineAction.stalkHom_add (A : DeningerFineAction F) (ρ σ : C(X, ℝ)) (x : X) :
    A.stalkHom (ρ + σ) x = A.stalkHom ρ x + A.stalkHom σ x := by
  show (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (A.hom (ρ + σ)) = _
  rw [A.hom_add]
  exact Functor.map_add _

theorem DeningerFineAction.stalkHom_one (A : DeningerFineAction F) (x : X) :
    A.stalkHom 1 x = 𝟙 _ := by
  show (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (A.hom 1) = _
  rw [A.hom_one]
  exact CategoryTheory.Functor.map_id _ _

/-- Multiplication by a function that vanishes near a point kills that stalk. -/
theorem DeningerFineAction.stalkHom_eq_zero (A : DeningerFineAction F) {ρ : C(X, ℝ)} {V : Opens X}
    (hρ : ∀ y ∈ V, ρ y = 0) {x : X} (hx : x ∈ V) (t : ToType (F.presheaf.stalk x)) :
    ConcreteCategory.hom (A.stalkHom ρ x) t = 0 := by
  obtain ⟨W, hxW, s, hs⟩ := F.presheaf.exists_germ_eq t
  have hle : W ⊓ V ≤ W := inf_le_left
  have hxWV : x ∈ W ⊓ V := ⟨hxW, hx⟩
  have hres : ConcreteCategory.hom (F.presheaf.germ (W ⊓ V) x hxWV) (deningerRes F hle s)
      = ConcreteCategory.hom (F.presheaf.germ W x hxW) s :=
    F.presheaf.germ_res_apply (homOfLE hle) x hxWV s
  rw [← hs, ← hres, A.stalkHom_germ ρ (W ⊓ V) x hxWV,
    A.smul_eq_zero ρ (W ⊓ V) _ (fun y hy => hρ y hy.2), map_zero]

/-- **The sheaf of arbitrary sections of the stalks of a fine sheaf is fine.** -/
noncomputable def DeningerFineAction.godement (A : DeningerFineAction F) :
    DeningerFineAction (deningerGodementSheaf F) where
  smul ρ _ s := fun x => ConcreteCategory.hom (A.stalkHom ρ x.1) (s x)
  smul_add ρ _ s t := by
    funext x
    exact map_add _ (s x) (t x)
  add_smul ρ σ _ s := by
    funext x
    rw [A.stalkHom_add ρ σ x.1]
    rfl
  one_smul _ s := by
    funext x
    rw [A.stalkHom_one x.1]
    rfl
  smul_res := by
    intro ρ U V i s
    funext x
    rfl
  smul_eq_zero ρ U s hρ := by
    funext x
    exact A.stalkHom_eq_zero hρ x.2 (s x)

/-- The germ embedding intertwines the multiplication on a sheaf with the multiplication on the
sheaf of arbitrary sections of its stalks. -/
theorem DeningerFineAction.godement_square (A : DeningerFineAction F) (ρ : C(X, ℝ)) :
    deningerGodementι F ≫ A.godement.homSheaf ρ = A.homSheaf ρ ≫ deningerGodementι F := by
  refine CategoryTheory.ObjectProperty.hom_ext _ ?_
  ext U s
  funext x
  exact (A.stalkHom_germ ρ (unop U) x.1 x.2 s).symm

end Godement

section Quotient

variable {F : TopCat.Sheaf AddCommGrpCat.{u} X}

/-- Multiplication by a function on the Godement quotient. -/
noncomputable def DeningerFineAction.quotientHom (A : DeningerFineAction F) (ρ : C(X, ℝ)) :
    (deningerGodementComplex F).X₃ ⟶ (deningerGodementComplex F).X₃ :=
  cokernel.map (deningerGodementι F) (deningerGodementι F) (A.homSheaf ρ) (A.godement.homSheaf ρ)
    (A.godement_square ρ)

theorem DeningerFineAction.quotientHom_spec (A : DeningerFineAction F) (ρ : C(X, ℝ)) :
    cokernel.π (deningerGodementι F) ≫ A.quotientHom ρ
      = A.godement.homSheaf ρ ≫ cokernel.π (deningerGodementι F) := by
  simp [DeningerFineAction.quotientHom]

theorem DeningerFineAction.quotientHom_add (A : DeningerFineAction F) (ρ σ : C(X, ℝ)) :
    A.quotientHom (ρ + σ) = A.quotientHom ρ + A.quotientHom σ := by
  refine (cancel_epi (cokernel.π (deningerGodementι F))).1 ?_
  rw [A.quotientHom_spec, Preadditive.comp_add, A.quotientHom_spec, A.quotientHom_spec,
    A.godement.homSheaf_add, Preadditive.add_comp]

theorem DeningerFineAction.quotientHom_one (A : DeningerFineAction F) :
    A.quotientHom 1 = 𝟙 _ := by
  refine (cancel_epi (cokernel.π (deningerGodementι F))).1 ?_
  rw [A.quotientHom_spec, A.godement.homSheaf_one, Category.id_comp, Category.comp_id]

/-- **The Godement quotient of a fine sheaf is fine.**  The multiplication descends because it
commutes with the germ embedding, and it still kills the sections over an open set where the
function vanishes because the quotient map is locally surjective. -/
noncomputable def DeningerFineAction.godementQuotient (A : DeningerFineAction F) :
    DeningerFineAction (deningerGodementComplex F).X₃ where
  smul ρ U g := ConcreteCategory.hom ((A.quotientHom ρ).1.app (op U)) g
  smul_add ρ _ s t := map_add _ s t
  add_smul ρ σ U s := by
    rw [A.quotientHom_add ρ σ]
    rfl
  one_smul U s := by
    rw [A.quotientHom_one]
    rfl
  smul_res ρ i s := (CategoryTheory.NatTrans.naturality_apply (A.quotientHom ρ).1 i s).symm
  smul_eq_zero ρ U g hρ := by
    refine TopCat.Presheaf.section_ext _ U _ _ fun x hx => ?_
    have hloc : TopCat.Presheaf.IsLocallySurjective (cokernel.π (deningerGodementι F)).1 :=
      (TopCat.Sheaf.isLocallySurjective_iff_epi _).2 inferInstance
    obtain ⟨V, hVU, ⟨h, hh⟩, hxV⟩ :=
      (TopCat.Presheaf.isLocallySurjective_iff _).1 hloc U g x hx
    have hnat := (A.quotientHom ρ).1.naturality (homOfLE hVU).op
    have hstep : deningerRes (deningerGodementComplex F).X₃ hVU
        (ConcreteCategory.hom ((A.quotientHom ρ).1.app (op U)) g)
        = ConcreteCategory.hom ((A.quotientHom ρ).1.app (op V))
            (deningerRes (deningerGodementComplex F).X₃ hVU g) :=
      (CategoryTheory.NatTrans.naturality_apply (A.quotientHom ρ).1 (homOfLE hVU).op g).symm
    have hzero : ConcreteCategory.hom ((A.quotientHom ρ).1.app (op V))
        (deningerRes (deningerGodementComplex F).X₃ hVU g) = 0 := by
      rw [← hh]
      have hsq := A.quotientHom_spec ρ
      have := congrFun (congrArg ConcreteCategory.hom
        (congrArg (fun φ => Sheaf.Hom.hom φ |>.app (op V)) hsq)) h
      rw [show ConcreteCategory.hom ((A.quotientHom ρ).1.app (op V))
            (ConcreteCategory.hom ((cokernel.π (deningerGodementι F)).1.app (op V)) h)
          = ConcreteCategory.hom (((cokernel.π (deningerGodementι F)).1.app (op V)) ≫
              ((A.quotientHom ρ).1.app (op V))) h from rfl]
      rw [show (((cokernel.π (deningerGodementι F)).1.app (op V)) ≫
              ((A.quotientHom ρ).1.app (op V)))
          = ((A.godement.homSheaf ρ).1.app (op V)) ≫
              ((cokernel.π (deningerGodementι F)).1.app (op V)) from
        congrArg (fun φ => (Sheaf.Hom.hom φ).app (op V)) hsq]
      show ConcreteCategory.hom ((cokernel.π (deningerGodementι F)).1.app (op V))
          (A.godement.smul ρ V h) = 0
      rw [A.godement.smul_eq_zero ρ V h (fun y hy => hρ y (hVU hy)), map_zero]
    have hgerm : ConcreteCategory.hom
        ((deningerGodementComplex F).X₃.presheaf.germ V x hxV)
        (deningerRes (deningerGodementComplex F).X₃ hVU
          (ConcreteCategory.hom ((A.quotientHom ρ).1.app (op U)) g))
        = ConcreteCategory.hom ((deningerGodementComplex F).X₃.presheaf.germ U x hx)
          (ConcreteCategory.hom ((A.quotientHom ρ).1.app (op U)) g) :=
      (deningerGodementComplex F).X₃.presheaf.germ_res_apply (homOfLE hVU) x hxV _
    rw [← hgerm, hstep, hzero, map_zero, map_zero]

end Quotient

end RHTower
