import GaloisForLFunctions.RHTower.Deninger.DeningerGodement

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
structure DeningerFineAction (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (R : AddSubgroup C(X, ℝ)) where
  /-- The unit function is an admissible multiplier. -/
  one_mem : (1 : C(X, ℝ)) ∈ R
  /-- Multiplication of a section by an admissible multiplier. -/
  smul : ↥R → ∀ U : Opens X, ToType (F.1.obj (op U)) → ToType (F.1.obj (op U))
  smul_add : ∀ (ρ : ↥R) (U : Opens X) (s t : ToType (F.1.obj (op U))),
    smul ρ U (s + t) = smul ρ U s + smul ρ U t
  add_smul : ∀ (ρ σ : ↥R) (U : Opens X) (s : ToType (F.1.obj (op U))),
    smul (ρ + σ) U s = smul ρ U s + smul σ U s
  one_smul : ∀ (U : Opens X) (s : ToType (F.1.obj (op U))), smul ⟨1, one_mem⟩ U s = s
  smul_res : ∀ (ρ : ↥R) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (s : ToType (F.1.obj U)),
    ConcreteCategory.hom (F.1.map i) (smul ρ (unop U) s)
      = smul ρ (unop V) (ConcreteCategory.hom (F.1.map i) s)
  smul_eq_zero : ∀ (ρ : ↥R) (U : Opens X) (s : ToType (F.1.obj (op U))),
    (∀ x ∈ U, (ρ : C(X, ℝ)) x = 0) → smul ρ U s = 0

variable {F : TopCat.Sheaf AddCommGrpCat.{u} X} {R : AddSubgroup C(X, ℝ)}

theorem DeningerFineAction.zero_smul (A : DeningerFineAction F R) (U : Opens X)
    (s : ToType (F.1.obj (op U))) : A.smul 0 U s = 0 :=
  A.smul_eq_zero 0 U s fun _ _ => rfl

theorem DeningerFineAction.sub_smul (A : DeningerFineAction F R) (ρ σ : ↥R) (U : Opens X)
    (s : ToType (F.1.obj (op U))) : A.smul (ρ - σ) U s = A.smul ρ U s - A.smul σ U s := by
  have h := A.add_smul (ρ - σ) σ U s
  rw [sub_add_cancel] at h
  rw [h]
  abel

/-- Two functions agreeing on an open set act the same way on its sections. -/
theorem DeningerFineAction.smul_congr (A : DeningerFineAction F R) {ρ σ : ↥R} {U : Opens X}
    (h : ∀ x ∈ U, (ρ : C(X, ℝ)) x = (σ : C(X, ℝ)) x) (s : ToType (F.1.obj (op U))) :
    A.smul ρ U s = A.smul σ U s := by
  have h0 : A.smul (ρ - σ) U s = 0 := by
    refine A.smul_eq_zero _ U s fun x hx => ?_
    show ((ρ : C(X, ℝ)) - (σ : C(X, ℝ))) x = 0
    rw [ContinuousMap.sub_apply, h x hx, sub_self]
  rw [A.sub_smul, sub_eq_zero] at h0
  exact h0

theorem DeningerFineAction.smul_zero (A : DeningerFineAction F R) (ρ : ↥R) (U : Opens X) :
    A.smul ρ U 0 = 0 := by
  have h := A.smul_add ρ U 0 0
  rw [add_zero] at h
  simpa using h.symm

theorem DeningerFineAction.smul_sub (A : DeningerFineAction F R) (ρ : ↥R) (U : Opens X)
    (s t : ToType (F.1.obj (op U))) : A.smul ρ U (s - t) = A.smul ρ U s - A.smul ρ U t := by
  have h := A.smul_add ρ U (s - t) t
  rw [sub_add_cancel] at h
  rw [h]
  abel

/-- Multiplication by a finite sum of functions is the sum of the multiplications. -/
theorem DeningerFineAction.finset_sum_smul (A : DeningerFineAction F R) {ι : Type*}
    (T : Finset ι) (ρ : ι → ↥R) (U : Opens X) (s : ToType (F.1.obj (op U))) :
    A.smul (∑ j ∈ T, ρ j) U s = ∑ j ∈ T, A.smul (ρ j) U s := by
  classical
  induction T using Finset.induction with
  | empty => simpa using A.zero_smul U s
  | insert j T hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj, A.add_smul, ih]

/-- Multiplication commutes with restriction. -/
theorem DeningerFineAction.smul_res' (A : DeningerFineAction F R) (ρ : ↥R) {U W : Opens X}
    (h : W ≤ U) (s : ToType (F.1.obj (op U))) :
    deningerRes F h (A.smul ρ U s) = A.smul ρ W (deningerRes F h s) :=
  A.smul_res ρ (homOfLE h).op s

/-- Multiplication by a function, as an endomorphism of the underlying presheaf. -/
def DeningerFineAction.hom (A : DeningerFineAction F R) (ρ : ↥R) : F.1 ⟶ F.1 where
  app U := AddCommGrpCat.ofHom
    { toFun := A.smul ρ (unop U)
      map_zero' := A.smul_zero ρ (unop U)
      map_add' := A.smul_add ρ (unop U) }
  naturality _ _ i := by
    ext s
    exact (A.smul_res ρ i s).symm

@[simp] theorem DeningerFineAction.hom_app_apply (A : DeningerFineAction F R) (ρ : ↥R)
    (U : (Opens X)ᵒᵖ) (s : ToType (F.1.obj U)) :
    ConcreteCategory.hom ((A.hom ρ).app U) s = A.smul ρ (unop U) s := rfl

theorem DeningerFineAction.hom_add (A : DeningerFineAction F R) (ρ σ : ↥R) :
    A.hom (ρ + σ) = A.hom ρ + A.hom σ := by
  ext U s
  exact A.add_smul ρ σ (unop U) s

theorem DeningerFineAction.hom_one (A : DeningerFineAction F R) :
    A.hom ⟨1, A.one_mem⟩ = 𝟙 F.1 := by
  ext U s
  exact A.one_smul (unop U) s

/-- Multiplication by a function, as an endomorphism of the sheaf. -/
def DeningerFineAction.homSheaf (A : DeningerFineAction F R) (ρ : ↥R) : F ⟶ F :=
  ⟨A.hom ρ⟩

theorem DeningerFineAction.homSheaf_add (A : DeningerFineAction F R) (ρ σ : ↥R) :
    A.homSheaf (ρ + σ) = A.homSheaf ρ + A.homSheaf σ :=
  CategoryTheory.ObjectProperty.hom_ext _ (A.hom_add ρ σ)

theorem DeningerFineAction.homSheaf_one (A : DeningerFineAction F R) :
    A.homSheaf ⟨1, A.one_mem⟩ = 𝟙 F :=
  CategoryTheory.ObjectProperty.hom_ext _ A.hom_one

end Definition

section Godement

variable {F : TopCat.Sheaf AddCommGrpCat.{u} X} {R : AddSubgroup C(X, ℝ)}

/-- Multiplication by a function on the stalks. -/
noncomputable def DeningerFineAction.stalkHom (A : DeningerFineAction F R) (ρ : ↥R) (x : X) :
    F.presheaf.stalk x ⟶ F.presheaf.stalk x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (A.hom ρ)

theorem DeningerFineAction.stalkHom_germ (A : DeningerFineAction F R) (ρ : ↥R) (U : Opens X)
    (x : X) (hx : x ∈ U) (s : ToType (F.1.obj (op U))) :
    ConcreteCategory.hom (A.stalkHom ρ x) (ConcreteCategory.hom (F.presheaf.germ U x hx) s)
      = ConcreteCategory.hom (F.presheaf.germ U x hx) (A.smul ρ U s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx (A.hom ρ) s

theorem DeningerFineAction.stalkHom_add (A : DeningerFineAction F R) (ρ σ : ↥R) (x : X) :
    A.stalkHom (ρ + σ) x = A.stalkHom ρ x + A.stalkHom σ x := by
  show (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (A.hom (ρ + σ)) = _
  rw [A.hom_add]
  exact Functor.map_add _

theorem DeningerFineAction.stalkHom_one (A : DeningerFineAction F R) (x : X) :
    A.stalkHom ⟨1, A.one_mem⟩ x = 𝟙 _ := by
  show (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (A.hom ⟨1, A.one_mem⟩) = _
  rw [A.hom_one]
  exact CategoryTheory.Functor.map_id _ _

/-- Multiplication by a function that vanishes near a point kills that stalk. -/
theorem DeningerFineAction.stalkHom_eq_zero (A : DeningerFineAction F R) {ρ : ↥R} {V : Opens X}
    (hρ : ∀ y ∈ V, (ρ : C(X, ℝ)) y = 0) {x : X} (hx : x ∈ V) (t : ToType (F.presheaf.stalk x)) :
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
noncomputable def DeningerFineAction.godement (A : DeningerFineAction F R) :
    DeningerFineAction (deningerGodementSheaf F) R where
  one_mem := A.one_mem
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
theorem DeningerFineAction.godement_square (A : DeningerFineAction F R) (ρ : ↥R) :
    deningerGodementι F ≫ A.godement.homSheaf ρ = A.homSheaf ρ ≫ deningerGodementι F := by
  refine CategoryTheory.ObjectProperty.hom_ext _ ?_
  ext U s
  funext x
  show ConcreteCategory.hom (A.stalkHom ρ x.1)
      (ConcreteCategory.hom (F.presheaf.germ (unop U) x.1 x.2) s)
    = ConcreteCategory.hom (F.presheaf.germ (unop U) x.1 x.2) (A.smul ρ (unop U) s)
  exact A.stalkHom_germ ρ (unop U) x.1 x.2 s

end Godement

section Transport

variable {F G : TopCat.Sheaf AddCommGrpCat.{u} X} {R : AddSubgroup C(X, ℝ)}

/-- **A fine structure transports along an epimorphism** that intertwines the multiplications.
The multiplication on the target kills the sections over an open set where the function vanishes
because the epimorphism is locally surjective, so every germ there comes from a section upstairs
which the multiplication already kills. -/
noncomputable def deningerFineAction_of_epi (B : DeningerFineAction F R) {φ : F ⟶ G} (hepi : Epi φ)
    (Φ : ↥R → (G ⟶ G)) (hΦ : ∀ ρ, φ ≫ Φ ρ = B.homSheaf ρ ≫ φ)
    (hadd : ∀ ρ σ, Φ (ρ + σ) = Φ ρ + Φ σ) (hone : Φ ⟨1, B.one_mem⟩ = 𝟙 G) :
    DeningerFineAction G R where
  one_mem := B.one_mem
  smul ρ U g := ConcreteCategory.hom ((Φ ρ).1.app (op U)) g
  smul_add _ _ s t := map_add _ s t
  add_smul ρ σ _ _ := by rw [hadd ρ σ]; rfl
  one_smul _ _ := by rw [hone]; rfl
  smul_res := by
    intro ρ U V i s
    exact (CategoryTheory.NatTrans.naturality_apply (Φ ρ).1 i s).symm
  smul_eq_zero ρ U g hρ := by
    refine TopCat.Presheaf.section_ext G U _ 0 fun x hx => ?_
    have hloc : TopCat.Presheaf.IsLocallySurjective φ.1 :=
      (TopCat.Sheaf.isLocallySurjective_iff_epi φ).2 hepi
    obtain ⟨V, hVU, ⟨h, hh⟩, hxV⟩ :=
      (TopCat.Presheaf.isLocallySurjective_iff φ.1).1 hloc U g x hx
    have hsq : ConcreteCategory.hom ((Φ ρ).1.app (op V))
        (ConcreteCategory.hom (φ.1.app (op V)) h)
        = ConcreteCategory.hom (φ.1.app (op V)) (B.smul ρ V h) := by
      exact congrArg (fun ψ : F ⟶ G => ConcreteCategory.hom (ψ.1.app (op V)) h) (hΦ ρ)
    have hh' : ConcreteCategory.hom (φ.1.app (op V)) h
        = ConcreteCategory.hom (G.1.map (homOfLE hVU).op) g := hh
    have key : ConcreteCategory.hom ((Φ ρ).1.app (op V))
        (ConcreteCategory.hom (G.1.map (homOfLE hVU).op) g) = 0 := by
      rw [← hh', hsq, B.smul_eq_zero ρ V h fun y hy => hρ y (hVU hy), map_zero]
    have hres : ConcreteCategory.hom (G.presheaf.germ V x hxV)
        (ConcreteCategory.hom (G.1.map (homOfLE hVU).op)
          (ConcreteCategory.hom ((Φ ρ).1.app (op U)) g))
        = ConcreteCategory.hom (G.presheaf.germ U x hx)
          (ConcreteCategory.hom ((Φ ρ).1.app (op U)) g) :=
      G.presheaf.germ_res_apply (homOfLE hVU) x hxV _
    rw [← hres, ← CategoryTheory.NatTrans.naturality_apply (Φ ρ).1 (homOfLE hVU).op g, key,
      map_zero, map_zero]

end Transport

section Quotient

variable {F : TopCat.Sheaf AddCommGrpCat.{u} X} {R : AddSubgroup C(X, ℝ)}

/-- Multiplication by a function on the Godement quotient. -/
noncomputable def DeningerFineAction.quotientHom (A : DeningerFineAction F R) (ρ : ↥R) :
    (deningerGodementComplex F).X₃ ⟶ (deningerGodementComplex F).X₃ :=
  cokernel.map (deningerGodementι F) (deningerGodementι F) (A.homSheaf ρ) (A.godement.homSheaf ρ)
    (A.godement_square ρ)

theorem DeningerFineAction.quotientHom_spec (A : DeningerFineAction F R) (ρ : ↥R) :
    cokernel.π (deningerGodementι F) ≫ A.quotientHom ρ
      = A.godement.homSheaf ρ ≫ cokernel.π (deningerGodementι F) := by
  simp [DeningerFineAction.quotientHom]

theorem DeningerFineAction.quotientHom_add (A : DeningerFineAction F R) (ρ σ : ↥R) :
    A.quotientHom (ρ + σ) = A.quotientHom ρ + A.quotientHom σ := by
  refine (cancel_epi (cokernel.π (deningerGodementι F))).1 ?_
  rw [A.quotientHom_spec, Preadditive.comp_add, A.quotientHom_spec, A.quotientHom_spec,
    A.godement.homSheaf_add, Preadditive.add_comp]

theorem DeningerFineAction.quotientHom_one (A : DeningerFineAction F R) :
    A.quotientHom ⟨1, A.one_mem⟩ = 𝟙 _ := by
  refine (cancel_epi (cokernel.π (deningerGodementι F))).1 ?_
  rw [A.quotientHom_spec, A.godement.homSheaf_one, Category.id_comp, Category.comp_id]

/-- **The Godement quotient of a fine sheaf is fine.** -/
noncomputable def DeningerFineAction.godementQuotient (A : DeningerFineAction F R) :
    DeningerFineAction (deningerGodementComplex F).X₃ R :=
  deningerFineAction_of_epi A.godement (φ := cokernel.π (deningerGodementι F)) inferInstance
    A.quotientHom (fun ρ => A.quotientHom_spec ρ) A.quotientHom_add A.quotientHom_one

end Quotient

end RHTower
