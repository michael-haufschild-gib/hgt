import GaloisForLFunctions.RHTower.Deninger.DeningerAcyclicResolution

/-!
# The sheaf of discontinuous sections

Every sheaf embeds in the sheaf of arbitrary — not necessarily continuous — sections of its stalks.
That sheaf is flasque, because a family of stalk elements defined on a smaller open set extends by
zero, and the embedding is a monomorphism because a section with all germs zero is zero.

This is the first step of the Godement resolution, and it is what makes the cohomology of a sheaf
computable by dimension shifting: the quotient by the original sheaf inherits whatever extra
structure the sheaf carried, since the construction is stalkwise.

* `RHTower.deningerGodementPresheaf` : the presheaf of arbitrary sections of the stalks.
* `RHTower.deningerGodementSheaf` : it is a sheaf, and it is flasque.
* `RHTower.deningerGodementι` : the germ embedding, a monomorphism.
* `RHTower.deningerGodementShortExact` : the resulting short exact sequence.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat

universe u

variable {X : TopCat.{u}}

section Presheaf

/-- The presheaf of arbitrary sections of the stalks. -/
noncomputable def deningerGodementPresheaf (F : TopCat.Presheaf AddCommGrpCat.{u} X) :
    TopCat.Presheaf AddCommGrpCat.{u} X where
  obj U := AddCommGrpCat.of (∀ x : (unop U : Opens X), ToType (F.stalk x.1))
  map {_ _} i := AddCommGrpCat.ofHom
    { toFun := fun s x => s ⟨x.1, i.unop.le x.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem deningerGodementPresheaf_map_apply {F : TopCat.Presheaf AddCommGrpCat.{u} X}
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (s : ∀ x : (unop U : Opens X), ToType (F.stalk x.1)) (x : (unop V : Opens X)) :
    ConcreteCategory.hom ((deningerGodementPresheaf F).map i) s x = s ⟨x.1, i.unop.le x.2⟩ := rfl

/-- The underlying presheaf of types is the presheaf of arbitrary sections of the stalks. -/
noncomputable def deningerGodementForgetIso (F : TopCat.Presheaf AddCommGrpCat.{u} X) :
    TopCat.presheafToTypes X (fun x => ToType (F.stalk x)) ≅
      deningerGodementPresheaf F ⋙ forget AddCommGrpCat.{u} :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- **The presheaf of arbitrary sections of the stalks is a sheaf.** -/
theorem deningerGodement_isSheaf (F : TopCat.Presheaf AddCommGrpCat.{u} X) :
    (deningerGodementPresheaf F).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat.{u})]
  exact TopCat.Presheaf.isSheaf_of_iso (deningerGodementForgetIso F)
    (TopCat.Presheaf.toTypes_isSheaf X _)

/-- **The presheaf of arbitrary sections of the stalks is flasque**: a family defined on a smaller
open set extends by zero. -/
instance deningerGodement_isFlasque (F : TopCat.Presheaf AddCommGrpCat.{u} X) :
    (deningerGodementPresheaf F).IsFlasque where
  epi {U V} i := by
    classical
    rw [AddCommGrpCat.epi_iff_surjective]
    intro t
    refine ⟨fun x => if h : x.1 ∈ (unop V : Opens X) then t ⟨x.1, h⟩ else 0, ?_⟩
    funext x
    exact dif_pos x.2

end Presheaf

section Sheaf

variable (F : TopCat.Sheaf AddCommGrpCat.{u} X)

/-- **The sheaf of arbitrary sections of the stalks.** -/
noncomputable def deningerGodementSheaf : TopCat.Sheaf AddCommGrpCat.{u} X :=
  ⟨deningerGodementPresheaf F.1, deningerGodement_isSheaf F.1⟩

instance deningerGodementSheaf_isFlasque : (deningerGodementSheaf F).IsFlasque :=
  deningerGodement_isFlasque F.1

/-- The germ embedding of a sheaf into the sheaf of arbitrary sections of its stalks. -/
noncomputable def deningerGodementι : F ⟶ deningerGodementSheaf F :=
  ⟨{ app := fun U => AddCommGrpCat.ofHom
      { toFun := fun s x => ConcreteCategory.hom (F.presheaf.germ (unop U) x.1 x.2) s
        map_zero' := by
          funext x
          exact map_zero _
        map_add' := fun a b => by
          funext x
          exact map_add _ a b }
     naturality := fun U V i => by
       ext s
       funext x
       exact F.presheaf.germ_res_apply i.unop x.1 x.2 s }⟩

@[simp] theorem deningerGodementι_app_apply (U : (Opens X)ᵒᵖ) (s : ToType (F.1.obj U))
    (x : (unop U : Opens X)) :
    ConcreteCategory.hom ((deningerGodementι F).1.app U) s x =
      ConcreteCategory.hom (F.presheaf.germ (unop U) x.1 x.2) s := rfl

/-- **The germ embedding is a monomorphism**: a section all of whose germs vanish is zero. -/
instance deningerGodementι_mono : Mono (deningerGodementι F) := by
  haveI : ∀ U, Mono ((deningerGodementι F).1.app U) := by
    intro U
    rw [AddCommGrpCat.mono_iff_injective]
    intro s t hst
    refine TopCat.Presheaf.section_ext F (unop U) s t fun x hx => ?_
    exact congrFun hst ⟨x, hx⟩
  haveI : Mono (deningerGodementι F).1 := NatTrans.mono_of_mono_app _
  exact CategoryTheory.Sheaf.Hom.mono_of_presheaf_mono _ _ _

/-- The short exact sequence embedding a sheaf into the flasque sheaf of arbitrary sections of its
stalks. -/
noncomputable abbrev deningerGodementComplex : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk (deningerGodementι F) (cokernel.π (deningerGodementι F)) (by simp)

theorem deningerGodementShortExact : (deningerGodementComplex F).ShortExact where
  exact := ShortComplex.exact_cokernel _
  mono_f := inferInstance
  epi_g := inferInstance

end Sheaf

end RHTower
