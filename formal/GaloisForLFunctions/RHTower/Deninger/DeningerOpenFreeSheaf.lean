import GaloisForLFunctions.RHTower.Deninger.DeningerOpenSubterminalSheaf
import Mathlib

/-!
# The free abelian sheaf on an open set

Applying the free abelian group functor to the sheaf represented by an open set and sheafifying
gives an abelian sheaf whose maps into any abelian sheaf are exactly its sections over that open
set.  This is the object that corepresents sections, and the inclusion of one open set into another
gives a monomorphism between the corresponding free abelian sheaves.

* `deningerOpenFree` : the free abelian sheaf on an open set.
* `deningerOpenFreeHomEquiv` : maps out of it are sections over the open set.
* `deningerOpenFreeIncl`, `deningerOpenFreeIncl_mono` : the monomorphism attached to an inclusion.
-/

namespace RHTower

open CategoryTheory TopologicalSpace Opposite TopCat

universe u

variable {X : TopCat.{u}}

/-- The free abelian sheaf functor: apply the free abelian group functor and sheafify. -/
noncomputable abbrev deningerFreeSheafFunctor (X : TopCat.{u}) :
    TopCat.Sheaf (Type u) X ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  CategoryTheory.Sheaf.composeAndSheafify (Opens.grothendieckTopology X) AddCommGrpCat.free

/-- **The free abelian sheaf on an open set.** -/
noncomputable def deningerOpenFree (U : Opens X) : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (deningerFreeSheafFunctor X).obj (deningerOpenType U)

/-- **Maps out of the free abelian sheaf on an open set are sections over that open set.** -/
noncomputable def deningerOpenFreeHomEquiv (U : Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (deningerOpenFree U ⟶ F) ≃ ToType (F.1.obj (op U)) :=
  ((CategoryTheory.Sheaf.adjunction (Opens.grothendieckTopology X)
      AddCommGrpCat.adj).homEquiv _ _).trans
    (deningerOpenTypeHomEquiv U
      ((CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
        (forget AddCommGrpCat)).obj F))

/-- The inclusion of represented sheaves attached to an inclusion of open sets. -/
def deningerOpenTypeIncl {V U : Opens X} (h : V ≤ U) :
    deningerOpenType V ⟶ deningerOpenType U :=
  (deningerOpenTypeHomEquiv V (deningerOpenType U)).symm
    (⟨⟨h⟩⟩ : deningerOpenCarrier U (op V))

/-- Any two maps into a represented sheaf agree, its values being subsingletons. -/
theorem deningerOpenType_hom_subsingleton (U : Opens X) (G : TopCat.Sheaf (Type u) X)
    (f g : G ⟶ deningerOpenType U) : f = g := by
  refine CategoryTheory.Sheaf.hom_ext ?_
  refine NatTrans.ext (funext fun W => ?_)
  refine ConcreteCategory.hom_ext_iff.2 (fun a => ?_)
  exact Subsingleton.elim (α := deningerOpenCarrier U W) _ _

instance deningerOpenTypeIncl_mono {V U : Opens X} (h : V ≤ U) :
    Mono (deningerOpenTypeIncl h) :=
  ⟨fun {Z} f g _ => deningerOpenType_hom_subsingleton V Z f g⟩

/-- **The monomorphism of free abelian sheaves attached to an inclusion of open sets.** -/
noncomputable def deningerOpenFreeIncl {V U : Opens X} (h : V ≤ U) :
    deningerOpenFree V ⟶ deningerOpenFree U :=
  (deningerFreeSheafFunctor X).map (deningerOpenTypeIncl h)

instance deningerOpenTypeIncl_app_mono {V U : Opens X} (h : V ≤ U) (W : (Opens X)ᵒᵖ) :
    Mono ((deningerOpenTypeIncl h).hom.app W) :=
  ⟨fun {Z} g₁ g₂ _ => by
    refine ConcreteCategory.hom_ext_iff.2 (fun z => ?_)
    exact Subsingleton.elim (α := deningerOpenCarrier V W) _ _⟩

instance deningerOpenTypeIncl_hom_mono {V U : Opens X} (h : V ≤ U) :
    Mono ((deningerOpenTypeIncl h).hom) :=
  NatTrans.mono_of_mono_app _

instance deningerOpenTypeInclFree_mono {V U : Opens X} (h : V ≤ U) :
    Mono (Functor.whiskerRight ((deningerOpenTypeIncl h).hom) AddCommGrpCat.free) := by
  haveI : ∀ W, Mono (AddCommGrpCat.free.map ((deningerOpenTypeIncl h).hom.app W)) :=
    fun W => Functor.map_mono _ _
  exact NatTrans.mono_of_mono_app _

instance deningerOpenFreeIncl_mono {V U : Opens X} (h : V ≤ U) :
    Mono (deningerOpenFreeIncl h) := by
  show Mono ((CategoryTheory.presheafToSheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}).map
      (Functor.whiskerRight ((deningerOpenTypeIncl h).hom) AddCommGrpCat.free))
  exact Functor.map_mono _ _

end RHTower

namespace RHTower

open CategoryTheory TopologicalSpace Opposite TopCat

universe u

variable {X : TopCat.{u}}

/-- A map out of a represented sheaf is determined by its value on the tautological section. -/
theorem deningerOpenTypeHomEquiv_app (U : Opens X) (G : TopCat.Sheaf (Type u) X)
    (φ : deningerOpenType U ⟶ G) (W : (Opens X)ᵒᵖ) (a : deningerOpenCarrier U W) :
    φ.hom.app W a = G.1.map (homOfLE a.1.1).op (deningerOpenTypeHomEquiv U G φ) := by
  have h := congrArg (fun ψ : deningerOpenType U ⟶ G => ψ.hom.app W a)
    ((deningerOpenTypeHomEquiv U G).left_inv φ)
  exact h.symm

/-- **The corepresentation of sections is natural in the open set**: restricting a section is
precomposing with the inclusion of free abelian sheaves. -/
theorem deningerOpenFreeHomEquiv_naturality {V U : Opens X} (h : V ≤ U)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (φ : deningerOpenFree U ⟶ F) :
    deningerOpenFreeHomEquiv V F (deningerOpenFreeIncl h ≫ φ)
      = F.1.map (homOfLE h).op (deningerOpenFreeHomEquiv U F φ) := by
  have hleft : (CategoryTheory.Sheaf.adjunction (Opens.grothendieckTopology X)
        AddCommGrpCat.adj).homEquiv _ _ (deningerOpenFreeIncl h ≫ φ) =
      deningerOpenTypeIncl h ≫ (CategoryTheory.Sheaf.adjunction
        (Opens.grothendieckTopology X) AddCommGrpCat.adj).homEquiv _ _ φ :=
    (CategoryTheory.Sheaf.adjunction (Opens.grothendieckTopology X)
      AddCommGrpCat.adj).homEquiv_naturality_left (deningerOpenTypeIncl h) φ
  show deningerOpenTypeHomEquiv V _ ((CategoryTheory.Sheaf.adjunction
      (Opens.grothendieckTopology X) AddCommGrpCat.adj).homEquiv _ _
        (deningerOpenFreeIncl h ≫ φ)) = _
  rw [hleft]
  set ψ := (CategoryTheory.Sheaf.adjunction (Opens.grothendieckTopology X)
    AddCommGrpCat.adj).homEquiv _ _ φ with hψ
  show (deningerOpenTypeIncl h ≫ ψ).hom.app (op V) (deningerOpenTypeUnit V) = _
  have happ := deningerOpenTypeHomEquiv_app U _ ψ (op V)
    ((deningerOpenTypeIncl h).hom.app (op V) (deningerOpenTypeUnit V))
  show ψ.hom.app (op V) ((deningerOpenTypeIncl h).hom.app (op V) (deningerOpenTypeUnit V)) = _
  rw [happ]
  rfl

/-- **An injective abelian sheaf is flasque.**  Restriction is precomposition with the
monomorphism of free abelian sheaves attached to the inclusion of open sets, and an injective
object turns that monomorphism into a surjection on maps. -/
theorem deningerInjective_isFlasque (I : TopCat.Sheaf AddCommGrpCat.{u} X)
    [CategoryTheory.Injective I] : TopCat.Sheaf.IsFlasque I := by
  constructor
  intro W₁ W₂ i
  refine (AddCommGrpCat.epi_iff_surjective _).2 (fun t => ?_)
  set h : W₂.unop ≤ W₁.unop := leOfHom i.unop with hh
  set ψ := (deningerOpenFreeHomEquiv W₂.unop I).symm t with hψ
  refine ⟨deningerOpenFreeHomEquiv W₁.unop I
    (CategoryTheory.Injective.factorThru ψ (deningerOpenFreeIncl h)), ?_⟩
  have hfac : deningerOpenFreeIncl h ≫
      CategoryTheory.Injective.factorThru ψ (deningerOpenFreeIncl h) = ψ :=
    CategoryTheory.Injective.comp_factorThru ψ (deningerOpenFreeIncl h)
  have hnat := deningerOpenFreeHomEquiv_naturality h I
    (CategoryTheory.Injective.factorThru ψ (deningerOpenFreeIncl h))
  rw [hfac] at hnat
  have hi : (homOfLE h).op = i := Subsingleton.elim _ _
  rw [hi] at hnat
  rw [← hnat, hψ]
  exact (deningerOpenFreeHomEquiv W₂.unop I).apply_symm_apply t

end RHTower

namespace RHTower

open CategoryTheory TopologicalSpace Opposite TopCat

universe u

variable {X : TopCat.{u}}

/-- **The corepresentation of sections is natural in the sheaf.** -/
theorem deningerOpenFreeHomEquiv_naturality_right (U : Opens X)
    {F F' : TopCat.Sheaf AddCommGrpCat.{u} X} (g : F ⟶ F')
    (φ : deningerOpenFree U ⟶ F) :
    deningerOpenFreeHomEquiv U F' (φ ≫ g)
      = g.hom.app (op U) (deningerOpenFreeHomEquiv U F φ) := by
  have hright : (CategoryTheory.Sheaf.adjunction (Opens.grothendieckTopology X)
        AddCommGrpCat.adj).homEquiv _ _ (φ ≫ g) =
      (CategoryTheory.Sheaf.adjunction (Opens.grothendieckTopology X)
        AddCommGrpCat.adj).homEquiv _ _ φ ≫
        (CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
          (forget AddCommGrpCat)).map g :=
    (CategoryTheory.Sheaf.adjunction (Opens.grothendieckTopology X)
      AddCommGrpCat.adj).homEquiv_naturality_right φ g
  show deningerOpenTypeHomEquiv U _ ((CategoryTheory.Sheaf.adjunction
      (Opens.grothendieckTopology X) AddCommGrpCat.adj).homEquiv _ _ (φ ≫ g)) = _
  rw [hright]
  rfl

end RHTower
