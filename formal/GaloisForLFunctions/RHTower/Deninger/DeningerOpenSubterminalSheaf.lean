import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# The sheaf of types represented by an open set

For an open set `U` of a topological space, the presheaf sending an open set `W` to the proposition
`W ≤ U` is a sheaf: its values are subsingletons, and a family of opens contained in `U` has union
contained in `U`.  Maps out of it into a sheaf of types are exactly its sections over `U`, which is
the Yoneda lemma for this site in the form needed to build the free abelian sheaf on an open set.

* `deningerOpenType` : the sheaf represented by an open set.
* `deningerOpenTypeHomEquiv` : maps out of it are sections over the open set.
-/

namespace RHTower

open CategoryTheory TopologicalSpace Opposite TopCat

universe u

variable {X : TopCat.{u}}

/-- The value of the represented presheaf on an open set. -/
abbrev deningerOpenCarrier (U : Opens X) (W : (Opens X)ᵒᵖ) : Type u :=
  ULift.{u} (PLift (W.unop ≤ U))

instance (U : Opens X) (W : (Opens X)ᵒᵖ) : Subsingleton (deningerOpenCarrier U W) :=
  ⟨fun a b => by
    cases a with
    | up a => cases b with
      | up b => cases a; cases b; rfl⟩

/-- The presheaf of types represented by an open set. -/
def deningerOpenTypePresheaf (U : Opens X) : TopCat.Presheaf (Type u) X where
  obj W := deningerOpenCarrier U W
  map {W₁ W₂} h := ↾(fun (s : deningerOpenCarrier U W₁) =>
    (⟨⟨le_trans (leOfHom h.unop) s.1.1⟩⟩ : deningerOpenCarrier U W₂))
  map_id W := by
    refine ConcreteCategory.hom_ext_iff.2 (fun a => ?_)
    exact Subsingleton.elim (α := deningerOpenCarrier U W) _ _
  map_comp {W₁ W₂ W₃} f g := by
    refine ConcreteCategory.hom_ext_iff.2 (fun a => ?_)
    exact Subsingleton.elim (α := deningerOpenCarrier U W₃) _ _

theorem deningerOpenTypePresheaf_isSheaf (U : Opens X) :
    (deningerOpenTypePresheaf U).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types]
  intro ι V sf _
  refine ⟨(⟨⟨iSup_le (fun i => (sf i).1.1)⟩⟩ : deningerOpenCarrier U (op (iSup V))), ?_, ?_⟩
  · intro i
    exact Subsingleton.elim (α := deningerOpenCarrier U (op (V i))) _ _
  · intro t _
    exact Subsingleton.elim (α := deningerOpenCarrier U (op (iSup V))) _ _

/-- **The sheaf of types represented by an open set.** -/
def deningerOpenType (U : Opens X) : TopCat.Sheaf (Type u) X :=
  ⟨deningerOpenTypePresheaf U, deningerOpenTypePresheaf_isSheaf U⟩

/-- The tautological section of the represented sheaf over its own open set. -/
def deningerOpenTypeUnit (U : Opens X) : deningerOpenCarrier U (op U) :=
  ⟨⟨le_refl U⟩⟩

/-- **Maps out of the represented sheaf are sections over the open set.** -/
def deningerOpenTypeHomEquiv (U : Opens X) (G : TopCat.Sheaf (Type u) X) :
    (deningerOpenType U ⟶ G) ≃ G.1.obj (op U) where
  toFun φ := φ.hom.app (op U) (deningerOpenTypeUnit U)
  invFun s :=
    { hom :=
        { app := fun W => ↾(fun (h : deningerOpenCarrier U W) => G.1.map (homOfLE h.1.1).op s)
          naturality := by
            intro W₁ W₂ h
            refine ConcreteCategory.hom_ext_iff.2 (fun a => ?_)
            show G.1.map (homOfLE _).op s = G.1.map h (G.1.map (homOfLE a.1.1).op s)
            rw [← Functor.map_comp_apply]
            rfl } }
  left_inv φ := by
    refine CategoryTheory.Sheaf.hom_ext ?_
    refine NatTrans.ext (funext fun W => ?_)
    refine ConcreteCategory.hom_ext_iff.2 (fun a => ?_)
    show G.1.map (homOfLE (a : deningerOpenCarrier U W).1.1).op
        (φ.hom.app (op U) (deningerOpenTypeUnit U)) = φ.hom.app W a
    have hnat := ConcreteCategory.congr_hom
      (φ.hom.naturality (homOfLE (a : deningerOpenCarrier U W).1.1).op)
      (deningerOpenTypeUnit U)
    simp only [ConcreteCategory.comp_apply] at hnat
    have hsub : φ.hom.app W a =
        φ.hom.app W ((deningerOpenTypePresheaf U).map
          (homOfLE (a : deningerOpenCarrier U W).1.1).op (deningerOpenTypeUnit U)) :=
      congrArg _ (Subsingleton.elim (α := deningerOpenCarrier U W) _ _)
    rw [hsub]
    exact hnat.symm
  right_inv s := by
    show G.1.map (homOfLE (le_refl U)).op s = s
    rw [show (homOfLE (le_refl U) : U ⟶ U) = 𝟙 U from rfl]
    simp

end RHTower
