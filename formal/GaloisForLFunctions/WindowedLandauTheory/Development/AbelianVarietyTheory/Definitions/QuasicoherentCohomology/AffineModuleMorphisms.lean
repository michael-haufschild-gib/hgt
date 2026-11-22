import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! Morphisms of scheme modules can be constructed on the affine basis. -/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace GlobalTheory.SchemeCohomology

universe u

variable {X : Scheme.{u}} {F G : X.Modules}

private theorem sections_ext_affine {U : X.Opens} {a b : Γ(F, U)}
    (h : ∀ (V : X.Opens) (_ : IsAffineOpen V) (i : V ⟶ U),
      F.presheaf.map i.op a = F.presheaf.map i.op b) : a = b :=
  TopCat.Sheaf.eq_of_locally_eq' (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    (fun V : {V : X.Opens // IsAffineOpen V ∧ V ≤ U} => V.val) U (fun V => homOfLE V.prop.2)
    (fun p hp => by
      obtain ⟨V, hV, hpV, hVU⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hp
      exact Opens.mem_iSup.2 ⟨⟨V, hV, hVU⟩, hpV⟩)
    a b (fun V => h V.val V.prop.1 (homOfLE V.prop.2))

private abbrev AffineOpen (X : Scheme.{u}) := { U : X.Opens // IsAffineOpen U }

private theorem affineBasis (X : Scheme.{u}) :
    Opens.IsBasis (Set.range fun U : AffineOpen X => U.val) := by
  have e : (Set.range fun U : AffineOpen X => U.val) = {U : X.Opens | IsAffineOpen U} :=
    Set.ext fun U => ⟨fun ⟨V, h⟩ => h ▸ V.prop, fun h => ⟨⟨U, h⟩, rfl⟩⟩
  exact e.symm ▸ X.isBasis_affineOpens

variable (φ : ∀ U : AffineOpen X, Γ(G, U.val) →ₗ[Γ(X, U.val)] Γ(F, U.val))
  (hφ : ∀ (U V : AffineOpen X) (i : V.val ⟶ U.val) (x : Γ(G, U.val)),
    F.presheaf.map i.op (φ U x) = φ V (G.presheaf.map i.op x))

private def affinePresheafHom : G.presheaf ⟶ F.presheaf :=
  TopCat.Sheaf.restrictHomEquivHom G.presheaf (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    (affineBasis X)
    { app U := AddCommGrpCat.ofHom (φ U.unop).toAddMonoidHom
      naturality U V i := AddCommGrpCat.ext fun x => (hφ U.unop V.unop i.unop.hom x).symm }

private theorem affinePresheafHom_app (U : AffineOpen X) (x : Γ(G, U.val)) :
    (affinePresheafHom φ hφ).app (op U.val) x = φ U x :=
  congrArg (fun a => a.hom x)
    (TopCat.Sheaf.extend_hom_app G.presheaf
      (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X) (affineBasis X) _ U)

/-- Compatible maps on affine opens extend uniquely to a morphism of scheme modules. -/
def homOfAffineSections : G ⟶ F :=
  SheafOfModules.Hom.mk <| PresheafOfModules.homMk (affinePresheafHom φ hφ) fun U r x => by
    refine sections_ext_affine (F := F) (U := U.unop) fun V hV i => ?_
    have h (y : Γ(G, U.unop)) :
        F.presheaf.map i.op ((affinePresheafHom φ hφ).app U y) =
          φ ⟨V, hV⟩ (G.presheaf.map i.op y) :=
      (ConcreteCategory.congr_hom ((affinePresheafHom φ hφ).naturality i.op) y).symm.trans
        (affinePresheafHom_app φ hφ ⟨V, hV⟩ _)
    exact (h _).trans (((congrArg (φ ⟨V, hV⟩) (G.map_smul i r x)).trans
      ((φ ⟨V, hV⟩).map_smul _ _)).trans
        ((F.map_smul i r _).trans (congrArg (X.presheaf.map i.op r • ·) (h x))).symm)

@[simp] theorem homOfAffineSections_app (U : AffineOpen X) (x : Γ(G, U.val)) :
    (homOfAffineSections φ hφ).app U.val x = φ U x := affinePresheafHom_app φ hφ U x

theorem moduleHom_ext_affine {a b : G ⟶ F}
    (h : ∀ U : X.Opens, IsAffineOpen U → ∀ x, a.app U x = b.app U x) : a = b := by
  apply Scheme.Modules.hom_ext
  intro U
  apply AddCommGrpCat.ext
  intro x
  refine sections_ext_affine fun V hV i => ?_
  have e (m : G ⟶ F) : F.presheaf.map i.op (m.app U x) =
      m.app V (G.presheaf.map i.op x) :=
    (ConcreteCategory.congr_hom (m.mapPresheaf.naturality i.op) x).symm
  exact (e a).trans ((h V hV _).trans (e b).symm)

end GlobalTheory.SchemeCohomology
