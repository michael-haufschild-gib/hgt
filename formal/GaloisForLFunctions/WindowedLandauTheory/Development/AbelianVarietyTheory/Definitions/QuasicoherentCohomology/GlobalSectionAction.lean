import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! Global scalar multiplication on sheaves of modules over a scheme. -/

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

namespace GlobalTheory.SchemeCohomology

universe u

variable {X : Scheme.{u}}

/-- Restriction from global sections of the structure sheaf to an open set. -/
abbrev restrictGlobal (X : Scheme.{u}) (U : X.Opens) : Γ(X, ⊤) →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom

private theorem map_restrictGlobal {U V : X.Opens} (i : V ⟶ U) (r : Γ(X, ⊤)) :
    X.presheaf.map i.op (restrictGlobal X U r) = restrictGlobal X V r := by
  rw [restrictGlobal, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

private def scalarHom (F : X.Modules) (r : Γ(X, ⊤)) : F ⟶ F :=
  SheafOfModules.Hom.mk <| PresheafOfModules.homMk
    { app := fun U => F.smul (restrictGlobal X U.unop r)
      naturality := fun _ _ i => by
        have h := F.map_comp_smul i.unop (restrictGlobal X _ r)
        rw [map_restrictGlobal] at h
        exact h.symm }
    (fun U a m => smul_comm (restrictGlobal X U.unop r)
      (show Γ(X, U.unop) from a) (show Γ(F, U.unop) from m))

@[simp] private theorem scalarHom_apply (F : X.Modules) (r : Γ(X, ⊤))
    (U : X.Opens) (x : Γ(F, U)) :
    (scalarHom F r).app U x = restrictGlobal X U r • x := rfl

private theorem end_ext {F : X.Modules} {a b : End F}
    (h : ∀ (U : X.Opens) (x : Γ(F, U)), (a : F ⟶ F).app U x = (b : F ⟶ F).app U x) :
    a = b :=
  Scheme.Modules.hom_ext a b fun U => AddCommGrpCat.ext (h U)

/-- A global section acts by multiplication by its restriction on each open set. -/
def globalSectionEnd (F : X.Modules) : Γ(X, ⊤) →+* End F where
  toFun := scalarHom F
  map_one' := by
    apply end_ext
    intro U x
    change (scalarHom F 1).app U x = x
    rw [scalarHom_apply, map_one, one_smul]
  map_mul' r s := by
    apply end_ext
    intro U x
    change (scalarHom F (r * s)).app U x =
      (scalarHom F r).app U ((scalarHom F s).app U x)
    simp only [scalarHom_apply, map_mul, mul_smul]
  map_zero' := by
    apply end_ext
    intro U x
    change (scalarHom F 0).app U x = 0
    rw [scalarHom_apply, map_zero, zero_smul]
  map_add' r s := by
    apply end_ext
    intro U x
    change (scalarHom F (r + s)).app U x =
      (scalarHom F r).app U x + (scalarHom F s).app U x
    simp only [scalarHom_apply, map_add, add_smul]

@[simp] theorem globalSectionEnd_app (F : X.Modules) (r : Γ(X, ⊤))
    (U : X.Opens) (x : Γ(F, U)) :
    (globalSectionEnd F r).app U x = restrictGlobal X U r • x := rfl

@[reassoc] theorem globalSectionEnd_natural {F G : X.Modules} (φ : F ⟶ G) (r : Γ(X, ⊤)) :
    globalSectionEnd F r ≫ φ = φ ≫ globalSectionEnd G r := by
  ext U x
  exact φ.app_smul (restrictGlobal X U r) x

end GlobalTheory.SchemeCohomology
