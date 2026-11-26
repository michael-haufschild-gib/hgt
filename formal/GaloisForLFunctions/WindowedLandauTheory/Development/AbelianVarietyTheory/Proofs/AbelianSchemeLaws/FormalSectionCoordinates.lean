import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FormalSectionModule
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.GlobalLineBundleCoordinates

/-! Global sections of the glued line bundle and values of its chart coordinates
give the same module over functions on the base. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.LineBundleSections

namespace GlobalTheory.MulSplit

variable {X Y B : Scheme.{0}} {L : LB X} (p : Y ⟶ B)
  {I : Type} [Fintype I] (f : I → (Y ⟶ X)) (d : I → ℤ)

/-- Base scalars act on global sections through the structural map. -/
abbrev globalSectionModule (M : LB Y) : Module Γ(B, ⊤) Γ(toMod M, ⊤) :=
  Module.compHom _ p.appTop.hom

/-- Glued sections and the germ-value presentation give linearly equivalent modules. -/
theorem nonempty_globalSections_equiv_Sg (hL : L.IsLB) :
    letI := globalSectionModule p (LB.LinComb L f d)
    Nonempty (Γ(toMod (LB.LinComb L f d), ⊤) ≃ₗ[Γ(B, ⊤)] Sg L p (dv f d)) := by
  let M := LB.LinComb L f d
  letI := globalSectionModule p M
  let r : Γ(toMod M, ⊤) →ₗ[Γ(B, ⊤)] Vals L p :=
    { toFun := fun s => ev p (globalCoordinates s)
      map_add' := fun s t => ev_add fun j => by
        simp only [globalCoordinates_apply, coord_add, map_add]
      map_smul' := fun c s => ev_smul c fun j => by
        change (globalCoordinates (p.appTop.hom c • s)).f j =
          resG Y le_top (p.appTop.hom c) * (globalCoordinates s).f j
        simp only [globalCoordinates_apply, coord_smul, map_mul, resG_resG] }
  have hr : Function.Injective r := by
    intro s t h
    apply globalCoordinates.injective
    have e : (globalCoordinates s).f = (globalCoordinates t).f :=
      funext fun j => ev_inj hL h j
    generalize globalCoordinates s = a at e ⊢
    generalize globalCoordinates t = b at e ⊢
    cases a
    cases b
    cases e
    rfl
  have hrange : LinearMap.range r = Sg L p (dv f d) := by
    ext v
    rw [mem_Sg hL rfl v]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨globalCoordinates s, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨globalCoordinates.symm s, congrArg (ev p) (globalCoordinates.apply_symm_apply s)⟩
  exact ⟨(LinearEquiv.ofInjective r hr).trans (LinearEquiv.ofEq _ _ hrange)⟩

end GlobalTheory.MulSplit
