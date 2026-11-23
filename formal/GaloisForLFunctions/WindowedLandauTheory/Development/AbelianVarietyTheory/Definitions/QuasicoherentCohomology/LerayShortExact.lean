import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.GodementCechComparison

/-! Short exact sequences of sheaves yield short exact Čech complexes on
covers where the kernel sheaf is acyclic on the intersections. -/

noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace
  HTGeometry RHTower

namespace GlobalTheory.SchemeCohomology

variable {X : TopCat.{0}} {ι : Type} {V : Opens X} {U : ι → Opens X}

local instance lerayHasExt : HasExt.{0} (TopCat.Sheaf AddCommGrpCat.{0} X) :=
  hasExt_of_enoughInjectives _

/-- A sheaf is acyclic on the nonempty intersections of the cover. -/
abbrev CoverAcyclic (V : Opens X) (U : ι → Opens X) (F : TopCat.Sheaf AddCommGrpCat.{0} X) :=
  ∀ a : Finset ι, a.Nonempty → DeningerAcyclicOn.{0} F (coverInter V U a)

theorem coverAcyclic_of_injective (F : TopCat.Sheaf AddCommGrpCat.{0} X) [Injective F] :
    CoverAcyclic V U F := fun _ _ _ x => Ext.eq_zero_of_injective x

theorem CoverAcyclic.quotient {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)}
    (h₁ : CoverAcyclic V U S.X₁) (h₂ : CoverAcyclic V U S.X₂) (hS : S.ShortExact) :
    CoverAcyclic V U S.X₃ := by
  intro a ha n x
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ (deningerOpenFree (coverInter V U a)) hS x
    rfl (h₁ a ha (n + 1) _)
  rw [h₂ a ha n y, Ext.zero_comp] at hy
  exact hy.symm

end GlobalTheory.SchemeCohomology
