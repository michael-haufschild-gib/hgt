import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.RelativeFormsQuasicoherent
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.AffineQuasicoherentAcyclic

/-! Relative forms have vanishing higher cohomology on affine opens. -/

open AlgebraicGeometry CategoryTheory TopologicalSpace RHTower

noncomputable section

namespace GlobalTheory.SchemeCohomology

universe u w

variable {k : Type u} [CommRing k] {X : Scheme.{u}} (s : X ⟶ Spec (CommRingCat.of k)) (n : ℕ)

private abbrev abelianForms (s : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) :
    TopCat.Sheaf AddCommGrpCat.{u} X :=
  (SheafOfModules.toSheaf X.ringCatSheaf).obj (relativeForms s n)

/-- The abelian sheaf underlying the sheaf of relative forms is acyclic on affine opens. -/
theorem relativeForms_acyclicOn [HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} X)]
    {U : X.Opens} (hU : IsAffineOpen U) : DeningerAcyclicOn.{w} (abelianForms s n) U := by
  letI := relativeForms_isQuasicoherent s n
  exact quasicoherent_acyclicOn (relativeForms s n) hU

end GlobalTheory.SchemeCohomology
