import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FormalSectionCoordinates
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.FiniteGlobalLineBundleSections

/-! Formal section modules have the same dimension as global sections
over the coefficient field. -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open GlobalTheory.LineBundleSections GlobalTheory.SchemeCohomology UpperTheory.Cb
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.MulSplit

variable {K : Type} [Field K] {X Y : Scheme.{0}} (p : Y ⟶ Spec (.of K))
  {L : LB X}

private theorem globalSection_scalars (M : LB Y) :
    letI : Algebra K Γ(Spec (.of K), ⊤) := (Scheme.ΓSpecIso (.of K)).inv.hom.toAlgebra
    letI : Module Γ(Spec (.of K), ⊤) Γ(toMod M, ⊤) := globalSectionModule p M
    letI : Module K Γ(toMod M, ⊤) := sectionBaseModule p (toMod M) ⊤
    IsScalarTower K Γ(Spec (.of K), ⊤) Γ(toMod M, ⊤) := by
  letI : Algebra K Γ(Spec (.of K), ⊤) := (Scheme.ΓSpecIso (.of K)).inv.hom.toAlgebra
  letI : Module Γ(Spec (.of K), ⊤) Γ(toMod M, ⊤) := globalSectionModule p M
  letI : Module K Γ(toMod M, ⊤) := sectionBaseModule p (toMod M) ⊤
  refine IsScalarTower.of_algebraMap_smul fun a w => ?_
  have e : p.appTop = p.appLE ⊤ ⊤ (by simp) := p.app_eq_appLE
  exact congrArg (fun φ : Γ(Spec (.of K), ⊤) ⟶ Γ(Y, ⊤) =>
    φ ((Scheme.ΓSpecIso (.of K)).inv a) • w) e

/-- Compatible chart sections and their germ values give equal dimensions,
with the coefficient ring identified by the global functions of `Spec K`. -/
theorem finrank_formalSections {I : Type} [Fintype I] (f : I → (Y ⟶ X)) (d : I → ℤ)
    (hL : L.IsLB) {D : (Y ⟶ X) →₀ ℤ} (hD : dv f d = D) :
    letI := sectionBaseModule p (toMod (LB.LinComb L f d)) ⊤
    Module.finrank Γ(Spec (.of K), ⊤) (Sg L p D) =
      Module.finrank K Γ(toMod (LB.LinComb L f d), ⊤) := by
  let S := Γ(Spec (.of K), ⊤)
  let M := LB.LinComb L f d
  let W := Γ(toMod M, ⊤)
  letI : Module S W := globalSectionModule p M
  letI : Module K W := sectionBaseModule p (toMod M) ⊤
  letI : Algebra K S := (Scheme.ΓSpecIso (.of K)).inv.hom.toAlgebra
  letI := globalSection_scalars p M
  obtain ⟨e⟩ := nonempty_globalSections_equiv_Sg p f d hL
  rw [← hD, ← e.finrank_eq]
  exact (congrArg Cardinal.toNat (rank_eq_of_equiv_equiv (R := K) (R' := S)
    (Scheme.ΓSpecIso (.of K)).inv.hom (AddEquiv.refl W)
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv)
    (fun a w => (IsScalarTower.algebraMap_smul S a w).symm))).symm

/-- Projectivity makes every formal section module finite. -/
theorem moduleFinite_formalSections (hp : IsProjOver p) (hL : L.IsLB)
    (D : (Y ⟶ X) →₀ ℤ) : Module.Finite Γ(Spec (.of K), ⊤) (Sg L p D) := by
  let f (i : D.support) := i.1
  let d (i : D.support) := D i.1
  let M := LB.LinComb L f d
  let S := Γ(Spec (.of K), ⊤)
  let W := Γ(toMod M, ⊤)
  letI : Module S W := globalSectionModule p M
  letI : Module K W := sectionBaseModule p (toMod M) ⊤
  letI : Algebra K S := (Scheme.ΓSpecIso (.of K)).inv.hom.toAlgebra
  letI := globalSection_scalars p M
  letI : Module.Finite K W := moduleFinite_globalSections p hp (hL.linComb f d)
  letI : Module.Finite S W := Module.Finite.of_restrictScalars_finite K S W
  obtain ⟨e⟩ := nonempty_globalSections_equiv_Sg p f d hL
  have hD : dv f d = D := dv_support D
  rw [← hD]
  exact Module.Finite.of_surjective e.toLinearMap e.surjective

end GlobalTheory.MulSplit
