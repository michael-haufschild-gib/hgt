import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.PrincipalSectionsUpperBound
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.PrincipalSectionsNonzero
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FormalSectionDimension

/-! The section module of a rigidified symmetric principal polarization
over an algebraically closed field has dimension one. -/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory MonObj
open GlobalTheory.LineBundleSections GlobalTheory.SchemeCohomology GlobalTheory.MulSplit
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.PrincipalSections

attribute [local instance] Over.cartesianMonoidalCategory

private def oneFactorChart {X : Scheme.{0}} (L : LB X) :
    ChartPull (LB.LinComb L (fun _ : PUnit => 𝟙 X) (fun _ => 1)) L (𝟙 X) := by
  let f : PUnit → (X ⟶ X) := fun _ => 𝟙 X
  let d : PUnit → ℤ := fun _ => 1
  refine ⟨fun p => p PUnit.unit, fun p _ h => Set.mem_iInter.mp h PUnit.unit, fun p q => ?_⟩
  rw [pullLE_id]
  apply unit_ext
  intro z hz
  have e := gm_linComb L f d (𝟙 X) z p q hz.1 hz.2
  refine e.trans (Eq.trans ?_ (gm_res (𝟙 X) z _ hz _).symm)
  simp only [Fintype.prod_unique, f, d, Category.id_comp, zpow_one]

/-- The formal section module of the first power of a principal
polarization has dimension one over the global functions of the base. -/
theorem finrank_sections_eq_one {K : Type} [Field K] [IsAlgClosed K]
    {A : Over (Spec (.of K))} [GrpObj A] {L : LB A.left}
    (hA : IsAbelianScheme A) (hL : L.IsLB) (hAmp : RelAmple A L) (hK : KTriv A L)
    (hrig : ∃ t : (L.pull η[A].left).Gen, t.IsGen)
    (hsym : ∀ s : Spec (.of K), ∃ U : (Spec (.of K)).Opens, s ∈ U ∧
      ∃ t : (LB.LinComb L (K := Fin 2)
        ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] ![1, -1]).Gen, t.IsGen)
    (n : ℕ) [SmoothOfRelativeDimension n A.hom] :
    Module.finrank Γ(Spec (.of K), ⊤) (Sg L A.hom (Finsupp.single (𝟙 A.left) (1 : ℤ))) = 1 := by
  apply le_antisymm _ (MulSplit.one_le_finrank_sections hA hL hAmp hK hrig hsym)
  let f : PUnit → (A.left ⟶ A.left) := fun _ => 𝟙 A.left
  let d : PUnit → ℤ := fun _ => 1
  let M := LB.LinComb L f d
  let W := Γ(toMod M, ⊤)
  letI : Module K W := sectionBaseModule A.hom (toMod M) ⊤
  have hd : dv f d = Finsupp.single (𝟙 A.left) (1 : ℤ) := Fintype.sum_unique _
  rw [finrank_formalSections A.hom f d hL hd]
  obtain ⟨v, hv⟩ := (oneFactorChart L).iso_of_common (ChartPull.id L) hL
  letI := sectionAlgebra A.hom (⊤ : A.left.Opens)
  letI : Module K Γ(toMod L, ⊤) := sectionBaseModule A.hom (toMod L) ⊤
  letI : IsScalarTower K Γ(A.left, ⊤) W := .of_algebraMap_smul fun _ _ => rfl
  letI : IsScalarTower K Γ(A.left, ⊤) Γ(toMod L, ⊤) := .of_algebraMap_smul fun _ _ => rfl
  let j := (sectionIsoEquiv (hL.linComb f d) hL hv (V := ⊤)).restrictScalars K
  rw [j.finrank_eq]
  exact finrank_globalSections_le_one hA hL hAmp hK n

end GlobalTheory.PrincipalSections
