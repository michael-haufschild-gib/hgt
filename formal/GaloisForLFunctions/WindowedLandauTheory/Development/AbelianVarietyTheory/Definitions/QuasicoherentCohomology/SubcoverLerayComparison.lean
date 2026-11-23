import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.SubcoverCechRestriction
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LerayOpenFreeComparison

/-! Restriction to an acyclic subcover represents the identity on the
cohomology of the covered open. -/

noncomputable section

open CategoryTheory CategoryTheory.Abelian Opposite TopologicalSpace HTGeometry RHTower

namespace GlobalTheory.SchemeCohomology

variable {X : TopCat.{0}} {ι κ : Type} [DecidableEq ι] [LinearOrder ι]
  [DecidableEq κ] [LinearOrder κ] {V : Opens X} {U : ι → Opens X} (j : κ ↪o ι)

private abbrev AbSheaf := TopCat.Sheaf AddCommGrpCat.{0} X

local instance subcoverHasExt : HasExt.{0} (AbSheaf (X := X)) := hasExt_of_enoughInjectives _

private abbrev emptySectionMap (F : AbSheaf (X := X)) :
    AddCommGrpCat.of ((sheafCech F V U).obj ∅) ⟶
      AddCommGrpCat.of ((sheafCech F V (U ∘ j)).obj ∅) :=
  F.1.map (eqToHom ((coverInter_empty V (U ∘ j)).trans (coverInter_empty V U).symm)).op

private theorem sectionRestrictions_subcover (F : AbSheaf (X := X)) :
    sectionRestrictions F V U ≫ (subcoverCechMap V U j F).f 0 =
      emptySectionMap (V := V) (U := U) j F ≫ sectionRestrictions F V (U ∘ j) := by
  apply AddCommGrpCat.ext
  intro z
  apply Subtype.ext
  funext I
  let a := (subcoverCechMap V U j F).f 0 (sectionRestrictions F V U z)
  let b := sectionRestrictions F V (U ∘ j) (emptySectionMap (V := V) (U := U) j F z)
  change a.val I = b.val I
  by_cases hI : I.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hI
    rw [show a.val {i} = subcoverCochain V U j F (sectionRestrictions F V U z).val {i} from
      subcoverCechMap_apply V U j F _ _ _, show b.val {i} = _ from sectionRestrictions_singleton F V _ _ _]
    let J := ({i} : Finset κ).map j.toEmbedding
    have hJ (L : Finset ι) (hL : L = {j i}) :
        (sectionRestrictions F V U z).val L =
          (sheafCech F V U).res (Finset.empty_subset L) z := by
      subst L
      exact sectionRestrictions_singleton F V U z (j i)
    let e := eqToHom (coverInter_orderEmbedding V U j {i}).symm
    refine (congrArg (F.1.map e.op).hom (hJ J (Finset.map_singleton _ _))).trans ?_
    let r := homOfLE (coverInter_anti (V := V) (U := U) (Finset.empty_subset J))
    let q := homOfLE (coverInter_anti (V := V) (U := U ∘ j) (Finset.empty_subset {i}))
    let e₀ := eqToHom ((coverInter_empty V (U ∘ j)).trans (coverInter_empty V U).symm)
    have hc : r.op ≫ e.op = e₀.op ≫ q.op := Subsingleton.elim _ _
    exact (ConcreteCategory.congr_hom (F.1.map_comp r.op e.op) z).symm.trans
      ((ConcreteCategory.congr_hom (congrArg F.1.map hc) z).trans
        (ConcreteCategory.congr_hom (F.1.map_comp e₀.op q.op) z))
  · rw [a.property I hI, b.property I hI]

/-- Restriction to a subcover commutes with the comparison with sheaf cohomology. -/
theorem lerayOpenFreeEquiv_subcover
    (h₁ : V ≤ ⨆ i, U i) (h₂ : V ≤ ⨆ i, (U ∘ j) i) :
    ∀ (n : ℕ) (F : AbSheaf (X := X)) (hF : CoverAcyclic V U F)
      (hF' : CoverAcyclic V (U ∘ j) F) (x : (sheafCechComplex V U F).homology n),
      lerayOpenFreeEquiv h₂ (coverInter_empty V (U ∘ j)) F hF' n
          (HomologicalComplex.homologyMap (subcoverCechMap V U j F) n x) =
        lerayOpenFreeEquiv h₁ (coverInter_empty V U) F hF n x := by
  intro n
  induction n with
  | zero =>
    intro F hF hF' x
    obtain ⟨z, rfl⟩ := (sectionsToCechH0 F h₁).surjective x
    rw [sectionsToCechH0_of_commutes F h₁ h₂ _ _ (sectionRestrictions_subcover j F),
      lerayOpenFreeEquiv_zero, lerayOpenFreeEquiv_zero]
    congr 2
    let e₀ := eqToHom ((coverInter_empty V (U ∘ j)).trans (coverInter_empty V U).symm)
    let p := eqToHom (coverInter_empty V (U ∘ j)).symm
    let q := eqToHom (coverInter_empty V U).symm
    have hc : e₀.op ≫ p.op = q.op := Subsingleton.elim _ _
    exact (ConcreteCategory.congr_hom (F.1.map_comp e₀.op p.op) z).symm.trans
      (ConcreteCategory.congr_hom (congrArg F.1.map hc) z)
  | succ n ih =>
    intro F hF hF' x
    let S := deningerInjectiveEmbedding F
    let hS := deningerInjectiveEmbedding_shortExact F
    let h₂F : CoverAcyclic V U S.X₂ := coverAcyclic_of_injective S.X₂
    let h₂F' : CoverAcyclic V (U ∘ j) S.X₂ := coverAcyclic_of_injective S.X₂
    let hQ := CoverAcyclic.quotient (S := S) hF h₂F hS
    let hQ' := CoverAcyclic.quotient (S := S) hF' h₂F' hS
    let D := coverCech_shortExact hS hF
    let E := coverCech_shortExact hS hF'
    let a : S.map (abelianCechFunctor X V U) ⟶ S.map (abelianCechFunctor X V (U ∘ j)) :=
      { τ₁ := subcoverCechMap V U j S.X₁
        τ₂ := subcoverCechMap V U j S.X₂
        τ₃ := subcoverCechMap V U j S.X₃
        comm₁₂ := (subcoverCechMap_natural V U j S.f).symm
        comm₂₃ := (subcoverCechMap_natural V U j S.g).symm }
    have hz : HomologicalComplex.homologyMap (sheafCechComplexMap V U S.f) (n + 1) x = 0 := by
      let b := lerayOpenFreeEquiv h₁ (coverInter_empty V U) S.X₂ h₂F (n + 1)
      exact b.injective ((Ext.eq_zero_of_injective (b _)).trans (map_zero b).symm)
    obtain ⟨y, hy⟩ := (ShortComplex.ab_exact_iff _).mp (D.homology_exact₁ n (n + 1) rfl) x hz
    change D.δ n (n + 1) rfl y = x at hy
    have hd := ConcreteCategory.congr_hom (HomologicalComplex.HomologySequence.δ_naturality
      a D E n (n + 1) rfl) y
    change HomologicalComplex.homologyMap (subcoverCechMap V U j F) (n + 1)
        (D.δ n (n + 1) rfl y) =
      E.δ n (n + 1) rfl (HomologicalComplex.homologyMap (subcoverCechMap V U j S.X₃) n y) at hd
    rw [← hy, hd]
    let y' := HomologicalComplex.homologyMap (subcoverCechMap V U j S.X₃) n y
    exact (lerayOpenFreeEquiv_boundary h₂ (coverInter_empty V (U ∘ j)) hS hF' hQ' n y').trans
      ((congrArg (fun z : Ext (openFree V) S.X₃ n => z.comp hS.extClass rfl)
        (ih S.X₃ hQ hQ' y)).trans
        (lerayOpenFreeEquiv_boundary h₁ (coverInter_empty V U) hS hF hQ n y).symm)

end GlobalTheory.SchemeCohomology
