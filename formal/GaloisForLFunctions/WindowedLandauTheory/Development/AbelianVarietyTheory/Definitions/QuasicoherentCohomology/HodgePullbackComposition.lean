import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HodgeCohomology
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.RelativeFormsPullbackComposition
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.CohomologyPullbackComposition

/-! Pullback on Hodge cohomology is functorial over the base. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace GlobalTheory.SchemeCohomology

variable {K : Type} [CommRing K] {X Y Z : Scheme.{0}}
  {s : X ⟶ Spec (CommRingCat.of K)} {t : Y ⟶ Spec (CommRingCat.of K)}
  {v : Z ⟶ Spec (CommRingCat.of K)} {f : Y ⟶ X} {g : Z ⟶ Y}

/-- The Hodge pullback of a composite is the composite of the pullbacks in reverse order. -/
theorem hodgePullback_comp (hf : f ≫ s = t) (hg : g ≫ t = v)
    (hgf : (g ≫ f) ≫ s = v) (p q : ℕ) (x : HodgeCohomology s p q) :
    hodgePullback hg p q (hodgePullback hf p q x) = hodgePullback hgf p q x := by
  let A := SheafOfModules.toSheaf X.ringCatSheaf
  let B := SheafOfModules.toSheaf Y.ringCatSheaf
  let φ := A.map (relativeFormsPullback hf p)
  let ψ := B.map (relativeFormsPullback hg p)
  let χ := A.map (relativeFormsPullback hgf p)
  let T := TopCat.Sheaf.pushforward AddCommGrpCat.{0} f.base
  have he : φ ≫ T.map ψ = χ := by
    change φ ≫ T.map ψ = A.map (relativeFormsPullback hgf p)
    rw [← relativeFormsPullback_comp hf hg hgf p, Functor.map_comp]
    apply congrArg (φ ≫ ·)
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    intro U
    apply AddCommGrpCat.ext
    intro u
    change (relativeFormsPullback hg p).app (f ⁻¹ᵁ U.unop) u =
      ((Scheme.Modules.pushforward f).map (relativeFormsPullback hg p) ≫
        (Scheme.Modules.pushforwardComp g f).hom.app (relativeForms v p)).app U.unop u
    rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      Scheme.Modules.pushforwardComp_hom_app_app, ConcreteCategory.id_apply,
      Scheme.Modules.pushforward_map_app]
  change abelianCohomologyPullback g.base ψ ⊤ q
      (abelianCohomologyPullback f.base φ ⊤ q x) =
    abelianCohomologyPullback (g ≫ f).base χ ⊤ q x
  exact (abelianCohomologyPullback_comp f.base g.base φ ψ ⊤ q x).trans
    (congrArg (fun a => abelianCohomologyPullback (g ≫ f).base a ⊤ q x) he)

end GlobalTheory.SchemeCohomology
