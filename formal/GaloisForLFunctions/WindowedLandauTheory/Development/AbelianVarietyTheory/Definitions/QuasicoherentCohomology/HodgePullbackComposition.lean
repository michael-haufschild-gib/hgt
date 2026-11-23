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
    let c := (Scheme.Modules.pushforward f).map (relativeFormsPullback hg p) ≫
      (Scheme.Modules.pushforwardComp g f).hom.app (relativeForms v p)
    have h : χ = φ ≫ A.map c :=
      (congrArg A.map (relativeFormsPullback_comp hf hg hgf p).symm).trans (A.map_comp _ _)
    refine (congrArg (φ ≫ ·) ?_).trans h.symm
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.ext
    intro u
    change (relativeFormsPullback hg p).app (f ⁻¹ᵁ U.unop) u =
      ((Scheme.Modules.pushforward f).map (relativeFormsPullback hg p) ≫
        (Scheme.Modules.pushforwardComp g f).hom.app (relativeForms v p)).app U.unop u
    rfl
  have hg' := CohomologyOn.pullback_apply g (relativeFormsPullback hg p) ⊤ q
    (hodgePullback hf p q x)
  have hf' := congrArg (abelianCohomologyPullback g.base ψ (f ⁻¹ᵁ (⊤ : X.Opens)) q)
    (CohomologyOn.pullback_apply f (relativeFormsPullback hf p) ⊤ q x)
  have hcomp := abelianCohomologyPullback_comp f.base g.base φ ψ (⊤ : X.Opens) q x
  have he' := congrArg (fun a => abelianCohomologyPullback (g ≫ f).base a (⊤ : X.Opens) q x) he
  have hgf' := CohomologyOn.pullback_apply (g ≫ f) (relativeFormsPullback hgf p) ⊤ q x
  exact hg'.trans (hf'.trans (hcomp.trans (he'.trans hgf'.symm)))

end GlobalTheory.SchemeCohomology
