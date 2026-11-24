import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ClopenFormTrace
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.HodgeTraceTower

/-! The trace on Hodge cohomology is additive over clopen parts of the source. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace Opposite

namespace GlobalTheory.SchemeCohomology

local instance clopenTraceHasExt (T : TopCat.{0}) :
    HasExt.{0} (TopCat.Sheaf AddCommGrpCat.{0} T) := hasExt_of_enoughInjectives _

variable {K : Type} [CommRing K] {X Y : Scheme.{0}} {J : Type} [Fintype J]
  {s : X ⟶ Spec (CommRingCat.of K)} {t : Y ⟶ Spec (CommRingCat.of K)}
  {f : Y ⟶ X} [IsFinite f] [Etale f]

private theorem cohomology_map_sum {F G : X.Modules} (a : J → (F ⟶ G)) (q : ℕ)
    (x : CohomologyOn F ⊤ q) :
    CohomologyOn.map (∑ j, a j) ⊤ q x = ∑ j, CohomologyOn.map (a j) ⊤ q x := by
  let P := SheafOfModules.toSheaf X.ringCatSheaf
  change (x : Ext _ _ q).comp (Ext.mk₀ (P.map (∑ j, a j))) (add_zero q) =
    ∑ j, (x : Ext _ _ q).comp (Ext.mk₀ (P.map (a j))) (add_zero q)
  rw [P.map_sum, Ext.mk₀_sum, Ext.comp_sum]

private theorem sourcePart_comparison (hf : f ≫ s = t) (V : Y.Opens)
    [IsAffineHom (V.ι ≫ f)] (hg : (V.ι ≫ f) ≫ s = V.ι ≫ t) (p q : ℕ)
    (x : PushforwardFormsCohomology t f p q) :
    hodgePullback (f := V.ι) rfl p q (formsPushforwardEquiv hf p q x) =
      formsPushforwardEquiv hg p q (CohomologyOn.map (sourcePartForms t f V p) ⊤ q x) := by
  let A := SheafOfModules.toSheaf X.ringCatSheaf
  let B := SheafOfModules.toSheaf Y.ringCatSheaf
  let T := TopCat.Sheaf.pushforward AddCommGrpCat.{0} f.base
  let φ := relativeFormsPullback (f := V.ι) (s := t) rfl p
  let ψ := B.map φ
  let a := sourcePartForms t f V p
  have he : A.map a = T.map ψ := by
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.ext
    intro u
    rfl
  have hc := abelianCohomologyPullback_comp f.base V.ι.base (𝟙 _) ψ (⊤ : X.Opens) q x
  rw [Category.id_comp] at hc
  have h₁ := CohomologyOn.pullback_apply V.ι φ ⊤ q (formsPushforwardEquiv hf p q x)
  have h₂ := CohomologyOn.pullback_apply (V.ι ≫ f) a ⊤ q x
  have h₃ := congrArg
    (fun m => abelianCohomologyPullback (V.ι ≫ f).base m (⊤ : X.Opens) q x) he.symm
  exact h₁.trans (hc.trans (h₃.trans h₂.symm))

/-- The Hodge trace along a finite étale morphism is the sum of the traces
after pullback to the members of a clopen partition. -/
theorem hodgeTrace_eq_sum_clopen (hf : f ≫ s = t) (W : J → Y.Opens)
    (hdis : ∀ i j, i ≠ j → W i ⊓ W j = ⊥) (hcov : iSup W = ⊤)
    [∀ j, IsFinite ((W j).ι ≫ f)] [∀ j, Etale ((W j).ι ≫ f)]
    (p q : ℕ) (x : HodgeCohomology t p q) :
    hodgeTrace hf p q x =
      ∑ j, hodgeTrace (f := (W j).ι ≫ f) (by rw [Category.assoc, hf]) p q
        (hodgePullback (f := (W j).ι) rfl p q x) := by
  let hg (j : J) : ((W j).ι ≫ f) ≫ s = (W j).ι ≫ t := by rw [Category.assoc, hf]
  let E := formsPushforwardEquiv hf p q
  obtain ⟨y, rfl⟩ := E.surjective x
  change CohomologyOn.map (relativeFormsTrace hf p) ⊤ q (E.symm (E y)) = _
  rw [E.symm_apply_apply, relativeFormsTrace_eq_sum_clopen hf W hdis hcov p, cohomology_map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← CohomologyOn.map_comp_top, sourcePart_comparison hf (W j) (hg j) p q]
  let E' := formsPushforwardEquiv (hg j) p q
  let z := CohomologyOn.map (sourcePartForms t f (W j) p) ⊤ q y
  change CohomologyOn.map (relativeFormsTrace (hg j) p) ⊤ q z =
    CohomologyOn.map (relativeFormsTrace (hg j) p) ⊤ q (E'.symm (E' z))
  rw [E'.symm_apply_apply]

end GlobalTheory.SchemeCohomology
