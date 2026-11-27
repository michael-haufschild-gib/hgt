import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FormalPullbackGenerators
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELLineBundleTrivialization

/-! Pullback presentations of formal products of line bundles. -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LineBundleSections

variable {X Y Z : Scheme.{0}} {I : Type} [Fintype I]

/-- The formal product restricted along a morphism presents its ordinary pullback. -/
def _root_.ReciprocityTheory.ChartRestriction.G.Semi.ChartPull.linComb (L : LB X) (f : I → (Y ⟶ X)) (e : I → ℤ) (r : Z ⟶ Y) :
    ChartPull (LB.LinComb L (fun i => r ≫ f i) e) (LB.LinComb L f e) r where
  idx i := i
  le _ := fun _ h => Set.mem_iInter.2 fun k => Set.mem_iInter.1 h k
  g i j := by
    let V := LB.wchart L (fun k => r ≫ f k) i ⊓ LB.wchart L (fun k => r ≫ f k) j
    have hV : V ≤ r ⁻¹ᵁ (LB.wchart L f i ⊓ LB.wchart L f j) := fun _ h =>
      ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 h.1 k,
        Set.mem_iInter.2 fun k => Set.mem_iInter.1 h.2 k⟩
    apply unit_ext
    intro z hz
    have hi : r ((𝟙 Z : Z ⟶ Z) z) ∈ LB.wchart L f i := (hV hz).1
    have hj : r ((𝟙 Z : Z ⟶ Z) z) ∈ LB.wchart L f j := (hV hz).2
    let a := (LB.LinComb L f e).g i j
    have ha : gm (𝟙 Z) z V (pullLE r hV a) =
        gm (𝟙 Z ≫ r) z (LB.wchart L f i ⊓ LB.wchart L f j) a :=
      (congrArg (gm (𝟙 Z) z V) (res_pullU r _ hV a).symm).trans
        ((gm_res (𝟙 Z) z hV hz _).trans
          (gm_pull (𝟙 Z) r z (LB.wchart L f i ⊓ LB.wchart L f j) ⟨hi, hj⟩ a))
    change gm (𝟙 Z) z V _ = gm (𝟙 Z) z V (pullLE r hV _)
    refine (gm_linComb L (fun k => r ≫ f k) e (𝟙 Z) z i j hz.1 hz.2).trans ?_
    refine Eq.trans ?_ ((gm_linComb L f e (𝟙 Z ≫ r) z i j hi hj).symm.trans ha.symm)
    simp only [Category.assoc]

end GlobalTheory.LineBundleSections
