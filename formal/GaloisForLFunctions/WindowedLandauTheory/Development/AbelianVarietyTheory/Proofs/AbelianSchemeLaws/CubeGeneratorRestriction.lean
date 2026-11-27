import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FormalProductPullback

/-! Pullback of a formal product of line bundles and cancellation of equal factors. -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AbLaw.Cube

variable {X Y Z W : Scheme.{0}} {I : Type} [Fintype I]

/-- Triviality after composing the factors with a map is triviality of the pullback. -/
theorem trivial_pull_linComb (L : LB X) (hL : L.IsLB)
    (f : I → (Y ⟶ X)) (e : I → ℤ) (r : Z ⟶ Y) :
    (∃ t : ((LB.LinComb L f e).pull r).Gen, t.IsGen) ↔
      ∃ t : (LB.LinComb L (fun i => r ≫ f i) e).Gen, t.IsGen := by
  have hF := hL.linComb f e
  have h₁ := hF.pull r
  have h₂ := hL.linComb (fun i => r ≫ f i) e
  let P := ChartPull.pull (LB.LinComb L f e) r
  let Q := ChartPull.linComb L f e r
  obtain ⟨u, hu⟩ := ChartPull.iso_of_common P Q hF
  obtain ⟨v, hv⟩ := hu.symm
  exact ⟨fun ⟨s, hs⟩ => hs.exists_gen_of_iso hu h₁ h₂,
    fun ⟨s, hs⟩ => hs.exists_gen_of_iso hv h₂ h₁⟩

/-- A formal product whose exponents cancel at each factor has a normalized generator. -/
theorem exists_gen_of_cancellation (L : LB X) (hL : L.IsLB)
    (f : I → (Y ⟶ X)) (e : I → ℤ)
    (h : ∀ (U : Type) [CommGroup U] (k : (Y ⟶ X) → U), ∏ i, k (f i) ^ e i = 1) :
    ∃ t : (LB.LinComb L f e).Gen, t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι),
        Good L z J → val t r z J = 1 := by
  have he : FormEq (I := PEmpty) PEmpty.elim PEmpty.elim f e :=
    fun U _ k => (Fintype.prod_empty _).trans (h U k).symm
  have hs : (LB.oneGen L (Y := Y)).IsGen := by
    intro i j
    exact (map_one _).trans
      ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (mul_one _)).symm
  obtain ⟨t, ht, hv⟩ := exists_gen_of_formEq hL he (LB.oneGen L) hs
  refine ⟨t, ht, fun Z r z J hJ => (hv Z r z J hJ).trans ?_⟩
  exact map_one _

end GlobalTheory.AbLaw.Cube
