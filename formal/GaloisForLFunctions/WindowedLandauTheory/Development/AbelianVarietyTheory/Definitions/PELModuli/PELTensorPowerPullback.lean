import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELGeneratorTransport

/-! Tensor products of compatible pullbacks of an isomorphism of line bundles. -/

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

/-- A compatible family of diagrams transports the tensor product of bundle powers. -/
theorem iso_linComb_pull {w : LB.Iso L' (L.pull F)} (hw : w.IsGen)
    {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (φ' : K → (Y' ⟶ X'))
    (ε : K → ℤ) (h : Y' ⟶ Y) (hc : ∀ k, φ' k ≫ F = h ≫ φ k) :
    ∃ a : LB.Iso (LB.LinComb L' φ' ε) ((LB.LinComb L φ ε).pull h), a.IsGen := by
  classical
  let A := LB.LinComb L' φ' ε
  let B := (LB.LinComb L φ ε).pull h
  let C := LB.LinComb L (fun k => φ' k ≫ F) ε
  let i (p : B.ι × A.ι) : K → L.ι := p.1 PUnit.unit
  have hi (p : B.ι × A.ι) (y : Y') (hy : y ∈ B.U p.1) : y ∈ C.U (i p) := by
    have hB : h y ∈ LB.wchart L φ (i p) := mem_pull.mp hy
    refine Set.mem_iInter.mpr fun k => ?_
    change (φ' k ≫ F) y ∈ L.U (i p k)
    exact (congrArg (fun g : Y' ⟶ X => g y ∈ L.U (i p k)) (hc k)).mpr (Set.mem_iInter.mp hB k)
  have hh (p : B.ι × A.ι) : B.U p.1 ⊓ A.U p.2 ≤ C.U (i p) ⊓ A.U p.2 :=
    fun y hy => ⟨hi p y hy.1, hy.2⟩
  choose u hu using fun p : B.ι × A.ι => exists_pw w φ' ε (i p) p.2
  let a : LB.Iso A B := ⟨fun p => res (hh p) (u p)⟩
  have ea (p : B.ι × A.ι) (y : Y') (hy : y ∈ B.U p.1 ⊓ A.U p.2) :
      gm (𝟙 Y') y _ (a.s p) = pw w φ' ε (𝟙 Y') y (i p) p.2 :=
    (gm_res (𝟙 Y') y (hh p) hy _).trans (hu p Y' (𝟙 Y') y (hh p hy))
  have eb (p q : B.ι × A.ι) (y : Y') (hp : y ∈ B.U p.1) (hq : y ∈ B.U q.1) :
      gm (𝟙 Y') y _ (B.g p.1 q.1) = trF (fun k => φ' k ≫ F) ε (𝟙 Y') y (i p) (i q) := by
    refine (gm_pull_g (LB.LinComb L φ ε) h (𝟙 Y') y p.1 q.1 hp hq).trans ?_
    refine (gm_linComb L φ ε (𝟙 Y' ≫ h) y (i p) (i q)
      (mem_pull.mp hp) (mem_pull.mp hq)).trans ?_
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Category.assoc, ← hc k]
  refine ⟨a, fun p q => unit_ext fun y hy => ?_⟩
  have leftTransition := eb p q y hy.1.1 hy.2.1
  have rightTransition := gm_linComb L' φ' ε (𝟙 Y') y p.2 q.2 hy.1.2 hy.2.2
  have move := pw_trans (pGen_of_isGen hw) φ' ε (𝟙 Y') y
    (hi p y hy.1.1) (hi q y hy.2.1) hy.1.2 hy.2.2
  have full := (gm_div A B (𝟙 Y') y p q hy).trans
    (congrArg₂ (fun b c => b * c⁻¹) leftTransition rightTransition)
  exact ((gm_res (𝟙 Y') y inf_le_left hy _).trans (ea p y hy.1)).trans
    (move.trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) full ((gm_res (𝟙 Y') y inf_le_right hy _).trans (ea q y hy.2)))).symm)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
