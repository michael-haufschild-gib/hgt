import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.AdditiveTranslationDifference
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FieldTranslationBundles
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleTwists
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELIsomorphismGerms

/-! The theorem of the cube gives an isomorphism between the pullback of a
translation difference by addition and its exterior product. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TwistTranslate GlobalTheory.LineBundleSections
open scoped CategoryTheory.Obj

namespace GlobalTheory.TranslateAdditive

attribute [local instance] Over.cartesianMonoidalCategory

private def pullFormalChart {X Y Z : Scheme.{0}} (L : LB X) {I : Type} [Fintype I]
    (f : I → (Y ⟶ X)) (d : I → ℤ) (r : Z ⟶ Y) :
    ChartPull ((LB.LinComb L f d).pull r) (LB.LinComb L (fun k => r ≫ f k) d) (𝟙 Z) where
  idx p := p PUnit.unit
  le p := fun _ hz => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (mem_pull.mp hz) k
  g p q := by
    rw [pullLE_id]
    apply unit_ext
    intro z hz
    have hp := mem_pull.mp hz.1
    have hq := mem_pull.mp hz.2
    refine (gm_pull_g (LB.LinComb L f d) r (𝟙 Z) z p q hz.1 hz.2).trans ?_
    refine (gm_linComb L f d (𝟙 Z ≫ r) z _ _ hp hq).trans ?_
    refine Eq.trans ?_ ((gm_res (𝟙 Z) z _ hz _).trans
      (gm_linComb L (fun k => r ≫ f k) d (𝟙 Z) z _ _
        (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hp k)
        (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hq k))).symm
    simp only [Category.assoc]

private theorem gm_chartPull {Y : Scheme.{0}} {B C : LB Y}
    (P : ChartPull B C (𝟙 Y)) (z : Y) (p q : B.ι) (hp : z ∈ B.U p) (hq : z ∈ B.U q) :
    gm (𝟙 Y) z _ (B.g p q) = gm (𝟙 Y) z _ (C.g (P.idx p) (P.idx q)) := by
  rw [P.g p q, pullLE_id]
  exact gm_res (𝟙 Y) z (le_inf (inf_le_left.trans (P.le p))
    (inf_le_right.trans (P.le q))) ⟨hp, hq⟩ _

private def quotientProductChart {X Y : Scheme.{0}} (L : LB X) {I : Type} [Fintype I]
    (d : I → ℤ) {f₀ f₁ f₂ : I → (Y ⟶ X)} {B₀ B₁ B₂ : LB Y}
    (P₀ : ChartPull B₀ (LB.LinComb L f₀ d) (𝟙 Y))
    (P₁ : ChartPull B₁ (LB.LinComb L f₁ d) (𝟙 Y))
    (P₂ : ChartPull B₂ (LB.LinComb L f₂ d) (𝟙 Y)) :
    ChartPull ((twist B₁ B₂ 1).div B₀)
      (LB.LinComb L (Sum.elim f₁ (Sum.elim f₂ f₀)) (Sum.elim d (Sum.elim d fun k => - d k))) (𝟙 Y) := by
  let F := Sum.elim f₁ (Sum.elim f₂ f₀)
  let D := Sum.elim d (Sum.elim d fun k => - d k)
  let B := (twist B₁ B₂ 1).div B₀
  let idx (p : B.ι) := Sum.elim (P₁.idx p.1.1) (Sum.elim (P₂.idx p.1.2) (P₀.idx p.2))
  have hle (p : B.ι) : B.U p ≤ LB.wchart L F (idx p) := fun z hz => Set.mem_iInter.2 (by
    rintro (k | k | k)
    · exact Set.mem_iInter.1 (P₁.le _ hz.1.1) k
    · exact Set.mem_iInter.1 (P₂.le _ hz.1.2) k
    · exact Set.mem_iInter.1 (P₀.le _ hz.2) k)
  refine ⟨idx, hle, fun p q => ?_⟩
  rw [pullLE_id]
  apply unit_ext
  intro z hz
  have e₀ := (gm_chartPull P₀ z p.2 q.2 hz.1.2 hz.2.2).trans
    (gm_linComb L f₀ d (𝟙 Y) z _ _ (P₀.le _ hz.1.2) (P₀.le _ hz.2.2))
  have e₁ := (gm_chartPull P₁ z p.1.1 q.1.1 hz.1.1.1 hz.2.1.1).trans
    (gm_linComb L f₁ d (𝟙 Y) z _ _ (P₁.le _ hz.1.1.1) (P₁.le _ hz.2.1.1))
  have e₂ := (gm_chartPull P₂ z p.1.2 q.1.2 hz.1.1.2 hz.2.1.2).trans
    (gm_linComb L f₂ d (𝟙 Y) z _ _ (P₂.le _ hz.1.1.2) (P₂.le _ hz.2.1.2))
  have e₂' : gm (𝟙 Y) z _ ((transitionPower B₂ (-1)).g p.1.2 q.1.2) =
      gm (𝟙 Y) z _ (B₂.g p.1.2 q.1.2) ^ (-1 : ℤ) := map_zpow _ _ _
  have e₁₂ := (gm_div (transitionPower B₂ (-1)) B₁ (𝟙 Y) z p.1 q.1 ⟨hz.1.1, hz.2.1⟩).trans
    (congrArg₂ (fun a b => a * b⁻¹) e₁ (e₂'.trans (congrArg (· ^ (-1 : ℤ)) e₂)))
  refine ((gm_div B₀ (twist B₁ B₂ 1) (𝟙 Y) z p q hz).trans
    (congrArg₂ (fun a b => a * b⁻¹) e₁₂ e₀)).trans ?_
  refine Eq.trans ?_ ((gm_res (𝟙 Y) z _ hz _).trans
    (gm_linComb L F D (𝟙 Y) z _ _ (hle p hz.1) (hle q hz.2))).symm
  simp only [F, D, idx, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
    inv_inv, ← Finset.prod_inv_distrib, zpow_neg, zpow_one, _root_.mul_assoc]
  rfl

/-- The translation difference is additive as a line bundle. -/
theorem exists_iso_additive {K : Type} [Field K]
    {A : Over (Spec (.of K))} [GrpObj A] {L : LB A.left}
    (hA : IsAbelianScheme A) (hL : L.IsLB) (hAmp : RelAmple A L)
    (x : 𝟙_ (Over (Spec (.of K))) ⟶ A) :
    let M := LB.LinComb L (K := Fin 2) ![(translate A x).left, 𝟙 A.left] ![1, -1]
    ∃ w : LB.Iso (M.pull μ[A].left) (twist (M.pull (fst A A).left) (M.pull (snd A A).left) 1),
      w.IsGen := by
  let Z := A ⊗ A
  let p : Z ⟶ A := fst A A
  let q : Z ⟶ A := snd A A
  let m : Z ⟶ A := μ[A]
  let a := toUnit Z ≫ x
  let f : Fin 2 → (A.left ⟶ A.left) := ![(translate A x).left, 𝟙 A.left]
  let d : Fin 2 → ℤ := ![1, -1]
  let F (r : Z ⟶ A) := fun k => r.left ≫ f k
  have hm : p * q = m := by rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  have h (r : Z ⟶ A) : r ≫ translate A x = a * r := by
    change r ≫ ((toUnit A ≫ x) * 𝟙 A) = _
    rw [MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id]
  have h₀ : a * p * q = a * m := (_root_.mul_assoc _ _ _).trans (congrArg (a * ·) hm)
  obtain ⟨s, hs⟩ := exists_gen_additive_of_constant hA hL hAmp x p q
  let u := LB.invGen L _ _ s
  obtain ⟨v, hv, -⟩ := exists_gen_of_formEq hL
    (g := Sum.elim (F p) (Sum.elim (F q) (F m)))
    (d := Sum.elim d (Sum.elim d fun k => - d k))
    (fun U _ k => by
      simp only [f, d, F, Fintype.prod_sum_type, Fin.prod_univ_succ, Fin.prod_univ_zero,
        Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_succ,
        zpow_one, zpow_neg_one, neg_neg, _root_.mul_one, Category.comp_id]
      have h' (r : Z ⟶ A) : r.left ≫ (translate A x).left = (a * r).left :=
        congrArg Over.Hom.left (h r)
      rw [h' p, h' q, h' m, h₀, hm]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) u (invGen_isGen hs)
  exact (quotientProductChart L d (pullFormalChart L f d m.left)
    (pullFormalChart L f d p.left) (pullFormalChart L f d q.left)).exists_gen hv

end GlobalTheory.TranslateAdditive
