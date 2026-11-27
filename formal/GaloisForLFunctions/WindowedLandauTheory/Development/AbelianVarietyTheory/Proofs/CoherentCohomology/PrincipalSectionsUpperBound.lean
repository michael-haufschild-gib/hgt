import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.MumfordBundleCohomology
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.PowerBundleCharts
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.AdditiveLineBundleAcyclic

/-! A principal polarization has at most one independent global section. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open TopologicalSpace HTGeometry GlobalTheory.LineBundleSections
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Finset.HasAntidiagonal
open scoped CategoryTheory.Obj

namespace GlobalTheory.PrincipalSections

attribute [local instance] Over.cartesianMonoidalCategory

private def chartTwistInverse {X Y : Scheme.{0}} (L : LB X) (a b : Y ⟶ X) :
    ChartPull (twist (L.pull a) ((transitionPower L (-1)).pull b) 1)
      (LB.LinComb L (K := Fin 2) ![a, b] ![1, -1]) (𝟙 Y) := by
  let B := (transitionPower L (-1)).pull b
  let T := twist (L.pull a) B 1
  let F : Fin 2 → (Y ⟶ X) := ![a, b]
  let d : Fin 2 → ℤ := ![1, -1]
  let idx (p : T.ι) : Fin 2 → L.ι := ![p.1 PUnit.unit, p.2 PUnit.unit]
  have le (p : T.ι) : T.U p ≤ LB.wchart L F (idx p) := fun _ hy =>
    Set.mem_iInter.mpr (Fin.forall_fin_two.mpr
      ⟨Set.mem_iInter.mp hy.1 PUnit.unit, Set.mem_iInter.mp hy.2 PUnit.unit⟩)
  refine ⟨idx, le, fun p q => ?_⟩
  rw [pullLE_id]
  apply unit_ext
  intro z hz
  have e₁ := gm_pull_g L a (𝟙 Y) z p.1 q.1 hz.1.1 hz.2.1
  have e₂ := (gm_pull_g (transitionPower L (-1)) b (𝟙 Y) z p.2 q.2 hz.1.2 hz.2.2).trans
    (map_zpow _ _ (-1 : ℤ))
  have e₃ : gm (𝟙 Y) z _ ((transitionPower B (-1)).g p.2 q.2) =
      gm (𝟙 Y) z _ (B.g p.2 q.2) ^ (-1 : ℤ) := map_zpow _ _ _
  refine ((gm_div (transitionPower B (-1)) (L.pull a) (𝟙 Y) z p q hz).trans
    (congrArg₂ (fun u v => u * v⁻¹) e₁ (e₃.trans (congrArg (· ^ (-1 : ℤ)) e₂)))).trans ?_
  refine Eq.trans ?_ ((gm_res (𝟙 Y) z _ hz _).trans
    (gm_linComb L F d (𝟙 Y) z _ _ (le p hz.1) (le q hz.2))).symm
  rw [Fin.prod_univ_two]
  refine congrArg₂ (· * ·) (zpow_one _).symm ?_
  rw [zpow_neg_one, inv_inv]
  rfl

/-- The addition shear expresses the Mumford bundle as an external
product with the inverse polarization. Künneth and concentration in one
degree bound the dimension of global sections by one. -/
theorem finrank_globalSections_le_one {K : Type} [Field K] [IsAlgClosed K]
    {A : Over (Spec (.of K))} [GrpObj A] {L : LB A.left}
    (hA : IsAbelianScheme A) (hL : L.IsLB) (hAmp : RelAmple A L) (hK : KTriv A L)
    (d : ℕ) [SmoothOfRelativeDimension d A.hom] :
    letI := sectionBaseModule A.hom (toMod L) ⊤
    Module.finrank K Γ(toMod L, ⊤) ≤ 1 := by
  letI := sectionBaseModule A.hom (toMod L) ⊤
  let Z := A ⊗ A
  let p := (fst A A).left
  let q := (snd A A).left
  let m := (translPt A (𝟙 A)).left
  let N := transitionPower L (-1)
  let M := translDiff A L (𝟙 A)
  have hN : N.IsLB := transitionPower_isLB hL _
  have hM : M.IsLB := hL.linComb _ _
  have H : IsPullback p q A.hom A.hom := IsPullback.of_hasPullback _ _
  have H' : IsPullback m q A.hom A.hom := by
    simpa only [m, translPt, Category.comp_id, lift_fst_snd, Category.id_comp] using
      AbLaw.isPullback_mul_snd A
  have hp := ProjectiveSections.isProjOver_of_relAmple hL hAmp
  have hpZ := ProjectiveSections.isProjOver_product H hp hp
  letI : CompactSpace A.left := hp.compactSpace
  letI : CompactSpace Z.left := hpZ.compactSpace
  letI : A.left.IsSeparated := hp.isSeparated
  letI : Z.left.IsSeparated := hpZ.isSeparated
  letI : HasExt.{0} (TopCat.Sheaf AddCommGrpCat.{0} Z.left) := hasExt_of_enoughInjectives _
  obtain ⟨I, hI, U, j, hU, hj, cU⟩ := exists_finite_affine_refinement hL
  obtain ⟨J, hJ, W, _, hW, _, cW⟩ := exists_finite_affine_refinement (LB.isLB_trivial Z.left)
  letI : Fintype I := hI
  letI : Fintype J := hJ
  letI : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  letI : LinearOrder J := LinearOrder.lift' (Fintype.equivFin J) (Fintype.equivFin J).injective
  let C := cech A.hom (toMod L) U
  let D := cech A.hom (toMod N) U
  have hFinL n : Module.Finite K (C.homology n) :=
    cech_homology_finite A.hom hL U cU.ge (affine_coverInter_of_affine U hU) hp n
  have hFinN n : Module.Finite K (D.homology n) :=
    cech_homology_finite A.hom hN U cU.ge (affine_coverInter_of_affine U hU) hp n
  let e := cechHomologyZeroEquiv A.hom (toMod L) U cU
  rw [← e.finrank_eq]
  refine le_one_of_convolution (fun n => Module.finrank K (C.homology n))
    (fun n => Module.finrank K (D.homology n)) d (fun n => ?_)
  have he := finrank_cech_externalProduct U U W H' hL hN hU hU hW
    (fun i => ⟨j i, hj i⟩) (fun i => ⟨j i, hj i⟩) cU cU cW hFinL hFinN n
  have hf : m ≫ A.hom = Z.hom := Over.w (translPt A (𝟙 A))
  rw [hf] at he
  obtain ⟨w, hw⟩ := (chartTwistInverse L m q).iso_of_common (ChartPull.id M) hM
  let i := cechIsoOfIsGen Z.hom W (twist_isLB (hL.pull m) (hN.pull q) 1) hM hw
  exact he.symm.trans (((HomologicalComplex.homologyMapIso i n).toLinearEquiv.finrank_eq).trans
    (MumfordFibre.finrank_cech_universal_translation hA hL hAmp hK d W hW cW n))

end GlobalTheory.PrincipalSections
