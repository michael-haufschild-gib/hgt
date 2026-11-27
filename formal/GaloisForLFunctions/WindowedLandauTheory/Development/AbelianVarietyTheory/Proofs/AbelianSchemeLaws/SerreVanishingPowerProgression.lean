import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ProjectivityFromRelativeAmple
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.AffineSectionCoordinates
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FormalProductPullback
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.CechCohomologyVanishing
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleCechIsomorphism
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleCechBaseChange
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleKunneth
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.OpenIsoCech
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.SerreVanishingTwists

/-! Every arithmetic progression of powers of a relatively ample bundle
has a common vanishing threshold for positive cohomology. -/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace HTGeometry
open GlobalTheory.LineBundleSections GlobalTheory.ProjectiveSections GlobalTheory.SchemeCohomology UpperTheory.Cb
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

namespace GlobalTheory.PrincipalSections

attribute [local instance] Over.cartesianMonoidalCategory

private def chart_progressionTwist {X Y : Scheme.{0}} (L : LB X) (π : Y ⟶ X)
    (N : ℕ) (r t : ℤ) :
    ChartPull (LB.LinComb L (fun _ : PUnit => π) (fun _ => r + (N : ℤ) * t))
      (twist (LB.LinComb L (fun _ : PUnit => π) (fun _ => r))
        (LB.LinComb L (fun _ : Fin N => π) (fun _ => 1)) t) (𝟙 Y) where
  idx i := (i, fun _ => i PUnit.unit)
  le i := le_inf le_rfl (fun _ h => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 h PUnit.unit)
  g i j := by
    rw [pullLE_id]
    let F : PUnit → (Y ⟶ X) := fun _ => π
    let G : Fin N → (Y ⟶ X) := fun _ => π
    let M := LB.LinComb L F (fun _ => r)
    let H := LB.LinComb L G (fun _ => 1)
    let a : Fin N → L.ι := fun _ => i PUnit.unit
    let b : Fin N → L.ι := fun _ => j PUnit.unit
    let U := L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)
    let W := LB.wchart L F i ⊓ LB.wchart L F j
    let V := LB.wchart L G a ⊓ LB.wchart L G b
    have wi : LB.wchart L F i ≤ H.U a := fun _ h =>
      Set.mem_iInter.2 fun _ => Set.mem_iInter.1 h PUnit.unit
    have wj : LB.wchart L F j ≤ H.U b := fun _ h =>
      Set.mem_iInter.2 fun _ => Set.mem_iInter.1 h PUnit.unit
    have hw : W ≤ V := le_inf (inf_le_left.trans wi) (inf_le_right.trans wj)
    let u := L.g (i PUnit.unit) (j PUnit.unit)
    let v : W ≤ π ⁻¹ᵁ U := le_inf
      (inf_le_left.trans (LB.wchart_le L F i PUnit.unit))
      (inf_le_right.trans (LB.wchart_le L F j PUnit.unit))
    have hP (z : ℤ) : (LB.LinComb L F (fun _ => z)).g i j = (pullLE π v u) ^ z := by
      change (∏ k : PUnit, _) = _
      rw [Fintype.prod_unique]
      exact congrArg (fun x : Γ(Y, W)ˣ => x ^ z) (res_pullU π U v u)
    have hH : res hw (H.g a b) = (pullLE π v u) ^ N := by
      let h (k : Fin N) : V ≤ π ⁻¹ᵁ U := le_inf
        (inf_le_left.trans (LB.wchart_le L G a k))
        (inf_le_right.trans (LB.wchart_le L G b k))
      change res hw (∏ k : Fin N, (pullLE π (h k) u) ^ (1 : ℤ)) = _
      simp only [map_prod, zpow_one, res_pullLE]
      exact (Finset.prod_const _).trans (congrArg (fun n => (pullLE π v u) ^ n) (Fintype.card_fin N))
    have e := res_twist_g (M := M) (H := H) t (i, a) (j, b)
      (W := W) (le_inf inf_le_left (inf_le_left.trans wi)) (le_inf inf_le_right (inf_le_right.trans wj))
    let z := pullLE π v u
    let g₀ : Γ(Y, W)ˣ := M.g i j
    have eM : res (le_rfl : W ≤ W) g₀ = z ^ r := (res_refl g₀).trans (hP r)
    have eH : (res hw (H.g a b)) ^ t = z ^ ((N : ℤ) * t) :=
      (congrArg (· ^ t) hH).trans
        ((congrArg (· ^ t) (zpow_natCast z N).symm).trans (zpow_mul z (N : ℤ) t).symm)
    have hpow : z ^ r * z ^ ((N : ℤ) * t) = z ^ (r + (N : ℤ) * t) :=
      (zpow_add z r ((N : ℤ) * t)).symm
    exact (hP _).trans (e.trans ((congrArg₂ (· * ·) eM eH).trans hpow)).symm

/-- A positive very ample power gives vanishing of each sufficiently high
term of the progression of powers starting at any fixed exponent. -/
theorem exists_cohomology_vanishing_progression {K : Type} [Field K]
    {A : Over (Spec (.of K))} [GrpObj A] [Smooth A.hom] {L : LB A.left}
    (hL : L.IsLB) (hAmp : RelAmple A L) (r : ℤ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ b : ℤ, ∀ t : ℤ, b ≤ t → ∀ k : ℕ,
      Subsingleton (CohomologyOn
        (toMod (LB.LinComb L (fun _ : PUnit => 𝟙 A.left) (fun _ => r + (N : ℤ) * t))) ⊤ (k + 1)) := by
  let O : (Spec (.of K)).Opens := ⊤
  let V := A.hom ⁻¹ᵁ O
  let π := V.ι
  let Y := V.toScheme
  let f := π ≫ A.hom
  let q := A.hom ∣_ O
  letI : IsIso π := inferInstanceAs (IsIso A.left.topIso.hom)
  letI : IsIso O.ι := inferInstanceAs (IsIso (Spec (.of K)).topIso.hom)
  letI : Smooth f := inferInstanceAs (Smooth (π ≫ A.hom))
  have hp := isProjOver_of_relAmple hL hAmp
  have hp' : IsProjOver f := hp.restrict_clopen V isClosed_univ
  letI : CompactSpace Y := hp'.compactSpace
  letI : Y.IsSeparated := hp'.isSeparated
  obtain ⟨N, hN, n, s, hc, hs⟩ := hAmp O (isAffineOpen_top _)
  let H := powOver A L O N
  let M := LB.LinComb L (fun _ : PUnit => π) (fun _ => r)
  have hH : H.IsLB := hL.linComb _ _
  have hM : M.IsLB := hL.linComb _ _
  choose u hu using fun i => (hs i).2
  have hf : q ≫ O.ι = f := morphismRestrict_ι _ _
  have hsurj (i : Fin (n + 1)) : letI := sectionAlgebra f (nonzeroLocus (s i))
      Function.Surjective (MvPolynomial.aeval (R := K) (u i)) := by
    have e := sectionAlgebra_comp_iso q O.ι _ (u i) (hu i).2
    rw [hf] at e
    exact e
  obtain ⟨b, hb⟩ := exists_twist_cech_exactAt_succ f hM hH s (fun i => (hs i).1) u
    (fun i => (hu i).1) hsurj
  obtain ⟨n', j, hj, hjf⟩ := hp
  letI := hj
  let W (i : Fin (n' + 1)) := j ⁻¹ᵁ PSpace.coordinateOpen K n' i
  let W' (i : Fin (n' + 1)) := π ⁻¹ᵁ W i
  have hcov : ⨆ i, W i = ⊤ := j.iSup_preimage_eq_top (PSpace.iSup_coordinateOpen K n')
  have ha (a : Finset (Fin (n' + 1))) (e : a.Nonempty) : IsAffineOpen (coverInter ⊤ W a) :=
    (coverInter_pull (π := j) (PSpace.coordinateOpen K n') a).symm ▸
      (PSpace.isAffineOpen_coordinateInter K n' e).preimage j
  have ha' (a : Finset (Fin (n' + 1))) (e : a.Nonempty) : IsAffineOpen (coverInter ⊤ W' a) :=
    (coverInter_pull (π := π) W a).symm ▸ (ha a e).preimage π
  refine ⟨N, hN, b, fun t ht k => ?_⟩
  let d : PUnit → ℤ := fun _ => r + (N : ℤ) * t
  let B := LB.LinComb L (fun _ : PUnit => 𝟙 A.left) d
  let D := LB.LinComb L (fun _ : PUnit => π) d
  let T := twist M H t
  have hB : B.IsLB := hL.linComb _ _
  have hD : D.IsLB := hL.linComb _ _
  have hT : T.IsLB := twist_isLB hM hH t
  have hTvan : Subsingleton (CohomologyOn (toMod T) ⊤ (k + 1)) :=
    (exactAt_cech_iff_subsingleton_cohomology f hT _ hc.ge
      (affine_coverInter_of_affine _ (fun i => (hs i).1)) _).mp (hb t ht k)
  have ht' : (cech f (toMod T) W').ExactAt (k + 1) :=
    (exactAt_cech_iff_subsingleton_cohomology f hT W' (π.iSup_preimage_eq_top hcov).ge ha' _).mpr hTvan
  let E := cechPullbackIso_of_isIso A.hom hB π W ha
  let Q : ChartPull D B π := by
    have he : (fun _ : PUnit => π ≫ 𝟙 A.left) = fun _ => π := funext fun _ => Category.comp_id π
    exact (congrArg (fun g => ChartPull (LB.LinComb L g d) B π) he).mp
      (ChartPull.linComb L (fun _ : PUnit => 𝟙 A.left) d π)
  obtain ⟨v, hv⟩ := (ChartPull.pull B π).iso_of_common Q hB
  obtain ⟨x, hx⟩ := (chart_progressionTwist L π N r t).iso_of_common (ChartPull.id T) hT
  let e := E ≪≫ cechIsoOfIsGen f W' (hB.pull π) hD hv ≪≫ cechIsoOfIsGen f W' hD hT hx
  exact (exactAt_cech_iff_subsingleton_cohomology A.hom hB W hcov.ge ha _).mp (ht'.of_iso e.symm)

end GlobalTheory.PrincipalSections
