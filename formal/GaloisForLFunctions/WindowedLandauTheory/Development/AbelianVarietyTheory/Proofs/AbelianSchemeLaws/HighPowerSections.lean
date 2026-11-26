import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.PowerBundleCharts
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FormalSectionModule
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ProjectivityFromRelativeAmple
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.NonzeroTwistSections

/-! Relative ampleness supplies nonzero sections in all sufficiently large
powers in an arithmetic progression starting at the original bundle. -/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.LineBundleSections UpperTheory.Cb
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.MulSplit

attribute [local instance] Over.cartesianMonoidalCategory

private theorem pullSec_coord_ne_zero {X Y Z : Scheme.{0}} {L : LB X} {I : Type} [Fintype I]
    {f : I → (Y ⟶ X)} {d : I → ℤ} (s : (LB.LinComb L f d).Sec)
    (r : Z ⟶ Y) [IsIso r] (j : I → L.ι) (hj : s.f j ≠ 0) : (pullSec s r).f j ≠ 0 := by
  let W := LB.wchart L (fun i => r ≫ f i) j
  let U := LB.wchart L f j
  have h₁ : W ≤ r ⁻¹ᵁ U := fun _ hz => Set.mem_iInter.2 fun i => Set.mem_iInter.1 hz i
  have h₂ : r ⁻¹ᵁ U ≤ W := fun _ hz => Set.mem_iInter.2 fun i => Set.mem_iInter.1 hz i
  intro h
  have e := congrArg (resG Z h₂) h
  change resG Z h₂ (resG Z h₁ (r.app U (s.f j))) = resG Z h₂ 0 at e
  rw [resG_resG, resG_self, map_zero] at e
  exact hj ((ConcreteCategory.bijective_of_isIso (r.app U)).1 (e.trans (map_zero (r.app U).hom).symm))

/-- Choose a nonvanishing affine chart of a positive power and clear denominators
of a nonzero local section of the original bundle. -/
theorem exists_nontrivial_high_power_of_relAmple {K : Type} [Field K]
    {A : Over (Spec (.of K))} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (hAmp : RelAmple A L) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ k : ℕ, ∀ j : ℕ, k ≤ j →
      Nontrivial (Sg L A.hom (Finsupp.single (𝟙 A.left) (1 + (j : ℤ) * (N : ℤ)))) := by
  let O : (Spec (.of K)).Opens := ⊤
  obtain ⟨N, hN, n, s, hcov, hs⟩ := hAmp O (isAffineOpen_top _)
  let V := A.hom ⁻¹ᵁ O
  let π := V.ι
  let Y := V.toScheme
  letI : IsIso π := inferInstanceAs (IsIso A.left.topIso.hom)
  let r : A.left ⟶ Y := inv π
  haveI : IsIso r := inferInstanceAs (IsIso (inv π))
  let y : Y := r (η[A].left (IsLocalRing.closedPoint K))
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
    (hcov.ge (show y ∈ (⊤ : Y.Opens) from trivial))
  let M := L.pull π
  have hM : M.IsLB := hL.pull π
  let s₀ : (transitionPower M (N : ℤ)).Sec :=
    refineCoordinates (ChartPull.repeatedPullbackPower L π N) (s i)
  have hlocus : nonzeroLocus s₀ = nonzeroLocus (s i) :=
    nonzeroLocus_refineCoordinates (transitionPower_isLB hM _) _ _
  have hproj : IsProjOver (π ≫ A.hom) :=
    (ProjectiveSections.isProjOver_of_relAmple hL hAmp).restrict_clopen V isClosed_univ
  letI : CompactSpace Y := hproj.compactSpace
  letI : Y.IsSeparated := hproj.isSeparated
  obtain ⟨k, hk⟩ := exists_nonzero_high_twist hM hM s₀
    (hlocus.symm ▸ (hs i).1) ⟨y, hlocus.symm ▸ hi⟩
  refine ⟨N, hN, k, fun j hj => ?_⟩
  let t := (j : ℤ) * (N : ℤ)
  obtain ⟨b, hb⟩ := hk j hj
  let B := twist M M t
  let b₀ : B.Sec := globalCoordinates b
  let P := ChartPull.singlePullbackTwist L π t
  let s' := refineCoordinates P b₀
  have hs' : ∃ i, s'.f i ≠ 0 := by
    by_contra! h
    apply hb
    apply globalCoordinates.injective
    have he : (globalCoordinates b).f = (globalCoordinates (0 : Γ(toMod B, ⊤))).f :=
      funext fun i => (coord_eq_zero_of_refineCoordinates ((hL.linComb _ _) : (LB.LinComb L _ _).IsLB)
        P b₀ h i).trans (by simp only [globalCoordinates_apply, coord_zero, map_zero])
    generalize globalCoordinates b = v at he ⊢
    generalize globalCoordinates (0 : Γ(toMod B, ⊤)) = w at he ⊢
    cases v
    cases w
    cases he
    rfl
  let Q (f : PUnit → (A.left ⟶ A.left)) := ∃ u : (LB.LinComb L f (fun _ => 1 + t)).Sec, ∃ i, u.f i ≠ 0
  obtain ⟨l, hl⟩ := hs'
  have he : (fun _ : PUnit => r ≫ π) = fun _ => 𝟙 A.left := funext fun _ => IsIso.inv_hom_id π
  have hQ : Q (fun _ => r ≫ π) := ⟨pullSec s' r, l, pullSec_coord_ne_zero s' r l hl⟩
  obtain ⟨u, i, hu⟩ : Q (fun _ => 𝟙 A.left) := he ▸ hQ
  have hsum : dv (fun _ : PUnit => 𝟙 A.left) (fun _ => 1 + t) =
      Finsupp.single (𝟙 A.left) (1 + t) := Fintype.sum_unique _
  have hu₀ : ev A.hom u ≠ 0 := by
    intro hz
    let z : (LB.LinComb L (fun _ : PUnit => 𝟙 A.left) (fun _ => 1 + t)).Sec :=
      ⟨fun _ => 0, fun _ _ => by simp only [map_zero, mul_zero]⟩
    exact hu (ev_inj hL (hz.trans (ev_zero (s := z) (fun _ => rfl)).symm) i)
  let v : Sg L A.hom (Finsupp.single (𝟙 A.left) (1 + t)) :=
    ⟨ev A.hom u, (mem_Sg hL hsum _).2 ⟨u, rfl⟩⟩
  exact ⟨⟨v, 0, fun hz => hu₀ (congrArg Subtype.val hz)⟩⟩

end GlobalTheory.MulSplit
