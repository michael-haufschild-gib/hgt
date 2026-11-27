import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.TwistedSectionLocalization
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.FlatLineBundleCech
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedCechComplex
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LinearCechMaps

/-! Homogeneous localizations give the sections of each twist on intersections
of the coordinate charts, compatibly with restriction. -/

noncomputable section

open AlgebraicGeometry CategoryTheory DirectSum HTGeometry MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.SchemeCohomology

namespace GlobalTheory.LineBundleSections

variable {R : Type} [CommRing R] {X : Scheme.{0}} [CompactSpace X] [X.IsSeparated]
  (f : X ⟶ Spec (CommRingCat.of R)) {M H : LB X} (hM : M.IsLB) (hH : H.IsLB)
  {ι : Type} (s : ι → H.Sec)

local notation "coordinateOpens" => fun i => nonzeroLocus (s i)
local notation "intersectionOpen" => coverInter ⊤ coordinateOpens
local notation "globalSections" => gradedTwistSections f M ⊤ s
local notation "globalGrading" => GrSum.grading (twistSections_commute f M ⊤ s)
local notation "intersectionSections" => fun I => gradedTwistSections f M (intersectionOpen I) s
local notation "intersectionGrading" => fun I => GrSum.grading (twistSections_commute f M (intersectionOpen I) s)

include hM hH in
private theorem isLocalized_coverInter (I : Finset ι) :
    IsLocalizedModule.Away (xProd R I) (gradedTwistSections_res f M s (le_top : intersectionOpen I ≤ ⊤)) := by
  let T (W : X.Opens) : Prop := IsLocalizedModule.Away (xProd R I)
    (gradedTwistSections_res f M s (le_top : W ≤ ⊤))
  have e : intersectionOpen I = nonzeroLocus (sectionProduct s I) := by
    simp only [coverInter, top_inf_eq, Finset.inf_eq_iInf, nonzeroLocus_sectionProduct hH]
  exact (congrArg T e.symm).mp (isLocalizedModule_gradedTwistSections f hM hH s I)

private def chartLoc (I : Finset ι) : LocalizedModule.Away (xProd R I) globalSections ≃ₗ[MvPolynomial ι R] intersectionSections I :=
  letI := isLocalized_coverInter f hM hH s I
  IsLocalizedModule.iso (Submonoid.powers (xProd R I)) (gradedTwistSections_res f M s le_top)

private theorem chartLoc_frac_zero (I : Finset ι) (b : globalSections) :
    chartLoc f hM hH s I (ModuleFraction.frac (xProd R I) 0 b) =
      gradedTwistSections_res f M s (le_top : intersectionOpen I ≤ ⊤) b := by
  letI := isLocalized_coverInter f hM hH s I
  rw [ModuleFraction.frac_zero]
  exact IsLocalizedModule.iso_mk_one _ _ b

private theorem chartLoc_isGraded (I : Finset ι) :
    IsGradedMap (homLoc globalGrading I) (intersectionGrading I) (chartLoc f hM hH s I).toLinearMap := by
  let ρ := gradedTwistSections_res f M s (le_top : intersectionOpen I ≤ ⊤)
  letI := isLocalized_coverInter f hM hH s I
  intro n z hz
  obtain ⟨k, hk⟩ := exists_frac_of_mem_homLoc globalGrading hz
  obtain ⟨b, hb, rfl⟩ := hk k le_rfl
  let y := chartLoc f hM hH s I (ModuleFraction.frac (xProd R I) k b)
  have he : xProd R I ^ k • y = ρ b := by
    rw [show y = chartLoc f hM hH s I (ModuleFraction.frac (xProd R I) k b) from rfl,
      ← map_smul, ModuleFraction.pow_smul_frac, chartLoc_frac_zero]
  have hp := proj_smul_of_mem (D := intersectionGrading I) (xProd_pow_mem R I k) n y
  have hr : ρ b ∈ intersectionGrading I (n + k * I.card) :=
    gradedTwistSections_res_isGraded f M s le_top hb
  rw [he, gradedProj_of_mem _ hr] at hp
  have hy : gradedProj (intersectionGrading I) n y = y :=
    IsLocalizedModule.smul_injective ρ (⟨xProd R I ^ k, k, rfl⟩ : Submonoid.powers (xProd R I))
      (hp.symm.trans he.symm)
  change y ∈ intersectionGrading I n
  exact hy ▸ gradedProj_mem (intersectionGrading I) n y

private theorem chartLoc_restrict {I J : Finset ι} (h : I ⊆ J)
    (z : LocalizedModule.Away (xProd R I) globalSections) :
    (chartLoc f hM hH s J) (ModuleFraction.restrict (xProd_dvd R h) z) =
      gradedTwistSections_res f M s (coverInter_anti h : intersectionOpen J ≤ intersectionOpen I) (chartLoc f hM hH s I z) := by
  let e := chartLoc f hM hH s J
  let ρ := gradedTwistSections_res f M s (coverInter_anti h : intersectionOpen J ≤ intersectionOpen I)
  let S := MvPolynomial ι R
  let N := LocalizedModule.Away (xProd R J) globalSections
  let u := e.symm.toLinearMap.comp (ρ.comp (chartLoc f hM hH s I).toLinearMap)
  have hunit (a : Submonoid.powers (xProd R I)) :
      IsUnit (algebraMap S (Module.End S N) (a : S)) := by
    obtain ⟨_, k, rfl⟩ := a
    rw [map_pow]
    exact (ModuleFraction.isUnit_smul_of_dvd (M := globalSections) (xProd_dvd R h)).pow k
  have hc : u.comp (LocalizedModule.mkLinearMap (Submonoid.powers (xProd R I)) globalSections) =
      LocalizedModule.mkLinearMap (Submonoid.powers (xProd R J)) globalSections := by
    apply LinearMap.ext
    intro b
    rw [← ModuleFraction.frac_zero, ← ModuleFraction.frac_zero]
    change e.symm (ρ (chartLoc f hM hH s I (ModuleFraction.frac (xProd R I) 0 b))) =
      ModuleFraction.frac (xProd R J) 0 b
    rw [chartLoc_frac_zero]
    apply e.symm_apply_eq.2
    exact (LinearMap.congr_fun (gradedTwistSections_res_comp f M s le_top (coverInter_anti h)) b).trans
      (chartLoc_frac_zero f hM hH s J b).symm
  have he : u = ModuleFraction.restrict (xProd_dvd R h) :=
    IsLocalizedModule.ext (Submonoid.powers (xProd R I)) (LocalizedModule.mkLinearMap _ globalSections)
      hunit (hc.trans (ModuleFraction.restrict_comp_mkLinearMap (xProd_dvd R h)).symm)
  exact (congrArg e (LinearMap.congr_fun he z)).symm.trans (e.apply_symm_apply _)

/-- Homogeneous fractions of degree `t` correspond to sections of the `t`-th twist. -/
def twistChartPiece (I : Finset ι) (t : ℤ) :
    homLoc globalGrading I t ≃ₗ[R] TwistSections f M H (intersectionOpen I) t := by
  let e := chartLoc f hM hH s I
  let φ : homLoc globalGrading I t →ₗ[R] intersectionGrading I t :=
    ((e.toLinearMap.restrictScalars R).domRestrict _).codRestrict _
      fun a => chartLoc_isGraded f hM hH s I a.2
  refine (LinearEquiv.ofBijective φ ⟨fun a b hab => Subtype.ext (e.injective (congrArg Subtype.val hab)),
    ?_⟩).trans (GrSum.pieceEquiv (twistSections_commute f M (intersectionOpen I) s) t).symm
  intro a
  let z := e.symm a.1
  refine ⟨⟨gradedProj (homLoc globalGrading I) t z, gradedProj_mem _ _ _⟩, Subtype.ext ?_⟩
  change e (gradedProj (homLoc globalGrading I) t z) = a.1
  have hp := (chartLoc_isGraded f hM hH s I).proj_apply t z
  change gradedProj (intersectionGrading I) t (e z) = e (gradedProj (homLoc globalGrading I) t z) at hp
  exact hp.symm.trans ((congrArg (gradedProj (intersectionGrading I) t) (e.apply_symm_apply a.1)).trans
    (gradedProj_of_mem _ a.2))

private theorem twistChartPiece_apply (I : Finset ι) (t : ℤ) (z : homLoc globalGrading I t) :
    GrSum.of (twistSections_commute f M (intersectionOpen I) s) t (twistChartPiece f hM hH s I t z) =
      chartLoc f hM hH s I z.1 := by
  let e := GrSum.pieceEquiv (twistSections_commute f M (intersectionOpen I) s) t
  let y : intersectionGrading I t :=
    ⟨chartLoc f hM hH s I z.1, chartLoc_isGraded f hM hH s I z.2⟩
  change (e (e.symm y)).1 = y.1
  exact congrArg Subtype.val (e.apply_symm_apply y)

theorem twistChartPiece_natural {I J : Finset ι} (h : I ⊆ J) (t : ℤ) (z : homLoc globalGrading I t) :
    twistChartPiece f hM hH s J t (homLocRes globalGrading h t z) =
      twistSections_res f M (coverInter_anti h : intersectionOpen J ≤ intersectionOpen I) t
        (twistChartPiece f hM hH s I t z) := by
  apply GrSum.of_injective (twistSections_commute f M (intersectionOpen J) s) t
  rw [twistChartPiece_apply, ← gradedTwistSections_res_of f M s (coverInter_anti h), twistChartPiece_apply]
  exact chartLoc_restrict f hM hH s h z.1

end GlobalTheory.LineBundleSections
