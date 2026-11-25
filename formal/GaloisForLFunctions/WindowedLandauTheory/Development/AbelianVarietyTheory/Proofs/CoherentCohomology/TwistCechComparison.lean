import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.TwistedSectionLocalization
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.FlatLineBundleCech
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LinearCechMaps
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.ZeroTwistSections

/-! Degree zero in the graded localization complex recovers the Čech complex of the line bundle. -/

noncomputable section

open AlgebraicGeometry CategoryTheory DirectSum HTGeometry MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.SchemeCohomology

namespace GlobalTheory.LineBundleSections

variable {R : Type} [CommRing R] {X : Scheme.{0}} [CompactSpace X] [X.IsSeparated]
  (f : X ⟶ Spec (CommRingCat.of R)) {M H : LB X} (hM : M.IsLB) (hH : H.IsLB)
  {ι : Type} (s : ι → H.Sec)

local notation "U" => fun i => nonzeroLocus (s i)
local notation "V" => coverInter ⊤ U
local notation "B" => gradedTwistSections f M ⊤ s
local notation "D" => GrSum.grading (twistSections_commute f M ⊤ s)
local notation "G" => fun I => gradedTwistSections f M (V I) s
local notation "E" => fun I => GrSum.grading (twistSections_commute f M (V I) s)

include hM hH in
private theorem isLocalized_coverInter (I : Finset ι) :
    IsLocalizedModule.Away (xProd R I) (gradedTwistSections_res f M s (le_top : V I ≤ ⊤)) := by
  let T (W : X.Opens) : Prop := IsLocalizedModule.Away (xProd R I)
    (gradedTwistSections_res f M s (le_top : W ≤ ⊤))
  have e : V I = nonzeroLocus (sectionProduct s I) := by
    simp only [coverInter, top_inf_eq, Finset.inf_eq_iInf, nonzeroLocus_sectionProduct hH]
  exact (congrArg T e.symm).mp (isLocalizedModule_gradedTwistSections f hM hH s I)

private def chartLoc (I : Finset ι) : LocalizedModule.Away (xProd R I) B ≃ₗ[MvPolynomial ι R] G I :=
  letI := isLocalized_coverInter f hM hH s I
  IsLocalizedModule.iso (Submonoid.powers (xProd R I)) (gradedTwistSections_res f M s le_top)

private theorem chartLoc_frac_zero (I : Finset ι) (b : B) :
    chartLoc f hM hH s I (ModuleFraction.frac (xProd R I) 0 b) =
      gradedTwistSections_res f M s (le_top : V I ≤ ⊤) b := by
  letI := isLocalized_coverInter f hM hH s I
  rw [ModuleFraction.frac_zero]
  exact IsLocalizedModule.iso_mk_one _ _ b

private theorem chartLoc_isGraded (I : Finset ι) :
    IsGradedMap (homLoc D I) (E I) (chartLoc f hM hH s I).toLinearMap := by
  let ρ := gradedTwistSections_res f M s (le_top : V I ≤ ⊤)
  letI := isLocalized_coverInter f hM hH s I
  intro n z hz
  obtain ⟨k, b, hb, rfl⟩ := exists_frac_of_mem_homLoc D hz
  let y := chartLoc f hM hH s I (ModuleFraction.frac (xProd R I) k b)
  have he : xProd R I ^ k • y = ρ b := by
    rw [show y = chartLoc f hM hH s I (ModuleFraction.frac (xProd R I) k b) from rfl,
      ← map_smul, ModuleFraction.pow_smul_frac, chartLoc_frac_zero]
  have hp := proj_smul_of_mem (D := E I) (xProd_pow_mem R I k) n y
  have hr : ρ b ∈ E I (n + k * I.card) :=
    gradedTwistSections_res_isGraded f M s le_top hb
  rw [he, gradedProj_of_mem _ hr] at hp
  have hy : gradedProj (E I) n y = y :=
    IsLocalizedModule.smul_injective ρ (⟨xProd R I ^ k, k, rfl⟩ : Submonoid.powers (xProd R I))
      (hp.symm.trans he.symm)
  exact hy ▸ gradedProj_mem (E I) n y

private theorem chartLoc_restrict {I J : Finset ι} (h : I ⊆ J)
    (z : LocalizedModule.Away (xProd R I) B) :
    (chartLoc f hM hH s J) (ModuleFraction.restrict (xProd_dvd R h) z) =
      gradedTwistSections_res f M s (coverInter_anti h : V J ≤ V I) (chartLoc f hM hH s I z) := by
  let e := chartLoc f hM hH s J
  let ρ := gradedTwistSections_res f M s (coverInter_anti h : V J ≤ V I)
  obtain ⟨k, b, rfl⟩ := ModuleFraction.exists_frac z
  suffices he : e.symm (ρ (chartLoc f hM hH s I (ModuleFraction.frac (xProd R I) k b))) =
      ModuleFraction.restrict (xProd_dvd R h) (ModuleFraction.frac (xProd R I) k b) by
    exact (congrArg e he).symm.trans (e.apply_symm_apply _)
  let a := xProd R I
  have hu := (ModuleFraction.isUnit_smul_of_dvd (M := B) (xProd_dvd R h)).pow k
  rw [← map_pow] at hu
  apply (Module.End.isUnit_iff.1 hu).1
  change a ^ k • e.symm (ρ (chartLoc f hM hH s I (ModuleFraction.frac a k b))) =
    a ^ k • ModuleFraction.restrict (xProd_dvd R h) (ModuleFraction.frac a k b)
  rw [← map_smul, ← map_smul, ← map_smul, ← map_smul, ModuleFraction.pow_smul_frac,
    ModuleFraction.restrict_frac_zero, chartLoc_frac_zero]
  apply e.symm_apply_eq.2
  rw [show e (ModuleFraction.frac (xProd R J) 0 b) =
    gradedTwistSections_res f M s (le_top : V J ≤ ⊤) b from chartLoc_frac_zero f hM hH s J b]
  exact LinearMap.congr_fun (gradedTwistSections_res_comp f M s le_top (coverInter_anti h)) b

/-- Homogeneous fractions of degree zero correspond to untwisted sections on each intersection. -/
private def chartPiece (I : Finset ι) : homLoc D I 0 ≃ₗ[R] TwistSections f M H (V I) 0 := by
  let e := chartLoc f hM hH s I
  let φ : homLoc D I 0 →ₗ[R] E I 0 :=
    ((e.toLinearMap.restrictScalars R).domRestrict _).codRestrict _
      fun a => chartLoc_isGraded f hM hH s I a.2
  refine (LinearEquiv.ofBijective φ ⟨fun a b hab => Subtype.ext (e.injective (congrArg Subtype.val hab)),
    ?_⟩).trans (GrSum.pieceEquiv (twistSections_commute f M (V I) s) 0).symm
  intro a
  let z := e.symm a.1
  refine ⟨⟨gradedProj (homLoc D I) 0 z, gradedProj_mem _ _ _⟩, Subtype.ext ?_⟩
  change e (gradedProj (homLoc D I) 0 z) = a.1
  rw [← (chartLoc_isGraded f hM hH s I).proj_apply, LinearEquiv.toLinearMap_apply,
    LinearEquiv.apply_symm_apply, gradedProj_of_mem _ a.2]

private theorem chartPiece_apply (I : Finset ι) (z : homLoc D I 0) :
    GrSum.of (twistSections_commute f M (V I) s) 0 (chartPiece f hM hH s I z) =
      chartLoc f hM hH s I z.1 := by
  change ((GrSum.pieceEquiv _ 0) ((GrSum.pieceEquiv _ 0).symm
    (⟨chartLoc f hM hH s I z.1, chartLoc_isGraded f hM hH s I z.2⟩ : E I 0))).1 = _
  rw [LinearEquiv.apply_symm_apply]

private theorem chartPiece_natural {I J : Finset ι} (h : I ⊆ J) (z : homLoc D I 0) :
    chartPiece f hM hH s J (homLocRes D h 0 z) =
      twistSections_res f M (coverInter_anti h : V J ≤ V I) 0 (chartPiece f hM hH s I z) := by
  apply GrSum.of_injective (twistSections_commute f M (V J) s) 0
  rw [chartPiece_apply, ← gradedTwistSections_res_of s (coverInter_anti h), chartPiece_apply]
  exact chartLoc_restrict f hM hH s h z.1

variable [DecidableEq ι] [LinearOrder ι]

private def untwistPiece (I : Finset ι) :
    letI := sectionDatumModule f (toMod M) U I
    TwistSections f M H (V I) 0 ≃ₗ[R] (sectionDatum (toMod M) U).obj I := by
  letI := sectionDatumModule f (toMod M) U I
  letI := sectionAlgebra f (V I)
  let e := (zeroTwistEquiv (V := V I) hM hH).symm
  exact { e.toAddEquiv with
    map_smul' r z := e.map_smul (algebraMap R Γ(X, V I) r) z }

private theorem untwistPiece_natural {I J : Finset ι} (h : I ⊆ J)
    (z : TwistSections f M H (V I) 0) :
    (sectionDatum (toMod M) U).res h (untwistPiece f hM hH s I z) =
      untwistPiece f hM hH s J (twistSections_res f M (coverInter_anti h : V J ≤ V I) 0 z) := by
  let eI := zeroTwistEquiv (V := V I) hM hH
  let eJ := zeroTwistEquiv (V := V J) hM hH
  let i := homOfLE (coverInter_anti h : V J ≤ V I)
  apply eJ.injective
  change eJ ((toMod M).presheaf.map i.op (eI.symm z)) =
    eJ (eJ.symm ((toMod (twist M H 0)).presheaf.map i.op z))
  rw [eJ.apply_symm_apply, zeroTwistEquiv_restrict, eI.apply_symm_apply]

include hM hH in
/-- Degree-zero localized fractions recover the line-bundle section complex, including
its restriction maps. -/
theorem nonempty_gradedCech_iso :
    Nonempty (gradedCech D 0 ≅ cech f (toMod M) U) := by
  letI (I : Finset ι) := sectionDatumModule f (toMod M) U I
  let e (I : Finset ι) := (chartPiece f hM hH s I).trans (untwistPiece f hM hH s I)
  let φ : (homLocDatum D 0).Hom (sectionDatum (toMod M) U) :=
    { app := fun I => (e I).toLinearMap.toAddMonoidHom
      comm := fun h z => by
        change (sectionDatum (toMod M) U).res h (untwistPiece f hM hH s _
          (chartPiece f hM hH s _ z)) =
          untwistPiece f hM hH s _ (chartPiece f hM hH s _ (homLocRes D h 0 z))
        rw [chartPiece_natural f hM hH s h, untwistPiece_natural f hM hH s h] }
  have hφ I r z : φ.app I (r • z) = r • φ.app I z := (e I).map_smul r z
  let g := FinsetCechDatum.linearCochainMap
    (fun h => homLocDatum_res_smul D h 0) (res_base_smul f (toMod M) U) φ hφ
  haveI : IsIso g := FinsetCechDatum.isIso_linearCochainMap _ _ _ _ fun I _ => (e I).bijective
  exact ⟨asIso g⟩

end GlobalTheory.LineBundleSections
