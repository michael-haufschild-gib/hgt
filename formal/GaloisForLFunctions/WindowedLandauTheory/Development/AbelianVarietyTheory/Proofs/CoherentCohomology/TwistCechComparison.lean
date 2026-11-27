import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.TwistCechCharts
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.ZeroTwistSections

/-! Degree zero in the graded localization complex recovers the Čech complex of the line bundle. -/

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
local notation "globalGrading" => GrSum.grading (twistSections_commute f M ⊤ s)

variable [DecidableEq ι] [LinearOrder ι]

include hM hH in
/-- The degree-`t` localizations are separated on the cover by the nonvanishing opens. -/
theorem gradedTwistSections_exactBot (t : ℤ) (hcov : ⊤ ≤ ⨆ i, nonzeroLocus (s i)) :
    (homLocDatum (ι := ι) globalGrading t).ExactBot := by
  let F := sectionDatum (toMod (twist M H t)) coordinateOpens
  let e (I : Finset ι) := twistChartPiece f hM hH s I t
  let φ : (homLocDatum (ι := ι) globalGrading t).Hom F :=
    { app := fun I => (e I).toAddMonoidHom
      comm := fun h z => (twistChartPiece_natural f hM hH s h t z).symm }
  have hF : F.ExactBot := sheafCech_exactBot _ hcov
  intro c hc hd
  have hb : F.IsBot (φ.onCochain c) := by
    intro I hI
    change φ.app I (c I) = 0
    rw [hc I hI, map_zero]
  have hδ : F.d (φ.onCochain c) = 0 := by
    rw [φ.d_onCochain, hd]
    funext I
    exact map_zero (φ.app I)
  have hzero := hF _ hb hδ
  funext I
  exact (e I).injective ((congrFun hzero I).trans ((e I).map_zero).symm)

private def untwistPiece (I : Finset ι) :
    letI := sectionDatumModule f (toMod M) coordinateOpens I
    TwistSections f M H (intersectionOpen I) 0 ≃ₗ[R] (sectionDatum (toMod M) coordinateOpens).obj I := by
  letI := sectionDatumModule f (toMod M) coordinateOpens I
  letI := sectionAlgebra f (intersectionOpen I)
  let e := (zeroTwistEquiv (V := intersectionOpen I) hM hH).symm
  exact { e.toAddEquiv with
    map_smul' r z := e.map_smul (algebraMap R Γ(X, intersectionOpen I) r) z }

omit [CompactSpace X] [X.IsSeparated] [DecidableEq ι] [LinearOrder ι] in
private theorem untwistPiece_natural {I J : Finset ι} (h : I ⊆ J)
    (z : TwistSections f M H (intersectionOpen I) 0) :
    (sectionDatum (toMod M) coordinateOpens).res h (untwistPiece f hM hH s I z) =
      untwistPiece f hM hH s J (twistSections_res f M (coverInter_anti h : intersectionOpen J ≤ intersectionOpen I) 0 z) := by
  let eI := zeroTwistEquiv (V := intersectionOpen I) hM hH
  let eJ := zeroTwistEquiv (V := intersectionOpen J) hM hH
  let i := homOfLE (coverInter_anti h : intersectionOpen J ≤ intersectionOpen I)
  apply eJ.injective
  change eJ ((toMod M).presheaf.map i.op (eI.symm z)) =
    eJ (eJ.symm ((toMod (twist M H 0)).presheaf.map i.op z))
  rw [eJ.apply_symm_apply, zeroTwistEquiv_restrict, eI.apply_symm_apply]

include hM hH in
/-- Degree-zero localized fractions recover the line-bundle section complex, including
its restriction maps. -/
theorem nonempty_gradedCech_iso :
    Nonempty (gradedCech (ι := ι) globalGrading 0 ≅ cech f (toMod M) coordinateOpens) := by
  letI (I : Finset ι) := sectionDatumModule f (toMod M) coordinateOpens I
  let e (I : Finset ι) := (twistChartPiece f hM hH s I 0).trans (untwistPiece f hM hH s I)
  let φ : (homLocDatum (ι := ι) globalGrading 0).Hom (sectionDatum (toMod M) coordinateOpens) :=
    { app := fun I => (e I).toLinearMap.toAddMonoidHom
      comm := fun h z => by
        change (sectionDatum (toMod M) coordinateOpens).res h (untwistPiece f hM hH s _
          (twistChartPiece f hM hH s _ 0 z)) =
          untwistPiece f hM hH s _ (twistChartPiece f hM hH s _ 0 (homLocRes globalGrading h 0 z))
        rw [twistChartPiece_natural f hM hH s h 0, untwistPiece_natural f hM hH s h] }
  have hφ I r z : φ.app I (r • z) = r • φ.app I z := (e I).map_smul r z
  let g : gradedCech (ι := ι) globalGrading 0 ⟶ cech f (toMod M) coordinateOpens :=
    FinsetCechDatum.linearCochainMap (fun h => homLocDatum_res_smul globalGrading h 0)
      (res_base_smul f (toMod M) coordinateOpens) φ hφ
  have hg : IsIso g := FinsetCechDatum.isIso_linearCochainMap _ _ _ _ fun I _ => (e I).bijective
  exact ⟨@asIso _ _ _ _ g hg⟩

end GlobalTheory.LineBundleSections
