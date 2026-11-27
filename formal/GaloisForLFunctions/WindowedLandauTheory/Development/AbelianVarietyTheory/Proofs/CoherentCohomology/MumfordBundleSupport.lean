import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.MumfordBundleOffOrigin
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.PerfectFibreSupport
import Mathlib.AlgebraicGeometry.Noetherian

/-! On an affine base open, cohomology of the universal translation
difference is finite and its closed-point support lies at the identity. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open MonObj TopologicalSpace HTGeometry
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.LineBundleSections GlobalTheory.SchemeCohomology
open scoped CategoryTheory.Obj

namespace GlobalTheory.MumfordFibre

attribute [local instance] Over.cartesianMonoidalCategory

/-- For the universal translation difference over an affine chart, each
cohomology module is annihilated off the identity on the base. -/
theorem cohomology_finite_and_vanishes_off_origin {K R : Type} [Field K] [CommRing R]
    {A : Over (Spec (.of K))} [GrpObj A] {L : LB A.left}
    (hA : IsAbelianScheme A) (hL : L.IsLB) (hAmp : RelAmple A L) (hK : KTriv A L)
    (t : Spec (.of R) ⟶ A.left) [IsOpenImmersion t]
    {Y : Scheme.{0}} {π : Y ⟶ (A ⊗ A).left} {f : Y ⟶ Spec (.of R)}
    (H : IsPullback π f (fst A A).left t)
    {κ : Type} [LinearOrder κ] [Fintype κ] (U : κ → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (cU : ⨆ i, U i = ⊤) :
    let M := translDiff A L (𝟙 A)
    let C := cech f (toMod (M.pull π)) U
    IsNoetherianRing R ∧ (∀ n, Module.Flat R (C.X n)) ∧
      (∀ n, Module.Finite R (C.homology n)) ∧
      ∀ χ : R →+* K, (Spec.map (CommRingCat.ofHom χ) ≫ t) ≫ A.hom = 𝟙 _ →
        Spec.map (CommRingCat.ofHom χ) ≫ t ≠ η[A].left →
        ∀ n, ∃ r : R, χ r ≠ 0 ∧ ∀ z : C.homology n, r • z = 0 := by
  let M := translDiff A L (𝟙 A)
  let C := cech f (toMod (M.pull π)) U
  have hM : M.IsLB := hL.linComb _ _
  let φ := (Spec.preimage (t ≫ A.hom)).hom
  have hφ : t ≫ A.hom = Spec.map (CommRingCat.ofHom φ) := (Spec.map_preimage _).symm
  have Hprod : IsPullback (fst A A).left (snd A A).left A.hom A.hom :=
    IsPullback.of_hasPullback A.hom A.hom
  have Hf : IsPullback (π ≫ (snd A A).left) f A.hom (Spec.map (CommRingCat.ofHom φ)) :=
    hφ ▸ H.paste_horiz Hprod.flip
  letI : Smooth A.hom := hA.smooth
  letI : Smooth f := MorphismProperty.of_isPullback Hf inferInstance
  letI : IsLocallyNoetherian (Spec (.of R)) := LocallyOfFiniteType.isLocallyNoetherian (t ≫ A.hom)
  letI hR : IsNoetherianRing R := (isLocallyNoetherian_Spec (R := .of R)).mp inferInstance
  have hproj := ProjectiveSections.isProjOver_baseChange φ Hf
    (ProjectiveSections.isProjOver_of_relAmple hL hAmp)
  letI : Y.IsSeparated := hproj.isSeparated
  have hI := affine_coverInter_of_affine U hU
  have hflat : ∀ n, Module.Flat R (C.X n) := cech_flat f U (hM.pull π) hI
  have hfin : ∀ n, Module.Finite R (C.homology n) := cech_homology_finite f (hM.pull π) U cU.ge hI hproj
  refine ⟨hR, hflat, hfin, fun χ hχ hn n => ?_⟩
  let j := Spec.map (CommRingCat.ofHom χ)
  let a := pullback.fst f j
  let b := pullback.snd f j
  have Hχ : IsPullback a b f j := IsPullback.of_hasPullback f j
  let x : 𝟙_ (Over (Spec (.of K))) ⟶ A := Over.homMk (j ≫ t) hχ
  have hx : x ≠ 1 := fun he => hn (congrArg Over.Hom.left he)
  have hV (i : κ) : IsAffineOpen (a ⁻¹ᵁ U i) := by
    simpa only [Scheme.Hom.preimage_top, inf_top_eq] using
      isAffineOpen_product Hχ (hU i) (isAffineOpen_top (Spec (.of K)))
  have cV : ⨆ i, a ⁻¹ᵁ U i = ⊤ := by rw [← Scheme.Hom.preimage_iSup, cU, Scheme.Hom.preimage_top]
  have h := cech_acyclic_off_origin hA hL hAmp hK x hx (Hχ.paste_horiz H)
    (fun i => a ⁻¹ᵁ U i) hV cV
  obtain ⟨w, hw⟩ := exists_iso_pull_comp hM π a
  let I := cechBaseChangeIso (M.pull π) U (hM.pull π) χ Hχ hI ≪≫
    cechIsoOfIsGen b (fun i => a ⁻¹ᵁ U i) ((hM.pull π).pull a) (hM.pull (a ≫ π)) hw
  exact exists_smul_homology_eq_zero_of_acyclic_fibre χ C (Fintype.card κ)
    (fun k hk => cech_isZero f (toMod (M.pull π)) U k hk.le) hflat hfin
    (fun k => (h k).of_iso I.symm) n

end GlobalTheory.MumfordFibre
