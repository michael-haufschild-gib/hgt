import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleKunneth
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.CechHomologyZero
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.CohomologyConvolution
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleCechIsomorphism
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.TwistRestrictionVanishing
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.AbelianAdditionPullback
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.TranslationDifferenceSections
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.TranslationDifferenceAdditivity
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ProjectiveProducts

/-! A translation difference outside the kernel of a principal polarization has
vanishing coherent cohomology in every degree. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open MonObj TopologicalSpace HTGeometry
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.LineBundleSections GlobalTheory.SchemeCohomology GlobalTheory.TwistTranslate
open Finset.HasAntidiagonal
open scoped CategoryTheory.Obj

namespace GlobalTheory.TranslateAdditive

attribute [local instance] Over.cartesianMonoidalCategory

private def cechEquivCohomology {K : Type} [Field K] {X : Scheme.{0}} [X.IsSeparated]
    (f : X ⟶ Spec (.of K)) {M : LB X} (hM : M.IsLB)
    {κ : Type} [LinearOrder κ] (U : κ → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (cU : ⨆ i, U i = ⊤) (n : ℕ) :
    letI := sectionAlgebra f (⊤ : X.Opens)
    letI := Module.compHom (CohomologyOn (toMod M) ⊤ n) (algebraMap K Γ(X, ⊤))
    (cech f (toMod M) U).homology n ≃ₗ[K] CohomologyOn (toMod M) ⊤ n := by
  let F := toMod M
  letI : F.IsQuasicoherent := isQuasicoherent_toMod hM
  letI := sectionAlgebra f (⊤ : X.Opens)
  letI := Module.compHom (CohomologyOn F ⊤ n) (algebraMap K Γ(X, ⊤))
  let E := ModuleCechCohomology ⊤ U F n
  letI := Module.compHom E (algebraMap K Γ(X, ⊤))
  have e : E ≃ₗ[Γ(X, ⊤)] CohomologyOn F ⊤ n := by
    have a := moduleLerayLinearEquiv ⊤ U F n cU.ge
      (fun s hs => quasicoherent_acyclicOn F (affine_coverInter_of_affine U hU s hs))
    rwa [coverInter_empty] at a
  exact (cechCohomologyEquiv f F U n).trans
    { e.toAddEquiv with map_smul' := fun r z => e.map_smul (algebraMap K Γ(X, ⊤) r) z }

/-- Off the translation kernel, all Čech cohomology of the polarization
difference vanishes. The shear equates its self-convolution to the
convolution with the dimensions of the structure sheaf. -/
theorem cech_acyclic_of_translation_ne_one {K : Type} [Field K]
    {A : Over (Spec (.of K))} [GrpObj A] {L : LB A.left} (hA : IsAbelianScheme A)
    (hL : L.IsLB) (hAmp : RelAmple A L) (hK : KTriv A L)
    (x : 𝟙_ (Over (Spec (.of K))) ⟶ A) (hx : x ≠ 1)
    {κ : Type} [LinearOrder κ] [Fintype κ] (U : κ → A.left.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (cU : ⨆ i, U i = ⊤) :
    let M := LB.LinComb L (K := Fin 2) ![(translate A x).left, 𝟙 A.left] ![1, -1]
    (cech A.hom (toMod M) U).Acyclic := by
  classical
  let M := LB.LinComb L (K := Fin 2) ![(translate A x).left, 𝟙 A.left] ![1, -1]
  change (cech A.hom (toMod M) U).Acyclic
  let O := LB.trivial A.left
  have hM : M.IsLB := hL.linComb _ _
  have hO : O.IsLB := LB.isLB_trivial _
  let Z := A ⊗ A
  let p := (fst A A).left
  let q := (snd A A).left
  let m := μ[A].left
  have H : IsPullback p q A.hom A.hom := IsPullback.of_hasPullback A.hom A.hom
  have H' : IsPullback m q A.hom A.hom := AbLaw.isPullback_mul_snd A
  have hf : m ≫ A.hom = p ≫ A.hom := (Over.w μ[A]).trans (Over.w (fst A A)).symm
  have hproj := ProjectiveSections.isProjOver_of_relAmple hL hAmp
  have hprojZ := ProjectiveSections.isProjOver_product H hproj hproj
  letI : CompactSpace A.left := hproj.compactSpace
  letI : CompactSpace Z.left := hprojZ.compactSpace
  letI : A.left.IsSeparated := hproj.isSeparated
  letI : Z.left.IsSeparated := hprojZ.isSeparated
  letI : HasExt.{0} (TopCat.Sheaf AddCommGrpCat.{0} Z.left) := hasExt_of_enoughInjectives _
  obtain ⟨J, hJ, V, iV, hV, hVM, cV⟩ := exists_finite_affine_refinement hM
  obtain ⟨T, hT, W, _, hW, _, cW⟩ := exists_finite_affine_refinement (LB.isLB_trivial Z.left)
  letI : Fintype J := hJ
  letI : Fintype T := hT
  letI : LinearOrder J := LinearOrder.lift' (Fintype.equivFin J) (Fintype.equivFin J).injective
  letI : LinearOrder T := LinearOrder.lift' (Fintype.equivFin T) (Fintype.equivFin T).injective
  let C := cech A.hom (toMod M) V
  let C₀ := cech A.hom (toMod O) V
  let a (n : ℕ) := Module.finrank K (C.homology n)
  let b (n : ℕ) := Module.finrank K (C₀.homology n)
  have finM (n : ℕ) : Module.Finite K (C.homology n) :=
    cech_homology_finite A.hom hM V cV.ge (affine_coverInter_of_affine V hV) hproj n
  have finO (n : ℕ) : Module.Finite K (C₀.homology n) :=
    cech_homology_finite A.hom hO V cV.ge (affine_coverInter_of_affine V hV) hproj n
  have eM := cechHomologyZeroEquiv A.hom (toMod M) V cV
  have eO := cechHomologyZeroEquiv A.hom (toMod O) V cV
  have ha : a 0 = 0 := by
    have hzero (s : M.Sec) : ∀ i, s.f i = 0 :=
      section_eq_zero_of_translation_ne_one hA hL hAmp hK x hx s
    letI : Subsingleton M.Sec := ⟨fun s t => by
      obtain ⟨s, hs⟩ := s
      obtain ⟨t, ht⟩ := t
      congr 1
      funext i
      exact (hzero ⟨s, hs⟩ i).trans (hzero ⟨t, ht⟩ i).symm⟩
    letI : Subsingleton Γ(toMod M, ⊤) := globalCoordinates.subsingleton
    letI : Subsingleton (C.homology 0) := eM.toEquiv.subsingleton
    exact Module.finrank_zero_of_subsingleton
  have hb : 0 < b 0 := by
    letI : IsIso A.hom.appTop := hA.isIso_appTop
    let e : Γ(A.left, ⊤) ≃+* K :=
      (asIso A.hom.appTop).symm.commRingCatIsoToRingEquiv.trans
        (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv
    letI : Nontrivial Γ(A.left, ⊤) := e.toEquiv.nontrivial
    let e' : Γ(toMod O, ⊤) ≃ₗ[Γ(A.left, ⊤)] Γ(A.left, ⊤) :=
      chartEquiv hO PUnit.unit (V := ⊤) le_rfl
    letI : Nontrivial Γ(toMod O, ⊤) := e'.toEquiv.nontrivial
    letI : Nontrivial (C₀.homology 0) := eO.toEquiv.nontrivial
    letI := finO 0
    exact Module.finrank_pos
  obtain ⟨w, hw⟩ := exists_iso_additive hA hL hAmp x
  let iso := (cechIsoPullTrivial (p ≫ A.hom) W q (hM.pull m)).symm ≪≫
    cechIsoOfIsGen (p ≫ A.hom) W (hM.pull m)
      (twist_isLB (hM.pull p) (hM.pull q) 1) hw
  have hconv (n : ℕ) : (∑ t ∈ antidiagonal n, a t.1 * a t.2) =
      ∑ t ∈ antidiagonal n, a t.1 * b t.2 := by
    have h₁ := finrank_cech_externalProduct V V W H hM hM hV hV hW
      (fun i => ⟨iV i, hVM i⟩) (fun i => ⟨iV i, hVM i⟩) cV cV cW finM finM n
    have h₂ := finrank_cech_externalProduct V V W H' hM hO hV hV hW
      (fun i => ⟨iV i, hVM i⟩) (fun _ => ⟨PUnit.unit, le_top⟩) cV cV cW finM finO n
    rw [hf] at h₂
    exact h₁.symm.trans (((HomologicalComplex.homologyMapIso iso n).toLinearEquiv.finrank_eq).symm.trans h₂)
  intro n
  letI := finM n
  letI : Subsingleton (C.homology n) :=
    Module.finrank_zero_iff.mp (PrincipalSections.eq_zero_of_selfConvolution a b ha hb hconv n)
  let e := (cechEquivCohomology A.hom hM U hU cU n).trans (cechEquivCohomology A.hom hM V hV cV n).symm
  letI := e.toEquiv.subsingleton
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ n).mpr
    (ModuleCat.isZero_iff_subsingleton.mpr inferInstance)

end GlobalTheory.TranslateAdditive
