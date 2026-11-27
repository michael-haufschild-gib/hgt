import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.AdditiveLineBundleAcyclic
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleCechBaseChange
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.MumfordBundleFibres

/-! The Čech complex of the universal translation difference on a
nonidentity fibre is acyclic. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open MonObj TopologicalSpace HTGeometry
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.LineBundleSections GlobalTheory.TwistTranslate
open scoped CategoryTheory.Obj

namespace GlobalTheory.MumfordFibre

attribute [local instance] Over.cartesianMonoidalCategory

private def cechIsoOfPullbackId {K : Type} [Field K] {X Y : Scheme.{0}}
    {f : X ⟶ Spec (.of K)} {g : Y ⟶ Spec (.of K)} {π : Y ⟶ X} (M : LB X)
    (hM : M.IsLB) (H : IsPullback π g f (𝟙 (Spec (.of K)))) {κ : Type} [LinearOrder κ]
    [Fintype κ] (U : κ → X.Opens)
    (hU : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (coverInter ⊤ U s)) :
    cech f (toMod M) U ≅ cech g (toMod (M.pull π)) (fun i => π ⁻¹ᵁ U i) := by
  let C := cech f (toMod M) U
  let e := ModuleCat.extendScalarsId K
  let i : (((ModuleCat.extendScalars (RingHom.id K)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj C) ≅ C :=
    HomologicalComplex.Hom.isoOfComponents (fun n => e.app (C.X n)) fun n k _ =>
      (e.hom.naturality (C.d n k)).symm
  let H' : IsPullback π g f (Spec.map (CommRingCat.ofHom (RingHom.id K))) := by
    simpa only [CommRingCat.ofHom_id, Spec.map_id] using H
  exact i.symm ≪≫ cechBaseChangeIso M U hM (RingHom.id K) H' hU

/-- For a principal polarization, every nonidentity geometric fibre of
the universal translation difference has vanishing cohomology. -/
theorem cech_acyclic_off_origin {K : Type} [Field K]
    {A : Over (Spec (.of K))} [GrpObj A] {L : LB A.left}
    (hA : IsAbelianScheme A) (hL : L.IsLB) (hAmp : RelAmple A L) (hK : KTriv A L)
    (x : 𝟙_ (Over (Spec (.of K))) ⟶ A) (hx : x ≠ 1)
    {Y : Scheme.{0}} {π : Y ⟶ (A ⊗ A).left} {f : Y ⟶ Spec (.of K)}
    (H : IsPullback π f (fst A A).left x.left)
    {κ : Type} [LinearOrder κ] [Fintype κ] (U : κ → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (cU : ⨆ i, U i = ⊤) :
    (cech f (toMod ((translDiff A L (𝟙 A)).pull π)) U).Acyclic := by
  let e := π ≫ (snd A A).left
  have Hprod : IsPullback (fst A A).left (snd A A).left A.hom A.hom :=
    IsPullback.of_hasPullback A.hom A.hom
  have hxbase : (x.left : Spec (.of K) ⟶ A.left) ≫ A.hom = 𝟙 (Spec (.of K)) := Over.w x
  have H' : IsPullback e f A.hom (𝟙 (Spec (.of K))) := by
    rw [← hxbase]
    exact H.paste_horiz Hprod.flip
  letI : IsIso e := H'.isIso_fst_of_isIso
  have hπ : π ≫ (A ⊗ A).hom = f := by
    rw [← Over.w (fst A A), ← Category.assoc, H.w, Category.assoc]
    exact (congrArg (fun g : Spec (.of K) ⟶ Spec (.of K) => f ≫ g) hxbase).trans
      (Category.comp_id f)
  let P : Over.mk f ⟶ A ⊗ A := Over.homMk π hπ
  have hP : P ≫ fst A A = toUnit (Over.mk f) ≫ x := by
    ext1
    exact H.w
  let M := LB.LinComb L (K := Fin 2) ![(translate A x).left, 𝟙 A.left] ![1, -1]
  let N := (translDiff A L (𝟙 A)).pull π
  have hM : M.IsLB := hL.linComb _ _
  have hN : N.IsLB := (hL.linComb _ _).pull π
  obtain ⟨w, hw⟩ := exists_iso_pull_translDiff hL P x hP
  let V (i : κ) := inv e ⁻¹ᵁ U i
  have hV (i : κ) : IsAffineOpen (V i) := (hU i).preimage_of_isIso _
  have cV : ⨆ i, V i = ⊤ := by simp only [V, ← Scheme.Hom.preimage_iSup, cU, Scheme.Hom.preimage_top]
  letI : A.left.IsSeparated := (ProjectiveSections.isProjOver_of_relAmple hL hAmp).isSeparated
  have hU' : (fun i => e ⁻¹ᵁ V i) = U := by
    funext i
    change e ⁻¹ᵁ (inv e ⁻¹ᵁ U i) = U i
    rw [← Scheme.Hom.comp_preimage, IsIso.hom_inv_id]
    rfl
  have I : cech A.hom (toMod M) V ≅ cech f (toMod (M.pull e)) U := by
    rw [← hU']
    exact cechIsoOfPullbackId M hM H' V (affine_coverInter_of_affine V hV)
  let J := cechIsoOfIsGen f U (hM.pull e) hN hw
  have h := TranslateAdditive.cech_acyclic_of_translation_ne_one hA hL hAmp hK x hx V hV cV
  exact fun n => (h n).of_iso (I ≪≫ J)

end GlobalTheory.MumfordFibre
