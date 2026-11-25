import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ProjectiveSectionRatios
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleSectionPullback
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveChartMorphisms
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! A generating system of sections defines a morphism to projective space. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.LineBundleSections GlobalTheory.SchemeCohomology UpperTheory.Cb

namespace GlobalTheory.ProjectiveSections

variable {R : Type} [CommRing R] [Nontrivial R] {X : Scheme.{0}} {L : LB X}
  {n : ℕ} (s : Fin (n + 1) → L.Sec) (f : X ⟶ Spec (CommRingCat.of R))
  (r : ∀ i j : Fin (n + 1), Γ(X, nonzeroLocus (s i)))
  (hr : ∀ i j k,
    resG X (inf_le_right : nonzeroLocus (s i) ⊓ L.U k ≤ L.U k) ((s j).f k) =
      resG X inf_le_left (r i j) * resG X inf_le_right ((s i).f k))
  (hL : L.IsLB)

private abbrev U (i : Fin (n + 1)) := nonzeroLocus (s i)
private abbrev V (i : Fin (n + 1)) := PSpace.coordinateOpen R n i

private theorem appLE_congr {X Y : Scheme.{0}} {a b : X ⟶ Y} (e : a = b)
    (U : Y.Opens) (W : X.Opens) (ha : W ≤ a ⁻¹ᵁ U) (hb : W ≤ b ⁻¹ᵁ U) :
    a.appLE U W ha = b.appLE U W hb := by
  subst b
  rfl

private def chartMap (i : Fin (n + 1)) : (U s i).toScheme ⟶ PSpace R n :=
  pspaceOfCoordinates f (U s i) i (r i)

include hr hL in
private theorem chartMap_preimage (i j : Fin (n + 1)) :
    chartMap s f r i ⁻¹ᵁ V (R := R) j = (U s i).ι ⁻¹ᵁ U s j := by
  let a := chartMap s f r i
  let hi : ⊤ ≤ a ⁻¹ᵁ V (R := R) i := pspaceOfCoordinates_preimage f _ i (r i)
  have h := basicOpen_pspacePullRatio a ⊤ i hi j
  change (U s i).toScheme.basicOpen ((a.appLE _ ⊤ hi).hom (pspaceChartRatio R i j)) =
    ⊤ ⊓ a ⁻¹ᵁ V (R := R) j at h
  rw [top_inf_eq, pspaceOfCoordinates_ratio f _ i _ (sectionRatio_self s r hr hL i)] at h
  refine h.symm.trans ?_
  rw [Scheme.basicOpen_appLE, top_inf_eq, basicOpen_sectionRatio s r hr hL,
    Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, top_inf_eq]

include hr hL in
private theorem chartMap_agree {Z : Scheme.{0}} (i j : Fin (n + 1))
    (a : Z ⟶ (U s i).toScheme) (b : Z ⟶ (U s j).toScheme)
    (hab : a ≫ (U s i).ι = b ≫ (U s j).ι) :
    a ≫ chartMap s f r i = b ≫ chartMap s f r j := by
  let p := a ≫ chartMap s f r i
  let q := b ≫ chartMap s f r j
  let u := b ≫ (U s j).ι
  have ha : ⊤ ≤ (a ≫ (U s i).ι) ⁻¹ᵁ U s i :=
    a.preimage_mono (U s i).ι_preimage_self.ge
  have hi : ⊤ ≤ u ⁻¹ᵁ U s i := hab ▸ ha
  have hj : ⊤ ≤ u ⁻¹ᵁ U s j := b.preimage_mono (U s j).ι_preimage_self.ge
  have hp : ⊤ ≤ p ⁻¹ᵁ V (R := R) i := by
    dsimp only [p]
    rw [Scheme.Hom.comp_preimage, chartMap_preimage s f r hr hL]
    exact ha
  have hqi : ⊤ ≤ q ⁻¹ᵁ V (R := R) i := by
    dsimp only [q]
    rw [Scheme.Hom.comp_preimage, chartMap_preimage s f r hr hL]
    exact hi
  have hqj : ⊤ ≤ q ⁻¹ᵁ V (R := R) j := by
    dsimp only [q]
    rw [Scheme.Hom.comp_preimage, chartMap_preimage s f r hr hL]
    exact hj
  have hbase : p ≫ PSpace.str R n = q ≫ PSpace.str R n := by
    simpa only [p, q, chartMap, Category.assoc, pspaceOfCoordinates_base] using
      congrArg (fun p => p ≫ f) hab
  have ha' (k : Fin (n + 1)) :
      pspacePullRatio p ⊤ i hp k = (u.appLE _ ⊤ hi).hom (r i k) := by
    refine (pspacePullRatio_comp_ofCoordinates f _ i _ (sectionRatio_self s r hr hL i)
      a ⊤ hp ha k).trans ?_
    exact ConcreteCategory.congr_hom (appLE_congr hab (U s i) ⊤ ha hi) _
  have hb' (k : Fin (n + 1)) :
      pspacePullRatio q ⊤ j hqj k = (u.appLE _ ⊤ hj).hom (r j k) :=
    pspacePullRatio_comp_ofCoordinates f _ j _ (sectionRatio_self s r hr hL j) b ⊤ hqj hj k
  have hmul (i' j' k : Fin (n + 1)) (hi' : ⊤ ≤ u ⁻¹ᵁ U s i') (hj' : ⊤ ≤ u ⁻¹ᵁ U s j') :
      (u.appLE _ ⊤ hi').hom (r i' j') * (u.appLE _ ⊤ hj').hom (r j' k) =
        (u.appLE _ ⊤ hi').hom (r i' k) := by
    let W := U s i' ⊓ U s j'
    have hW : ⊤ ≤ u ⁻¹ᵁ W := le_inf hi' hj'
    have e := congrArg (u.appLE W ⊤ hW).hom
      (sectionRatio_mul s r hr hL i' j' k (W := W) inf_le_left inf_le_right)
    simpa only [map_mul, appLE_resG] using e
  have hu : IsUnit (pspacePullRatio q ⊤ j hqj i) := by
    rw [hb']
    refine IsUnit.of_mul_eq_one _ ((hmul j i j hj hi).trans ?_)
    rw [sectionRatio_self s r hr hL, map_one]
  apply Scheme.hom_ext_of_forall p q
  intro z
  refine ⟨⊤, trivial, pspace_restrict_eq_of_ratios hbase ⊤ i hp hqi fun k => ?_⟩
  apply hu.mul_left_cancel
  rw [pspacePullRatio_mul q ⊤ j i k hqj hqi, hb' i, ha' k, hb' k]
  exact hmul j i k hj hi

variable (hc : iSup (U s) = ⊤)

/-- The ratios of the sections glue to a morphism into projective space. -/
def sectionMorphism : X ⟶ PSpace R n :=
  (X.openCoverOfIsOpenCover (U s) (IsOpenCover.mk hc)).glueMorphisms
    (chartMap s f r) fun i j => chartMap_agree s f r hr hL i j _ _ pullback.condition

theorem ι_sectionMorphism (i : Fin (n + 1)) :
    (U s i).ι ≫ sectionMorphism s f r hr hL hc = chartMap s f r i :=
  (X.openCoverOfIsOpenCover (U s) (IsOpenCover.mk hc)).ι_glueMorphisms _ _ i

theorem sectionMorphism_base : sectionMorphism s f r hr hL hc ≫ PSpace.str R n = f := by
  apply Scheme.hom_ext_of_forall
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hc.ge (Set.mem_univ x))
  refine ⟨U s i, hi, ?_⟩
  rw [← Category.assoc, ι_sectionMorphism, chartMap, pspaceOfCoordinates_base]

theorem sectionMorphism_preimage (j : Fin (n + 1)) :
    sectionMorphism s f r hr hL hc ⁻¹ᵁ V (R := R) j = U s j := by
  apply SetLike.ext
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hc.ge (Set.mem_univ x))
  let z : (U s i).toScheme := ⟨x, hi⟩
  have h := congrArg (fun a : (U s i).toScheme ⟶ PSpace R n => a z)
    (ι_sectionMorphism s f r hr hL hc i)
  change ((sectionMorphism s f r hr hL hc) x ∈ V (R := R) j ↔ _)
  change (sectionMorphism s f r hr hL hc) x = chartMap s f r i z at h
  rw [h]
  change z ∈ chartMap s f r i ⁻¹ᵁ V (R := R) j ↔ _
  rw [chartMap_preimage s f r hr hL]
  rfl

theorem sectionMorphism_ratio (i j : Fin (n + 1)) :
    pspacePullRatio (sectionMorphism s f r hr hL hc) (U s i) i
      (sectionMorphism_preimage s f r hr hL hc i).ge j = r i j := by
  let a := sectionMorphism s f r hr hL hc
  let W := U s i
  let Z := V (R := R) i
  let η := W.ι.appLE W ⊤ W.ι_preimage_self.ge
  haveI : IsIso η := inferInstanceAs (IsIso (W.ι.appLE W ⊤ W.ι_preimage_self.ge))
  apply (ConcreteCategory.bijective_of_isIso η).1
  let ev (u : Γ(PSpace R n, Z) ⟶ Γ(W.toScheme, ⊤)) := u.hom (pspaceChartRatio R i j)
  have h := congrArg ev (Scheme.Hom.appLE_comp_appLE W.ι a Z W ⊤
    (sectionMorphism_preimage s f r hr hL hc i).ge W.ι_preimage_self.ge)
  have hh := appLE_congr (ι_sectionMorphism s f r hr hL hc i) Z ⊤
    (W.ι_preimage_self.ge.trans
      (W.ι.preimage_mono (sectionMorphism_preimage s f r hr hL hc i).ge))
    (pspaceOfCoordinates_preimage f W i (r i))
  exact h.trans ((congrArg ev hh).trans
    (pspaceOfCoordinates_ratio f W i (r i) (sectionRatio_self s r hr hL i) j))

/-- When the ratios generate the affine coordinate rings, the section morphism is a closed
immersion. -/
theorem sectionMorphism_isClosedImmersion (haff : ∀ i, IsAffineOpen (U s i))
    (hsurj : ∀ i,
      letI := sectionAlgebra f (U s i)
      Function.Surjective (MvPolynomial.eval₂Hom (algebraMap R Γ(X, U s i)) (r i))) :
    IsClosedImmersion (sectionMorphism s f r hr hL hc) := by
  let a := sectionMorphism s f r hr hL hc
  have hpre (i : Fin (n + 1)) : a ⁻¹ᵁ V (R := R) i = U s i :=
    sectionMorphism_preimage s f r hr hL hc i
  have hsurj' (i : Fin (n + 1)) :
      Function.Surjective (a.appLE (V (R := R) i) (U s i) (hpre i).ge).hom := by
    letI := sectionAlgebra f (U s i)
    letI := sectionAlgebra (PSpace.str R n) (V (R := R) i)
    let ρ := (a.appLE (V (R := R) i) (U s i) (hpre i).ge).hom
    have hconst (c : R) : ρ (algebraMap R Γ(PSpace R n, V (R := R) i) c) =
        algebraMap R Γ(X, U s i) c :=
      congrArg (fun u : CommRingCat.of R ⟶ Γ(X, U s i) => u.hom c)
        ((Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) (Scheme.Hom.appLE_comp_appLE a (PSpace.str R n)
            ⊤ (V (R := R) i) (U s i) le_top (hpre i).ge)).trans
            (appLE_congr (sectionMorphism_base s f r hr hL hc) ⊤ (U s i) le_top le_top
              |> congrArg ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ ·))))
    intro b
    obtain ⟨p, rfl⟩ := hsurj i b
    change MvPolynomial.eval₂Hom _ (r i) p ∈ ρ.range
    induction p using MvPolynomial.induction_on with
    | C c => exact ⟨_, (hconst c).trans (MvPolynomial.eval₂Hom_C _ _ c).symm⟩
    | add p q hp hq =>
      rw [map_add]
      exact add_mem hp hq
    | mul_X p j hp =>
      rw [map_mul, MvPolynomial.eval₂Hom_X']
      exact mul_mem hp ⟨_, sectionMorphism_ratio s f r hr hL hc i j⟩
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion)
    (PSpace.coordinateOpen R n) (PSpace.iSup_coordinateOpen R n)).2 fun i => ?_
  let Z := V (R := R) i
  haveI : IsAffine Z.toScheme := pspaceChart_isAffine i
  haveI : IsAffine (a ⁻¹ᵁ Z).toScheme := (hpre i).symm ▸ haff i
  apply IsClosedImmersion.of_surjective_of_isAffine
  rw [morphismRestrict_appTop]
  have hz : Z.ι ''ᵁ ⊤ = Z := Scheme.Opens.ι_image_top _
  have hrng : Function.Surjective (a.app (Z.ι ''ᵁ ⊤)) := by
    rw [hz]
    let e := X.presheaf.map (eqToHom (hpre i).symm).op
    intro y
    obtain ⟨x, hx⟩ := hsurj' i (e y)
    exact ⟨x, (ConcreteCategory.bijective_of_isIso e).1 hx⟩
  exact (ConcreteCategory.bijective_of_isIso _).2.comp hrng

end GlobalTheory.ProjectiveSections
