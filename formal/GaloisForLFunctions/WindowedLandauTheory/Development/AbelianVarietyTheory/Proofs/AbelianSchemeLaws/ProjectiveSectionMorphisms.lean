import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ProjectiveSectionRatios
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleSectionPullback
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.RelativeFormsPullback
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveChartMorphisms
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! Projective coordinate ratios glue on overlaps to define a morphism to projective space. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.LineBundleSections GlobalTheory.SchemeCohomology UpperTheory.Cb

namespace GlobalTheory.ProjectiveSections

variable {R : Type} [CommRing R] [Nontrivial R] {X : Scheme.{0}} {n : ℕ}

omit [Nontrivial R] in
/-- The empty scheme is projective over an affine base. -/
theorem isProjOver_of_isEmpty (f : X ⟶ Spec (CommRingCat.of R)) [IsEmpty X] :
    IsProjOver f := by
  let a := isInitialOfIsEmpty (X := X)
  let i := a.to (PSpace R 0)
  have hclosed : IsClosed (Set.range i) := by
    rw [Set.range_eq_empty]
    exact isClosed_empty
  exact ⟨0, i, IsClosedImmersion.of_isPreimmersion i hclosed, a.hom_ext _ _⟩

/-- A cover with the coordinate ratios and transition identities of projective space. -/
structure Coordinates (X : Scheme.{0}) (n : ℕ) where
  U : Fin (n + 1) → X.Opens
  cover : ⨆ i, U i = ⊤
  ratio : ∀ i, Fin (n + 1) → Γ(X, U i)
  ratio_self : ∀ i, ratio i i = 1
  basicOpen_ratio : ∀ i j, X.basicOpen (ratio i j) = U i ⊓ U j
  ratio_mul : ∀ i j k,
    resG X (inf_le_left : U i ⊓ U j ≤ U i) (ratio i j) *
      resG X inf_le_right (ratio j k) = resG X inf_le_left (ratio i k)

/-- Generating sections of a line bundle give projective coordinate ratios. -/
def Coordinates.ofSections {L : LB X} (hL : L.IsLB) (s : Fin (n + 1) → L.Sec)
    (r : ∀ i, Fin (n + 1) → Γ(X, nonzeroLocus (s i)))
    (hr : ∀ i j k,
      resG X (inf_le_right : nonzeroLocus (s i) ⊓ L.U k ≤ L.U k) ((s j).f k) =
        resG X inf_le_left (r i j) * resG X inf_le_right ((s i).f k))
    (hc : ⨆ i, nonzeroLocus (s i) = ⊤) : Coordinates X n where
  U i := nonzeroLocus (s i)
  cover := hc
  ratio := r
  ratio_self := sectionRatio_self s r hr hL
  basicOpen_ratio := basicOpen_sectionRatio s r hr hL
  ratio_mul i j k := sectionRatio_mul s r hr hL i j k inf_le_left inf_le_right

namespace Coordinates

variable (C : Coordinates X n) (f : X ⟶ Spec (CommRingCat.of R))

private abbrev V (i : Fin (n + 1)) := PSpace.coordinateOpen R n i

private theorem appLE_congr {X Y : Scheme.{0}} {a b : X ⟶ Y} (e : a = b)
    (U : Y.Opens) (W : X.Opens) (ha : W ≤ a ⁻¹ᵁ U) (hb : W ≤ b ⁻¹ᵁ U) :
    a.appLE U W ha = b.appLE U W hb := by
  subst b
  rfl

private def chartMap (i : Fin (n + 1)) : (C.U i).toScheme ⟶ PSpace R n :=
  pspaceOfCoordinates f (C.U i) i (C.ratio i)

private theorem chartMap_preimage (i j : Fin (n + 1)) :
    chartMap C f i ⁻¹ᵁ V (R := R) j = (C.U i).ι ⁻¹ᵁ C.U j := by
  let a := chartMap C f i
  let hi : ⊤ ≤ a ⁻¹ᵁ V (R := R) i := pspaceOfCoordinates_preimage f _ i (C.ratio i)
  have h := basicOpen_pspacePullRatio a ⊤ i hi j
  change (C.U i).toScheme.basicOpen ((a.appLE _ ⊤ hi).hom (pspaceChartRatio R i j)) =
    ⊤ ⊓ a ⁻¹ᵁ V (R := R) j at h
  have hr := pspaceOfCoordinates_ratio f (C.U i) i (C.ratio i) (C.ratio_self i) j
  change (a.appLE _ ⊤ hi).hom (pspaceChartRatio R i j) = _ at hr
  rw [top_inf_eq, hr] at h
  refine h.symm.trans ?_
  rw [Scheme.basicOpen_appLE, top_inf_eq, C.basicOpen_ratio,
    Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, top_inf_eq]

private theorem chartMap_agree {Z : Scheme.{0}} (i j : Fin (n + 1))
    (a : Z ⟶ (C.U i).toScheme) (b : Z ⟶ (C.U j).toScheme)
    (hab : a ≫ (C.U i).ι = b ≫ (C.U j).ι) :
    a ≫ chartMap C f i = b ≫ chartMap C f j := by
  let p := a ≫ chartMap C f i
  let q := b ≫ chartMap C f j
  let u := b ≫ (C.U j).ι
  have ha : ⊤ ≤ (a ≫ (C.U i).ι) ⁻¹ᵁ C.U i :=
    a.preimage_mono (C.U i).ι_preimage_self.ge
  have hi : ⊤ ≤ u ⁻¹ᵁ C.U i := by
    change ⊤ ≤ (b ≫ (C.U j).ι) ⁻¹ᵁ C.U i
    rwa [← hab]
  have hj : ⊤ ≤ u ⁻¹ᵁ C.U j := b.preimage_mono (C.U j).ι_preimage_self.ge
  have hp : ⊤ ≤ p ⁻¹ᵁ V (R := R) i := by
    dsimp only [p]
    rw [Scheme.Hom.comp_preimage, chartMap_preimage C f]
    exact ha
  have hqi : ⊤ ≤ q ⁻¹ᵁ V (R := R) i := by
    dsimp only [q]
    rw [Scheme.Hom.comp_preimage, chartMap_preimage C f]
    exact hi
  have hqj : ⊤ ≤ q ⁻¹ᵁ V (R := R) j := by
    dsimp only [q]
    rw [Scheme.Hom.comp_preimage, chartMap_preimage C f]
    exact hj
  have hbase : p ≫ PSpace.str R n = q ≫ PSpace.str R n := by
    simpa only [p, q, chartMap, Category.assoc, pspaceOfCoordinates_base] using
      congrArg (fun p => p ≫ f) hab
  have ha' (k : Fin (n + 1)) :
      pspacePullRatio p ⊤ i hp k = (u.appLE _ ⊤ hi).hom (C.ratio i k) := by
    refine (pspacePullRatio_comp_ofCoordinates f _ i _ (C.ratio_self i)
      a ⊤ hp ha k).trans ?_
    exact ConcreteCategory.congr_hom (appLE_congr hab (C.U i) ⊤ ha hi) _
  have hb' (k : Fin (n + 1)) :
      pspacePullRatio q ⊤ j hqj k = (u.appLE _ ⊤ hj).hom (C.ratio j k) :=
    pspacePullRatio_comp_ofCoordinates f _ j _ (C.ratio_self j) b ⊤ hqj hj k
  have hmul (i' j' k : Fin (n + 1)) (hi' : ⊤ ≤ u ⁻¹ᵁ C.U i') (hj' : ⊤ ≤ u ⁻¹ᵁ C.U j') :
      (u.appLE _ ⊤ hi').hom (C.ratio i' j') * (u.appLE _ ⊤ hj').hom (C.ratio j' k) =
        (u.appLE _ ⊤ hi').hom (C.ratio i' k) := by
    let W := C.U i' ⊓ C.U j'
    have hW : ⊤ ≤ u ⁻¹ᵁ W := le_inf hi' hj'
    have e := congrArg (u.appLE W ⊤ hW).hom
      (C.ratio_mul i' j' k)
    simpa only [map_mul, appLE_resG] using e
  have hu : IsUnit (pspacePullRatio q ⊤ j hqj i) := by
    rw [hb']
    refine IsUnit.of_mul_eq_one _ ((hmul j i j hj hi).trans ?_)
    rw [C.ratio_self, map_one]
  apply Scheme.hom_ext_of_forall p q
  intro z
  refine ⟨⊤, trivial, pspace_restrict_eq_of_ratios hbase ⊤ i hp hqi fun k => ?_⟩
  apply hu.mul_left_cancel
  rw [pspacePullRatio_mul q ⊤ j i k hqj hqi, hb' i, ha' k, hb' k]
  exact hmul j i k hj hi

/-- The ratios on the cover glue to a morphism into projective space. -/
def sectionMorphism : X ⟶ PSpace R n :=
  (X.openCoverOfIsOpenCover C.U (IsOpenCover.mk C.cover)).glueMorphisms
    (chartMap C f) fun i j => chartMap_agree C f i j _ _ pullback.condition

theorem ι_sectionMorphism (i : Fin (n + 1)) :
    (C.U i).ι ≫ sectionMorphism C f = chartMap C f i :=
  (X.openCoverOfIsOpenCover C.U (IsOpenCover.mk C.cover)).ι_glueMorphisms _ _ i

theorem sectionMorphism_base : sectionMorphism C f ≫ PSpace.str R n = f := by
  apply Scheme.hom_ext_of_forall
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (C.cover.ge (Set.mem_univ x))
  refine ⟨C.U i, hi, ?_⟩
  rw [← Category.assoc, ι_sectionMorphism, chartMap, pspaceOfCoordinates_base]

theorem sectionMorphism_preimage (j : Fin (n + 1)) :
    sectionMorphism C f ⁻¹ᵁ V (R := R) j = C.U j := by
  apply SetLike.ext
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (C.cover.ge (Set.mem_univ x))
  let z : (C.U i).toScheme := ⟨x, hi⟩
  have h := congrArg (fun a : (C.U i).toScheme ⟶ PSpace R n => a z)
    (ι_sectionMorphism C f i)
  change ((sectionMorphism C f) x ∈ V (R := R) j ↔ _)
  change (sectionMorphism C f) x = chartMap C f i z at h
  rw [h]
  change z ∈ chartMap C f i ⁻¹ᵁ V (R := R) j ↔ _
  rw [chartMap_preimage C f]
  rfl

theorem sectionMorphism_ratio (i j : Fin (n + 1)) :
    pspacePullRatio (sectionMorphism C f) (C.U i) i
      (sectionMorphism_preimage C f i).ge j = C.ratio i j := by
  let a := sectionMorphism C f
  let W := C.U i
  let Z := V (R := R) i
  let η := W.ι.appLE W ⊤ W.ι_preimage_self.ge
  haveI : IsIso η := inferInstanceAs (IsIso (W.ι.appLE W ⊤ W.ι_preimage_self.ge))
  apply (ConcreteCategory.bijective_of_isIso η).1
  let ev (u : Γ(PSpace R n, Z) ⟶ Γ(W.toScheme, ⊤)) := u.hom (pspaceChartRatio R i j)
  have h := congrArg ev (Scheme.Hom.appLE_comp_appLE W.ι a Z W ⊤
    (sectionMorphism_preimage C f i).ge W.ι_preimage_self.ge)
  have hh := appLE_congr (ι_sectionMorphism C f i) Z ⊤
    (W.ι_preimage_self.ge.trans
      (W.ι.preimage_mono (sectionMorphism_preimage C f i).ge))
    (pspaceOfCoordinates_preimage f W i (C.ratio i))
  exact h.trans ((congrArg ev hh).trans
    (pspaceOfCoordinates_ratio f W i (C.ratio i) (C.ratio_self i) j))

/-- When the ratios generate the affine coordinate rings, the section morphism is a closed
immersion. -/
theorem sectionMorphism_isClosedImmersion (haff : ∀ i, IsAffineOpen (C.U i))
    (hsurj : ∀ i,
      letI := sectionAlgebra f (C.U i)
      Function.Surjective (MvPolynomial.eval₂Hom (algebraMap R Γ(X, C.U i)) (C.ratio i))) :
    IsClosedImmersion (sectionMorphism C f) := by
  let a := sectionMorphism C f
  have hpre (i : Fin (n + 1)) : a ⁻¹ᵁ V (R := R) i = C.U i :=
    sectionMorphism_preimage C f i
  have hsurj' (i : Fin (n + 1)) :
      Function.Surjective (a.appLE (V (R := R) i) (C.U i) (hpre i).ge).hom := by
    let W := C.U i
    let Z := V (R := R) i
    let ρ : SectionRing (PSpace.str R n) Z →ₐ[R] SectionRing f W :=
      (sectionRes f (homOfLE (hpre i).ge)).comp (sectionPullback (sectionMorphism_base C f) Z)
    change Function.Surjective ρ
    intro b
    obtain ⟨p, rfl⟩ := hsurj i b
    change MvPolynomial.eval₂Hom (algebraMap R (SectionRing f W)) (C.ratio i) p ∈
      ρ.toRingHom.range
    induction p using MvPolynomial.induction_on with
    | C c => exact ⟨_, (ρ.commutes c).trans (MvPolynomial.eval₂Hom_C _ _ c).symm⟩
    | add p q hp hq =>
      rw [map_add]
      exact add_mem hp hq
    | mul_X p j hp =>
      rw [map_mul, MvPolynomial.eval₂Hom_X']
      exact mul_mem hp ⟨_, sectionMorphism_ratio C f i j⟩
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
  let e := X.presheaf.map (eqToHom (image_morphismRestrict_preimage a Z ⊤)).op
  change Function.Surjective ((a.app (Z.ι ''ᵁ ⊤)) ≫ e)
  exact (ConcreteCategory.bijective_of_isIso e).2.comp hrng

/-- Affine charts generated by these ratios present a projective scheme over the base. -/
theorem isProjOver (haff : ∀ i, IsAffineOpen (C.U i))
    (hsurj : ∀ i,
      letI := sectionAlgebra f (C.U i)
      Function.Surjective (MvPolynomial.eval₂Hom (algebraMap R Γ(X, C.U i)) (C.ratio i))) :
    IsProjOver f :=
  ⟨n, C.sectionMorphism f, C.sectionMorphism_isClosedImmersion f haff hsurj,
    C.sectionMorphism_base f⟩

end Coordinates

end GlobalTheory.ProjectiveSections
