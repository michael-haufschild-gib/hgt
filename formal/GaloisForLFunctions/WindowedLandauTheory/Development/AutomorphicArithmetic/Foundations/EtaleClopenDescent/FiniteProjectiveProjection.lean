import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveChartMorphisms
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! Homogeneous forms of one positive degree without common zeros define a
finite morphism from a closed projective subscheme. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open UpperTheory.Cb

namespace GlobalTheory.SchemeCohomology

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ}
  (ι : X ⟶ PSpace K N) (F : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K)
  (hF : ∀ j, (F j).IsHomogeneous e)

/-- The chart where the indicated form does not vanish. -/
def projectionOpen (i : Fin (d + 1)) : X.Opens :=
  ι ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (F i)

private abbrev ratio (i j : Fin (d + 1)) : Γ(X, projectionOpen ι F i) :=
  projectiveRatio ι (hF i) (hF j)

variable (s : X ⟶ Spec (CommRingCat.of K))

private theorem appLE_congr_of_eq {A B : Scheme.{0}} {a b : A ⟶ B} (h : a = b)
    (U : B.Opens) (V : A.Opens) (ha : V ≤ a ⁻¹ᵁ U) (hb : V ≤ b ⁻¹ᵁ U) :
    a.appLE U V ha = b.appLE U V hb := by
  subst b
  rfl

private def projectionChart (i : Fin (d + 1)) : (projectionOpen ι F i).toScheme ⟶ PSpace K d :=
  pspaceOfCoordinates s (projectionOpen ι F i) i (ratio ι F hF i)

private theorem appLE_ratios_mul {Z : Scheme.{0}} (g : Z ⟶ X) (W : Z.Opens)
    (i j k : Fin (d + 1)) (hi : W ≤ g ⁻¹ᵁ projectionOpen ι F i)
    (hj : W ≤ g ⁻¹ᵁ projectionOpen ι F j) :
    (g.appLE _ W hi).hom (ratio ι F hF i j) * (g.appLE _ W hj).hom (ratio ι F hF j k) =
      (g.appLE _ W hi).hom (ratio ι F hF i k) := by
  let U := projectionOpen ι F i
  let V := projectionOpen ι F j
  have h : W ≤ g ⁻¹ᵁ (U ⊓ V) := fun x hx => ⟨hi hx, hj hx⟩
  have hmul := congrArg (g.appLE (U ⊓ V) W h).hom (projectiveRatio_mul ι (hF i) (hF j) (hF k))
  have hl (a : Γ(X, U)) :
      (g.appLE (U ⊓ V) W h).hom (X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op a) =
      (g.appLE U W hi).hom a :=
    ConcreteCategory.congr_hom (g.map_appLE h (homOfLE (inf_le_left : U ⊓ V ≤ U)).op) a
  have hr (a : Γ(X, V)) :
      (g.appLE (U ⊓ V) W h).hom (X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op a) =
      (g.appLE V W hj).hom a :=
    ConcreteCategory.congr_hom (g.map_appLE h (homOfLE (inf_le_right : U ⊓ V ≤ V)).op) a
  let H := (g.appLE (U ⊓ V) W h).hom
  let a := X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op (ratio ι F hF i j)
  let b := X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op (ratio ι F hF j k)
  exact (congrArg₂ (· * ·) (hl (ratio ι F hF i j)) (hr (ratio ι F hF j k))).symm.trans
    ((H.map_mul a b).symm.trans (hmul.trans (hl (ratio ι F hF i k))))

private theorem projectionChart_preimage (i j : Fin (d + 1)) :
    projectionChart ι F hF s i ⁻¹ᵁ PSpace.coordinateOpen K d j =
      (projectionOpen ι F i).ι ⁻¹ᵁ projectionOpen ι F j := by
  let U := projectionOpen ι F i
  let V := PSpace.coordinateOpen K d i
  let f := projectionChart ι F hF s i
  let hi : ⊤ ≤ f ⁻¹ᵁ V :=
    pspaceOfCoordinates_preimage s U i (ratio ι F hF i)
  have h := basicOpen_pspacePullRatio f ⊤ i hi j
  change U.toScheme.basicOpen ((f.appLE V ⊤ hi).hom (pspaceChartRatio K i j)) =
    ⊤ ⊓ f ⁻¹ᵁ PSpace.coordinateOpen K d j at h
  have hratio : (f.appLE V ⊤ hi).hom (pspaceChartRatio K i j) =
      (U.ι.appLE U ⊤ U.ι_preimage_self.ge).hom (ratio ι F hF i j) :=
    pspaceOfCoordinates_ratio s U i _ (projectiveRatio_self ι (hF i)) j
  rw [top_inf_eq, hratio] at h
  refine h.symm.trans ?_
  have hr : X.basicOpen (ratio ι F hF i j) = U ⊓ projectionOpen ι F j :=
    basicOpen_projectiveRatio ι (hF i) (hF j)
  rw [Scheme.basicOpen_appLE, top_inf_eq, hr]
  rw [Scheme.Hom.preimage_inf, U.ι_preimage_self, top_inf_eq]

private theorem projectionChart_agree {Z : Scheme.{0}} (i j : Fin (d + 1))
    (a : Z ⟶ (projectionOpen ι F i).toScheme) (b : Z ⟶ (projectionOpen ι F j).toScheme)
    (hab : a ≫ (projectionOpen ι F i).ι = b ≫ (projectionOpen ι F j).ι) :
    a ≫ projectionChart ι F hF s i = b ≫ projectionChart ι F hF s j := by
  let U := projectionOpen ι F
  let f := a ≫ projectionChart ι F hF s i
  let g := b ≫ projectionChart ι F hF s j
  let a' := a ≫ (U i).ι
  let b' := b ≫ (U j).ι
  have hai : ⊤ ≤ a' ⁻¹ᵁ U i := a.preimage_mono (U i).ι_preimage_self.ge
  have hbj : ⊤ ≤ b' ⁻¹ᵁ U j := b.preimage_mono (U j).ι_preimage_self.ge
  have hbi : ⊤ ≤ b' ⁻¹ᵁ U i :=
    (congrArg (fun m : Z ⟶ X => ⊤ ≤ m ⁻¹ᵁ U i) hab).mp hai
  have hf : ⊤ ≤ f ⁻¹ᵁ PSpace.coordinateOpen K d i := by
    change ⊤ ≤ (a ≫ projectionChart ι F hF s i) ⁻¹ᵁ _
    rw [Scheme.Hom.comp_preimage, projectionChart_preimage]
    exact hai
  have hgj : ⊤ ≤ g ⁻¹ᵁ PSpace.coordinateOpen K d j := by
    change ⊤ ≤ (b ≫ projectionChart ι F hF s j) ⁻¹ᵁ _
    rw [Scheme.Hom.comp_preimage, projectionChart_preimage]
    exact hbj
  have hg : ⊤ ≤ g ⁻¹ᵁ PSpace.coordinateOpen K d i := by
    change ⊤ ≤ (b ≫ projectionChart ι F hF s j) ⁻¹ᵁ _
    rw [Scheme.Hom.comp_preimage, projectionChart_preimage]
    exact hbi
  have hs : f ≫ PSpace.str K d = g ≫ PSpace.str K d := by
    simpa only [f, g, projectionChart, Category.assoc, pspaceOfCoordinates_base] using
      congrArg (fun m => m ≫ s) hab
  have hbf (k : Fin (d + 1)) :
      pspacePullRatio g ⊤ j hgj k = (b'.appLE _ ⊤ hbj).hom (ratio ι F hF j k) :=
    pspacePullRatio_comp_ofCoordinates s _ j _ (projectiveRatio_self ι (hF j)) b ⊤ hgj hbj k
  have haf (k : Fin (d + 1)) :
      pspacePullRatio f ⊤ i hf k = (b'.appLE _ ⊤ hbi).hom (ratio ι F hF i k) := by
    refine (pspacePullRatio_comp_ofCoordinates s _ i _ (projectiveRatio_self ι (hF i))
      a ⊤ hf hai k).trans ?_
    exact ConcreteCategory.congr_hom (appLE_congr_of_eq hab (U i) ⊤ hai hbi) _
  have hunit : IsUnit (pspacePullRatio g ⊤ j hgj i) := by
    rw [hbf]
    refine IsUnit.of_mul_eq_one _ ((appLE_ratios_mul ι F hF b' ⊤ j i j hbj hbi).trans ?_)
    let A := (b'.appLE (U j) ⊤ hbj).hom
    exact (congrArg A (projectiveRatio_self ι (hF j))).trans A.map_one
  apply Scheme.hom_ext_of_forall f g
  intro z
  refine ⟨⊤, trivial, pspace_restrict_eq_of_ratios hs ⊤ i hf hg fun k => ?_⟩
  apply hunit.mul_left_cancel
  rw [pspacePullRatio_mul g ⊤ j i k hgj hg, hbf i, haf k, hbf k]
  exact appLE_ratios_mul ι F hF b' ⊤ j i k hbj hbi

variable (hcov : iSup (projectionOpen ι F) = ⊤)

/-- Projective projection defined by homogeneous forms with no common zero. -/
def formProjection : X ⟶ PSpace K d :=
  (X.openCoverOfIsOpenCover (projectionOpen ι F) (IsOpenCover.mk hcov)).glueMorphisms
    (projectionChart ι F hF s) fun i j =>
      projectionChart_agree ι F hF s i j _ _ pullback.condition

theorem ι_formProjection (i : Fin (d + 1)) :
    (projectionOpen ι F i).ι ≫ formProjection ι F hF s hcov = projectionChart ι F hF s i :=
  (X.openCoverOfIsOpenCover (projectionOpen ι F) (IsOpenCover.mk hcov)).ι_glueMorphisms _ _ i

theorem formProjection_base : formProjection ι F hF s hcov ≫ PSpace.str K d = s := by
  apply Scheme.hom_ext_of_forall
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcov.ge (Set.mem_univ x))
  refine ⟨projectionOpen ι F i, hi, ?_⟩
  rw [← Category.assoc, ι_formProjection, projectionChart, pspaceOfCoordinates_base]

theorem formProjection_preimage (j : Fin (d + 1)) :
    formProjection ι F hF s hcov ⁻¹ᵁ PSpace.coordinateOpen K d j = projectionOpen ι F j := by
  apply SetLike.ext
  intro x
  let V := PSpace.coordinateOpen K d j
  let g := formProjection ι F hF s hcov
  change g x ∈ V ↔ x ∈ projectionOpen ι F j
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcov.ge (Set.mem_univ x))
  let U := projectionOpen ι F i
  let z : U.toScheme := ⟨x, hi⟩
  have hmap : g x = projectionChart ι F hF s i z :=
    congrArg (fun m : U.toScheme ⟶ PSpace K d => m z) (ι_formProjection ι F hF s hcov i)
  have hm : (projectionChart ι F hF s i z ∈ V) = (x ∈ projectionOpen ι F j) :=
    congrArg (fun W : U.toScheme.Opens => z ∈ W) (projectionChart_preimage ι F hF s i j)
  exact Iff.of_eq ((congrArg (fun p : PSpace K d => p ∈ V) hmap).trans hm)

theorem formProjection_ratio (i j : Fin (d + 1)) :
    pspacePullRatio (formProjection ι F hF s hcov) (projectionOpen ι F i) i
      (formProjection_preimage ι F hF s hcov i).ge j = projectiveRatio ι (hF i) (hF j) := by
  let U := projectionOpen ι F i
  let V := PSpace.coordinateOpen K d i
  let g := formProjection ι F hF s hcov
  let φ := U.ι.appLE U ⊤ U.ι_preimage_self.ge
  letI : IsIso φ := inferInstanceAs (IsIso (U.ι.appLE U ⊤ U.ι_preimage_self.ge))
  apply (ConcreteCategory.bijective_of_isIso φ).1
  let ev (a : Γ(PSpace K d, V) ⟶ Γ(U.toScheme, ⊤)) := a.hom (pspaceChartRatio K i j)
  have hm := congrArg ev
    (Scheme.Hom.appLE_comp_appLE U.ι g V U ⊤
      (formProjection_preimage ι F hF s hcov i).ge U.ι_preimage_self.ge)
  have hmap := appLE_congr_of_eq (ι_formProjection ι F hF s hcov i) V ⊤
    (U.ι_preimage_self.ge.trans
      (U.ι.preimage_mono (formProjection_preimage ι F hF s hcov i).ge))
    (pspaceOfCoordinates_preimage s U i (ratio ι F hF i))
  exact hm.trans ((congrArg ev hmap).trans
    (pspaceOfCoordinates_ratio s U i _ (projectiveRatio_self ι (hF i)) j))

private theorem pspace_structure_proper (n : ℕ) : IsProper (PSpace.str K n) := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K
  haveI : IsScalarTower K (𝒜 0) (MvPolynomial (Fin (n + 1)) K) :=
    IsScalarTower.of_algebraMap_eq (R := K) (S := ↥(𝒜 0))
      (A := MvPolynomial (Fin (n + 1)) K) (fun _ => rfl)
  haveI : Algebra.FiniteType (𝒜 0) (MvPolynomial (Fin (n + 1)) K) :=
    Algebra.FiniteType.of_restrictScalars_finiteType K _ _
  have h : Function.Bijective (algebraMap K (𝒜 0)) := by
    constructor
    · intro x y hxy
      exact MvPolynomial.C_injective (Fin (n + 1)) K (congrArg Subtype.val hxy)
    · intro a
      have ha := a.2
      change a.1 ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K 0 at ha
      rw [MvPolynomial.homogeneousSubmodule_zero, Submodule.mem_one] at ha
      obtain ⟨r, hr⟩ := ha
      exact ⟨r, Subtype.ext hr⟩
  let E := (RingEquiv.ofBijective (algebraMap K (𝒜 0)) h).toCommRingCatIso
  change IsProper (Proj.toSpecZero 𝒜 ≫ Spec.map E.hom)
  infer_instance

/-- The projection is finite because the positive-degree chart preimages are
affine and the source is projective. -/
theorem formProjection_isFinite [IsClosedImmersion ι] (hs : ι ≫ PSpace.str K N = s)
    (he : 0 < e) : IsFinite (formProjection ι F hF s hcov) := by
  let g := formProjection ι F hF s hcov
  haveI := pspace_structure_proper (K := K) N
  haveI := pspace_structure_proper (K := K) d
  haveI : IsProper (g ≫ PSpace.str K d) := by
    have hg : g ≫ PSpace.str K d = s := formProjection_base ι F hF s hcov
    rw [hg, ← hs]
    infer_instance
  refine IsFinite.iff_isProper_and_isAffineHom.2 ⟨IsProper.of_comp g (PSpace.str K d), ?_⟩
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsAffineHom)
    (PSpace.coordinateOpen K d) (PSpace.iSup_coordinateOpen K d)).2 fun j => ?_
  haveI : IsAffine (PSpace.coordinateOpen K d j).toScheme := pspaceChart_isAffine j
  haveI : IsAffine (g ⁻¹ᵁ PSpace.coordinateOpen K d j).toScheme := by
    have hg : g ⁻¹ᵁ PSpace.coordinateOpen K d j = projectionOpen ι F j :=
      formProjection_preimage ι F hF s hcov j
    rw [hg]
    exact (Proj.isAffineOpen_basicOpen _ _ (hF j) he).preimage ι
  infer_instance

end GlobalTheory.SchemeCohomology
