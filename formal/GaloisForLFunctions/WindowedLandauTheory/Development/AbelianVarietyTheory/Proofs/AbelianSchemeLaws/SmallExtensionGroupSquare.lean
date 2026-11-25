import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.AbelianProductBaseChange
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.AbelianSchemeGlobalSections
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CechProductSlices
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.SmallExtensionCechFibre

/-! A trivialization on a square-zero quotient lifts on an abelian square normalized on
its two axes. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open TopologicalSpace
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
open GlobalTheory.LineBundleSections

namespace GlobalTheory.AbLaw.SmallExtension

attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R] [IsLocalRing R]
  {A : Over (Spec (CommRingCat.of R))} [GrpObj A]
  {L : LB (A ⊗ A).left} {ε : R}

private theorem isClosedImmersion_of_section {X Y : Scheme.{0}}
    {a : X ⟶ Y} {r : Y ⟶ X} [IsSeparated r] (h : a ≫ r = 𝟙 X) :
    IsClosedImmersion a := by
  haveI : IsClosedImmersion (a ≫ r) := by rw [h]; infer_instance
  exact IsClosedImmersion.of_comp a r

/-- The infinitesimal Čech obstruction is killed by the trivializations on the two axes. -/
theorem exists_gen_of_small_extension
    (hA : IsAbelianScheme A) (hL : L.IsLB)
    (hann : ∀ a ∈ IsLocalRing.maximalIdeal R, a * ε = 0)
    (hε : ε ∈ IsLocalRing.maximalIdeal R)
    {X' : Scheme.{0}} {π : X' ⟶ (A ⊗ A).left}
    {f' : X' ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {ε}))}
    (H : IsPullback π f' (A ⊗ A).hom
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))))
    (t : (L.pull π).Gen) (ht : t.IsGen)
    (h₁ : ∃ g : (L.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, g.IsGen)
    (h₂ : ∃ g : (L.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, g.IsGen) :
    ∃ g : L.Gen, g.IsGen := by
  let X := (A ⊗ A).left
  let p := (A ⊗ A).hom
  haveI := hA.smooth
  haveI := hA.proper
  haveI := (hA.tensor hA).smooth
  haveI := (hA.tensor hA).proper
  haveI : IsSeparated (fst A A).left :=
    MorphismProperty.of_isPullback (P := @IsSeparated) (IsPullback.of_hasPullback A.hom A.hom).flip
      inferInstance
  haveI : IsSeparated (snd A A).left :=
    MorphismProperty.of_isPullback (P := @IsSeparated) (IsPullback.of_hasPullback A.hom A.hom)
      inferInstance
  haveI : X.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  let I := {q : L.ι × X.Opens // IsAffineOpen q.2 ∧ q.2 ≤ L.U q.1}
  let W (i : I) := i.1.2
  let c (i : I) := i.1.1
  have haff (i : I) : IsAffineOpen (W i) := i.2.1
  have hle (i : I) : W i ≤ L.U (c i) := i.2.2
  have hc : ⨆ i, W i = ⊤ := by
    refine top_unique fun x _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hL.cover.ge (Set.mem_univ x))
    obtain ⟨V, hV, hx, hsub⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hi
    exact Opens.mem_iSup.mpr ⟨⟨(i, V), hV, hsub⟩, hx⟩
  obtain ⟨u, α, hu, h⟩ := exists_local_lifts H (hann ε hε) t ht W c hle haff
  by_cases hzero : ε = 0
  · refine exists_gen_of_refinement hL W hc c hle u hu fun i j => ?_
    simpa only [hzero, map_zero, zero_mul, add_zero, mul_one] using h i j
  let K := IsLocalRing.ResidueField R
  let φ := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))
  let A₀ := (Over.pullback φ).obj A
  let f₀ := (A₀ ⊗ A₀).hom
  let π₀ := pφ₂ φ A
  have H₀ : IsPullback π₀ f₀ p φ := pφ₂_isPullback φ A
  have hA₀ : IsAbelianScheme A₀ := hA.pullback φ
  haveI := hA₀.proper
  haveI : CompactSpace A₀.left := QuasiCompact.compactSpace_of_compactSpace A₀.hom
  haveI : A₀.left.IsSeparated := ⟨by rw [← terminal.comp_from A₀.hom]; infer_instance⟩
  let T := (A₀ ⊗ A₀).left
  let a : A₀ ⟶ A₀ ⊗ A₀ := lift (𝟙 A₀) (1 : A₀ ⟶ A₀)
  let b : A₀ ⟶ A₀ ⊗ A₀ := lift (1 : A₀ ⟶ A₀) (𝟙 A₀)
  let s : A₀.left ⟶ T := a.left
  let t₀ : A₀.left ⟶ T := b.left
  have hprod : IsPullback (fst A₀ A₀).left (snd A₀ A₀).left A₀.hom A₀.hom :=
    IsPullback.of_hasPullback _ _
  haveI : Smooth (snd A₀ A₀).left := MorphismProperty.of_isPullback hprod hA₀.smooth
  haveI : IsProper (snd A₀ A₀).left := MorphismProperty.of_isPullback hprod hA₀.proper
  haveI : GeometricallyConnected (snd A₀ A₀).left :=
    MorphismProperty.of_isPullback hprod hA₀.geomConnected
  haveI : IsIso A₀.hom.appTop := hA₀.isIso_appTop
  have hf₀ : Function.Surjective A₀.hom.appTop :=
    (ConcreteCategory.bijective_of_isIso A₀.hom.appTop).2
  have hslice (i : A ⟶ A ⊗ A) (r : A ⊗ A ⟶ A) [IsSeparated r.left] (hi : i ≫ r = 𝟙 A)
      (v : (L.pull i.left).Gen) (hv : v.IsGen)
      (j : A₀.left ⟶ T) (hj : j ≫ π₀ = pφ φ A ≫ i.left) :
      ∃ β : ∀ k, Γ(A₀.left, j ⁻¹ᵁ π₀ ⁻¹ᵁ W k),
        ∀ k l, j.app (π₀ ⁻¹ᵁ W k ⊓ π₀ ⁻¹ᵁ W l) (fibreDefect π₀ α k l) =
          resG A₀.left (j.preimage_mono inf_le_left) (β k) -
            resG A₀.left (j.preimage_mono inf_le_right) (β l) := by
    haveI : IsClosedImmersion i.left := isClosedImmersion_of_section (congrArg Over.Hom.left hi)
    have hi' : i.left ≫ p = A.hom := Over.w i
    haveI : Flat (i.left ≫ p) := hi'.symm ▸ inferInstanceAs (Flat A.hom)
    let B := (Over.pullback q).obj A
    have HQ : IsPullback (pφ q A) B.hom (i.left ≫ p) q := by
      rw [hi']
      exact IsPullback.of_hasPullback _ _
    have HK : IsPullback (pφ φ A) A₀.hom (i.left ≫ p) φ := by
      rw [hi']
      exact IsPullback.of_hasPullback _ _
    haveI : IsIso B.hom.appTop := (hA.pullback q).isIso_appTop
    exact h.coboundary_on_fibre_slice hu hzero hε hann hc haff i.left v hv HQ
      (ConcreteCategory.bijective_of_isIso B.hom.appTop).2 HK j hj
  obtain ⟨v₁, hv₁⟩ := h₁
  obtain ⟨v₂, hv₂⟩ := h₂
  have ha : s ≫ (fst A₀ A₀).left = 𝟙 _ := congrArg Over.Hom.left (lift_fst _ _)
  have hb : t₀ ≫ (snd A₀ A₀).left = 𝟙 _ := congrArg Over.Hom.left (lift_snd _ _)
  let y : Spec (CommRingCat.of K) ⟶ A₀.left := η[A₀].left
  have hy : y ≫ A₀.hom = 𝟙 _ := Over.w (η[A₀])
  have ha' : s ≫ (snd A₀ A₀).left = A₀.hom ≫ y := by
    have e := congrArg Over.Hom.left (lift_snd (𝟙 A₀) (1 : A₀ ⟶ A₀))
    exact e
  have ha₀ : s ≫ π₀ = pφ φ A ≫ (lift (𝟙 A) (1 : A ⟶ A)).left := by
    simpa only [Functor.map_id, Functor.map_one] using lift_pφ₂ φ A (𝟙 A) (1 : A ⟶ A)
  have hb₀ : t₀ ≫ π₀ = pφ φ A ≫ (lift (1 : A ⟶ A) (𝟙 A)).left := by
    simpa only [Functor.map_id, Functor.map_one] using lift_pφ₂ φ A (1 : A ⟶ A) (𝟙 A)
  have haxis₁ := hslice (lift (𝟙 A) 1) (fst A A) (lift_fst _ _) v₁ hv₁ s ha₀
  have haxis₂ := hslice (lift 1 (𝟙 A)) (snd A A) (lift_snd _ _) v₂ hv₂ t₀ hb₀
  obtain ⟨β, hβ⟩ := GlobalTheory.CechOne.exists_coboundary_of_pointed_product hprod hf₀ hy ha ha' hb
    (π₀.iSup_preimage_eq_top hc) (h.isCocycle_fibre hL haff hu hzero hε hann H₀) haxis₁ haxis₂
  refine h.exists_gen_of_coboundary hL hc haff hu hzero hε hann H₀ β fun i j => ?_
  rw [Scheme.Hom.app_eq_appLE]
  exact hβ i j

end GlobalTheory.AbLaw.SmallExtension
