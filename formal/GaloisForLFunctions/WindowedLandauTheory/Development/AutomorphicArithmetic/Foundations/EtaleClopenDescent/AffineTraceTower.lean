import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveTraceTower
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineFiniteEtaleTrace

/-! Affine traces of functions and differential forms compose
along towers of finite étale morphisms. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TensorProduct

namespace GlobalTheory.SchemeCohomology

variable {k : Type} [CommRing k] {X Y Z : Scheme.{0}}
  {s : X ⟶ Spec (CommRingCat.of k)} {t : Y ⟶ Spec (CommRingCat.of k)}
  {u : Z ⟶ Spec (CommRingCat.of k)} {f : Y ⟶ X} {g : Z ⟶ Y}
  [IsFinite f] [Etale f]

private theorem affineSectionAlgebra_etale {U : X.Opens} (hU : IsAffineOpen U) :
    letI : Algebra (SectionRing s U) (SectionRing t (f ⁻¹ᵁ U)) := (f.app U).hom.toAlgebra
    Algebra.Etale (SectionRing s U) (SectionRing t (f ⁻¹ᵁ U)) := by
  have h := f.etale_appLE hU (hU.preimage f) le_rfl
  rw [← Scheme.Hom.app_eq_appLE] at h
  exact h

/-- Forms over the pullback affine are sums of multiples of
pullbacks of forms over the base affine. -/
theorem affineEtaleForms_induction (hf : f ≫ s = t) {U : X.Opens} (hU : IsAffineOpen U)
    (p : ℕ) {P : FormsOn t (f ⁻¹ᵁ U) p → Prop}
    (h0 : P 0) (ha : ∀ x y, P x → P y → P (x + y))
    (hb : ∀ (b : SectionRing t (f ⁻¹ᵁ U)) (ω : FormsOn s U p),
      P (b • ExteriorDifferentials.map (sectionPullback hf U) p ω))
    (y : FormsOn t (f ⁻¹ᵁ U) p) : P y := by
  let A := SectionRing s U
  let B := SectionRing t (f ⁻¹ᵁ U)
  letI : Algebra A B := (f.app U).hom.toAlgebra
  letI : IsScalarTower k A B := .of_algebraMap_eq fun r => ((sectionPullback hf U).commutes r).symm
  letI : Algebra.Etale A B := affineSectionAlgebra_etale (s := s) (t := t) (f := f) hU
  let H := algebraFormPullback_isBaseChange k A B p
  obtain ⟨z, rfl⟩ := H.equiv.surjective y
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact h0
  | add a b ha' hb' => rw [map_add]; exact ha _ _ ha' hb'
  | tmul b ω =>
    rw [H.equiv_tmul, algebraFormPullback_eq_map k A B (sectionPullback hf U) rfl]
    exact hb b ω

variable [IsFinite g] [Etale g]

/-- Trace of functions over an affine open is transitive. -/
theorem affineSectionTrace_trans {U : X.Opens} (hU : IsAffineOpen U)
    (b : SectionRing u ((g ≫ f) ⁻¹ᵁ U)) :
    affineSectionTrace (f := g ≫ f) s u hU b =
      affineSectionTrace (f := f) s t hU (affineSectionTrace (f := g) t u (hU.preimage f) b) := by
  let A := SectionRing s U
  let B := SectionRing t (f ⁻¹ᵁ U)
  let C := SectionRing u ((g ≫ f) ⁻¹ᵁ U)
  letI : Algebra A B := (f.app U).hom.toAlgebra
  letI : Algebra B C := (g.app (f ⁻¹ᵁ U)).hom.toAlgebra
  letI : Algebra A C := ((g ≫ f).app U).hom.toAlgebra
  letI : IsScalarTower A B C := .of_algebraMap_eq fun a =>
    ConcreteCategory.congr_hom (Scheme.Hom.comp_app g f U) a
  letI : Module.Finite A B := f.finite_app U hU
  letI : Module.Finite B C := g.finite_app _ (hU.preimage f)
  letI : Module.Finite A C := (g ≫ f).finite_app U hU
  letI : Algebra.Etale A B := affineSectionAlgebra_etale (s := s) (t := t) (f := f) hU
  letI : Algebra.Etale B C := affineSectionAlgebra_etale (s := t) (t := u) (f := g) (hU.preimage f)
  letI : Algebra.Etale A C := affineSectionAlgebra_etale (s := s) (t := u) (f := g ≫ f) hU
  exact finiteEtaleAlgebraTrace_trans b

/-- Trace of forms over an affine open is transitive. -/
theorem affineFormTrace_trans (hf : f ≫ s = t) (hg : g ≫ t = u) (hgf : (g ≫ f) ≫ s = u)
    {U : X.Opens} (hU : IsAffineOpen U) (p : ℕ) (ω : FormsOn u ((g ≫ f) ⁻¹ᵁ U) p) :
    affineFormTrace hgf hU p ω =
      affineFormTrace hf hU p (affineFormTrace hg (hU.preimage f) p ω) := by
  let L := affineFormTrace hgf hU p
  let R : FormsOn u ((g ≫ f) ⁻¹ᵁ U) p →+ FormsOn s U p :=
    (affineFormTrace hf hU p).comp (affineFormTrace hg (hU.preimage f) p)
  refine affineEtaleForms_induction hgf hU p (P := fun ω => L ω = R ω)
    (L.map_zero.trans R.map_zero.symm)
    (fun a b ha hb => by rw [L.map_add, R.map_add, ha, hb]) ?_ ω
  intro b ξ
  have he : sectionPullback hgf U =
      (sectionPullback hg (f ⁻¹ᵁ U)).comp (sectionPullback hf U) :=
    AlgHom.ext fun a => ConcreteCategory.congr_hom (Scheme.Hom.comp_app g f U) a
  let η := ExteriorDifferentials.map (sectionPullback hf U) p ξ
  let ζ : FormsOn u ((g ≫ f) ⁻¹ᵁ U) p :=
    ExteriorDifferentials.map (sectionPullback hg (f ⁻¹ᵁ U)) p η
  have hmap : ExteriorDifferentials.map (sectionPullback hgf U) p ξ = ζ := by
    exact (congrArg (fun a => ExteriorDifferentials.map a p ξ) he).trans
      (ExteriorDifferentials.map_comp _ _ p ξ)
  let b' : SectionRing u (g ⁻¹ᵁ (f ⁻¹ᵁ U)) := b
  let τ := affineSectionTrace (f := g) t u (hU.preimage f) b'
  have hR : R (b • ζ) = affineSectionTrace (f := f) s t hU τ • ξ :=
    (congrArg (fun z => affineFormTrace hf hU p z)
      (affineFormTrace_smul_pullback hg (hU.preimage f) p b' η)).trans
      (affineFormTrace_smul_pullback hf hU p τ ξ)
  calc
    _ = affineSectionTrace (f := g ≫ f) s u hU b • ξ :=
      affineFormTrace_smul_pullback hgf hU p b ξ
    _ = affineSectionTrace (f := f) s t hU τ • ξ :=
      congrArg (· • ξ) (affineSectionTrace_trans hU b)
    _ = R (b • ζ) := hR.symm
    _ = _ := congrArg (fun z => R (b • z)) hmap.symm

private theorem finiteEtaleAlgebraTrace_one_of_bijective {A B : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] [Algebra.Etale A B]
    (h : Function.Bijective (algebraMap A B)) : finiteEtaleAlgebraTrace A B 1 = 1 := by
  letI : Module.FinitePresentation A B := .of_finite_of_finitePresentation A B
  letI : Module.Projective A B := Module.Flat.projective_of_finitePresentation
  let e : A ≃ₐ[A] B := AlgEquiv.ofBijective (Algebra.ofId A B) h
  have hmul : LinearMap.mul A B (1 : B) = e.symm.toLinearMap.smulRight (1 : B) := by
    apply LinearMap.ext
    intro b
    change (1 : B) * b = (e.symm b) • (1 : B)
    rw [one_mul, Algebra.smul_def, mul_one]
    exact (e.apply_symm_apply b).symm
  change projectiveTrace A B (LinearMap.mul A B (1 : B)) = 1
  rw [hmul, projectiveTrace_rankOne]
  exact e.symm.map_one

/-- The affine algebra of an identity morphism has trace one. -/
theorem affineSectionTrace_id_one (s : X ⟶ Spec (CommRingCat.of k))
    {U : X.Opens} (hU : IsAffineOpen U) :
    affineSectionTrace (f := 𝟙 X) s s hU 1 = 1 := by
  let i : X ⟶ X := 𝟙 X
  let A := SectionRing s U
  let B := SectionRing s (i ⁻¹ᵁ U)
  letI : Algebra A B := (i.app U).hom.toAlgebra
  letI : Module.Finite A B := i.finite_app U hU
  letI : Algebra.Etale A B := affineSectionAlgebra_etale (s := s) (t := s) (f := i) hU
  have hm (a : A) : (i.app U).hom a = a := by
    change ((𝟙 X : X ⟶ X).app U).hom a = a
    rw [Scheme.Hom.id_app] <;> rfl
  have hb : Function.Bijective (algebraMap A B) := by
    change Function.Bijective (i.app U).hom
    exact ⟨fun a b h => (hm a).symm.trans (h.trans (hm b)), fun b => ⟨b, hm b⟩⟩
  exact finiteEtaleAlgebraTrace_one_of_bijective hb

end GlobalTheory.SchemeCohomology
