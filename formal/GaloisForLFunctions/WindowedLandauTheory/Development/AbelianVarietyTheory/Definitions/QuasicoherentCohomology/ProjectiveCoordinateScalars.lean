import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveCompactness
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.RelativeForms

/-! Base scalars on projective coordinate charts are constant homogeneous fractions. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace GlobalTheory.SchemeCohomology

universe u

private theorem toSpecZero_chart {A σ : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] {d : ℕ} {f : A}
    (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv ≫
        (Proj.toSpecZero 𝒜).appLE ⊤ (Proj.basicOpen 𝒜 f) (by simp) =
      CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f)) ≫
        Proj.awayToSection 𝒜 f := by
  let U := Proj.basicOpen 𝒜 f
  let e := Proj.basicOpenIsoSpec 𝒜 f hf hd
  let v := CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f))
  have hchart : U.ι ≫ Proj.toSpecZero 𝒜 = Proj.basicOpenToSpec 𝒜 f ≫ Spec.map v := by
    have h := congrArg (fun g => e.hom ≫ g) (Proj.awayι_toSpecZero 𝒜 f hf hd)
    simpa only [v, Proj.awayι, ← Category.assoc, e.hom_inv_id, Category.id_comp,
      Proj.basicOpenIsoSpec_hom, e] using h
  have hres : U.ι.appTop ≫ U.topIso.hom =
      (Proj 𝒜).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op := by
    rw [Scheme.Opens.ι_appTop]
    change (Proj 𝒜).presheaf.map (homOfLE (x := U.ι ''ᵁ ⊤) le_top).op ≫
      (Proj 𝒜).presheaf.map (eqToHom U.ι_image_top.symm).op = _
    rw [← Functor.map_comp]
    rfl
  have he : (Proj.toSpecZero 𝒜).appLE ⊤ U (by simp) =
      (U.ι ≫ Proj.toSpecZero 𝒜).appTop ≫ U.topIso.hom := by
    rw [Scheme.Hom.comp_appTop, Category.assoc, hres]
    rfl
  change _ ≫ (Proj.toSpecZero 𝒜).appLE ⊤ U _ = v ≫ _
  rw [he, hchart, Scheme.Hom.comp_appTop, Proj.basicOpenToSpec_app_top]
  rw [← Category.assoc, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  simp [Category.assoc]

open UpperTheory.Cb

attribute [local instance] MvPolynomial.gradedAlgebra

/-- On positive-degree basic opens, the ordinary base algebra sends a scalar to the
constant fraction in the section ring. -/
theorem pspace_algebraMap_basicOpen {K : Type u} [CommRing K] (N : ℕ)
    {d : ℕ} {f : MvPolynomial (Fin (N + 1)) K}
    (hf : f.IsHomogeneous d) (hd : 0 < d) (c : K) :
    let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K
    letI := sectionAlgebra (PSpace.str K N) (Proj.basicOpen 𝒜 f)
    algebraMap K Γ(PSpace K N, Proj.basicOpen 𝒜 f) c =
      (Proj.awayToSection 𝒜 f).hom
        (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f) (algebraMap K (𝒜 0) c)) := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K
  let U := Proj.basicOpen 𝒜 f
  let b := CommRingCat.ofHom (algebraMap K (𝒜 0))
  have h : (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (PSpace.str K N).appLE ⊤ U (by simp) =
      b ≫ CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f)) ≫
        Proj.awayToSection 𝒜 f := by
    change (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      (Proj.toSpecZero 𝒜 ≫ Spec.map b).appLE ⊤ U _ = _
    rw [Scheme.Hom.comp_appLE, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      toSpecZero_chart 𝒜 hf hd]
  exact ConcreteCategory.congr_hom h c

/-- The value of a base scalar at any point of a projective coordinate chart
is the image of the constant polynomial in the local ring. -/
theorem pspace_algebraMap_basicOpen_val {K : Type u} [CommRing K] (N : ℕ)
    {d : ℕ} {f : MvPolynomial (Fin (N + 1)) K}
    (hf : f.IsHomogeneous d) (hd : 0 < d) (c : K)
    (x : Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f) :
    let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K
    letI := sectionAlgebra (PSpace.str K N) (Proj.basicOpen 𝒜 f)
    ((algebraMap K Γ(PSpace K N, Proj.basicOpen 𝒜 f) c).1 x).val =
      algebraMap _ (Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl) (MvPolynomial.C c) := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K
  let b := algebraMap K (𝒜 0) c
  letI := sectionAlgebra (PSpace.str K N) (Proj.basicOpen 𝒜 f)
  change ((algebraMap K Γ(PSpace K N, Proj.basicOpen 𝒜 f) c).1 x).val = _
  rw [pspace_algebraMap_basicOpen N hf hd]
  erw [ProjectiveSpectrum.Proj.awayToSection_apply]
  have hval : (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f) b).val =
      algebraMap _ (Localization.Away f) b.1 := by
    change (HomogeneousLocalization.mk ⟨0, b, 1, one_mem (Submonoid.powers f)⟩).val = _
    rw [HomogeneousLocalization.val_mk]
    exact Localization.mk_one_eq_algebraMap _
  change IsLocalization.map (M := Submonoid.powers f) (T := x.1.asHomogeneousIdeal.toIdeal.primeCompl)
    _ (RingHom.id _) (Submonoid.powers_le.mpr x.2)
      (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f) b).val = _
  rw [hval, IsLocalization.map_eq]
  rfl

end GlobalTheory.SchemeCohomology
