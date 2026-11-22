import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.RelativeForms
import GaloisForLFunctions.HTGeometry.AlgebraicGroupRationalPointEvaluation
import GaloisForLFunctions.HTGeometry.BaseFieldPointComplexification

/-! Over an affine open, a base-field point is determined by its algebra
evaluation map on sections. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open GaloisForLFunctions.HTGeometry

namespace GlobalTheory.SchemeCohomology

variable {K : Type} [Field K] {X : Scheme.{0}} {s : X ⟶ Spec (CommRingCat.of K)}
  {U : X.Opens}

/-- Evaluation of sections at a point over the identity base point. -/
def affinePointEval (y : X.BaseFieldPointOver K s) (hy : y.hom default ∈ U) :
    SectionRing s U →ₐ[K] K where
  toRingHom := pointEval y.hom U hy
  commutes' r := pointEval_structureSection s y.hom y.commutes U hy r

private theorem fromSpec_over (hU : IsAffineOpen U) :
    hU.fromSpec ≫ s = Spec.map (CommRingCat.ofHom (algebraMap K (SectionRing s U))) := by
  let Z := Spec (CommRingCat.of K)
  have e : U ≤ s ⁻¹ᵁ ⊤ := by simp
  let hZ := isAffineOpen_top Z
  calc
    _ = Spec.map (s.appLE ⊤ U e) ≫ hZ.fromSpec :=
      (hZ.SpecMap_appLE_fromSpec s hU e).symm
    _ = Spec.map ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ s.appLE ⊤ U e) := by
      rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, Spec.map_comp]
    _ = _ := rfl

private theorem pointEval_fromSpec (hU : IsAffineOpen U) (y : Spec (CommRingCat.of K) ⟶ X)
    (hy : y default ∈ U) :
    Spec.map (CommRingCat.ofHom (pointEval y U hy)) ≫ hU.fromSpec = y := by
  let Z := Spec (CommRingCat.of K)
  let e : ⊤ ≤ y ⁻¹ᵁ U := top_le_preimage_of_mem y hy
  let hZ := isAffineOpen_top Z
  let t := Scheme.ΓSpecIso (CommRingCat.of K)
  change Spec.map (y.appLE U ⊤ e ≫ t.hom) ≫ hU.fromSpec = _
  rw [Spec.map_comp, Category.assoc, hU.SpecMap_appLE_fromSpec y hZ e,
    ← Category.assoc, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.id_comp]

/-- A homomorphism from the section algebra of an affine open to the base
field gives a rational point in that open. -/
def affinePointOfAlgHom (hU : IsAffineOpen U) (χ : SectionRing s U →ₐ[K] K) :
    {y : X.BaseFieldPointOver K s // y.hom default ∈ U} := by
  let y := Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ hU.fromSpec
  have hy : y ≫ s = 𝟙 _ := by
    have hχ : CommRingCat.ofHom (algebraMap K (SectionRing s U)) ≫ CommRingCat.ofHom χ.toRingHom =
        𝟙 (CommRingCat.of K) := by
      apply CommRingCat.ext
      intro r
      exact χ.commutes r
    change Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ hU.fromSpec ≫ s = _
    rw [fromSpec_over hU, ← Spec.map_comp, hχ, Spec.map_id]
  refine ⟨⟨y, hy⟩, ?_⟩
  change hU.fromSpec (Spec.map (CommRingCat.ofHom χ.toRingHom) default) ∈ U
  rw [← hU.range_fromSpec]
  exact Set.mem_range_self _

/-- The affine correspondence between rational points and algebra homomorphisms. -/
def affinePointEquiv (hU : IsAffineOpen U) :
    {y : X.BaseFieldPointOver K s // y.hom default ∈ U} ≃ (SectionRing s U →ₐ[K] K) :=
  Equiv.ofBijective (fun y => affinePointEval y.1 y.2) (by
    constructor
    · intro x y h
      have hx := pointEval_fromSpec hU x.1.hom x.2
      have hy := pointEval_fromSpec hU y.1.hom y.2
      have he := congrArg (fun χ : SectionRing s U →ₐ[K] K =>
        Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ hU.fromSpec) h
      have hxy : x.1.hom = y.1.hom := hx.symm.trans (he.trans hy)
      apply Subtype.ext
      rcases x with ⟨⟨x, hx⟩, _⟩
      rcases y with ⟨⟨y, hy⟩, _⟩
      change x = y at hxy
      cases hxy
      rfl
    · intro χ
      let y := affinePointOfAlgHom hU χ
      refine ⟨y, ?_⟩
      have h := pointEval_fromSpec hU y.1.hom y.2
      change Spec.map (CommRingCat.ofHom (affinePointEval y.1 y.2).toRingHom) ≫ hU.fromSpec =
        Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ hU.fromSpec at h
      have e := Spec.map_injective ((cancel_mono hU.fromSpec).mp h)
      exact AlgHom.ext fun r => ConcreteCategory.congr_hom e r)

end GlobalTheory.SchemeCohomology
