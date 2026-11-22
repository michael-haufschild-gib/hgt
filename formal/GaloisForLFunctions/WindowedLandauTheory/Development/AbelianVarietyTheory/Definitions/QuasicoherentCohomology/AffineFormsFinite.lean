import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.AffineFormsSections
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! Relative differential forms are finite modules on affine opens of a finite-type scheme. -/

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace GlobalTheory.SchemeCohomology

private theorem exteriorPower_finite {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [Module.Finite A M] (p : ℕ) : Module.Finite A (⋀[A]^p M) := by
  classical
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := A) (M := M)
  let wedge (v : Fin p → G) : ⋀[A]^p M := exteriorPower.ιMulti A p fun i => (v i).val
  have e : Set.range wedge = exteriorPower.ιMulti A p '' {v | Set.range v ⊆ (G : Set M)} := by
    ext w
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨fun i => (v i).val, ?_, rfl⟩
      rintro _ ⟨i, rfl⟩
      exact (v i).prop
    · rintro ⟨v, hv, rfl⟩
      exact ⟨fun i => ⟨v i, hv ⟨i, rfl⟩⟩, rfl⟩
  refine ⟨⟨Finset.univ.image wedge, ?_⟩⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, e]
  exact exteriorPower.ιMulti_span_of_span A p M hG

universe u

variable {k : Type u} [CommRing k] {X : Scheme.{u}} (s : X ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType s]

/-- An affine section algebra of a scheme locally of finite type is of finite type over the base. -/
theorem sectionRing_finiteType {U : X.Opens} (hU : IsAffineOpen U) :
    Algebra.FiniteType k (SectionRing s U) := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of k)).inv
  have he : e.hom.FiniteType := RingHom.FiniteType.of_surjective _
    (ConcreteCategory.bijective_of_isIso e).surjective
  have h := s.finiteType_appLE (isAffineOpen_top _) hU (by simp : U ≤ s ⁻¹ᵁ ⊤)
  change (e ≫ s.appLE ⊤ U _).hom.FiniteType
  rw [CommRingCat.hom_comp]
  exact RingHom.FiniteType.comp h he

/-- Sections of relative forms on an affine open are finitely generated over its section ring. -/
theorem relativeForms_sections_finite {U : X.Opens} (hU : IsAffineOpen U) (p : ℕ) :
    Module.Finite Γ(X, U) Γ(relativeForms s p, U) := by
  letI := sectionRing_finiteType s hU
  haveI : Module.Finite (SectionRing s U) (FormsOn s U p) := exteriorPower_finite p
  letI : Module (SectionRing s U) Γ(relativeForms s p, U) :=
    inferInstanceAs (Module Γ(X, U) Γ(relativeForms s p, U))
  have h : Module.Finite (SectionRing s U) Γ(relativeForms s p, U) :=
    Module.Finite.equiv (affineFormsSections s p hU)
  exact h

end GlobalTheory.SchemeCohomology
