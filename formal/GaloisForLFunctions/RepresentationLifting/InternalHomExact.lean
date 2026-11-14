import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Exactness of internal Hom for representations over a field

Applying `Hom(V, -)` to a short exact sequence of representations preserves
short exactness. Linear sections need not be equivariant: they prove surjectivity
and identify the kernel of the equivariant internal-Hom maps on underlying
vector spaces. This supplies the coefficient sequence used in Scavia's Lemma 6.1.
-/

noncomputable section

open CategoryTheory

namespace GaloisForLFunctions.RepresentationLifting

universe u

section Ring

variable {k G : Type u} [CommRing k] [Group G]

/-- Postcomposition is additive in the coefficient morphism. -/
instance representationIHom_additive (V : Rep k G) : (Rep.ihom V).Additive where
  map_add := by
    intro X Y f g
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro T
    apply LinearMap.ext
    intro v
    rfl

/-- Postcomposition is linear in the coefficient morphism. -/
instance representationIHom_linear (V : Rep k G) : Functor.Linear k (Rep.ihom V) where
  map_smul f a := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro T
    apply LinearMap.ext
    intro v
    rfl

end Ring

variable {k G : Type u} [Field k] [Group G]

/-- Internal Hom preserves short exact sequences of representations over a field. -/
theorem representationIHom_shortExact (V : Rep k G) (X : ShortComplex (Rep k G))
    (hX : X.ShortExact) : (X.map (Rep.ihom V)).ShortExact := by
  have hf : Function.Injective X.f.hom.toLinearMap := (Rep.mono_iff_injective X.f).mp hX.mono_f
  have hg : Function.Surjective X.g.hom.toLinearMap := (Rep.epi_iff_surjective X.g).mp hX.epi_g
  have hfg : LinearMap.range X.f.hom.toLinearMap = LinearMap.ker X.g.hom.toLinearMap :=
    (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
  obtain ⟨r, hr⟩ := X.f.hom.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)
  obtain ⟨s, hs⟩ := X.g.hom.toLinearMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hg)
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · apply (forget₂ (Rep k G) (ModuleCat k)).reflects_exact_of_faithful
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    change LinearMap.range ((Rep.ihom V).map X.f).hom.toLinearMap =
      LinearMap.ker ((Rep.ihom V).map X.g).hom.toLinearMap
    ext φ
    constructor
    · rintro ⟨ψ, rfl⟩
      change V →ₗ[k] X.X₁ at ψ
      apply LinearMap.ext
      intro v
      exact congrArg (fun f : X.X₁ ⟶ X.X₃ => f.hom (ψ v)) X.zero
    · intro hφ
      change V →ₗ[k] X.X₂ at φ
      have hzero : X.g.hom.toLinearMap.comp φ = 0 := hφ
      refine ⟨r.comp φ, ?_⟩
      apply LinearMap.ext
      intro v
      have hv : φ v ∈ LinearMap.range X.f.hom.toLinearMap := by
        rw [hfg]
        exact LinearMap.congr_fun hzero v
      obtain ⟨x, hx⟩ := hv
      change X.f.hom (r (φ v)) = φ v
      rw [← hx]
      exact congrArg X.f.hom (LinearMap.congr_fun hr x)
  · rw [Rep.mono_iff_injective]
    intro φ ψ h
    apply LinearMap.ext
    intro v
    apply hf
    exact LinearMap.congr_fun h v
  · rw [Rep.epi_iff_surjective]
    intro φ
    change V →ₗ[k] X.X₃ at φ
    refine ⟨s.comp φ, ?_⟩
    apply LinearMap.ext
    intro v
    exact LinearMap.congr_fun hs (φ v)

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.representationIHom_shortExact
