import GaloisForLFunctions.RHTower.DeningerDynSysProp35Global
import GaloisForLFunctions.RHTower.DeningerDynSysIntegralLift
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Normalization

/-!
# Proposition 3.5, surjectivity, for an integral morphism

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 3.5, the
surjectivity half.

For an integral morphism of schemes whose section maps are injective, every point with values in
an algebraically closed field lifts.  No group action is involved: over an affine open of the base
the section map is an injective integral ring homomorphism, and along such a map homomorphisms
into an algebraically closed field extend.

Applied to the relative normalization `π : f.normalization ⟶ Y` of a scheme-theoretically dominant
quasi-compact quasi-separated morphism `f : X ⟶ Y`, both hypotheses hold unconditionally: `π` is
integral, and its section maps are injective because `f` factors through `π`.
-/

namespace RHTower

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

variable {X X₀ : Scheme.{u}} (π : X ⟶ X₀) {C : Type u} [Field C] [IsAlgClosed C]

/-- **Deninger, Proposition 3.5, surjectivity.**  Along an integral morphism with injective
section maps, every point of the base with values in an algebraically closed field lifts. -/
theorem deningerSchemePoint_surjective_of_isIntegralHom [IsIntegralHom π]
    (hinj : ∀ U₀ : X₀.Opens, IsAffineOpen U₀ → Function.Injective (π.app U₀).hom) :
    Function.Surjective (fun h : Spec (CommRingCat.of C) ⟶ X => h ≫ π) := by
  refine deningerSchemePoint_surjective π fun x₀ => ?_
  obtain ⟨U₀, hU₀, hmem, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (X := X₀) (x := x₀) (U := ⊤) trivial
  refine ⟨U₀, hU₀, hmem, hU₀.preimage π, ?_⟩
  intro φ
  obtain ⟨ψ, hψ⟩ := deningerHom_exists_extension_of_ringHom_isIntegral
      (C := C) (π.app U₀).hom (IsIntegralHom.isIntegral_app π U₀ hU₀) (hinj U₀ hU₀) φ.hom
  exact ⟨CommRingCat.ofHom ψ, by ext x; exact congrArg (fun r : Γ(X₀, U₀) →+* C => r x) hψ⟩

variable {Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- The section maps of the relative normalization are injective when those of the given morphism
are: the morphism factors through its normalization, so its section map factors through that of
`fromNormalization`. -/
theorem deningerNormalization_app_injective [IsSchemeTheoreticallyDominant f] (U : Y.Opens) :
    Function.Injective (f.fromNormalization.app U).hom := by
  intro a b hab
  refine f.app_injective U ?_
  have h1 : ((f.toNormalization ≫ f.fromNormalization).app U).hom a
      = ((f.toNormalization ≫ f.fromNormalization).app U).hom b := by
    show (f.toNormalization.app (f.fromNormalization ⁻¹ᵁ U)).hom
        ((f.fromNormalization.app U).hom a)
      = (f.toNormalization.app (f.fromNormalization ⁻¹ᵁ U)).hom
        ((f.fromNormalization.app U).hom b)
    rw [hab]
  rw [Scheme.Hom.toNormalization_fromNormalization] at h1
  exact h1

/-- **Deninger, Proposition 3.5, surjectivity for the relative normalization.**  Every point of
the base with values in an algebraically closed field lifts to the normalization of the base in a
scheme-theoretically dominant morphism. -/
theorem deningerNormalizationPoint_surjective [IsSchemeTheoreticallyDominant f] :
    Function.Surjective (fun h : Spec (CommRingCat.of C) ⟶ f.normalization =>
      h ≫ f.fromNormalization) :=
  deningerSchemePoint_surjective_of_isIntegralHom (C := C) f.fromNormalization
    fun U _ => deningerNormalization_app_injective f U

end

end RHTower
