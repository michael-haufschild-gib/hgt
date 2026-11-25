import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! Functions descend along an effective epimorphism from equality on its kernel pair. -/

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.FlatDescent

universe u

variable {X Y Z : Scheme.{u}}

/-- Pullback of global functions is injective along an epimorphism. -/
theorem injective_appTop_of_epi (p : Y ⟶ X) [Epi p] : Function.Injective p.appTop := by
  have : Epi (Scheme.Γ.rightOp.map p) :=
    have := ΓSpec.adjunction.isLeftAdjoint
    inferInstance
  have : Mono p.appTop := inferInstanceAs (Mono (Scheme.Γ.rightOp.map p).unop)
  exact ConcreteCategory.injective_of_mono_of_preservesPullback p.appTop

/-- The affine target representing a function descends along the kernel pair. -/
theorem exists_appTop_eq_of_effectiveEpi (p : Y ⟶ X) [EffectiveEpi p] {f g : Z ⟶ Y}
    (h : IsPullback f g p p) (s : Γ(Y, ⊤)) (hs : f.appTop s = g.appTop s) :
    ∃ a : Γ(X, ⊤), p.appTop a = s := by
  let E := RingHom.eqLocus f.appTop.hom g.appTop.hom
  let ι : CommRingCat.of E ⟶ Γ(Y, ⊤) := CommRingCat.ofHom E.subtype
  have hι : ι ≫ f.appTop = ι ≫ g.appTop := by
    ext x
    exact x.2
  have : HasPullback p p := inferInstance
  obtain ⟨u, hu⟩ := IsRegularEpi.exists_of_isKernelPair p h (Y.toSpecΓ ≫ Spec.map ι) (by
    rw [Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp,
      ← Spec.map_comp, hι])
  refine ⟨u.appTop ((Scheme.ΓSpecIso (.of E)).inv ⟨s, hs⟩), ?_⟩
  have h1 : (Scheme.ΓSpecIso (.of E)).inv ≫ u.appTop ≫ p.appTop = ι := by
    rw [← Scheme.Hom.comp_appTop, hu, Scheme.Hom.comp_appTop,
      ← Scheme.ΓSpecIso_inv_naturality_assoc]
    simp
  exact congr($h1 ⟨s, hs⟩)

end GlobalTheory.FlatDescent
