import Mathlib.RingTheory.AdjoinRoot

/-!
# Translation of a polynomial root algebra

Translating the generator induces an algebra equivalence between the root
algebras of `f(X+t)` and `f(X)`. No irreducibility, monicity, or field
assumption is needed.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Polynomial
variable {R : Type*} [CommRing R]

/-- Substitute the original root minus the translation into the translated equation. -/
def adjoinRootTranslationHom (f : R[X]) (t : R) :
    AdjoinRoot (f.comp (X + C t)) →ₐ[R] AdjoinRoot f :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R (AdjoinRoot f))
    (AdjoinRoot.root f - algebraMap R (AdjoinRoot f) t) (by
      change (f.comp (X + C t)).eval₂ (algebraMap R (AdjoinRoot f))
        (AdjoinRoot.root f - algebraMap R (AdjoinRoot f) t) = 0
      rw [eval₂_comp, eval₂_add, eval₂_X, eval₂_C, sub_add_cancel]
      exact AdjoinRoot.eval₂_root f)

/-- Substitute the translated root plus the translation into the original equation. -/
def adjoinRootTranslationInvHom (f : R[X]) (t : R) :
    AdjoinRoot f →ₐ[R] AdjoinRoot (f.comp (X + C t)) :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R (AdjoinRoot (f.comp (X + C t))))
    (AdjoinRoot.root (f.comp (X + C t)) +
      algebraMap R (AdjoinRoot (f.comp (X + C t))) t) (by
      have h := AdjoinRoot.eval₂_root (f.comp (X + C t))
      rw [eval₂_comp, eval₂_add, eval₂_X, eval₂_C] at h
      exact h)

/-- Translation of the generator is an equivalence of the full quotient algebras. -/
def adjoinRootTranslationEquiv (f : R[X]) (t : R) :
    AdjoinRoot (f.comp (X + C t)) ≃ₐ[R] AdjoinRoot f :=
  AlgEquiv.ofAlgHom (adjoinRootTranslationHom f t) (adjoinRootTranslationInvHom f t)
    (by
      apply AdjoinRoot.algHom_ext
      simp [adjoinRootTranslationHom, adjoinRootTranslationInvHom])
    (by
      apply AdjoinRoot.algHom_ext
      simp [adjoinRootTranslationHom, adjoinRootTranslationInvHom])

end GaloisForLFunctions.HTGeometry
