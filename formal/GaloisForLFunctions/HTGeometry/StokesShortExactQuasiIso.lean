import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Middle quasi-isomorphism for short exact chain-complex sequences

This file supplies the middle two-out-of-three lemma missing from mathlib's current
homology-sequence API for nonnegative chain complexes. It is the five-lemma bridge used
to propagate quasi-isomorphisms through finite projective-cell filtrations.
-/

namespace GaloisForLFunctions.IrregularStokes.ShortExactQuasiIso

open CategoryTheory ComposableArrows Abelian
open HomologicalComplex

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  {S₁ S₂ : ShortComplex (ChainComplex C ℕ)}

/-- In a morphism of short exact nonnegative chain-complex sequences,
quasi-isomorphisms on the outer terms force one on the middle term. -/
theorem quasiIso_middle (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
    (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) : QuasiIso φ.τ₂ := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hmono : Mono (homologyMap φ.τ₂ i) := by
    apply mono_of_epi_of_mono_of_mono
      ((δ₀Functor ⋙ δ₀Functor).map
        (HomologySequence.mapComposableArrows₅ φ hS₁ hS₂ (i + 1) i (by simp)))
    · exact (HomologySequence.composableArrows₅_exact hS₁ (i + 1) i (by simp)).δ₀.δ₀
    · exact (HomologySequence.composableArrows₅_exact hS₂ (i + 1) i (by simp)).δ₀.δ₀
    · change Epi (homologyMap φ.τ₃ (i + 1))
      letI : QuasiIsoAt φ.τ₃ (i + 1) := h₃.quasiIsoAt (i + 1)
      infer_instance
    · change Mono (homologyMap φ.τ₁ i)
      letI : QuasiIsoAt φ.τ₁ i := h₁.quasiIsoAt i
      infer_instance
    · change Mono (homologyMap φ.τ₃ i)
      letI : QuasiIsoAt φ.τ₃ i := h₃.quasiIsoAt i
      infer_instance
  have hepi : Epi (homologyMap φ.τ₂ i) := by
    cases i with
    | zero =>
        apply epi_of_epi_of_epi_of_epi
          (HomologySequence.mapComposableArrows₂ φ 0)
          (HomologySequence.composableArrows₂_exact hS₂ 0)
        · have := hS₁.epi_g
          apply epi_homologyMap_of_epi_of_not_rel S₁.g 0
          simp
        · change Epi (homologyMap φ.τ₁ 0)
          letI : QuasiIsoAt φ.τ₁ 0 := h₁.quasiIsoAt 0
          infer_instance
        · change Epi (homologyMap φ.τ₃ 0)
          letI : QuasiIsoAt φ.τ₃ 0 := h₃.quasiIsoAt 0
          infer_instance
    | succ n =>
        apply epi_of_epi_of_epi_of_mono
          ((δlastFunctor ⋙ δlastFunctor).map
            (HomologySequence.mapComposableArrows₅ φ hS₁ hS₂ (n + 1) n (by simp)))
        · exact (HomologySequence.composableArrows₅_exact hS₁ (n + 1) n (by simp)).δlast.δlast
        · exact (HomologySequence.composableArrows₅_exact hS₂ (n + 1) n (by simp)).δlast.δlast
        · change Epi (homologyMap φ.τ₁ (n + 1))
          letI : QuasiIsoAt φ.τ₁ (n + 1) := h₁.quasiIsoAt (n + 1)
          infer_instance
        · change Epi (homologyMap φ.τ₃ (n + 1))
          letI : QuasiIsoAt φ.τ₃ (n + 1) := h₃.quasiIsoAt (n + 1)
          infer_instance
        · change Mono (homologyMap φ.τ₁ n)
          letI : QuasiIsoAt φ.τ₁ n := h₁.quasiIsoAt n
          infer_instance
  letI := hmono
  letI := hepi
  exact isIso_of_mono_of_epi _

end GaloisForLFunctions.IrregularStokes.ShortExactQuasiIso
