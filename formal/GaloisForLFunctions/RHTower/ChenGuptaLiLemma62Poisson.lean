import GaloisForLFunctions.RHTower.ChenGuptaLiLemma45CharacterPoisson
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62FunctionalEquation

/-!
# Chen--Gupta--Li Lemma 6.2: character Poisson representation

This is equation (6.1) in the normalization where both sides are multiplied
by `N / q`.  The original source transform is the complete additive-character
Fourier series, while the equal physical-side expression is a smoothed
Dirichlet character sum.  The exact equality supplies the Mellin input for
the contour-shift stage of Lemma 6.2.
-/

open Complex
open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

/-- The finite additive-character transform in CGL Lemma 6.2, normalized by
`N / q`.  This avoids any division theorem: it is exactly the Fourier side
already produced by affine Poisson summation. -/
def cglLemma62NormalizedPoissonTransform
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus)
    (χ : DirichletCharacter ℂ Q.value) (t : ℝ) : ℂ :=
  ∑ a : ZMod Q.value, ∑' m : ℤ,
    χ a * ZMod.stdAddChar (a * (m : ZMod Q.value)) *
      ((cglAffineFourierScale N Q : ℂ) *
        𝓕 (cglSmoothBumpHt w.toCGLSmoothBump t : ℝ → ℂ)
          (cglAffineFourierScale N Q * (m : ℝ)))

/-- The physical-side smoothed character sum from CGL equation (6.1).
Compact support makes this a closed `tsum`, with no convergence premise. -/
def cglLemma62SmoothedCharacterSum
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus)
    (χ : DirichletCharacter ℂ Q.value) (t : ℝ) : ℂ :=
  ∑' n : ℕ,
    χ n * cglSmoothBumpHt w.toCGLSmoothBump t ((n : ℝ) / N.value)

/-- Multiplication by the conjugate principal character leaves a Dirichlet
character unchanged, including at nonunits. -/
theorem cglLemma62_mul_conj_principal_eq
    (Q : CGLPositiveModulus) (χ : DirichletCharacter ℂ Q.value)
    (a : ZMod Q.value) :
    χ a * (starRingEnd ℂ) ((1 : DirichletCharacter ℂ Q.value) a) = χ a := by
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    simp
  · rw [χ.map_nonunit ha]
    simp

/-- **CGL Lemma 6.2, equation (6.1), normalized.**  The additive character
Poisson transform equals the corresponding smoothed character sum exactly. -/
theorem cglLemma62_smoothedCharacterSum_eq_normalizedPoissonTransform
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus)
    (χ : DirichletCharacter ℂ Q.value) (t : ℝ) :
    cglLemma62SmoothedCharacterSum w N Q χ t =
      cglLemma62NormalizedPoissonTransform w N Q χ t := by
  calc
    cglLemma62SmoothedCharacterSum w N Q χ t =
        ∑' n : ℕ, cglLemma45CharacterPairHtnatTerm w N Q χ 1 t n := by
      unfold cglLemma62SmoothedCharacterSum cglLemma45CharacterPairHtnatTerm
      apply tsum_congr
      intro n
      rw [cglLemma62_mul_conj_principal_eq Q χ (n : ZMod Q.value)]
    _ = ∑ a : ZMod Q.value, ∑' m : ℤ,
        cglLemma45CharacterPairFourierTerm w N Q χ 1 t a m :=
      cglLemma45CharacterPairHtnatTerm_tsum_eq_residueFourierSum w N Q χ 1 t
    _ = cglLemma62NormalizedPoissonTransform w N Q χ t := by
      unfold cglLemma62NormalizedPoissonTransform cglLemma45CharacterPairFourierTerm
      apply Finset.sum_congr rfl
      intro a ha
      apply tsum_congr
      intro m
      rw [cglLemma62_mul_conj_principal_eq Q χ a]
      ring

end RHTower
