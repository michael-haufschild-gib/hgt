/-
# Chen--Gupta--Li Lemma 4.5 one-pair affine Poisson identity

Applies CGL's proved affine Poisson formula to the exact character-pair
integer lattice from the finite cubic trace.  This gives the one-coordinate
Poisson expansion used three times in CGL Lemma 4.5.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiLemma45ResiduePoisson

open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

/-- One frequency term in the affine Poisson expansion of a character-pair
`h_t` kernel. -/
def cglLemma45CharacterPairFourierTerm (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (χ ψ : DirichletCharacter ℂ Q.value) (t : ℝ)
    (a : ZMod Q.value) (m : ℤ) : ℂ :=
  χ a * (starRingEnd ℂ) (ψ a) *
    (ZMod.stdAddChar (a * (m : ZMod Q.value)) *
      ((cglAffineFourierScale N Q : ℂ) *
        𝓕 (cglSmoothBumpHt w.toCGLSmoothBump t : ℝ → ℂ)
          (cglAffineFourierScale N Q * (m : ℝ))))

/-- **CGL Lemma 4.5, one-coordinate character Poisson expansion.** The
finite dyadic character-pair `h_t` sum equals its complete residue/Fourier
series, with no unproved convergence or support premise. -/
theorem cglLemma45CharacterPairHtnatTerm_tsum_eq_residueFourierSum
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (χ ψ : DirichletCharacter ℂ Q.value) (t : ℝ) :
    ∑' n : ℕ, cglLemma45CharacterPairHtnatTerm w N Q χ ψ t n =
      ∑ a : ZMod Q.value, ∑' m : ℤ,
        cglLemma45CharacterPairFourierTerm w N Q χ ψ t a m := by
  calc
    ∑' n : ℕ, cglLemma45CharacterPairHtnatTerm w N Q χ ψ t n =
        ∑ a : ZMod Q.value, ∑' m : ℕ,
          cglLemma45CharacterPairAffineNatTerm w N Q χ ψ t a m :=
      cglLemma45CharacterPairHtnatTerm_tsum_eq_residueNatSum w N Q χ ψ t
    _ = ∑ a : ZMod Q.value, ∑' k : ℤ,
          cglLemma45CharacterPairAffineIntTerm w N Q χ ψ t a k := by
      apply Finset.sum_congr rfl
      intro a ha
      exact (cglLemma45CharacterPairAffineIntTerm_tsum_eq_natSum w N Q χ ψ t a).symm
    _ = ∑ a : ZMod Q.value,
          (χ a * (starRingEnd ℂ) (ψ a)) *
            ∑' k : ℤ, cglSmoothBumpHt w.toCGLSmoothBump t
              (((a.val : ℝ) + Q.value * (k : ℝ)) / N.value) := by
      apply Finset.sum_congr rfl
      intro a ha
      unfold cglLemma45CharacterPairAffineIntTerm
      rw [tsum_mul_left]
    _ = ∑ a : ZMod Q.value,
          (χ a * (starRingEnd ℂ) (ψ a)) *
            ∑' m : ℤ, ZMod.stdAddChar (a * (m : ZMod Q.value)) *
              ((cglAffineFourierScale N Q : ℂ) *
                𝓕 (cglSmoothBumpHt w.toCGLSmoothBump t : ℝ → ℂ)
                  (cglAffineFourierScale N Q * (m : ℝ))) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [cglAffineResidue_tsum_eq_tsum_fourier_addChar]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [← tsum_mul_left]
      rfl

end RHTower
