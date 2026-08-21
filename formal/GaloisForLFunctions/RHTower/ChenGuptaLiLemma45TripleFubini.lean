/-
# Chen--Gupta--Li Lemma 4.5 three-coordinate Fourier assembly

Uses the closed absolute-summability certificates of the three character
Poisson series to turn their product into the exact triple-frequency sum.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiLemma45FrequencySummability

open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

/-- A three-frequency product in CGL Lemma 4.5's nested integer carrier. -/
def cglLemma45TripleFrequencyTerm (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus)
    (χ₁ ψ₁ χ₂ ψ₂ χ₃ ψ₃ : DirichletCharacter ℂ Q.value)
    (t₁ t₂ t₃ : ℝ) (a₁ a₂ a₃ : ZMod Q.value) (m : (ℤ × ℤ) × ℤ) : ℂ :=
  cglLemma45CharacterPairFourierTerm w N Q χ₁ ψ₁ t₁ a₁ m.1.1 *
    cglLemma45CharacterPairFourierTerm w N Q χ₂ ψ₂ t₂ a₂ m.1.2 *
      cglLemma45CharacterPairFourierTerm w N Q χ₃ ψ₃ t₃ a₃ m.2

/-- The product of CGL's three coordinate frequency series is its exact
three-frequency sum.  Each absolute-summability certificate is constructed
from the affine Schwartz map, so this theorem has no interchange premise. -/
theorem cglLemma45_threeFrequencyProduct_eq_tsum
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus)
    (χ₁ ψ₁ χ₂ ψ₂ χ₃ ψ₃ : DirichletCharacter ℂ Q.value)
    (t₁ t₂ t₃ : ℝ) (a₁ a₂ a₃ : ZMod Q.value) :
    (∑' m : ℤ, cglLemma45CharacterPairFourierTerm w N Q χ₁ ψ₁ t₁ a₁ m) *
        (∑' m : ℤ, cglLemma45CharacterPairFourierTerm w N Q χ₂ ψ₂ t₂ a₂ m) *
          (∑' m : ℤ, cglLemma45CharacterPairFourierTerm w N Q χ₃ ψ₃ t₃ a₃ m) =
      ∑' m : (ℤ × ℤ) × ℤ,
        cglLemma45TripleFrequencyTerm w N Q χ₁ ψ₁ χ₂ ψ₂ χ₃ ψ₃ t₁ t₂ t₃ a₁ a₂ a₃ m := by
  have h₁ := cglLemma45CharacterPairFourierTerm_summable_norm w N Q χ₁ ψ₁ t₁ a₁
  have h₂ := cglLemma45CharacterPairFourierTerm_summable_norm w N Q χ₂ ψ₂ t₂ a₂
  have h₃ := cglLemma45CharacterPairFourierTerm_summable_norm w N Q χ₃ ψ₃ t₃ a₃
  have h₁₂ : Summable fun m : ℤ × ℤ =>
      ‖cglLemma45CharacterPairFourierTerm w N Q χ₁ ψ₁ t₁ a₁ m.1 *
        cglLemma45CharacterPairFourierTerm w N Q χ₂ ψ₂ t₂ a₂ m.2‖ := by
    simpa only [norm_mul] using h₁.mul_norm h₂
  calc
    _ = (∑' m : ℤ × ℤ,
          cglLemma45CharacterPairFourierTerm w N Q χ₁ ψ₁ t₁ a₁ m.1 *
            cglLemma45CharacterPairFourierTerm w N Q χ₂ ψ₂ t₂ a₂ m.2) *
          ∑' m : ℤ, cglLemma45CharacterPairFourierTerm w N Q χ₃ ψ₃ t₃ a₃ m := by
      rw [tsum_mul_tsum_of_summable_norm h₁ h₂]
    _ = _ := by
      rw [tsum_mul_tsum_of_summable_norm h₁₂ h₃]
      rfl

end RHTower
