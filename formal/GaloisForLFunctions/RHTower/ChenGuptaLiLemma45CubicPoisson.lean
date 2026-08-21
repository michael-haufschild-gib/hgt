/-
# Chen--Gupta--Li Lemma 4.5 cubic Poisson assembly

Combines the literal weighted cubic row term with the three established
one-coordinate character Poisson identities.  The Mellin scale phases cancel
around the cubic cycle, and closed Schwartz summability supplies the exact
three-frequency Fubini equality.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiLemma45TripleFubini

open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

/-- **CGL Lemma 4.5, cubic row Poisson identity.** One literal weighted cubic
row term is exactly its three-residue, three-frequency Poisson expression.
All convergence and finite-to-lattice extensions are discharged by the closed
compact-support and Schwartz infrastructure. -/
theorem cglLemma45_cubicRow_eq_threeFrequencySum
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData Q.value)
    (rst : Fin R × Fin R × Fin R) :
    cglCharacterDyadicWeightedGramCubicTerm N.value Q.value R
      (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) rows rst =
      ∑ a₁ : ZMod Q.value, ∑ a₂ : ZMod Q.value, ∑ a₃ : ZMod Q.value,
        ∑' m : (ℤ × ℤ) × ℤ,
          cglLemma45TripleFrequencyTerm w N Q
            (rows rst.1).character (rows rst.2.1).character
            (rows rst.2.1).character (rows rst.2.2).character
            (rows rst.2.2).character (rows rst.1).character
            ((rows rst.1).time - (rows rst.2.1).time)
            ((rows rst.2.1).time - (rows rst.2.2).time)
            ((rows rst.2.2).time - (rows rst.1).time)
            a₁ a₂ a₃ m := by
  unfold cglCharacterDyadicWeightedGramCubicTerm cglCharacterDyadicWeightedGram
  rw [cglCharacterDyadicWeightedCorrelation_eq_scale_mul_ht_sum w N Q.value
      (rows rst.1) (rows rst.2.1),
    cglCharacterDyadicWeightedCorrelation_eq_scale_mul_ht_sum w N Q.value
      (rows rst.2.1) (rows rst.2.2),
    cglCharacterDyadicWeightedCorrelation_eq_scale_mul_ht_sum w N Q.value
      (rows rst.2.2) (rows rst.1)]
  let S₁ : ℂ := ∑ j : Fin N.value,
    (rows rst.1).character (cglCharacterDyadicIndex N.value j) *
      (starRingEnd ℂ) ((rows rst.2.1).character (cglCharacterDyadicIndex N.value j)) *
      cglSmoothBumpHt w.toCGLSmoothBump ((rows rst.1).time - (rows rst.2.1).time)
        ((cglCharacterDyadicIndex N.value j : ℝ) / N.value)
  let S₂ : ℂ := ∑ j : Fin N.value,
    (rows rst.2.1).character (cglCharacterDyadicIndex N.value j) *
      (starRingEnd ℂ) ((rows rst.2.2).character (cglCharacterDyadicIndex N.value j)) *
      cglSmoothBumpHt w.toCGLSmoothBump ((rows rst.2.1).time - (rows rst.2.2).time)
        ((cglCharacterDyadicIndex N.value j : ℝ) / N.value)
  let S₃ : ℂ := ∑ j : Fin N.value,
    (rows rst.2.2).character (cglCharacterDyadicIndex N.value j) *
      (starRingEnd ℂ) ((rows rst.1).character (cglCharacterDyadicIndex N.value j)) *
      cglSmoothBumpHt w.toCGLSmoothBump ((rows rst.2.2).time - (rows rst.1).time)
        ((cglCharacterDyadicIndex N.value j : ℝ) / N.value)
  have hcycle := cglMellinPhase_cyclic_difference_product N
    (rows rst.1).time (rows rst.2.1).time (rows rst.2.2).time
  have hS₁ : S₁ = ∑' n : ℕ, cglLemma45CharacterPairHtnatTerm w N Q
      (rows rst.1).character (rows rst.2.1).character
      ((rows rst.1).time - (rows rst.2.1).time) n := by
    simpa only [S₁] using
      (cglLemma45CharacterPairHtnatTerm_tsum_eq_finSum w N Q
        (rows rst.1).character (rows rst.2.1).character
        ((rows rst.1).time - (rows rst.2.1).time)).symm
  have hS₂ : S₂ = ∑' n : ℕ, cglLemma45CharacterPairHtnatTerm w N Q
      (rows rst.2.1).character (rows rst.2.2).character
      ((rows rst.2.1).time - (rows rst.2.2).time) n := by
    simpa only [S₂] using
      (cglLemma45CharacterPairHtnatTerm_tsum_eq_finSum w N Q
        (rows rst.2.1).character (rows rst.2.2).character
        ((rows rst.2.1).time - (rows rst.2.2).time)).symm
  have hS₃ : S₃ = ∑' n : ℕ, cglLemma45CharacterPairHtnatTerm w N Q
      (rows rst.2.2).character (rows rst.1).character
      ((rows rst.2.2).time - (rows rst.1).time) n := by
    simpa only [S₃] using
      (cglLemma45CharacterPairHtnatTerm_tsum_eq_finSum w N Q
        (rows rst.2.2).character (rows rst.1).character
        ((rows rst.2.2).time - (rows rst.1).time)).symm
  have hP₁ := cglLemma45CharacterPairHtnatTerm_tsum_eq_residueFourierSum w N Q
    (rows rst.1).character (rows rst.2.1).character
    ((rows rst.1).time - (rows rst.2.1).time)
  have hP₂ := cglLemma45CharacterPairHtnatTerm_tsum_eq_residueFourierSum w N Q
    (rows rst.2.1).character (rows rst.2.2).character
    ((rows rst.2.1).time - (rows rst.2.2).time)
  have hP₃ := cglLemma45CharacterPairHtnatTerm_tsum_eq_residueFourierSum w N Q
    (rows rst.2.2).character (rows rst.1).character
    ((rows rst.2.2).time - (rows rst.1).time)
  change
    (cglMellinPhase ((rows rst.1).time - (rows rst.2.1).time) N.value * S₁) *
        (cglMellinPhase ((rows rst.2.1).time - (rows rst.2.2).time) N.value * S₂) *
          (cglMellinPhase ((rows rst.2.2).time - (rows rst.1).time) N.value * S₃) = _
  calc
    _ =
        (cglMellinPhase ((rows rst.1).time - (rows rst.2.1).time) N.value *
          cglMellinPhase ((rows rst.2.1).time - (rows rst.2.2).time) N.value *
            cglMellinPhase ((rows rst.2.2).time - (rows rst.1).time) N.value) *
          (S₁ * S₂ * S₃) := by ring
    _ = S₁ * S₂ * S₃ := by
      rw [hcycle]
      ring
    _ =
        (∑ a₁ : ZMod Q.value, ∑' m : ℤ,
          cglLemma45CharacterPairFourierTerm w N Q
            (rows rst.1).character (rows rst.2.1).character
            ((rows rst.1).time - (rows rst.2.1).time) a₁ m) *
          (∑ a₂ : ZMod Q.value, ∑' m : ℤ,
            cglLemma45CharacterPairFourierTerm w N Q
              (rows rst.2.1).character (rows rst.2.2).character
              ((rows rst.2.1).time - (rows rst.2.2).time) a₂ m) *
            ∑ a₃ : ZMod Q.value, ∑' m : ℤ,
              cglLemma45CharacterPairFourierTerm w N Q
                (rows rst.2.2).character (rows rst.1).character
                ((rows rst.2.2).time - (rows rst.1).time) a₃ m := by
      rw [hS₁, hS₂, hS₃, hP₁, hP₂, hP₃]
    _ = _ := by
      rw [Finset.sum_mul_sum]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a₁ ha₁
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a₂ ha₂
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a₃ ha₃
      exact cglLemma45_threeFrequencyProduct_eq_tsum w N Q
        (rows rst.1).character (rows rst.2.1).character
        (rows rst.2.1).character (rows rst.2.2).character
        (rows rst.2.2).character (rows rst.1).character
        ((rows rst.1).time - (rows rst.2.1).time)
        ((rows rst.2.1).time - (rows rst.2.2).time)
        ((rows rst.2.2).time - (rows rst.1).time) a₁ a₂ a₃

end RHTower
