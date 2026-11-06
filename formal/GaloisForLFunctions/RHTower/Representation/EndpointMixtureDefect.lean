import GaloisForLFunctions.HTGeometry.SymmetricCharacters.MeanPreservingMixtures
import GaloisForLFunctions.RHTower.Representation.PositiveEndpointCharacter

/-!
# The sharp endpoint discrepancy under mean-preserving mixtures

Randomizing probability colors while keeping their mean equal to the positive endpoint alphabet
adds precisely the total color variance to the arithmetic transposition discrepancy. The
real-part alphabet is therefore the unique minimizer on the positive mixture support. Exact
agreement with the arithmetic transposition requires both RH and zero color variance.
-/

noncomputable section
open scoped BigOperators
namespace RHTower
open GaloisForLFunctions.SymmetricCharacters

variable {I : Type*} [Fintype I]

/-- Mean-preserving randomization adds color variance to the endpoint orientation energy. -/
theorem xiEndpointMixture_transposition_gap (mix : I → NNReal)
    (hmix : (∑ i, (mix i : ℝ)) = 1) (w : I → XiZeroCopy → NNReal)
    (hw : ∀ i, Summable fun q => (w i q : ℝ))
    (hm : ∀ i, (∑' q, (w i q : ℝ)) = 1)
    (hmean : ∀ q, colorMean mix (fun i q => (w i q : ℝ)) q = (xiEndpointColor q : ℝ)) :
    wordCharacterMixture mix w (finRotate 2) - xiEndpointSourceTransposition =
      xiEndpointOrientationEnergy / xiEndpointColorMass ^ 2 +
        colorMixtureVariance mix (fun i q => (w i q : ℝ)) := by
  have hs (i : I) := probabilityColor_sq_summable (w i) (hw i) (hm i)
  have hV := colorMixtureVariance_eq mix hmix (fun i q => (w i q : ℝ)) hs
  have hb : (∑' q, colorMean mix (fun i q => (w i q : ℝ)) q ^ 2) =
      xiEndpointPositiveTransposition := by
    simp only [hmean]
    change (∑' q, ((xiStripEdgeWeight q).re / xiEndpointColorMass) ^ 2) = _
    simp only [div_pow, tsum_div_const]
    rfl
  rw [hb] at hV
  rw [wordCharacterMixture_transposition]
  have hg := xiEndpointTransposition_gap
  linarith only [hV, hg]

/-- No mixture with these mean colors improves the deterministic endpoint discrepancy. -/
theorem xiEndpointMixture_transposition_gap_lower (mix : I → NNReal)
    (hmix : (∑ i, (mix i : ℝ)) = 1) (w : I → XiZeroCopy → NNReal)
    (hw : ∀ i, Summable fun q => (w i q : ℝ))
    (hm : ∀ i, (∑' q, (w i q : ℝ)) = 1)
    (hmean : ∀ q, colorMean mix (fun i q => (w i q : ℝ)) q = (xiEndpointColor q : ℝ)) :
    xiEndpointOrientationEnergy / xiEndpointColorMass ^ 2 ≤
      wordCharacterMixture mix w (finRotate 2) - xiEndpointSourceTransposition := by
  rw [xiEndpointMixture_transposition_gap mix hmix w hw hm hmean]
  exact le_add_of_nonneg_right (colorMixtureVariance_nonneg _ _)

/-- Equality in the minimum forces every positive-mass component to be the endpoint alphabet. -/
theorem xiEndpointMixture_minimum_iff (mix : I → NNReal)
    (hmix : (∑ i, (mix i : ℝ)) = 1) (w : I → XiZeroCopy → NNReal)
    (hw : ∀ i, Summable fun q => (w i q : ℝ))
    (hm : ∀ i, (∑' q, (w i q : ℝ)) = 1)
    (hmean : ∀ q, colorMean mix (fun i q => (w i q : ℝ)) q = (xiEndpointColor q : ℝ)) :
    wordCharacterMixture mix w (finRotate 2) - xiEndpointSourceTransposition =
        xiEndpointOrientationEnergy / xiEndpointColorMass ^ 2 ↔
      ∀ i, mix i ≠ 0 → ∀ q, w i q = xiEndpointColor q := by
  rw [xiEndpointMixture_transposition_gap mix hmix w hw hm hmean, add_eq_left,
    colorMixtureVariance_eq_zero_iff_mean mix hmix _
      (fun i => probabilityColor_sq_summable (w i) (hw i) (hm i))]
  simp only [hmean, NNReal.coe_inj]

/-- Exact arithmetic agreement requires both source purity and absence of color fluctuations. -/
theorem xiEndpointMixture_exact_iff (mix : I → NNReal)
    (hmix : (∑ i, (mix i : ℝ)) = 1) (w : I → XiZeroCopy → NNReal)
    (hw : ∀ i, Summable fun q => (w i q : ℝ))
    (hm : ∀ i, (∑' q, (w i q : ℝ)) = 1)
    (hmean : ∀ q, colorMean mix (fun i q => (w i q : ℝ)) q = (xiEndpointColor q : ℝ)) :
    wordCharacterMixture mix w (finRotate 2) = xiEndpointSourceTransposition ↔
      RiemannHypothesis ∧ ∀ i, mix i ≠ 0 → ∀ q, w i q = xiEndpointColor q := by
  have hE : 0 ≤ xiEndpointOrientationEnergy / xiEndpointColorMass ^ 2 :=
    div_nonneg xiEndpointOrientationEnergy_nonneg (sq_nonneg _)
  have hV := colorMixtureVariance_nonneg mix (fun i q => (w i q : ℝ))
  have hgap := xiEndpointMixture_transposition_gap mix hmix w hw hm hmean
  constructor
  · intro h
    have hE0 : xiEndpointOrientationEnergy / xiEndpointColorMass ^ 2 = 0 := by
      rw [h, sub_self] at hgap
      linarith only [hgap, hE, hV]
    have henergy : xiEndpointOrientationEnergy = 0 :=
      (div_eq_zero_iff.mp hE0).resolve_right (pow_ne_zero 2 xiEndpointColorMass_pos.ne')
    refine ⟨xiEndpointOrientationEnergy_eq_zero_iff_rh.mp henergy, ?_⟩
    apply (xiEndpointMixture_minimum_iff mix hmix w hw hm hmean).mp
    rw [h, sub_self, hE0]
  · rintro ⟨hRH, hcolors⟩
    have he := (xiEndpointMixture_minimum_iff mix hmix w hw hm hmean).mpr hcolors
    rw [xiEndpointOrientationEnergy_eq_zero_iff_rh.mpr hRH, zero_div] at he
    exact sub_eq_zero.mp he

end RHTower
