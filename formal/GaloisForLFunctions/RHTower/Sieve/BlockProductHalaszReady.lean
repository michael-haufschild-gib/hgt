import GaloisForLFunctions.RHTower.Sieve.LevelSetSpacedSample
import GaloisForLFunctions.RHTower.Sieve.LogPolyBlockBridge

/-!
# The bilinear Möbius block, reduced to Halász–Montgomery data

Three reductions compose here, and nothing else is used:

* the **dyadic level split** of the prime block (`integral_normSq_blockProduct_levelSplit`);
* the **level-set discretisation** (`exists_spaced_families_blockProduct_levelSplit`), which samples
  each level set at two one-spaced families of frequencies *inside it*;
* the **dyadic split of the cofactor's initial segment**
  (`sum_normSq_logPoly_Icc_le_card_mul_sum_blocks`) together with the identification of each block
  with a Gram row (`logPoly_dyadicSegmentBlock_eq_inner`).

The result is the mean square of the bilinear block bounded by the base level's mean square plus a
finite sum of quantities of the exact shape `∑_{r} ‖⟪dyadicDirRow N λ_r, c⟫‖²` over one-spaced
frequencies — which is what `halaszMontgomery_dyadic_explicit`, `huxley_multiblock_large_values`
and `largeValues_dirPoly_finset` bound.

This is the interface the Möbius Halász log-saving programme's large-values route plugs into; it
carries **no lower constraint on the block scale**, which is why it escapes the `(log x)^{-1/5}`
ceiling of the exact-Ramaré route.
-/

namespace RHTower.Sieve

open Finset MeasureTheory
open scoped InnerProductSpace

noncomputable section

/-- **The bilinear block, reduced to Gram rows at one-spaced frequencies.** -/
theorem exists_spaced_families_blockProduct_gramRows (a : ℕ → ℂ) (B : Finset ℕ) (M : ℕ)
    {G : ℝ} (hG : 0 ≤ G) {V₀ : ℝ} (hV₀ : 0 < V₀) {J : ℕ}
    (hJ : ((B.card : ℕ) : ℝ) ≤ 2 ^ J * V₀) :
    ∃ P₁ P₂ : ℕ → Finset ℝ,
      (∀ j, ∀ w ∈ P₁ j, w ∈ primeBlockLevelSet B G (2 ^ j * V₀))
      ∧ (∀ j, ∀ w ∈ P₂ j, w ∈ primeBlockLevelSet B G (2 ^ j * V₀))
      ∧ (∀ j, ∀ w ∈ P₁ j, ∀ u ∈ P₁ j, w ≠ u → (1 : ℝ) ≤ |w - u|)
      ∧ (∀ j, ∀ w ∈ P₂ j, ∀ u ∈ P₂ j, w ≠ u → (1 : ℝ) ≤ |w - u|)
      ∧ (∫ w in Set.Icc (-G) G, ‖primeBlockPoly B w * logPoly a (Finset.Icc 1 M) w‖ ^ 2)
          ≤ V₀ ^ 2 * (∫ w in Set.Icc (-G) G, ‖logPoly a (Finset.Icc 1 M) w‖ ^ 2)
            + ∑ j ∈ Finset.range J, (2 ^ (j + 1) * V₀) ^ 2 *
                (((Nat.log 2 M + 1 : ℕ) : ℝ) *
                  ∑ i ∈ Finset.range (Nat.log 2 M + 1),
                    ((∑ w ∈ P₁ j, ‖⟪dyadicDirRow (2 ^ i) (-(2 * Real.pi * w)),
                        blockCoeff (2 ^ i) (dyadicSegmentCoeff a M i) 0⟫_ℂ‖ ^ 2)
                      + ∑ w ∈ P₂ j, ‖⟪dyadicDirRow (2 ^ i) (-(2 * Real.pi * w)),
                          blockCoeff (2 ^ i) (dyadicSegmentCoeff a M i) 0⟫_ℂ‖ ^ 2)) := by
  classical
  obtain ⟨P₁, P₂, h₁, h₂, h₃, h₄, hbound⟩ :=
    exists_spaced_families_blockProduct_levelSplit a B (Finset.Icc 1 M) hG hV₀ hJ
  refine ⟨P₁, P₂, h₁, h₂, h₃, h₄, hbound.trans ?_⟩
  have hgram : ∀ (P : Finset ℝ) (i : ℕ),
      ∑ w ∈ P, ‖logPoly a (dyadicSegmentBlock M i) w‖ ^ 2
        = ∑ w ∈ P, ‖⟪dyadicDirRow (2 ^ i) (-(2 * Real.pi * w)),
            blockCoeff (2 ^ i) (dyadicSegmentCoeff a M i) 0⟫_ℂ‖ ^ 2 := by
    intro P i
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [logPoly_dyadicSegmentBlock_eq_inner]
  have hstep : ∀ j : ℕ,
      (∑ w ∈ P₁ j, ‖logPoly a (Finset.Icc 1 M) w‖ ^ 2)
          + ∑ w ∈ P₂ j, ‖logPoly a (Finset.Icc 1 M) w‖ ^ 2
        ≤ ((Nat.log 2 M + 1 : ℕ) : ℝ) *
            ∑ i ∈ Finset.range (Nat.log 2 M + 1),
              ((∑ w ∈ P₁ j, ‖⟪dyadicDirRow (2 ^ i) (-(2 * Real.pi * w)),
                  blockCoeff (2 ^ i) (dyadicSegmentCoeff a M i) 0⟫_ℂ‖ ^ 2)
                + ∑ w ∈ P₂ j, ‖⟪dyadicDirRow (2 ^ i) (-(2 * Real.pi * w)),
                    blockCoeff (2 ^ i) (dyadicSegmentCoeff a M i) 0⟫_ℂ‖ ^ 2) := by
    intro j
    have hA := sum_normSq_logPoly_Icc_le_card_mul_sum_blocks a M (P₁ j)
    have hB' := sum_normSq_logPoly_Icc_le_card_mul_sum_blocks a M (P₂ j)
    have hsplit : ∑ i ∈ Finset.range (Nat.log 2 M + 1),
          ((∑ w ∈ P₁ j, ‖⟪dyadicDirRow (2 ^ i) (-(2 * Real.pi * w)),
              blockCoeff (2 ^ i) (dyadicSegmentCoeff a M i) 0⟫_ℂ‖ ^ 2)
            + ∑ w ∈ P₂ j, ‖⟪dyadicDirRow (2 ^ i) (-(2 * Real.pi * w)),
                blockCoeff (2 ^ i) (dyadicSegmentCoeff a M i) 0⟫_ℂ‖ ^ 2)
        = (∑ i ∈ Finset.range (Nat.log 2 M + 1),
              ∑ w ∈ P₁ j, ‖logPoly a (dyadicSegmentBlock M i) w‖ ^ 2)
          + ∑ i ∈ Finset.range (Nat.log 2 M + 1),
              ∑ w ∈ P₂ j, ‖logPoly a (dyadicSegmentBlock M i) w‖ ^ 2 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hgram (P₁ j) i, hgram (P₂ j) i]
    rw [hsplit, mul_add]
    exact add_le_add hA hB'
  have hsum : ∑ j ∈ Finset.range J, (2 ^ (j + 1) * V₀) ^ 2 *
        ((∑ w ∈ P₁ j, ‖logPoly a (Finset.Icc 1 M) w‖ ^ 2)
          + ∑ w ∈ P₂ j, ‖logPoly a (Finset.Icc 1 M) w‖ ^ 2)
      ≤ ∑ j ∈ Finset.range J, (2 ^ (j + 1) * V₀) ^ 2 *
        (((Nat.log 2 M + 1 : ℕ) : ℝ) *
          ∑ i ∈ Finset.range (Nat.log 2 M + 1),
            ((∑ w ∈ P₁ j, ‖⟪dyadicDirRow (2 ^ i) (-(2 * Real.pi * w)),
                blockCoeff (2 ^ i) (dyadicSegmentCoeff a M i) 0⟫_ℂ‖ ^ 2)
              + ∑ w ∈ P₂ j, ‖⟪dyadicDirRow (2 ^ i) (-(2 * Real.pi * w)),
                  blockCoeff (2 ^ i) (dyadicSegmentCoeff a M i) 0⟫_ℂ‖ ^ 2)) :=
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hstep j) (sq_nonneg _)
  linarith [hsum]

end

end RHTower.Sieve
