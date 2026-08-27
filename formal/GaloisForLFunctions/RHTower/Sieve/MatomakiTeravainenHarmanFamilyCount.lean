import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanCellCoefficients
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenMainLayerPaperCount

/-!
# Proposition 2.2 family count including Harman cells

Active pair and triple rectangles cost only the square or cube of the active aligned-block count.
After multiplying by every recursion depth and active block chain, both families remain inside the
literal `exp((log log X)^5)` budget.
-/

namespace RHTower.Sieve

open Finset Filter

noncomputable section

/-- Pair rectangles times every repaired main-layer chain fit the exact Proposition 2.2 budget. -/
theorem eventually_pairCells_mul_sum_card_mtActiveBlockChains_le_exp_log_log_fifth
    (A : ℕ) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ (E : ℝ) (Y z₁ : ℕ),
      1 ≤ Y → (Y : ℝ) ≤ 4 * X →
      mtLowerCutoffNat X ≤ z₁ → (z₁ : ℝ) ≤ X →
      ∀ j : Fin (z₁ - mtLowerCutoffNat X + 1),
        ((mtHarmanActiveGoodPairCells
          (t := z₁ - mtLowerCutoffNat X)
          (mtPaperAlignedEndpoint (mtLowerCutoffNat X) z₁ (mtPaperWidth A X)) E).card : ℝ) *
          ((∑ depth ∈ Finset.range
              (Nat.floor (Real.log (Y : ℝ) /
                Real.log (mtLowerCutoffNat X : ℝ)) + 1),
              (mtActiveBlockChains
                (mtAdjacentPrimeBlock
                  (mtPaperAlignedEndpoint (mtLowerCutoffNat X) z₁ (mtPaperWidth A X)))
                depth j).card : ℕ) : ℝ) ≤
            Real.exp ((Real.log (Real.log X)) ^ 5) := by
  filter_upwards [eventually_cast_card_mtPaperAlignedActiveBlockIndices_le_six_mul_log_pow A,
    eventually_outer_mul_sum_card_mtActiveBlockChains_paperAligned_le_exp_log_log_fifth
      A (2 * (10 * A + 1)) 36 (by norm_num)] with X hactiveX htotalX
  intro E Y z₁ hY hYX hz hzX j
  let endpoint := mtPaperAlignedEndpoint (mtLowerCutoffNat X) z₁ (mtPaperWidth A X)
  let block := mtAdjacentPrimeBlock
    (t := z₁ - mtLowerCutoffNat X) endpoint
  have hcellNat := card_mtHarmanActiveGoodPairCells_le
    (t := z₁ - mtLowerCutoffNat X) endpoint E
  have hcell : ((mtHarmanActiveGoodPairCells
      (t := z₁ - mtLowerCutoffNat X) endpoint E).card : ℝ) ≤
      ((mtActiveBlockIndices block).card : ℝ) ^ 2 := by
    exact_mod_cast hcellNat
  have hactive : ((mtActiveBlockIndices block).card : ℝ) ≤
      6 * (Real.log X) ^ (10 * A + 1) := by
    dsimp [block, endpoint]
    rw [mtActiveBlockIndices_paperAligned]
    exact hactiveX z₁ hz hzX
  have hactiveNonneg : 0 ≤ ((mtActiveBlockIndices block).card : ℝ) := Nat.cast_nonneg _
  have hactivePow : ((mtActiveBlockIndices block).card : ℝ) ^ 2 ≤
      (6 * (Real.log X) ^ (10 * A + 1)) ^ 2 :=
    pow_le_pow_left₀ hactiveNonneg hactive 2
  calc
    ((mtHarmanActiveGoodPairCells
        (t := z₁ - mtLowerCutoffNat X) endpoint E).card : ℝ) *
        ((∑ depth ∈ Finset.range
            (Nat.floor (Real.log (Y : ℝ) /
              Real.log (mtLowerCutoffNat X : ℝ)) + 1),
            (mtActiveBlockChains block depth j).card : ℕ) : ℝ) ≤
      (6 * (Real.log X) ^ (10 * A + 1)) ^ 2 *
        ((∑ depth ∈ Finset.range
            (Nat.floor (Real.log (Y : ℝ) /
              Real.log (mtLowerCutoffNat X : ℝ)) + 1),
            (mtActiveBlockChains block depth j).card : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right (hcell.trans hactivePow) (by positivity)
    _ = 36 * (Real.log X) ^ (2 * (10 * A + 1)) *
        ((∑ depth ∈ Finset.range
            (Nat.floor (Real.log (Y : ℝ) /
              Real.log (mtLowerCutoffNat X : ℝ)) + 1),
            (mtActiveBlockChains block depth j).card : ℕ) : ℝ) := by
      rw [mul_pow, ← pow_mul]
      rw [Nat.mul_comm (10 * A + 1) 2]
      norm_num
    _ ≤ Real.exp ((Real.log (Real.log X)) ^ 5) := by
      simpa only [endpoint, block] using htotalX Y z₁ hY hYX hz hzX j

/-- Triple rectangles times every repaired main-layer chain fit the exact Proposition 2.2 budget. -/
theorem eventually_tripleCells_mul_sum_card_mtActiveBlockChains_le_exp_log_log_fifth
    (A : ℕ) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ (E : ℝ) (Y z₁ : ℕ),
      1 ≤ Y → (Y : ℝ) ≤ 4 * X →
      mtLowerCutoffNat X ≤ z₁ → (z₁ : ℝ) ≤ X →
      ∀ j : Fin (z₁ - mtLowerCutoffNat X + 1),
        ((mtHarmanActiveGoodTripleCells
          (t := z₁ - mtLowerCutoffNat X)
          (mtPaperAlignedEndpoint (mtLowerCutoffNat X) z₁ (mtPaperWidth A X)) E).card : ℝ) *
          ((∑ depth ∈ Finset.range
              (Nat.floor (Real.log (Y : ℝ) /
                Real.log (mtLowerCutoffNat X : ℝ)) + 1),
              (mtActiveBlockChains
                (mtAdjacentPrimeBlock
                  (mtPaperAlignedEndpoint (mtLowerCutoffNat X) z₁ (mtPaperWidth A X)))
                depth j).card : ℕ) : ℝ) ≤
            Real.exp ((Real.log (Real.log X)) ^ 5) := by
  filter_upwards [eventually_cast_card_mtPaperAlignedActiveBlockIndices_le_six_mul_log_pow A,
    eventually_outer_mul_sum_card_mtActiveBlockChains_paperAligned_le_exp_log_log_fifth
      A (3 * (10 * A + 1)) 216 (by norm_num)] with X hactiveX htotalX
  intro E Y z₁ hY hYX hz hzX j
  let endpoint := mtPaperAlignedEndpoint (mtLowerCutoffNat X) z₁ (mtPaperWidth A X)
  let block := mtAdjacentPrimeBlock
    (t := z₁ - mtLowerCutoffNat X) endpoint
  have hcellNat := card_mtHarmanActiveGoodTripleCells_le
    (t := z₁ - mtLowerCutoffNat X) endpoint E
  have hcell : ((mtHarmanActiveGoodTripleCells
      (t := z₁ - mtLowerCutoffNat X) endpoint E).card : ℝ) ≤
      ((mtActiveBlockIndices block).card : ℝ) ^ 3 := by
    exact_mod_cast hcellNat
  have hactive : ((mtActiveBlockIndices block).card : ℝ) ≤
      6 * (Real.log X) ^ (10 * A + 1) := by
    dsimp [block, endpoint]
    rw [mtActiveBlockIndices_paperAligned]
    exact hactiveX z₁ hz hzX
  have hactiveNonneg : 0 ≤ ((mtActiveBlockIndices block).card : ℝ) := Nat.cast_nonneg _
  have hactivePow : ((mtActiveBlockIndices block).card : ℝ) ^ 3 ≤
      (6 * (Real.log X) ^ (10 * A + 1)) ^ 3 :=
    pow_le_pow_left₀ hactiveNonneg hactive 3
  calc
    ((mtHarmanActiveGoodTripleCells
        (t := z₁ - mtLowerCutoffNat X) endpoint E).card : ℝ) *
        ((∑ depth ∈ Finset.range
            (Nat.floor (Real.log (Y : ℝ) /
              Real.log (mtLowerCutoffNat X : ℝ)) + 1),
            (mtActiveBlockChains block depth j).card : ℕ) : ℝ) ≤
      (6 * (Real.log X) ^ (10 * A + 1)) ^ 3 *
        ((∑ depth ∈ Finset.range
            (Nat.floor (Real.log (Y : ℝ) /
              Real.log (mtLowerCutoffNat X : ℝ)) + 1),
            (mtActiveBlockChains block depth j).card : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right (hcell.trans hactivePow) (by positivity)
    _ = 216 * (Real.log X) ^ (3 * (10 * A + 1)) *
        ((∑ depth ∈ Finset.range
            (Nat.floor (Real.log (Y : ℝ) /
              Real.log (mtLowerCutoffNat X : ℝ)) + 1),
            (mtActiveBlockChains block depth j).card : ℕ) : ℝ) := by
      rw [mul_pow, ← pow_mul]
      rw [Nat.mul_comm (10 * A + 1) 3]
      norm_num
    _ ≤ Real.exp ((Real.log (Real.log X)) ^ 5) := by
      simpa only [endpoint, block] using htotalX Y z₁ hY hYX hz hzX j

end

end RHTower.Sieve
