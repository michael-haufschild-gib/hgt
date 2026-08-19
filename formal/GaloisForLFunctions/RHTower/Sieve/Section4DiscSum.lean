import GaloisForLFunctions.RHTower.Sieve.GeomBlockCardBound
import GaloisForLFunctions.RHTower.Sieve.Section4DiscPiece

/-!
# The disc sum over the long ladder

Summing the disc bound of `Sieve/Section4DiscRel` over the long ladder.  Each term pairs the trivial
count of a long block with the relative cofactor saving of that block, and the block scale cancels
exactly between them, leaving the cofactor's top length and the relative saving.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **The disc sum over the long ladder.**  The block scale cancels term by term. -/
theorem sum_card_sq_mul_discBound_le {Q : Finset ℕ} {B₁ : ℕ} {RQ ηQ w₀ S : ℝ}
    (hRQ : 0 < RQ) (hηQ : 0 ≤ ηQ) (hw₀ : 0 ≤ w₀) (LQ : ℕ) :
    (∑ k ∈ Finset.range LQ, ((geomBlock Q RQ (1 + ηQ) k).card : ℝ) ^ 2
        * ((S * ((B₁ : ℝ) / (RQ * (1 + ηQ) ^ k))) ^ 2 * (2 * w₀)))
      ≤ (LQ : ℝ) * ((1 + ηQ) ^ 2 * (B₁ : ℝ) ^ 2 * S ^ 2 * (2 * w₀)) := by
  classical
  have hstep : ∀ k ∈ Finset.range LQ,
      ((geomBlock Q RQ (1 + ηQ) k).card : ℝ) ^ 2
          * ((S * ((B₁ : ℝ) / (RQ * (1 + ηQ) ^ k))) ^ 2 * (2 * w₀))
        ≤ (1 + ηQ) ^ 2 * (B₁ : ℝ) ^ 2 * S ^ 2 * (2 * w₀) := by
    intro k _
    have hbase : (0 : ℝ) < RQ * (1 + ηQ) ^ k := by positivity
    have hcard := card_geomBlock_le_endpoint (P := Q) (Q := RQ) (η := ηQ) hRQ hηQ k
    have hcard0 : (0 : ℝ) ≤ ((geomBlock Q RQ (1 + ηQ) k).card : ℝ) := Nat.cast_nonneg _
    have hsq : ((geomBlock Q RQ (1 + ηQ) k).card : ℝ) ^ 2
        ≤ ((RQ * (1 + ηQ) ^ k) * (1 + ηQ)) ^ 2 := by nlinarith [hcard, hcard0]
    have hrest : (0 : ℝ) ≤ (S * ((B₁ : ℝ) / (RQ * (1 + ηQ) ^ k))) ^ 2 * (2 * w₀) := by
      positivity
    have hmul := mul_le_mul_of_nonneg_right hsq hrest
    refine hmul.trans (le_of_eq ?_)
    field_simp
  refine (Finset.sum_le_sum hstep).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end

end RHTower.Sieve
