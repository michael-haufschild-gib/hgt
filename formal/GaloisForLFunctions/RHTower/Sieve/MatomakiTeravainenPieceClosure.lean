import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenOuterBoxClassification

/-!
# Sign closure of Proposition 2.2 pieces

The minorant expansion has alternating signs.  Each sign is absorbed into one divisor-bounded
coefficient, so negating a literal Type I, Type I/II, or Type II piece preserves its exact form.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

theorem mtRealIntervalAF_neg (f : ℕ → ℂ) (L U : ℝ) :
    mtRealIntervalAF (fun n => -f n) L U = -mtRealIntervalAF f L U := by
  ext n
  change (if n = 0 then 0 else if L < (n : ℝ) ∧ (n : ℝ) ≤ U then -f n else 0) =
    -(if n = 0 then 0 else if L < (n : ℝ) ∧ (n : ℝ) ≤ U then f n else 0)
  split_ifs <;> simp_all

/-- Exact proposition piece forms are stable under the alternating signs of the minorant. -/
theorem MTProposition22Piece.neg
    {X Y z₀ z delta epsilon : ℝ} {f : ArithmeticFunction ℂ}
    (hf : MTProposition22Piece X Y z₀ z delta epsilon f) :
    MTProposition22Piece X Y z₀ z delta epsilon (-f) := by
  cases hf with
  | typeI data =>
      let negData : MTTypeIPieceData X Y delta epsilon :=
        { data with
          α := fun n => -data.α n
          α_divisorBounded := by
            simpa only [neg_one_mul] using data.α_divisorBounded.smul (-1) }
      have hpiece : negData.pieceAF = -data.pieceAF := by
        unfold MTTypeIPieceData.pieceAF mtTypeIPieceAF
        rw [show mtRealIntervalAF negData.α negData.M₁ (2 * negData.M₁) =
            -mtRealIntervalAF data.α data.M₁ (2 * data.M₁) by
          simpa [negData] using mtRealIntervalAF_neg data.α data.M₁ (2 * data.M₁)]
        dsimp only [negData]
        exact neg_mul (α := ArithmeticFunction ℂ) _ _
      rw [← hpiece]
      exact MTProposition22Piece.typeI negData
  | typeI_II data =>
      let negData : MTTypeI_II_PieceData X Y delta epsilon :=
        { data with
          α := fun n => -data.α n
          α_divisorBounded := by
            simpa only [neg_one_mul] using data.α_divisorBounded.smul (-1) }
      have hpiece : negData.pieceAF = -data.pieceAF := by
        unfold MTTypeI_II_PieceData.pieceAF mtTypeI_II_PieceAF
        rw [show mtRealIntervalAF negData.α negData.M₁ (2 * negData.M₁) =
            -mtRealIntervalAF data.α data.M₁ (2 * data.M₁) by
          simpa [negData] using mtRealIntervalAF_neg data.α data.M₁ (2 * data.M₁)]
        dsimp only [negData]
        rw [neg_mul (α := ArithmeticFunction ℂ), neg_mul (α := ArithmeticFunction ℂ)]
      rw [← hpiece]
      exact MTProposition22Piece.typeI_II negData
  | typeII data =>
      let negData : MTTypeIIPieceData X Y z₀ z delta epsilon :=
        { data with
          β := fun n => -data.β n
          β_divisorBounded := by
            simpa only [neg_one_mul] using data.β_divisorBounded.smul (-1) }
      have hpiece : negData.pieceAF = -data.pieceAF := by
        unfold MTTypeIIPieceData.pieceAF mtTypeIIPieceAF
        rw [show mtRealIntervalAF negData.β negData.M₂ (2 * negData.M₂) =
            -mtRealIntervalAF data.β data.M₂ (2 * data.M₂) by
          simpa [negData] using mtRealIntervalAF_neg data.β data.M₂ (2 * data.M₂)]
        dsimp only [negData]
        exact mul_neg (α := ArithmeticFunction ℂ) _ _
      rw [← hpiece]
      exact MTProposition22Piece.typeII negData

end

end RHTower.Sieve
