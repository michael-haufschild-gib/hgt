import GaloisForLFunctions.RHTower.Sieve.SmoothPrimeCoprimeLogUniformRate
import GaloisForLFunctions.RHTower.Sieve.SmoothPrimeThreeQuarterSigmaBound

/-!
# Moving-modulus coprime logarithmic Möbius bound with sigma-minus-half factor
-/

namespace RHTower.Sieve

open ArithmeticFunction Finset Set
open scoped BigOperators ArithmeticFunction.Moebius

noncomputable section

/-- Quantitative moving-modulus estimate with Chen's squarefree `σ₋₁/₂` factor. -/
theorem exists_abs_coprimeLogMoebius_sub_totientRatio_sigmaNegHalfBound
    {r : ℕ} (hr : Squarefree r) :
    ∃ C K : ℝ, 0 ≤ C ∧ Real.exp 1 ≤ K ∧
      ∀ (Y : ℝ) (D : ℕ), 1 ≤ D → D ≤ ⌊Y⌋₊ → K ≤ Y / (D : ℝ) →
        |coprimeLogMoebius r Y - (r : ℝ) / (Nat.totient r : ℝ)| ≤
          C * ((r : ℝ) / (Nat.totient r : ℝ)) /
              (Real.log (Y / (D : ℝ))) ^ 2 +
            (7 + |Real.eulerMascheroniConstant|) *
              ((D : ℝ) ^ (-(1 / 4 : ℝ)) *
                ((4 : ℝ) ^ 16 * squarefreeSigmaNegHalf r)) := by
  obtain ⟨C, K, hC, hK, hbound⟩ :=
    exists_abs_coprimeLogMoebius_sub_totientRatio_smoothBound hr
  refine ⟨C, K, hC, hK, ?_⟩
  intro Y D hD hDN hscale
  calc
    |coprimeLogMoebius r Y - (r : ℝ) / (Nat.totient r : ℝ)| ≤
        C * ((r : ℝ) / (Nat.totient r : ℝ)) /
            (Real.log (Y / (D : ℝ))) ^ 2 +
          (7 + |Real.eulerMascheroniConstant|) *
            ((D : ℝ) ^ (-(1 / 4 : ℝ)) * smoothPrimeThreeQuarterMass r) :=
      hbound Y D hD hDN hscale
    _ ≤ C * ((r : ℝ) / (Nat.totient r : ℝ)) /
            (Real.log (Y / (D : ℝ))) ^ 2 +
          (7 + |Real.eulerMascheroniConstant|) *
            ((D : ℝ) ^ (-(1 / 4 : ℝ)) *
              ((4 : ℝ) ^ 16 * squarefreeSigmaNegHalf r)) := by
      gcongr
      exact smoothPrimeThreeQuarterMass_le_sigmaNegHalf
        (Nat.pos_of_ne_zero hr.ne_zero)

end

end RHTower.Sieve
