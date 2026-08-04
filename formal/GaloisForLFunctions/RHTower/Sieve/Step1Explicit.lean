import GaloisForLFunctions.RHTower.Sieve.Step1FromCorrelation

/-!
# Step 1 with the truncation defect discharged

`Step1FromCorrelation.card_le_good_add_correlation` carries two hypotheses: a bound `ε` on the
shifted Möbius correlations, and a bound `W` on the averaged truncation defect.  The second is not an
assumption at all — `AveragedSquarefreeTail.sum_tail_divisor_count_le` supplies it, because every
integer lies in at most `L` of the windows `(t, t+L]`.

Discharging it leaves the correlation bound as the single non-elementary input of the step, with the
defect contributing the explicit term

    L·((X + L)/R + M) / ( ½·L·D − (R + L/R) ).
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- **Step 1 with the defect supplied.**  Only the correlation bound `ε` remains as a hypothesis. -/
theorem card_le_good_add_correlation_explicit {X L R M : ℕ} {ε : ℝ} (hR : 1 ≤ R)
    (hM : ∀ t ∈ Finset.range X, t + L ≤ M)
    (hδ : 0 < (1 / 8) * squarefreeDensity * (L : ℝ))
    (hθ : 0 < (1 / 2) * ((L : ℝ) * squarefreeDensity) - ((R : ℝ) + (L : ℝ) / (R : ℝ)))
    (hε : 0 ≤ ε)
    (hcorr : ∀ h ∈ Finset.Ico 1 L,
      |∑ n ∈ (Finset.range (X + L + 1 - h)).filter (fun n => L ≤ n ∧ n + h ≤ X),
        ((moebius n : ℤ) : ℝ) * ((moebius (n + h) : ℤ) : ℝ)| ≤ ε) :
    ((Finset.range X).card : ℝ)
      ≤ (((Finset.range X).filter (fun t =>
          (3 / 16) * squarefreeDensity * (L : ℝ)
              ≤ (((Finset.Ioc t (t + L)).filter (fun n => moebius n = 1)).card : ℝ)
            ∧ (3 / 16) * squarefreeDensity * (L : ℝ)
              ≤ (((Finset.Ioc t (t + L)).filter (fun n => moebius n = -1)).card : ℝ))).card : ℝ)
        + ((L : ℝ) * (((Finset.range (X + L + 1)).filter (fun n => Squarefree n)).card : ℝ)
            + 2 * (L : ℝ) * ((L : ℝ) * ε + ((2 * L + 1 : ℕ) : ℝ) * (L : ℝ)))
          / ((1 / 8) * squarefreeDensity * (L : ℝ)) ^ 2
        + ((L : ℝ) * (((X : ℝ) + (L : ℝ)) / (R : ℝ) + (M : ℝ)))
          / ((1 / 2) * ((L : ℝ) * squarefreeDensity) - ((R : ℝ) + (L : ℝ) / (R : ℝ))) := by
  refine card_le_good_add_correlation hR hM hδ hθ hε hcorr ?_
  have htail := sum_tail_divisor_count_le 0 X L R M hR (by omega)
  rw [← Finset.range_eq_Ico] at htail
  simpa using htail

end RHTower.Sieve
