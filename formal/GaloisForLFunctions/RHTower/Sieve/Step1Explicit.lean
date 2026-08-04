import GaloisForLFunctions.RHTower.Sieve.Step1FromCorrelation

/-!
# Step 1 with the truncation defect discharged

Both forms of step 1 carry two hypotheses: an analytic one — a bound on the shifted Möbius
correlations, or a mean-square bound on the Möbius window sums — and a bound `W` on the averaged
truncation defect

    ∑_t ∑_{R < d ≤ M} #{n ∈ (t, t+L] : d² ∣ n}.

The second is not an assumption at all — `AveragedSquarefreeTail.sum_tail_divisor_count_le` supplies
it, because every integer lies in at most `L` of the windows `(t, t+L]`.

Discharging it leaves each form of step 1 with a single non-elementary hypothesis, with the defect
contributing the explicit term

    L·((B + L − A)/R + M) / ( ½·L·D − (R + L/R) ).
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

/-- **Step 1 from a mean-square bound, with the defect supplied.**  Only the mean-square bound `V` on
the Möbius window sums remains as a hypothesis. -/
theorem card_le_good_add_meanSquare_explicit {A B L R M : ℕ} {V : ℝ} (hR : 1 ≤ R)
    (hAB : A ≤ B + L)
    (hM : ∀ t ∈ Finset.Ico A B, t + L ≤ M)
    (hδ : 0 < (1 / 8) * squarefreeDensity * (L : ℝ))
    (hθ : 0 < (1 / 2) * ((L : ℝ) * squarefreeDensity) - ((R : ℝ) + (L : ℝ) / (R : ℝ)))
    (hms : ∑ t ∈ Finset.Ico A B,
      (∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ)) ^ 2 ≤ V) :
    ((Finset.Ico A B).card : ℝ)
      ≤ (((Finset.Ico A B).filter (fun t =>
          (3 / 16) * squarefreeDensity * (L : ℝ)
              ≤ (((Finset.Ioc t (t + L)).filter (fun n => moebius n = 1)).card : ℝ)
            ∧ (3 / 16) * squarefreeDensity * (L : ℝ)
              ≤ (((Finset.Ioc t (t + L)).filter (fun n => moebius n = -1)).card : ℝ))).card : ℝ)
        + V / ((1 / 8) * squarefreeDensity * (L : ℝ)) ^ 2
        + ((L : ℝ) * (((B : ℝ) + (L : ℝ) - (A : ℝ)) / (R : ℝ) + (M : ℝ)))
          / ((1 / 2) * ((L : ℝ) * squarefreeDensity) - ((R : ℝ) + (L : ℝ) / (R : ℝ))) := by
  refine card_le_good_add_explicit hR hM hδ hθ hms ?_
  simpa using sum_tail_divisor_count_le A B L R M hR hAB

end RHTower.Sieve
