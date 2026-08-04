import GaloisForLFunctions.RHTower.Sieve.MoebiusMeanSquareRealForm
import GaloisForLFunctions.RHTower.Sieve.Step1Explicit

/-!
# Step 1 of the Hall-law argument, unconditionally

Both hypotheses of `Step1Explicit.card_le_good_add_meanSquare_explicit` are now theorems of this
corpus: the averaged truncation defect is elementary, and the mean square is supplied by
`MoebiusMeanSquareRealForm.exists_sum_sq_real_moebius_Ico_le`.  Substituting the latter as `V` leaves
a statement with no analytic hypothesis.
-/

namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction GaloisForLFunctions.HTGeometry

/-- **Step 1 with the mean square supplied.**  The exceptional-start count is bounded with no
analytic hypothesis; the mean-square numerator is the explicit bound of this development. -/
theorem exists_card_le_good_add_moebius :
    ∃ Bd : ℝ → ℝ, Tendsto Bd atTop (𝓝 0) ∧
      ∀ᶠ N : ℝ in atTop, ∀ (L Y K J R Md : ℕ) (ε W : ℝ),
        Y + K + L < ⌊N⌋₊ + 1 → 0 < (L : ℝ) → 0 < (Y : ℝ) → 0 ≤ ε → 0 < W →
        8 * Real.pi * W + 5 ≤ ((contourParam (N + smoothWidth N) : ℕ) : ℝ) →
        (Y : ℝ) + K = (Y : ℝ) * (1 + ε) ^ J →
        1 ≤ R → (∀ t ∈ Finset.Ico Y (Y + K), t + L ≤ Md) →
        0 < (1 / 8) * squarefreeDensity * (L : ℝ) →
        0 < (1 / 2) * ((L : ℝ) * squarefreeDensity) - ((R : ℝ) + (L : ℝ) / (R : ℝ)) →
        (((Finset.Ico Y (Y + K)).card : ℝ)
          ≤ (((Finset.Ico Y (Y + K)).filter (fun t =>
              (3 / 16) * squarefreeDensity * (L : ℝ)
                  ≤ (((Finset.Ioc t (t + L)).filter (fun n => moebius n = 1)).card : ℝ)
                ∧ (3 / 16) * squarefreeDensity * (L : ℝ)
                  ≤ (((Finset.Ioc t (t + L)).filter (fun n => moebius n = -1)).card : ℝ))).card : ℝ)
            + (((Y : ℝ) * (1 + ε) ^ J)
                * ((J : ℝ) * blockCost (L : ℝ) (Y : ℝ) ε ((Bd N * N) ^ 2)
                    ((((⌊N⌋₊ + 1 : ℕ) : ℝ)) ^ 2) W))
              / ((1 / 8) * squarefreeDensity * (L : ℝ)) ^ 2
            + ((L : ℝ) * ((((Y + K : ℕ) : ℝ) + (L : ℝ) - (Y : ℝ)) / (R : ℝ) + (Md : ℝ)))
              / ((1 / 2) * ((L : ℝ) * squarefreeDensity)
                  - ((R : ℝ) + (L : ℝ) / (R : ℝ)))) := by
  obtain ⟨Bd, hBd, hev⟩ := exists_sum_sq_real_moebius_Ico_le
  refine ⟨Bd, hBd, ?_⟩
  filter_upwards [hev] with N hN
  intro L Y K J R Md ε W hM hL hY hε hW hWC hJ hR hMd hδ hθ
  have hms := hN L Y K J ε W hM hL hY hε hW hWC hJ
  exact card_le_good_add_meanSquare_explicit hR (by omega) hMd hδ hθ hms

end RHTower.Sieve
