import GaloisForLFunctions.RHTower.Sieve.MoebiusMeanSquareExplicit

/-!
# The normalized bound on a dyadic range

Taking `K = Y`, so that the starting points run over `[Y, 2Y)` and the range has ratio `2`, and
dividing by the trivial size `Y·L²`, the explicit bound becomes

    (mean square) / (Y L²)
      ≤ 2 log 2 · (1+ε)/ε · ( 2M₁/(Y L) + 4M₂/(π²W L²) + 2(εL+1)²·ε/L² ) .

The three summands are the cancellation, the frequency tail and the excess, each already divided by
the trivial size.  Their smallness conditions are visible: `M₁/(εYL) → 0`, `M₂/(εWL²) → 0`, `ε → 0`.
-/

namespace RHTower.Sieve

open Filter Topology Finset GaloisForLFunctions.HTGeometry

/-- **The explicit bound, normalized on a dyadic range.** -/
theorem normalized_bound_dyadic (Y L : ℕ) (ε W M₁ M₂ : ℝ) (hY : 0 < (Y : ℝ))
    (hL : 0 < (L : ℝ)) (hε : 0 < ε) (hW : 0 < W) :
    ((Y : ℝ) + (Y : ℝ)) * (Real.log (1 + (Y : ℝ) / (Y : ℝ)) * (1 + ε) / ε)
        * (2 * M₁ * ((L : ℝ) / (Y : ℝ)) + 4 * M₂ / (Real.pi ^ 2 * W)
            + 2 * (ε * (L : ℝ) + 1) ^ 2 * ε)
        / ((Y : ℝ) * (L : ℝ) ^ 2)
      = 2 * Real.log 2 * ((1 + ε) / ε)
          * (2 * M₁ / ((Y : ℝ) * (L : ℝ))
              + 4 * M₂ / (Real.pi ^ 2 * W * (L : ℝ) ^ 2)
              + 2 * (ε * (L : ℝ) + 1) ^ 2 * ε / (L : ℝ) ^ 2) := by
  have hself : (Y : ℝ) / (Y : ℝ) = 1 := div_self (ne_of_gt hY)
  rw [hself]
  have hpi : (0 : ℝ) < Real.pi ^ 2 * W := by positivity
  field_simp
  ring_nf

/-- **The mean square, normalized on a dyadic range.** -/
theorem exists_normalized_mean_square_le :
    ∃ B : ℝ → ℝ, Tendsto B atTop (𝓝 0) ∧
      ∀ᶠ N : ℝ in atTop, ∀ (L Y J : ℕ) (ε W : ℝ),
        Y + Y + L < ⌊N⌋₊ + 1 → 0 < (L : ℝ) → 0 < (Y : ℝ) → 0 < ε → 0 < W →
        8 * Real.pi * W + 5 ≤ ((contourParam (N + smoothWidth N) : ℕ) : ℝ) →
        (Y : ℝ) + (Y : ℝ) = (Y : ℝ) * (1 + ε) ^ J →
        (∑ t ∈ Finset.Ico Y (Y + Y),
            (∑ n ∈ Finset.Ioc t (t + L), ((ArithmeticFunction.moebius n : ℤ) : ℝ)) ^ 2)
            / ((Y : ℝ) * (L : ℝ) ^ 2)
          ≤ 2 * Real.log 2 * ((1 + ε) / ε)
              * (2 * (B N * N) ^ 2 / ((Y : ℝ) * (L : ℝ))
                  + 4 * ((((⌊N⌋₊ + 1 : ℕ) : ℝ)) ^ 2) / (Real.pi ^ 2 * W * (L : ℝ) ^ 2)
                  + 2 * (ε * (L : ℝ) + 1) ^ 2 * ε / (L : ℝ) ^ 2) := by
  obtain ⟨B, hB, hev⟩ := exists_sum_sq_real_moebius_explicit
  refine ⟨B, hB, ?_⟩
  filter_upwards [hev] with N hN
  intro L Y J ε W hM hL hY hε hW hWC hJ
  have hbase := hN L Y Y J ε W hM hL hY hε hW hWC hJ
  have hden : (0 : ℝ) < (Y : ℝ) * (L : ℝ) ^ 2 := by positivity
  rw [← normalized_bound_dyadic Y L ε W ((B N * N) ^ 2)
    ((((⌊N⌋₊ + 1 : ℕ) : ℝ)) ^ 2) hY hL hε hW]
  exact div_le_div_of_nonneg_right hbase hden.le

end RHTower.Sieve
