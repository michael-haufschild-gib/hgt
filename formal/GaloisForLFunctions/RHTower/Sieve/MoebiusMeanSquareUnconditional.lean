import GaloisForLFunctions.RHTower.Sieve.MoebiusMeanSquareFinal

/-!
# The Möbius short-interval mean square, unconditionally

Feeding the twisted contour bound into the mean-square bound leaves a statement with no analytic
hypothesis at all: there is a `B → 0` such that, for all large `N` and every admissible geometry,

    ∑_{k < K} |∑_{Y+k < n ≤ Y+k+L} μ(n)|²
      ≤ Y(1+ε)^J · J · ( 2((B(N)·N)²·log(1+L/Y) + (⌊N⌋+1)²·2/(π²W)) + 2(εL+1)²·log(1+ε) ) .

The admissible frequency band is `8πW + 5 ≤ contourParam(N + smoothWidth N)`, which grows faster than
any power of `log N`.
-/

namespace RHTower.Sieve

open Filter Topology Finset MeasureTheory GaloisForLFunctions.HTGeometry

/-- **The Möbius short-interval mean square, with no analytic hypothesis.** -/
theorem exists_sum_normSq_moebius_window_le :
    ∃ B : ℝ → ℝ, Tendsto B atTop (𝓝 0) ∧
      ∀ᶠ N : ℝ in atTop, ∀ (L Y K J : ℕ) (ε W : ℝ),
        Y + K + L < ⌊N⌋₊ + 1 → 0 < (L : ℝ) → 0 < (Y : ℝ) → 0 ≤ ε → 0 < W →
        8 * Real.pi * W + 5 ≤ ((contourParam (N + smoothWidth N) : ℕ) : ℝ) →
        (Y : ℝ) + K = (Y : ℝ) * (1 + ε) ^ J →
        (∑ k ∈ Finset.range K, ‖∑ n ∈ Finset.Ioc (Y + k) (Y + k + L), moebiusC n‖ ^ 2)
          ≤ ((Y : ℝ) * (1 + ε) ^ J)
              * ((J : ℝ) * blockCost (L : ℝ) (Y : ℝ) ε ((B N * N) ^ 2)
                  ((((⌊N⌋₊ + 1 : ℕ) : ℝ)) ^ 2) W) := by
  obtain ⟨B, hB, hev⟩ := exists_bound_norm_sum_moebiusTwist_div
  refine ⟨B, hB, ?_⟩
  filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with N hN hN0
  intro L Y K J ε W hM hL hY hε hW hWC hJ
  refine sum_normSq_moebius_window_le_of_twist L Y K (⌊N⌋₊ + 1) J hM hL hY hε hW hN0 ?_ hWC hJ
  intro τ hτ
  exact hN τ hτ

end RHTower.Sieve
