import GaloisForLFunctions.RHTower.Sieve.DampedContourBoundRatio

/-!
# The damped bound is the correction times the Möbius bound

Every one of the four contour terms carries exactly one edge constant, and in the damped chain each
of those is the `invZeta` constant multiplied by the *same* factor
`dampedCorrBound P (leftAbscissa K)`.  So the whole damped bound factors as that constant times the
expression appearing in `Sieve/MoebiusContourBoundRatio`.

This is what makes the rest of the `μ` optimisation chain reusable rather than needing to be
mirrored: any downstream bound `μ-expression ≤ B` yields
`damped ≤ dampedCorrBound P (leftAbscissa K) · B` by multiplying through by a nonnegative constant.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The damped contour bound, factored.** -/
theorem exists_norm_tsum_damped_smoothWeight_le_ratio_factored {P : Finset ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ (C C' M₀ : ℝ) (K₀ : ℕ), 0 ≤ C ∧ 0 ≤ C' ∧ 0 ≤ M₀ ∧
      ∀ N H L : ℝ, 0 < N → 1 ≤ H → N / H ≤ L → ∀ K : ℕ, K₀ ≤ K →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ, dampedOmegaMoebius P t n
          * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
        ≤ dampedCorrBound P (leftAbscissa K)
          * (2 * (invZetaRightBound K
                * (C * (L + 2) ^ 2 * (N + H + 1) ^ rightAbscissa K)) / truncHeight K
            + invZetaEdgeBound K * (C' * (L + 2) * (N + H + 1) ^ rightAbscissa K)
                / (truncHeight K) ^ (0 + 1) * (rightAbscissa K - leftAbscissa K)
            + invZetaEdgeBound K * (C' * (L + 2) * (N + H + 1) ^ rightAbscissa K)
                / (truncHeight K) ^ (0 + 1) * (rightAbscissa K - leftAbscissa K)
            + max M₀ (invZetaEdgeBound K)
                * (2 * ((N + H) ^ leftAbscissa K / leftAbscissa K)
                    + 2 * (C * (L + 2) ^ 2 * (N + H + 1) ^ leftAbscissa K))) := by
  obtain ⟨C, C', M₀, K₀, hC, hC', hM₀, hmain⟩ :=
    exists_norm_tsum_damped_smoothWeight_le_ratio hPprime ht0 ht1
  refine ⟨C, C', M₀, K₀, hC, hC', hM₀, fun N H L hN hH1 hL K hKle => ?_⟩
  refine le_trans (hmain N H L hN hH1 hL K hKle) (le_of_eq ?_)
  ring

/-- **Transfer.**  Any bound for the Möbius-shaped expression yields the damped bound. -/
theorem norm_tsum_damped_le_of_moebius_shape {P : Finset ℕ} {c : ℝ} (hP : ∀ q ∈ P, 2 ≤ q)
    (hc : 1 / 2 ≤ c) {A B D : ℝ} (hAB : A ≤ dampedCorrBound P c * B) (hBD : B ≤ D) :
    A ≤ dampedCorrBound P c * D :=
  le_trans hAB (mul_le_mul_of_nonneg_left hBD (dampedCorrBound_nonneg hP hc))

end

end RHTower.Sieve
