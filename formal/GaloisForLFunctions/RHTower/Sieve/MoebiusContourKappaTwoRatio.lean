import GaloisForLFunctions.RHTower.Sieve.WidthFactor
import GaloisForLFunctions.RHTower.Sieve.MoebiusContourKappaTwoGeneral

/-!
# The width-`log^{-2}` contour bound in terms of the smoothing ratio

Substituting the width factors turns the cutoff dependence of the uniform contour bound into a
single polynomial in the ratio `L = N/H`.  What is left depends on the cutoff only through the
trivial sizes `(N+H)^{c(K)}` and `(N+H+1)^{d(K)}`, plus the explicit price `(L+2)²` for narrowing
the smoothing.
-/

namespace RHTower.Sieve

open Complex Filter Topology GaloisForLFunctions.HTGeometry

/-- **The width-`log^{-2}` contour bound in terms of the smoothing ratio.** -/
theorem exists_norm_tsum_moebius_smoothWeight_le_kappa_two_ratio :
    ∃ (C C' Ms : ℝ) (K₀ : ℕ), 0 ≤ C ∧ 0 ≤ C' ∧ 0 ≤ Ms ∧
      ∀ N H L : ℝ, 0 < N → 1 ≤ H → N / H ≤ L → ∀ K : ℕ, K₀ ≤ K →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
          (ArithmeticFunction.moebius n : ℂ)
            * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
        ≤ 2 * (invZetaRightBoundTwo K
              * (C * (L + 2) ^ 2 * (N + H + 1) ^ rightAbscissaTwo K)) / truncHeight K
          + Ms * Real.log K ^ 2 * (C' * (L + 2) * (N + H + 1) ^ rightAbscissaTwo K)
              / (truncHeight K) ^ (0 + 1) * (rightAbscissaTwo K - leftAbscissaTwo K)
          + Ms * Real.log K ^ 2 * (C' * (L + 2) * (N + H + 1) ^ rightAbscissaTwo K)
              / (truncHeight K) ^ (0 + 1) * (rightAbscissaTwo K - leftAbscissaTwo K)
          + Ms * Real.log K ^ 2
              * (2 * ((N + H) ^ leftAbscissaTwo K / leftAbscissaTwo K)
                  + 2 * (C * (L + 2) ^ 2 * (N + H + 1) ^ leftAbscissaTwo K)) := by
  obtain ⟨C, C', Ms, K₀, hC, hC', hMs, hmain⟩ :=
    exists_norm_tsum_moebius_smoothWeight_le_kappa_two_general
  refine ⟨C, C', Ms, max K₀ 5, hC, hC', hMs, fun N H L hN hH1 hL K hKle => ?_⟩
  have hH : (0 : ℝ) < H := by linarith
  have hK5 : 5 ≤ K := le_trans (le_max_right _ _) hKle
  have hKR : (5 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK5
  have hbase := hmain N H hN hH K (le_trans (le_max_left _ _) hKle)
  have hL0 : (0 : ℝ) < Real.log K := Real.log_pos (by linarith)
  have hLsq0 : (0 : ℝ) < Real.log K ^ 2 := by positivity
  have hinv0 : (0 : ℝ) < 1 / Real.log K ^ 2 := by positivity
  have hgap0 : (0 : ℝ) ≤ rightAbscissaTwo K - leftAbscissaTwo K := by
    rw [rightAbscissaTwo, leftAbscissaTwo]; linarith
  have hT1 : (1 : ℝ) ≤ truncHeight K := by rw [truncHeight]; linarith
  have hT0 : (0 : ℝ) < truncHeight K := by linarith
  have hNH : (0 : ℝ) < N + H + 1 := by linarith
  have hd0 : (0 : ℝ) < (N + H + 1) ^ rightAbscissaTwo K := Real.rpow_pos_of_pos hNH _
  have hc0 : (0 : ℝ) < (N + H + 1) ^ leftAbscissaTwo K := Real.rpow_pos_of_pos hNH _
  have hRnn := invZetaRightBoundTwo_nonneg K
  have hMnn : (0 : ℝ) ≤ Ms * Real.log K ^ 2 := by positivity
  have hsq := sq_width_factor_le hH1 hN.le hL hC
  have hlin := width_factor_le hH1 hN.le hL hC'
  refine le_trans hbase ?_
  gcongr

end RHTower.Sieve
