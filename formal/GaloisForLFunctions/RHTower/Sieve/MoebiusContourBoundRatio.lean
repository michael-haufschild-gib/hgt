import GaloisForLFunctions.RHTower.Sieve.WidthFactor

/-!
# The contour bound in terms of the smoothing ratio

Substituting the width factors turns the cutoff dependence of the general contour bound into a
single polynomial in the ratio `L = N/H`.  What is left depends on the cutoff only through the
trivial sizes `(N+H)^{c(K)}` and `(N+H+1)^{d(K)}`, exactly as in the diagonal case, plus the
explicit price `(L+2)²` for narrowing the smoothing.
-/

namespace RHTower.Sieve

open Complex Filter Topology GaloisForLFunctions.HTGeometry

/-- **The contour bound in terms of the smoothing ratio.** -/
theorem exists_norm_tsum_moebius_smoothWeight_le_ratio :
    ∃ (C C' M₀ : ℝ) (K₀ : ℕ), 0 ≤ C ∧ 0 ≤ C' ∧ 0 ≤ M₀ ∧
      ∀ N H L : ℝ, 0 < N → 1 ≤ H → N / H ≤ L → ∀ K : ℕ, K₀ ≤ K →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
          (ArithmeticFunction.moebius n : ℂ) * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
        ≤ 2 * (invZetaRightBound K
              * (C * (L + 2) ^ 2 * (N + H + 1) ^ rightAbscissa K)) / truncHeight K
          + invZetaEdgeBound K * (C' * (L + 2) * (N + H + 1) ^ rightAbscissa K)
              / (truncHeight K) ^ (0 + 1) * (rightAbscissa K - leftAbscissa K)
          + invZetaEdgeBound K * (C' * (L + 2) * (N + H + 1) ^ rightAbscissa K)
              / (truncHeight K) ^ (0 + 1) * (rightAbscissa K - leftAbscissa K)
          + max M₀ (invZetaEdgeBound K)
              * (2 * ((N + H) ^ leftAbscissa K / leftAbscissa K)
                  + 2 * (C * (L + 2) ^ 2 * (N + H + 1) ^ leftAbscissa K)) := by
  obtain ⟨C, C', M₀, K₀, hC, hC', hM₀, hmain⟩ :=
    exists_norm_tsum_moebius_smoothWeight_le_general
  refine ⟨C, C', M₀, max K₀ 5, hC, hC', hM₀, fun N H L hN hH1 hL K hKle => ?_⟩
  have hH : (0 : ℝ) < H := by linarith
  have hK5 : 5 ≤ K := le_trans (le_max_right _ _) hKle
  have hKR : (5 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK5
  have hbase := hmain N H hN hH K (le_trans (le_max_left _ _) hKle)
  -- the geometry at `K`
  have hA0 := zeroFreeConst_pos
  have hA1 := zeroFreeConst_le_one
  have hL0 : (0 : ℝ) < Real.log K := Real.log_pos (by linarith)
  have hL9pos : (0 : ℝ) < (Real.log K) ^ 9 := by positivity
  have h16 : (0 : ℝ) < zeroFreeConst / (16 * (Real.log K) ^ 9) := by positivity
  have h2pos : (0 : ℝ) < zeroFreeConst / (2 * (Real.log K) ^ 9) := by positivity
  have hgap0 : (0 : ℝ) ≤ rightAbscissa K - leftAbscissa K := by
    rw [rightAbscissa, leftAbscissa]; linarith
  have hT1 : 1 ≤ truncHeight K := by rw [truncHeight]; linarith
  have hT0 : (0 : ℝ) < truncHeight K := by linarith
  have hNH : (0 : ℝ) < N + H + 1 := by linarith
  have hNH0 : (0 : ℝ) < N + H := by linarith
  have hd0 : (0 : ℝ) < (N + H + 1) ^ rightAbscissa K := Real.rpow_pos_of_pos hNH _
  have hc0 : (0 : ℝ) < (N + H + 1) ^ leftAbscissa K := Real.rpow_pos_of_pos hNH _
  have hRnn := invZetaRightBound_nonneg K
  have hEnn := invZetaEdgeBound_nonneg K
  have hMnn : (0 : ℝ) ≤ max M₀ (invZetaEdgeBound K) := le_trans hM₀ (le_max_left _ _)
  -- the width factors
  have hsq := sq_width_factor_le hH1 hN.le hL hC
  have hlin := width_factor_le hH1 hN.le hL hC'
  refine le_trans hbase ?_
  gcongr

end RHTower.Sieve
