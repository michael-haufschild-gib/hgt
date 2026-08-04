import GaloisForLFunctions.RHTower.Sieve.MoebiusTwistContourBoundGeneral
import GaloisForLFunctions.RHTower.Sieve.WidthFactor

/-!
# The twisted contour bound in terms of the smoothing ratio

Substituting the width factors turns the cutoff dependence of the twisted general bound into a
single polynomial in the ratio `L = N/H`, exactly as in the untwisted case.  The twist appears only
in the truncation height `twistHeight K τ` and in the side condition `5 + 4|τ| ≤ K`.
-/

namespace RHTower.Sieve

open Complex Filter Topology GaloisForLFunctions.HTGeometry

/-- **The twisted contour bound in terms of the smoothing ratio.** -/
theorem exists_norm_tsum_moebiusTwist_smoothWeight_le_ratio :
    ∃ (C C' M₀ : ℝ) (K₀ : ℕ), 0 ≤ C ∧ 0 ≤ C' ∧ 0 ≤ M₀ ∧
      ∀ N H L : ℝ, 0 < N → 1 ≤ H → N / H ≤ L → ∀ (τ : ℝ) (K : ℕ), K₀ ≤ K →
        5 + 4 * |τ| ≤ (K : ℝ) →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
          moebiusTwist τ n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
        ≤ 2 * (invZetaRightBound K
              * (C * (L + 2) ^ 2 * (N + H + 1) ^ rightAbscissa K)) / twistHeight K τ
          + invZetaEdgeBound K * (C' * (L + 2) * (N + H + 1) ^ rightAbscissa K)
              / (twistHeight K τ) ^ (0 + 1) * (rightAbscissa K - leftAbscissa K)
          + invZetaEdgeBound K * (C' * (L + 2) * (N + H + 1) ^ rightAbscissa K)
              / (twistHeight K τ) ^ (0 + 1) * (rightAbscissa K - leftAbscissa K)
          + max M₀ (invZetaEdgeBound K)
              * (2 * ((N + H) ^ leftAbscissa K / leftAbscissa K)
                  + 2 * (C * (L + 2) ^ 2 * (N + H + 1) ^ leftAbscissa K)) := by
  obtain ⟨C, C', M₀, K₀, hC, hC', hM₀, hmain⟩ :=
    exists_norm_tsum_moebiusTwist_smoothWeight_le_general
  refine ⟨C, C', M₀, max K₀ 5, hC, hC', hM₀, fun N H L hN hH1 hL τ K hKle hKτ => ?_⟩
  have hH : (0 : ℝ) < H := by linarith
  have hK5 : 5 ≤ K := le_trans (le_max_right _ _) hKle
  have hKR : (5 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK5
  have hbase := hmain N H hN hH τ K (le_trans (le_max_left _ _) hKle) hKτ
  have hA0 := zeroFreeConst_pos
  have hA1 := zeroFreeConst_le_one
  have hL0 : (0 : ℝ) < Real.log K := Real.log_pos (by linarith)
  have hL9pos : (0 : ℝ) < (Real.log K) ^ 9 := by positivity
  have h16 : (0 : ℝ) < zeroFreeConst / (16 * (Real.log K) ^ 9) := by positivity
  have h2pos : (0 : ℝ) < zeroFreeConst / (2 * (Real.log K) ^ 9) := by positivity
  have hgap0 : (0 : ℝ) ≤ rightAbscissa K - leftAbscissa K := by
    rw [rightAbscissa, leftAbscissa]; linarith
  have hT1 : 1 ≤ twistHeight K τ := one_le_twistHeight hKτ
  have hT0 : (0 : ℝ) < twistHeight K τ := by linarith
  have hNH : (0 : ℝ) < N + H + 1 := by linarith
  have hNH0 : (0 : ℝ) < N + H := by linarith
  have hd0 : (0 : ℝ) < (N + H + 1) ^ rightAbscissa K := Real.rpow_pos_of_pos hNH _
  have hc0 : (0 : ℝ) < (N + H + 1) ^ leftAbscissa K := Real.rpow_pos_of_pos hNH _
  have hRnn := invZetaRightBound_nonneg K
  have hEnn := invZetaEdgeBound_nonneg K
  have hMnn : (0 : ℝ) ≤ max M₀ (invZetaEdgeBound K) := le_trans hM₀ (le_max_left _ _)
  have hsq := sq_width_factor_le hH1 hN.le hL hC
  have hlin := width_factor_le hH1 hN.le hL hC'
  refine le_trans hbase ?_
  gcongr

end RHTower.Sieve
