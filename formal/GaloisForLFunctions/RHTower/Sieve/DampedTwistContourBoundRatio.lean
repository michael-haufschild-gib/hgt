import GaloisForLFunctions.RHTower.Sieve.DampedTwistContourBoundGeneral
import GaloisForLFunctions.RHTower.Sieve.WidthFactor

/-!
# The twisted damped contour bound in terms of the smoothing ratio

Substituting the width factors turns the cutoff dependence of the twisted damped general bound into
a single polynomial in the ratio `L = N/H`.  The twist appears only in the truncation height
`twistHeight K τ` and in the side condition `5 + 4|τ| ≤ K`; the damping only in the correction
factor multiplying each edge constant.
-/

namespace RHTower.Sieve

open Complex Filter Topology GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The twisted damped contour bound in ratio form.** -/
theorem exists_norm_tsum_dampedTwist_smoothWeight_le_ratio {P : Finset ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) :
    ∃ (C C' M₀ : ℝ) (K₀ : ℕ), 0 ≤ C ∧ 0 ≤ C' ∧ 0 ≤ M₀ ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ∀ N H L : ℝ, 0 < N → 1 ≤ H → N / H ≤ L → ∀ (τ : ℝ) (K : ℕ), K₀ ≤ K →
        5 + 4 * |τ| ≤ (K : ℝ) →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ, dampedTwist P t τ n
          * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
        ≤ 2 * ((invZetaRightBound K * dampedCorrBound P (leftAbscissa K))
              * (C * (L + 2) ^ 2 * (N + H + 1) ^ rightAbscissa K)) / twistHeight K τ
          + (invZetaEdgeBound K * dampedCorrBound P (leftAbscissa K))
              * (C' * (L + 2) * (N + H + 1) ^ rightAbscissa K)
              / (twistHeight K τ) ^ (0 + 1) * (rightAbscissa K - leftAbscissa K)
          + (invZetaEdgeBound K * dampedCorrBound P (leftAbscissa K))
              * (C' * (L + 2) * (N + H + 1) ^ rightAbscissa K)
              / (twistHeight K τ) ^ (0 + 1) * (rightAbscissa K - leftAbscissa K)
          + (max M₀ (invZetaEdgeBound K) * dampedCorrBound P (leftAbscissa K))
              * (2 * ((N + H) ^ leftAbscissa K / leftAbscissa K)
                  + 2 * (C * (L + 2) ^ 2 * (N + H + 1) ^ leftAbscissa K)) := by
  have hP2 : ∀ q ∈ P, 2 ≤ q := fun q hq => (hPprime q hq).two_le
  obtain ⟨C, C', M₀, K₀, hC, hC', hM₀, hmain⟩ :=
    exists_norm_tsum_dampedTwist_smoothWeight_le_general hPprime
  refine ⟨C, C', M₀, max K₀ 5, hC, hC', hM₀,
    fun t ht0 ht1 N H L hN hH1 hL τ K hKle hKτ => ?_⟩
  have hH : (0 : ℝ) < H := by linarith
  have hK5 : 5 ≤ K := le_trans (le_max_right _ _) hKle
  have hKR : (5 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK5
  have hbase := hmain t ht0 ht1 N H hN hH τ K (le_trans (le_max_left _ _) hKle) hKτ
  have hA0 := zeroFreeConst_pos
  have hA1 := zeroFreeConst_le_one
  have hL0 : (0 : ℝ) < Real.log K := Real.log_pos (by linarith)
  have hLone : (1 : ℝ) < Real.log K := by
    have he : Real.exp 1 < 5 := by
      have := Real.exp_one_lt_d9
      linarith
    exact (Real.lt_log_iff_exp_lt (by linarith)).2 (by linarith)
  have hL9one : (1 : ℝ) ≤ (Real.log K) ^ 9 := one_le_pow₀ hLone.le
  have hL9pos : (0 : ℝ) < (Real.log K) ^ 9 := by positivity
  have hchalf : (1 : ℝ) / 2 ≤ leftAbscissa K := by
    rw [leftAbscissa]
    have hsmall : zeroFreeConst / (16 * (Real.log K) ^ 9) ≤ 1 / 16 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hA1, hA0, hL9one]
    linarith
  have hcorr0 : 0 ≤ dampedCorrBound P (leftAbscissa K) := dampedCorrBound_nonneg hP2 hchalf
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
  have hRnn : (0 : ℝ) ≤ invZetaRightBound K * dampedCorrBound P (leftAbscissa K) :=
    mul_nonneg (invZetaRightBound_nonneg K) hcorr0
  have hEnn : (0 : ℝ) ≤ invZetaEdgeBound K * dampedCorrBound P (leftAbscissa K) :=
    mul_nonneg (invZetaEdgeBound_nonneg K) hcorr0
  have hMnn : (0 : ℝ)
      ≤ max M₀ (invZetaEdgeBound K) * dampedCorrBound P (leftAbscissa K) :=
    mul_nonneg (le_trans hM₀ (le_max_left _ _)) hcorr0
  have hsq := sq_width_factor_le hH1 hN.le hL hC
  have hlin := width_factor_le hH1 hN.le hL hC'
  refine le_trans hbase ?_
  gcongr

end

end RHTower.Sieve
