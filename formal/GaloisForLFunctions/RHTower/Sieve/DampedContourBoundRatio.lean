import GaloisForLFunctions.RHTower.Sieve.DampedContourBoundGeneral
import GaloisForLFunctions.RHTower.Sieve.MoebiusContourBoundRatio

/-!
# The contour bound in terms of the smoothing ratio, damped

The damped analogue of `Sieve/MoebiusContourBoundRatio`: the width factors `(N+H+1)^k/H^k` are
replaced by powers of a bound `L` for the ratio `N/H`, which is the form the parameter optimisation
consumes.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The contour bound in ratio form, damped.** -/
theorem exists_norm_tsum_damped_smoothWeight_le_ratio {P : Finset ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ (C C' M₀ : ℝ) (K₀ : ℕ), 0 ≤ C ∧ 0 ≤ C' ∧ 0 ≤ M₀ ∧
      ∀ N H L : ℝ, 0 < N → 1 ≤ H → N / H ≤ L → ∀ K : ℕ, K₀ ≤ K →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ, dampedOmegaMoebius P t n
          * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
        ≤ 2 * ((invZetaRightBound K * dampedCorrBound P (leftAbscissa K))
              * (C * (L + 2) ^ 2 * (N + H + 1) ^ rightAbscissa K)) / truncHeight K
          + (invZetaEdgeBound K * dampedCorrBound P (leftAbscissa K))
              * (C' * (L + 2) * (N + H + 1) ^ rightAbscissa K)
              / (truncHeight K) ^ (0 + 1) * (rightAbscissa K - leftAbscissa K)
          + (invZetaEdgeBound K * dampedCorrBound P (leftAbscissa K))
              * (C' * (L + 2) * (N + H + 1) ^ rightAbscissa K)
              / (truncHeight K) ^ (0 + 1) * (rightAbscissa K - leftAbscissa K)
          + (max M₀ (invZetaEdgeBound K) * dampedCorrBound P (leftAbscissa K))
              * (2 * ((N + H) ^ leftAbscissa K / leftAbscissa K)
                  + 2 * (C * (L + 2) ^ 2 * (N + H + 1) ^ leftAbscissa K)) := by
  have hP2 : ∀ q ∈ P, 2 ≤ q := fun q hq => (hPprime q hq).two_le
  obtain ⟨C, C', M₀, K₀, hC, hC', hM₀, hmain⟩ :=
    exists_norm_tsum_damped_smoothWeight_le_general hPprime ht0 ht1
  refine ⟨C, C', M₀, max K₀ 5, hC, hC', hM₀, fun N H L hN hH1 hL K hKle => ?_⟩
  have hH : (0 : ℝ) < H := by linarith
  have hK5 : 5 ≤ K := le_trans (le_max_right _ _) hKle
  have hKR : (5 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK5
  have hbase := hmain N H hN hH K (le_trans (le_max_left _ _) hKle)
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
  have hT1 : 1 ≤ truncHeight K := by rw [truncHeight]; linarith
  have hT0 : (0 : ℝ) < truncHeight K := by linarith
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
