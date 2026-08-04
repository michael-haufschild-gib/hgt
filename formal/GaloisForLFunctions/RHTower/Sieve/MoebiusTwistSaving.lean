import GaloisForLFunctions.RHTower.Sieve.MoebiusTwistContourBound
import GaloisForLFunctions.RHTower.Sieve.MoebiusSaving

/-!
# The twisted contour bound with the saving exposed

The left edge of the twisted contour sits at the same abscissa `c(K)` as the untwisted one, so its
term is again the trivial size `N+H` multiplied by

    exp(-c₀·log(N+H) / (16 log⁹K)),

a genuine decay whenever `log(N+H)/log⁹K` tends to infinity.  The twist changes nothing in this
step: it moved the *height* of the contour, not its abscissa.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology GaloisForLFunctions.HTGeometry

/-- **The twisted contour bound with the saving exposed.**  The left-edge term is the trivial size
`N+H` times `exp(-c₀ log(N+H)/(16 log⁹K))`, uniformly over twists with `5 + 4|τ| ≤ K`. -/
theorem exists_norm_tsum_moebiusTwist_smoothWeight_le_saving {N H : ℝ} (hN : 0 < N) (hH : 0 < H)
    (j : ℕ) :
    ∃ (C M₀ : ℝ) (K₀ : ℕ), 0 ≤ C ∧ 0 ≤ M₀ ∧ ∀ (τ : ℝ) (K : ℕ), K₀ ≤ K → 5 + 4 * |τ| ≤ (K : ℝ) →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
          moebiusTwist τ n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
        ≤ 2 * (invZetaRightBound K * C) / twistHeight K τ
            + invZetaEdgeBound K * C / (twistHeight K τ) ^ (j + 1)
                * (rightAbscissa K - leftAbscissa K)
            + invZetaEdgeBound K * C / (twistHeight K τ) ^ (j + 1)
                * (rightAbscissa K - leftAbscissa K)
            + max M₀ (invZetaEdgeBound K)
                * (4 * ((N + H) * Real.exp (-(zeroFreeConst / (16 * (Real.log K) ^ 9))
                      * Real.log (N + H))) + 2 * C) := by
  obtain ⟨C, M₀, K₁, hC, hM₀, hmain⟩ :=
    exists_norm_tsum_moebiusTwist_smoothWeight_le_concrete hN hH j
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨K₂, hK₂⟩ := eventually_atTop.1 (hlog.eventually_ge_atTop 3)
  refine ⟨C, M₀, max K₁ K₂, hC, hM₀, fun τ K hKle hKτ => ?_⟩
  have hbase := hmain τ K (le_trans (le_max_left _ _) hKle) hKτ
  have hlogK : (3 : ℝ) ≤ Real.log K := hK₂ K (le_trans (le_max_right _ _) hKle)
  have hNH : (0 : ℝ) < N + H := by linarith
  have hA0 := zeroFreeConst_pos
  have hA1 := zeroFreeConst_le_one
  have hL0 : (0 : ℝ) < Real.log K := by linarith
  have hL9 : (27 : ℝ) ≤ (Real.log K) ^ 9 := by
    calc (27 : ℝ) = 3 ^ 3 := by norm_num
      _ ≤ (Real.log K) ^ 3 := by gcongr
      _ ≤ (Real.log K) ^ 9 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h16small : zeroFreeConst / (16 * (Real.log K) ^ 9) ≤ 1 / 54 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hL9, hA1, hA0]
  have hcge : (1 : ℝ) / 2 ≤ leftAbscissa K := by rw [leftAbscissa]; linarith
  have hcpos : (0 : ℝ) < leftAbscissa K := by linarith
  set X : ℝ := (N + H) * Real.exp (-(zeroFreeConst / (16 * (Real.log K) ^ 9))
    * Real.log (N + H)) with hXdef
  have hX0 : (0 : ℝ) ≤ X := by rw [hXdef]; positivity
  have hstep : 2 * ((N + H) ^ leftAbscissa K / leftAbscissa K) ≤ 4 * X := by
    rw [rpow_leftAbscissa hNH, ← hXdef]
    have hdiv : X / leftAbscissa K ≤ X * 2 := by
      rw [div_le_iff₀ hcpos]
      nlinarith [hX0, hcge]
    linarith
  have hlast : max M₀ (invZetaEdgeBound K)
      * (2 * ((N + H) ^ leftAbscissa K / leftAbscissa K) + 2 * C)
      ≤ max M₀ (invZetaEdgeBound K) * (4 * X + 2 * C) :=
    mul_le_mul_of_nonneg_left (by linarith) (le_trans hM₀ (le_max_left _ _))
  rw [hXdef] at hlast
  linarith

end RHTower.Sieve
