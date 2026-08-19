import GaloisForLFunctions.RHTower.Sieve.DampedContourBound
import GaloisForLFunctions.RHTower.Sieve.MoebiusSaving

/-!
# The saving made explicit, for the damped series

The damped analogue of `Sieve/MoebiusSaving`.  The rewriting of the left-edge power as the trivial
size times `exp(−c₀ log(N+H)/(16 log⁹K))` is about the abscissa alone, so `rpow_leftAbscissa` is
reused; only the edge constants carry the extra factor `dampedCorrBound P (leftAbscissa K)`.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology GaloisForLFunctions.HTGeometry

noncomputable section

/-- The Euler correction bound is nonnegative. -/
theorem dampedCorrBound_nonneg {P : Finset ℕ} (hP : ∀ q ∈ P, 2 ≤ q) {c : ℝ} (hc : 1 / 2 ≤ c) :
    0 ≤ dampedCorrBound P c := by
  rw [dampedCorrBound]
  refine Finset.prod_nonneg fun p hp => ?_
  have hp2 := hP p hp
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hpos : (0 : ℝ) < (p : ℝ) ^ (-c) := Real.rpow_pos_of_pos (by linarith) _
  have hlt : (p : ℝ) ^ (-c) < 1 := rpow_neg_lt_one hp2 hc
  positivity

/-- **The damped contour bound with the saving exposed.** -/
theorem exists_norm_tsum_damped_smoothWeight_le_saving {P : Finset ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {N H : ℝ}
    (hN : 0 < N) (hH : 0 < H) (j : ℕ) :
    ∃ (C M₀ : ℝ) (K₀ : ℕ), 0 ≤ C ∧ 0 ≤ M₀ ∧ ∀ K : ℕ, K₀ ≤ K →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ, dampedOmegaMoebius P t n
          * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
        ≤ 2 * ((invZetaRightBound K * dampedCorrBound P (leftAbscissa K)) * C) / truncHeight K
            + (invZetaEdgeBound K * dampedCorrBound P (leftAbscissa K)) * C
                / (truncHeight K) ^ (j + 1) * (rightAbscissa K - leftAbscissa K)
            + (invZetaEdgeBound K * dampedCorrBound P (leftAbscissa K)) * C
                / (truncHeight K) ^ (j + 1) * (rightAbscissa K - leftAbscissa K)
            + (max M₀ (invZetaEdgeBound K) * dampedCorrBound P (leftAbscissa K))
                * (4 * ((N + H) * Real.exp (-(zeroFreeConst / (16 * (Real.log K) ^ 9))
                      * Real.log (N + H))) + 2 * C) := by
  have hP2 : ∀ q ∈ P, 2 ≤ q := fun q hq => (hPprime q hq).two_le
  obtain ⟨C, M₀, K₁, hC, hM₀, hmain⟩ :=
    exists_norm_tsum_damped_smoothWeight_le_concrete hPprime ht0 ht1 hN hH j
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨K₂, hK₂⟩ := eventually_atTop.1 (hlog.eventually_ge_atTop 3)
  refine ⟨C, M₀, max K₁ K₂, hC, hM₀, fun K hKle => ?_⟩
  have hbase := hmain K (le_trans (le_max_left _ _) hKle)
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
  have hcorr0 : 0 ≤ dampedCorrBound P (leftAbscissa K) := dampedCorrBound_nonneg hP2 hcge
  set X : ℝ := (N + H) * Real.exp (-(zeroFreeConst / (16 * (Real.log K) ^ 9))
    * Real.log (N + H)) with hXdef
  have hX0 : (0 : ℝ) ≤ X := by rw [hXdef]; positivity
  have hstep : 2 * ((N + H) ^ leftAbscissa K / leftAbscissa K) ≤ 4 * X := by
    rw [rpow_leftAbscissa hNH, ← hXdef]
    have hdiv : X / leftAbscissa K ≤ X * 2 := by
      rw [div_le_iff₀ hcpos]
      nlinarith [hX0, hcge]
    linarith
  have hcoef0 : 0 ≤ max M₀ (invZetaEdgeBound K) * dampedCorrBound P (leftAbscissa K) :=
    mul_nonneg (le_trans hM₀ (le_max_left _ _)) hcorr0
  have hlast : (max M₀ (invZetaEdgeBound K) * dampedCorrBound P (leftAbscissa K))
      * (2 * ((N + H) ^ leftAbscissa K / leftAbscissa K) + 2 * C)
      ≤ (max M₀ (invZetaEdgeBound K) * dampedCorrBound P (leftAbscissa K)) * (4 * X + 2 * C) :=
    mul_le_mul_of_nonneg_left (by linarith) hcoef0
  rw [hXdef] at hlast
  linarith

end

end RHTower.Sieve
