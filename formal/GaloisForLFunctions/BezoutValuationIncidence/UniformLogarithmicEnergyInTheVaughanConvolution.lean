import GaloisForLFunctions.BezoutValuationIncidence.TheVaughanConvolutionSeparatesItsSmoothMean
import GaloisForLFunctions.BezoutValuationIncidence.UniformLogarithmicCancellationInTruncatedMobiusReceivers
import GaloisForLFunctions.BezoutValuationIncidence.UniformLogarithmicEnergyFromPrefixCancellation

/-!
# Uniform logarithmic energy in the Vaughan convolution

A reciprocal divisor majorant pays one finite-head bound for every cutoff.
The actual convolution fluctuation and truncated Möbius prefixes therefore
inherit every logarithmic pronic norm saving below half damping.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- A summable coefficient majorant gives a common linear bound for the centered floor transform. -/
theorem abs_weightCenteredPrefix_le_linear_of_majorant {a b : ℕ → ℝ}
    (hb : Summable (fun d : ℕ => b d / d)) (hab : ∀ d, |a d| ≤ b d)
    {n : ℕ} (hn : 1 ≤ n) :
    |weightCenteredPrefix a (∑' d : ℕ, a d / d) n| ≤
      (∑' d : ℕ, b d / d) * n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hb0 (d : ℕ) : 0 ≤ b d := (abs_nonneg _).trans (hab d)
  have hfloor0 : 0 ≤ pmFloorAverage b n :=
    div_nonneg (sum_nonneg fun d _ => mul_nonneg (hb0 d) (Nat.cast_nonneg _)) (Nat.cast_nonneg n)
  have hdefect : pmFloorMeanDefect b n ≤ ∑' d : ℕ, b d / d :=
    sub_le_self _ hfloor0
  have heq : weightCenteredPrefix a (∑' d : ℕ, a d / d) n =
      (pmFloorAverage a n - ∑' d : ℕ, a d / d) * n := by
    rw [weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor,
      pmFloorAverage, sub_mul, div_mul_cancel₀ _ hn0.ne']
  rw [heq, abs_mul, Nat.abs_cast]
  exact mul_le_mul_of_nonneg_right
    ((abs_pmFloorAverage_sub_density_le hb hab n).trans hdefect) hn0.le

/-- One reciprocal divisor majorant controls the finite heads of every convolution fluctuation. -/
theorem abs_pmVaughanConvolutionFluctuationPrefix_le_linear {ε : ℝ} (hε : 0 < ε)
    (U V : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    |pmVaughanConvolutionFluctuationPrefix ε U V n| ≤
      (2 * ∑' d : ℕ, pmVaughanFloorMajorant ε d / d) * n := by
  have hb : Summable (fun d : ℕ => (2 * pmVaughanFloorMajorant ε d) / d) := by
    simpa only [mul_div_assoc] using (summable_pmVaughanFloorMajorant_div hε).mul_left 2
  have hmajor (d : ℕ) :
      |dampedSignWeight (pmVaughanConvolutionFluctuation U V) ε d| ≤
        2 * pmVaughanFloorMajorant ε d := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [dampedSignWeight, pmVaughanFloorMajorant, Real.zero_rpow (neg_ne_zero.mpr hε.ne')]
    · rw [dampedSignWeight, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
      simpa only [pmVaughanFloorMajorant, mul_assoc] using
        mul_le_mul_of_nonneg_right (abs_pmVaughanConvolutionFluctuation_le U V hd)
          (Real.rpow_nonneg (Nat.cast_nonneg d) (-ε))
  have hmass : (∑' d : ℕ, (2 * pmVaughanFloorMajorant ε d) / d) =
      2 * ∑' d : ℕ, pmVaughanFloorMajorant ε d / d := by
    simp_rw [mul_div_assoc]
    exact tsum_mul_left
  simpa only [pmVaughanConvolutionFluctuationPrefix, hmass] using
    abs_weightCenteredPrefix_le_linear_of_majorant hb hmajor hn

/-- Every convolution fluctuation shares a global smooth-power prefix bound. -/
theorem exists_uniform_pmVaughanConvolutionFluctuationPrefix_rpow_bound
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ U V n : ℕ, 1 ≤ n →
      |pmVaughanConvolutionFluctuationPrefix ε U V n| ≤ K * (n : ℝ) ^ (1 - ε) := by
  obtain ⟨B, hB, hzero⟩ := exists_uniform_pmVaughanConvolutionFluctuation_prefix_log_rate hε hε2 0
  have hA : 0 ≤ 2 * ∑' d : ℕ, pmVaughanFloorMajorant ε d / d := by
    exact mul_nonneg (by norm_num) (tsum_nonneg fun d =>
      div_nonneg (pmVaughanFloorMajorant_nonneg ε d) (Nat.cast_nonneg d))
  have hevent : ∀ᶠ n : ℕ in atTop, ∀ a : ℕ × ℕ,
      |pmVaughanConvolutionFluctuationPrefix ε a.1 a.2 n| ≤ B * (n : ℝ) ^ (1 - ε) := by
    filter_upwards [hzero] with n hn a
    simpa only [pmVaughanConvolutionFluctuationPrefix, pow_zero, div_one] using hn a.1 a.2
  obtain ⟨K, hK, hbound⟩ := exists_uniform_rpow_bound_of_eventually
    (f := fun a : ℕ × ℕ => pmVaughanConvolutionFluctuationPrefix ε a.1 a.2)
    hε.le hA hB (fun a n hn => abs_pmVaughanConvolutionFluctuationPrefix_le_linear hε a.1 a.2 hn)
      hevent
  exact ⟨K, hK, fun U V n hn => hbound (U, V) n hn⟩

/-- The actual convolution fluctuations have every logarithmic pronic norm saving uniformly. -/
theorem exists_uniform_pmVaughanConvolutionFluctuation_pronicNorm_log_rate
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (q : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ T : ℕ in atTop, ∀ U V : ℕ,
      pronicNorm (pmVaughanConvolutionFluctuationPrefix ε U V) T ≤
        B * Real.sqrt ((T : ℝ) ^ (1 - 2 * ε)) / Real.log (T : ℝ) ^ q := by
  obtain ⟨K, hK, hglobal⟩ := exists_uniform_pmVaughanConvolutionFluctuationPrefix_rpow_bound hε hε2.le
  have hlog (p : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n : ℕ in atTop, ∀ a : ℕ × ℕ,
      |pmVaughanConvolutionFluctuationPrefix ε a.1 a.2 n| ≤
        B * (n : ℝ) ^ (1 - ε) / Real.log (n : ℝ) ^ p := by
    obtain ⟨B, hB, h⟩ := exists_uniform_pmVaughanConvolutionFluctuation_prefix_log_rate hε hε2.le p
    exact ⟨B, hB, h.mono fun n hn a => hn a.1 a.2⟩
  obtain ⟨B, hB, h⟩ := exists_uniform_pronicNorm_log_rate_of_prefix_log_rate
    (f := fun a : ℕ × ℕ => pmVaughanConvolutionFluctuationPrefix ε a.1 a.2)
    hε hε2 hK (fun a n hn => hglobal a.1 a.2 n hn) hlog q
  exact ⟨B, hB, h.mono fun T hT U V => hT (U, V)⟩

/-- All truncated Möbius receivers have every logarithmic norm saving with one cutoff-independent bound. -/
theorem exists_uniform_patternPrefix_truncatedMoebius_pronicNorm_log_rate
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (q : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ T : ℕ in atTop, ∀ U : ℕ,
      pronicNorm (patternPrefix ε (Sieve.truncatedMoebius U)) T ≤
        B * Real.sqrt ((T : ℝ) ^ (1 - 2 * ε)) / Real.log (T : ℝ) ^ q := by
  have h1ε : 0 < 1 - ε := by linarith only [hε2]
  have hglobal (U n : ℕ) (hn : 1 ≤ n) :
      |patternPrefix ε (Sieve.truncatedMoebius U) n| ≤
        (1 + 1 / (1 - ε) + 1 / ε) * (n : ℝ) ^ (1 - ε) := by
    have hc : DampedClass 1 ε (dampedSignWeight (Sieve.truncatedMoebius U) ε) := by
      intro d
      rw [dampedSignWeight, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
      have hr : |Sieve.truncatedMoebius U d| ≤ 1 := by
        simpa only [Real.norm_eq_abs] using Sieve.norm_truncatedMoebius_le_one U d
      exact mul_le_mul_of_nonneg_right hr (Real.rpow_nonneg (Nat.cast_nonneg d) _)
    simpa only [one_mul, patternPrefix] using
      abs_weightCenteredPrefix_le_of_dampedClass hε (by linarith only [hε2]) hc hn
  exact exists_uniform_pronicNorm_log_rate_of_prefix_log_rate hε hε2
    (by positivity : 0 ≤ 1 + 1 / (1 - ε) + 1 / ε) hglobal
    (fun p => exists_uniform_patternPrefix_truncatedMoebius_log_rate hε hε2.le p) q

end GaloisForLFunctions.BezoutValuationIncidence
