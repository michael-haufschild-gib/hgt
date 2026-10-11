import GaloisForLFunctions.RHTower.WeilLogShiftEdgeCorrectionMoment
import GaloisForLFunctions.RHTower.WeilLogShiftMidpointBinomialLimit

/-! The edgewise log correction converges in mean square and at every fixed tail precision. -/

open Filter Topology
open scoped BigOperators

noncomputable section
namespace RHTower

theorem tendsto_finiteWeilCanonicalEdgeLogCorrectionSecondMoment_zero (t : ℕ → ℕ) :
    Tendsto (fun r : ℕ => finiteWeilCanonicalEdgeLogCorrectionSecondMoment r (2 * (r + 1) ^ 2 + t r))
      atTop (𝓝 (0 : ℝ)) := by
  apply squeeze_zero (fun r => finiteWeilCanonicalEdgeLogCorrectionSecondMoment_nonneg r _)
    (fun r => finiteWeilCanonicalEdgeLogCorrectionSecondMoment_quadratic_bound r (t r))
  have h := tendsto_finiteWeil_midpoint_binomial_error.const_mul (4 : ℝ)
  simpa only [mul_zero, ← mul_assoc, show (4 : ℝ) * 2 = 8 by norm_num] using h

def finiteWeilCanonicalEdgeLogCorrectionTailMass (r k q : ℕ) : ℝ :=
  ∑ i : Fin (r + 1), if 1 / ((q + 1 : ℕ) : ℝ) ≤ |finiteWeilCanonicalEdgeLogCorrection r k i - 1 / 2|
    then finiteWeilCanonicalEdgeMass r k i else 0

theorem finiteWeilCanonicalEdgeLogCorrectionTailMass_nonneg (r k q : ℕ) :
    0 ≤ finiteWeilCanonicalEdgeLogCorrectionTailMass r k q := by
  apply Finset.sum_nonneg
  intro i hi
  split_ifs
  · exact (finiteWeilCanonicalEdgeMass_pos r k i).le
  · exact le_rfl

theorem finiteWeilCanonicalEdgeLogCorrectionTailMass_bound (r k q : ℕ) :
    finiteWeilCanonicalEdgeLogCorrectionTailMass r k q ≤
      ((q + 1 : ℕ) : ℝ) ^ 2 * finiteWeilCanonicalEdgeLogCorrectionSecondMoment r k := by
  unfold finiteWeilCanonicalEdgeLogCorrectionTailMass finiteWeilCanonicalEdgeLogCorrectionSecondMoment
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hm := (finiteWeilCanonicalEdgeMass_pos r k i).le
  split_ifs with h
  · have hn : (0 : ℝ) < ((q + 1 : ℕ) : ℝ) := by positivity
    have h1 : 1 ≤ ((q + 1 : ℕ) : ℝ) * |finiteWeilCanonicalEdgeLogCorrection r k i - 1 / 2| := by
      have hh := (div_le_iff₀ hn).mp h
      nlinarith only [hh]
    have hs : 1 ≤ (((q + 1 : ℕ) : ℝ) * |finiteWeilCanonicalEdgeLogCorrection r k i - 1 / 2|) ^ 2 := by
      nlinarith only [h1, sq_nonneg (((q + 1 : ℕ) : ℝ) *
        |finiteWeilCanonicalEdgeLogCorrection r k i - 1 / 2| - 1)]
    rw [mul_pow, sq_abs] at hs
    calc
      _ = finiteWeilCanonicalEdgeMass r k i * 1 := by ring
      _ ≤ finiteWeilCanonicalEdgeMass r k i * (((q + 1 : ℕ) : ℝ) ^ 2 *
          (finiteWeilCanonicalEdgeLogCorrection r k i - 1 / 2) ^ 2) :=
        mul_le_mul_of_nonneg_left hs hm
      _ = _ := by ring
  · positivity

theorem tendsto_finiteWeilCanonicalEdgeLogCorrectionTailMass_zero (t : ℕ → ℕ) (q : ℕ) :
    Tendsto (fun r : ℕ => finiteWeilCanonicalEdgeLogCorrectionTailMass r (2 * (r + 1) ^ 2 + t r) q)
      atTop (𝓝 (0 : ℝ)) := by
  apply squeeze_zero (fun r => finiteWeilCanonicalEdgeLogCorrectionTailMass_nonneg r _ q)
    (fun r => finiteWeilCanonicalEdgeLogCorrectionTailMass_bound r _ q)
  simpa only [mul_zero] using
    (tendsto_finiteWeilCanonicalEdgeLogCorrectionSecondMoment_zero t).const_mul (((q + 1 : ℕ) : ℝ) ^ 2)

end RHTower
