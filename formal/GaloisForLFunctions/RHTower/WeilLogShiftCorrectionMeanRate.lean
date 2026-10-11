import GaloisForLFunctions.RHTower.WeilLogShiftMeanBiasBound
import GaloisForLFunctions.RHTower.WeilLogShiftTransportCorrection

/-! The mean transport correction converges at reciprocal order after controlling its index bias. -/

namespace RHTower

theorem finiteWeilCanonicalLogTransportCorrection_mean_rate (r k : ℕ)
    (hwidth : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    |finiteWeilCanonicalLogTransportCorrection r k - 1 / 2| ≤ 4 / ((r + 1 : ℕ) : ℝ) := by
  have hw : ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ) := by
    nlinarith only [hwidth, sq_nonneg (((r + 1 : ℕ) : ℝ))]
  have hc := finiteWeilCanonicalLogTransportCorrection_mean_bound r k hw
  have he := finiteWeilCanonicalEdgeIndexMean_normalized_bias_bound r k hwidth
  have hid : finiteWeilCanonicalLogTransportCorrection r k - 1 / 2 =
      (finiteWeilCanonicalLogTransportCorrection r k - finiteWeilCanonicalEdgeIndexMean r k / ((r + 1 : ℕ) : ℝ)) +
      (finiteWeilCanonicalEdgeIndexMean r k / ((r + 1 : ℕ) : ℝ) - 1 / 2) := by ring
  rw [hid]
  calc
    _ ≤ |finiteWeilCanonicalLogTransportCorrection r k - finiteWeilCanonicalEdgeIndexMean r k / ((r + 1 : ℕ) : ℝ)| +
        |finiteWeilCanonicalEdgeIndexMean r k / ((r + 1 : ℕ) : ℝ) - 1 / 2| := abs_add_le _ _
    _ ≤ 1 / ((r + 1 : ℕ) : ℝ) + 3 / ((r + 1 : ℕ) : ℝ) := add_le_add hc he
    _ = _ := by ring

theorem finiteWeilCanonicalLogTransportCorrection_quadratic_mean_rate (r t : ℕ) :
    |finiteWeilCanonicalLogTransportCorrection r (2 * (r + 1) ^ 2 + t) - 1 / 2| ≤
      4 / ((r + 1 : ℕ) : ℝ) := by
  apply finiteWeilCanonicalLogTransportCorrection_mean_rate
  push_cast
  have ht : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg _
  nlinarith only [ht]

end RHTower
