import GaloisForLFunctions.RHTower.WeilLogShiftTransportCorrection
import GaloisForLFunctions.RHTower.WeilLogShiftEdgeBinomialLimit

/-! The first normalized correction to logarithmic transport tends to one half. -/

open Filter Topology

namespace RHTower

theorem finiteWeilCanonicalLogTransportCorrection_quadratic_bound (r t : ℕ) :
    |finiteWeilCanonicalLogTransportCorrection r (2 * (r + 1) ^ 2 + t) - 1 / 2| ≤
      4 * (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ)) := by
  have hc := finiteWeilCanonicalLogTransportCorrection_quadratic_mean_bound r t
  have he := finiteWeilCanonicalEdgeIndexMean_quadratic_bound r t
  have hn : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by positivity
  have hn1 : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ r + 1 by omega)
  have hS : (1 : ℝ) ≤ 2 * Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) := by
    have hs0 := Real.sqrt_nonneg ((((r + 1 : ℕ) : ℝ) + 1) / 2)
    have hs2 := Real.sq_sqrt (show 0 ≤ (((r + 1 : ℕ) : ℝ) + 1) / 2 by positivity)
    nlinarith only [hs0, hs2, hn1]
  have hsmall : 1 / ((r + 1 : ℕ) : ℝ) ≤
      2 * (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ)) := by
    calc
      _ ≤ (2 * Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2)) / ((r + 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hS hn.le
      _ = _ := by ring
  have ht := abs_add_le
    (finiteWeilCanonicalLogTransportCorrection r (2 * (r + 1) ^ 2 + t) -
      finiteWeilCanonicalEdgeIndexMean r (2 * (r + 1) ^ 2 + t) / ((r + 1 : ℕ) : ℝ))
    (finiteWeilCanonicalEdgeIndexMean r (2 * (r + 1) ^ 2 + t) / ((r + 1 : ℕ) : ℝ) - 1 / 2)
  have hid : (finiteWeilCanonicalLogTransportCorrection r (2 * (r + 1) ^ 2 + t) -
      finiteWeilCanonicalEdgeIndexMean r (2 * (r + 1) ^ 2 + t) / ((r + 1 : ℕ) : ℝ)) +
      (finiteWeilCanonicalEdgeIndexMean r (2 * (r + 1) ^ 2 + t) / ((r + 1 : ℕ) : ℝ) - 1 / 2) =
      finiteWeilCanonicalLogTransportCorrection r (2 * (r + 1) ^ 2 + t) - 1 / 2 := by ring
  rw [hid] at ht
  linarith only [ht, hc, he, hsmall]

theorem tendsto_finiteWeilCanonicalLogTransportCorrection_half (t : ℕ → ℕ) :
    Tendsto (fun r : ℕ => finiteWeilCanonicalLogTransportCorrection r (2 * (r + 1) ^ 2 + t r))
      atTop (𝓝 ((1 : ℝ) / 2)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply squeeze_zero (fun r => abs_nonneg _)
    (fun r => finiteWeilCanonicalLogTransportCorrection_quadratic_bound r (t r))
  have h := tendsto_finiteWeil_midpoint_binomial_error.const_mul (2 : ℝ)
  simpa only [mul_zero, ← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num] using h

end RHTower
