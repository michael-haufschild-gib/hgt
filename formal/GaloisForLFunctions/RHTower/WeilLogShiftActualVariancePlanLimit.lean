import GaloisForLFunctions.RHTower.WeilLogShiftActualVarianceLimit
import GaloisForLFunctions.RHTower.WeilLogShiftCorrectionTestCost

/-! Optimal mixture plans inherit the actual-mean moving-part variance constant. -/

open Filter Topology

noncomputable section
namespace RHTower

def finiteWeilLogCorrectionVarianceCost (r k : ℕ) : Fin (r + 2) → Fin (r + 2) → ℝ :=
  finiteWeilLogCorrectionTestCost r k (fun x => (x - finiteWeilCanonicalLogTransportCorrection r k) ^ 2)

theorem finiteWeilMixtureCoupling_log_correction_variance (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1) :
    finiteWeilCouplingCost (finiteWeilMixtureCoupling r k a b) (finiteWeilLogCorrectionVarianceCost r k) =
      |(a : ℝ) - (b : ℝ)| * finiteWeilCanonicalEdgeLogCorrectionVariance r k := by
  exact finiteWeilMixtureCoupling_log_correction_test r k a b _

theorem finiteWeilMixtureCoupling_log_correction_variance_quadratic_bound (r t : ℕ)
    (a b : Set.Icc (0 : ℝ) 1) :
    |((r + 1 : ℕ) : ℝ) * finiteWeilCouplingCost (finiteWeilMixtureCoupling r (2 * (r + 1) ^ 2 + t) a b)
      (finiteWeilLogCorrectionVarianceCost r (2 * (r + 1) ^ 2 + t)) - |(a : ℝ) - (b : ℝ)| / 4| ≤
        38 * (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ)) := by
  have hd : |(a : ℝ) - (b : ℝ)| ≤ 1 := by
    apply abs_le.mpr
    exact ⟨by linarith only [a.property.1, b.property.2], by linarith only [a.property.2, b.property.1]⟩
  rw [finiteWeilMixtureCoupling_log_correction_variance]
  have hid : ((r + 1 : ℕ) : ℝ) * (|(a : ℝ) - (b : ℝ)| *
      finiteWeilCanonicalEdgeLogCorrectionVariance r (2 * (r + 1) ^ 2 + t)) - |(a : ℝ) - (b : ℝ)| / 4 =
      |(a : ℝ) - (b : ℝ)| * (((r + 1 : ℕ) : ℝ) *
        finiteWeilCanonicalEdgeLogCorrectionVariance r (2 * (r + 1) ^ 2 + t) - 1 / 4) := by ring
  rw [hid, abs_mul, abs_abs]
  calc
    _ ≤ |(a : ℝ) - (b : ℝ)| *
        (38 * (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left (finiteWeilCanonicalEdgeLogCorrectionVariance_quadratic_bound r t) (abs_nonneg _)
    _ ≤ 1 * (38 * (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_right hd (by positivity)
    _ = _ := one_mul _

theorem tendsto_finiteWeilMixtureCoupling_log_correction_variance_error_zero (t : ℕ → ℕ)
    (a b : ℕ → Set.Icc (0 : ℝ) 1) :
    Tendsto (fun r : ℕ => ((r + 1 : ℕ) : ℝ) *
      finiteWeilCouplingCost (finiteWeilMixtureCoupling r (2 * (r + 1) ^ 2 + t r) (a r) (b r))
        (finiteWeilLogCorrectionVarianceCost r (2 * (r + 1) ^ 2 + t r)) - |(a r : ℝ) - (b r : ℝ)| / 4)
      atTop (𝓝 (0 : ℝ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero, Real.norm_eq_abs]
  apply squeeze_zero (fun r => abs_nonneg _)
    (fun r => finiteWeilMixtureCoupling_log_correction_variance_quadratic_bound r (t r) (a r) (b r))
  have h := tendsto_finiteWeil_midpoint_binomial_error.const_mul (19 : ℝ)
  simpa only [mul_zero, ← mul_assoc, show (19 : ℝ) * 2 = 38 by norm_num] using h

end RHTower
