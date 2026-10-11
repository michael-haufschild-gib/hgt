import GaloisForLFunctions.RHTower.WeilLogShiftCorrectionPlanCost
import GaloisForLFunctions.RHTower.WeilLogShiftEdgeCorrectionLimit

/-! Every optimal mixture transport plan has vanishing moving-part correction dispersion. -/

open Filter Topology

namespace RHTower

theorem finiteWeilMixtureCoupling_log_correction_dispersion_bounds (r k : ℕ)
    (a b : Set.Icc (0 : ℝ) 1) :
    0 ≤ finiteWeilCouplingCost (finiteWeilMixtureCoupling r k a b) (finiteWeilLogCorrectionDispersionCost r k) ∧
      finiteWeilCouplingCost (finiteWeilMixtureCoupling r k a b) (finiteWeilLogCorrectionDispersionCost r k) ≤
        finiteWeilCanonicalEdgeLogCorrectionSecondMoment r k := by
  rw [finiteWeilMixtureCoupling_log_correction_dispersion]
  have hm := finiteWeilCanonicalEdgeLogCorrectionSecondMoment_nonneg r k
  constructor
  · exact mul_nonneg (abs_nonneg _) hm
  · have hd : |(a : ℝ) - (b : ℝ)| ≤ 1 := by
      apply abs_le.mpr
      constructor
      · linarith only [a.property.1, b.property.2]
      · linarith only [a.property.2, b.property.1]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hd hm

theorem tendsto_finiteWeilMixtureCoupling_log_correction_dispersion_zero (t : ℕ → ℕ)
    (a b : ℕ → Set.Icc (0 : ℝ) 1) :
    Tendsto (fun r : ℕ => finiteWeilCouplingCost (finiteWeilMixtureCoupling r (2 * (r + 1) ^ 2 + t r) (a r) (b r))
      (finiteWeilLogCorrectionDispersionCost r (2 * (r + 1) ^ 2 + t r))) atTop (𝓝 (0 : ℝ)) := by
  exact squeeze_zero
    (fun r => (finiteWeilMixtureCoupling_log_correction_dispersion_bounds r _ (a r) (b r)).1)
    (fun r => (finiteWeilMixtureCoupling_log_correction_dispersion_bounds r _ (a r) (b r)).2)
    (tendsto_finiteWeilCanonicalEdgeLogCorrectionSecondMoment_zero t)

end RHTower
