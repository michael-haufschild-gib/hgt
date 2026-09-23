import GaloisForLFunctions.RHTower.EulerDeletionSignedResidueCovariance
import GaloisForLFunctions.RHTower.EulerDeletionPeriodAveragingObstruction

/-!
# Weighted EDQ energy separates from uniform-period variance

The exact chronological Euler-deletion covariance is asymptotically negligible
relative to the unweighted complete-period variance.  Thus a proof of the EDQ
polylogarithmic ceiling cannot replace physical fibre weights by a uniform clock
average: the latter retains an isolated-prime component at a strictly larger scale.
-/

noncomputable section

open Filter Topology

namespace RHTower.DeletionSignedResidueCovariance

private theorem energy_nonneg (N : ℕ) : 0 ≤ energy N := by
  unfold energy
  apply Finset.sum_nonneg
  intro r hr
  exact mul_nonneg
    (DeletionResidueMartingale.historyFibre_mass_pos N r (Finset.mem_range.mp hr)).le
    (sq_nonneg _)

private theorem uniformPeriodVariance_tendsto_atTop :
    Tendsto (fun N : ℕ => DeletionPeriodGrowth.variance N) atTop atTop := by
  simpa using DeletionPeriodGrowth.variance_div_log_pow_tendsto 0

/-- The physical signed EDQ covariance is negligible compared with the unweighted complete-clock
variance.  Uniform period averaging therefore loses the cancellation that the remaining EDQ
cofinal bound must exploit. -/
theorem energy_div_uniformPeriodVariance_tendsto_zero :
    Tendsto (fun N : ℕ => energy N / DeletionPeriodGrowth.variance N) atTop (𝓝 0) := by
  have hsource := DeletionPeriodGrowth.modular_norm_sq_div_variance_tendsto_zero
  have hconst : Tendsto (fun N : ℕ => (4 : ℝ) / DeletionPeriodGrowth.variance N)
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop uniformPeriodVariance_tendsto_atTop
  have hupper : Tendsto (fun N : ℕ =>
      2 * (‖bdMobiusModularApproximantVec N‖ ^ (2 : ℕ) /
        DeletionPeriodGrowth.variance N) + 4 / DeletionPeriodGrowth.variance N)
      atTop (𝓝 0) :=
    by simpa using (hsource.const_mul 2).add hconst
  apply squeeze_zero' _ _ hupper
  · exact Eventually.of_forall fun N =>
      div_nonneg (energy_nonneg N) (by
        calc
          0 ≤ ((DeletionPeriodGrowth.upperPrimes N).card : ℝ) / 16 := by positivity
          _ ≤ DeletionPeriodGrowth.variance N :=
            DeletionPeriodGrowth.upperPrime_card_le_variance N)
  · filter_upwards [uniformPeriodVariance_tendsto_atTop.eventually_gt_atTop 0] with N hN
    have henergy := energy_le_two_modular_norm_sq_add_four N
    have hdiv := (div_le_div_iff_of_pos_right hN).mpr henergy
    rw [add_div] at hdiv
    calc
      energy N / DeletionPeriodGrowth.variance N ≤
          (2 * ‖bdMobiusModularApproximantVec N‖ ^ (2 : ℕ)) /
            DeletionPeriodGrowth.variance N + 4 / DeletionPeriodGrowth.variance N := hdiv
      _ = 2 * (‖bdMobiusModularApproximantVec N‖ ^ (2 : ℕ) /
            DeletionPeriodGrowth.variance N) + 4 / DeletionPeriodGrowth.variance N := by ring

end RHTower.DeletionSignedResidueCovariance
