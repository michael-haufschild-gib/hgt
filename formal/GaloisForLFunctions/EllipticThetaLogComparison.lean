import GaloisForLFunctions.EllipticThetaLogGlobalMeromorphic
import GaloisForLFunctions.JacobiThetaParallelogramCharge
import GaloisForLFunctions.MeromorphicNormalizedRemovable

/-!
# Constraint comparison with analytic Jacobi theta

The constructed theta-product logarithmic kernel and mathlib's analytic Jacobi-theta logarithmic
derivative obey the same additive constraints. Their difference is therefore periodic in both
`1` and `τ` on the common regular locus. The remaining comparison theorem is reduced to a divisor
statement: once this discrepancy is shown to have no poles, compact ellipticity makes it constant,
and every translated defect agrees without any normalization constant.
-/

open Complex Filter Topology

namespace GaloisForLFunctions

noncomputable section

/-- Discrepancy between the constructed product boundary and the analytic theta logarithmic
derivative in the aligned additive coordinate. -/
def ellipticThetaLogComparison (τ z : ℂ) : ℂ :=
  ellipticThetaAdditiveLogKernel τ z - thetaLogDeriv z τ

/-- The constructed-versus-analytic discrepancy is globally meromorphic. -/
theorem meromorphicOn_ellipticThetaLogComparison {τ : ℂ} (hτ : 0 < τ.im) :
    MeromorphicOn (ellipticThetaLogComparison τ) Set.univ := by
  intro z _
  have hconstructed := meromorphicOn_ellipticThetaAdditiveLogKernel hτ z (Set.mem_univ z)
  have hanalytic : MeromorphicAt (thetaLogDeriv · τ) z := by
    exact ((jacobiTheta₂'_analyticOnNhd_fst τ hτ) z (Set.mem_univ z)).meromorphicAt.div
      ((jacobiTheta₂_analyticOnNhd_fst τ hτ) z (Set.mem_univ z)).meromorphicAt
  exact hconstructed.sub hanalytic

/-- The comparison discrepancy is period-one. -/
theorem ellipticThetaLogComparison_add_one (τ z : ℂ) :
    ellipticThetaLogComparison τ (z + 1) = ellipticThetaLogComparison τ z := by
  rw [ellipticThetaLogComparison, ellipticThetaLogComparison,
    ellipticThetaAdditiveLogKernel_add_one, thetaLogDeriv_add_one]

/-- On the common regular locus, the two identical quasiperiod increments cancel, so the
comparison discrepancy is `τ`-periodic. -/
theorem ellipticThetaLogComparison_add_tau
    {τ z : ℂ} (hτ : 0 < τ.im) (hcoord : ellipticThetaCoordinate τ z ≠ 1)
    (htheta : jacobiTheta₂ z τ ≠ 0) :
    ellipticThetaLogComparison τ (z + τ) = ellipticThetaLogComparison τ z := by
  have hconstructed := ellipticThetaAdditiveLogKernel_add_tau_sub hτ hcoord
  have hanalytic := thetaLogDeriv_add_tau htheta
  rw [ellipticThetaLogComparison, ellipticThetaLogComparison, hanalytic]
  linear_combination hconstructed

/-- The constructed and analytic theta logarithmic kernels have the same normalized principal
part at the odd half-period; their comparison discrepancy has vanishing residue there. -/
theorem tendsto_ellipticThetaLogComparison_normalized_halfPeriod
    {τ : ℂ} (hτ : 0 < τ.im) :
    Tendsto
      (fun z : ℂ => (z - thetaHalfPeriod τ) * ellipticThetaLogComparison τ z)
      (𝓝[≠] thetaHalfPeriod τ) (𝓝 0) := by
  have hconstructed := tendsto_ellipticThetaAdditiveLogKernel_normalized_halfPeriod hτ
  have hanalytic : Tendsto
      (fun z : ℂ => (z - thetaHalfPeriod τ) * thetaLogDeriv z τ)
      (𝓝[≠] thetaHalfPeriod τ) (𝓝 1) := by
    simpa [thetaLogDeriv] using tendsto_thetaLogDeriv_normalized_halfPeriod hτ
  simpa [ellipticThetaLogComparison, mul_sub] using hconstructed.sub hanalytic

/-- The comparison discrepancy has no pole at the distinguished odd half-period. -/
theorem meromorphicOrderAt_ellipticThetaLogComparison_halfPeriod_nonneg
    {τ : ℂ} (hτ : 0 < τ.im) :
    0 ≤ meromorphicOrderAt (ellipticThetaLogComparison τ) (thetaHalfPeriod τ) := by
  apply meromorphicOrderAt_nonneg_of_tendsto_mul_sub_zero
  · exact meromorphicOn_ellipticThetaLogComparison hτ _ (Set.mem_univ _)
  · exact tendsto_ellipticThetaLogComparison_normalized_halfPeriod hτ

end

end GaloisForLFunctions
