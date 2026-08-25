import GaloisForLFunctions.RHTower.PolynomialFockFiniteTangentCellGrouping
import GaloisForLFunctions.RHTower.CriticalPrimeSamplingQuadraticForm

open MeasureTheory Set Filter Topology Metric
open scoped InnerProductSpace ComplexConjugate

namespace RHTower

noncomputable section

open ContinuousLinearMap

theorem sum_rpow_finiteTailCriticalPrimeResponse_svVec_le_cellMassTsum
    {m q : ℝ} (hm : 4 < m) (hq : criticalPrimeFockSchattenThreshold m < q)
    (T : Finset Nat.Primes)
    (hT : ∀ p ∈ T, 2 ≤ Real.log (p : ℝ))
    (S : Finset ℕ) :
    (∑ j ∈ S, (∑ p ∈ T, ‖criticalPrimeKernelRestriction
      (criticalPrimeMomentFockKernel (polynomialMomentFockData m (by linarith))) p
      (svVec (energyOp (polynomialCriticalPrimeSamplingIncidence m (by linarith))) j)‖ ^ 2) ^ q) ≤
      Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) ^ q *
        (Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) *
          3 ^ (m / 2 - 1)) *
        ∑' n : ℕ, criticalPrimeFockScaledAdaptedCellMass m
          (criticalPrimeFockOverlapCellScale m) n ^ q := by
  classical
  have hm4 : 4 ≤ m := hm.le
  have hm2 : 2 ≤ m := by linarith
  have hq1 : 1 < q := lt_trans (criticalPrimeFockSchattenThreshold_gt_one hm) hq
  have hq0 : 0 < q := by linarith
  let Op : MomentFock →L[ℂ] MomentFock :=
    polynomialCriticalPrimeSamplingIncidence m hm4
  let e : ℕ → MomentFock := fun j => svVec (energyOp Op) j
  let W : ℂ → ℝ := finiteCriticalPrimeTangentBallMass m T
  let U : Set ℂ := finiteCriticalPrimeTangentClosedBallUnion m T
  let D : ℕ → ℂ → ℝ := fun j =>
    polynomialMomentFockWeightedNormSq m hm2 (e j)
  let K : ℂ → ℝ := polynomialMomentFockKernelDiagonalDensity m hm2
  let B : ℝ := ∑ p ∈ T, criticalPrimeSamplingWeight p
  let Ce : ℝ := Real.exp (2 * (polynomialFockLocalBregmanConstant m / m))
  let Ct : ℝ := Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) *
    3 ^ (m / 2 - 1)
  have hcpt : IsCompactOperator Op :=
    polynomialCriticalPrimeSamplingIncidence_isCompactOperator hm
  have hnorm : ∀ j, ‖e j‖ ≤ 1 := by
    intro j
    by_cases hj : svVal (energyOp Op) j = 0
    · rw [show e j = 0 by exact svVec_eq_zero_of_svVal_eq_zero _ hj]
      simp
    · rw [show ‖e j‖ = 1 by
        exact norm_svVec_of_ne_zero (energyOp_compact hcpt)
          (energyOp_symmetric Op) (energyOp_pos Op) hj]
  have hJ : ∀ j, (∑ p ∈ T, ‖criticalPrimeKernelRestriction
      (criticalPrimeMomentFockKernel (polynomialMomentFockData m hm2)) p (e j)‖ ^ 2) ^ q ≤
      Ce ^ q * ∫ z in U, W z ^ q * D j z := by
    intro j
    simpa only [e, W, U, D, Ce] using
      sum_normSq_criticalPrimeKernelRestriction_rpow_le_weightedOverlapIntegral
        hm4 hq1 (e j) (hnorm j) T
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun p _ =>
    (criticalPrimeSamplingWeight_pos p).le
  have hW0 : ∀ z, 0 ≤ W z := finiteCriticalPrimeTangentBallMass_nonneg m T
  have hWle : ∀ z, W z ≤ B := finiteCriticalPrimeTangentBallMass_le_sum_weight m T
  have hprodint : ∀ j ∈ S, Integrable (fun z => W z ^ q * D j z)
      (volume.restrict U) := by
    intro j hj
    have hDint : Integrable (D j) :=
      integrable_polynomialMomentFockWeightedNormSq m hm2 (e j)
    have hright : Integrable (fun z => B ^ q * D j z) (volume.restrict U) :=
      (hDint.const_mul (B ^ q)).integrableOn
    apply hright.mono'
      (((Real.continuous_rpow_const hq0.le).measurable.comp
        (measurable_finiteCriticalPrimeTangentBallMass m T)).mul
        (continuous_polynomialMomentFockWeightedNormSq m hm2 (e j)).measurable).aestronglyMeasurable
    filter_upwards with z
    change ‖W z ^ q * D j z‖ ≤ B ^ q * D j z
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (hW0 z) _)
      (polynomialMomentFockWeightedNormSq_nonneg m hm2 (e j) z))]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (hW0 z) (hWle z) hq0.le)
      (polynomialMomentFockWeightedNormSq_nonneg m hm2 (e j) z)
  have hsumint : Integrable (fun z => ∑ j ∈ S, W z ^ q * D j z)
      (volume.restrict U) := integrable_finsetSum S hprodint
  have hKint : Integrable (fun z => W z ^ q * K z) (volume.restrict U) := by
    change IntegrableOn (fun z => W z ^ q * K z) U
    simpa only [W, K, U] using
      integrableOn_rpow_finiteCriticalPrimeTangentBallMass_mul_kernelDiagonalDensity
        hm4 hq1 T hT
  have hpoint : ∀ z, (∑ j ∈ S, W z ^ q * D j z) ≤ W z ^ q * K z := by
    intro z
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left
      (sum_polynomialMomentFockWeightedNormSq_svVec_le_kernelDiagonalDensity
        hm2 hm4 hm S z) (Real.rpow_nonneg (hW0 z) _)
  have hintegral :
      (∑ j ∈ S, ∫ z in U, W z ^ q * D j z) ≤
        ∫ z in U, W z ^ q * K z := by
    rw [← MeasureTheory.integral_finsetSum S hprodint]
    exact integral_mono_ae hsumint hKint (Filter.Eventually.of_forall hpoint)
  have hcells : Summable fun n : ℕ =>
      criticalPrimeFockScaledAdaptedCellMass m
        (criticalPrimeFockOverlapCellScale m) n ^ q :=
    (summable_rpow_criticalPrimeFockScaledAdaptedCellMass_iff_of_pos
      hm (criticalPrimeFockOverlapCellScale_pos m) hq0).2 hq
  calc
    (∑ j ∈ S, (∑ p ∈ T, ‖criticalPrimeKernelRestriction
      (criticalPrimeMomentFockKernel (polynomialMomentFockData m hm2)) p (e j)‖ ^ 2) ^ q) ≤
        ∑ j ∈ S, Ce ^ q * ∫ z in U, W z ^ q * D j z :=
      Finset.sum_le_sum fun j _ => hJ j
    _ = Ce ^ q * ∑ j ∈ S, ∫ z in U, W z ^ q * D j z := by
      rw [Finset.mul_sum]
    _ ≤ Ce ^ q * ∫ z in U, W z ^ q * K z :=
      mul_le_mul_of_nonneg_left hintegral (Real.rpow_nonneg (Real.exp_nonneg _) _)
    _ ≤ Ce ^ q * (Ct * ∑ p ∈ T, criticalPrimeSamplingWeight p *
        criticalPrimeFockScaledAdaptedCellMass m
          (criticalPrimeFockOverlapCellScale m)
          (criticalPrimeFockAdaptedCellIndex m (Real.log (p : ℝ))) ^ (q - 1)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Real.exp_nonneg _) _)
      exact integral_rpow_finiteCriticalPrimeTangentBallMass_mul_kernelDiagonalDensity_le
        hm4 hq1 T hT
    _ ≤ Ce ^ q * (Ct * ∑' n : ℕ,
        criticalPrimeFockScaledAdaptedCellMass m
          (criticalPrimeFockOverlapCellScale m) n ^ q) := by
      gcongr
      exact sum_weight_mul_scaledCellMass_rpow_sub_one_le_tsum_rpow_scaledCellMass
        hm4 hq1 T hT hcells
    _ = _ := by
      dsimp [Ce, Ct]
      ring

end

end RHTower
