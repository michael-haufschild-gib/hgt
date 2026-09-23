import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePIdealCentroidVarianceCorrection
import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePTerminalCoefficientSourceEnvelope

/-!
# Exact arithmetic null form of the Route P/SP-E history variance

Equal-mass quantile cells tile one interval. Their normalized centroid
variance therefore has a closed mass-and-cubic-width formula, independent of
cell order. Subtracting it from the literal matched variance yields one exact
arithmetic cancellation among the square-root Chebyshev moment, `psi`, critical
mass, and the bounded matched-centroid geometry. No sign follows from this
finite identity alone.
-/

open scoped BigOperators Chebyshev
open ArithmeticFunction

namespace RHTower

private theorem routeP_quantile_coordinate_two :
    ccmActualHeadQuantilePolarCoordinate 2 = 2 := by
  rw [ccmActualHeadQuantilePolarCoordinate_eq_two_add_cumulative]
  have hzero : criticalMellinAtomWeight 0 = 0 := by
    simp [criticalMellinAtomWeight]
  have hone : criticalMellinAtomWeight 1 = 0 := by
    simp [criticalMellinAtomWeight]
  simp [ccmOutgoingPrimeCumulative, Finset.sum_range_succ, hzero, hone]

private theorem routeP_quantile_coordinate_terminal (K : ℕ) :
    ccmActualHeadQuantilePolarCoordinate (K + 3) =
      2 + ccmActualHeadParabolicMass K := by
  rw [ccmActualHeadQuantilePolarCoordinate_eq_two_add_cumulative]
  have hzero : criticalMellinAtomWeight 0 = 0 := by
    simp [criticalMellinAtomWeight]
  have hone : criticalMellinAtomWeight 1 = 0 := by
    simp [criticalMellinAtomWeight]
  unfold ccmOutgoingPrimeCumulative ccmActualHeadParabolicMass
  rw [centroid_sum_range_shift_two criticalMellinAtomWeight hzero hone K]

private theorem routeP_quantile_first_sum (K : ℕ) :
    (∑ n ∈ Finset.range (K + 1),
      criticalMellinAtomWeight (n + 2) *
        ccmActualHeadQuantilePolarCentroid (n + 2)) =
      ccmActualHeadParabolicMass K ^ (2 : ℕ) / 2 +
        2 * ccmActualHeadParabolicMass K := by
  rw [← ccmActualHeadQuantileParabolicAggregate_one_eq_mass_sq_div_two_add_two_mul_mass]
  unfold ccmActualHeadQuantileParabolicAggregate
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro n hn
  change criticalMellinAtomWeight (n + 2) *
      ((ccmActualHeadQuantilePolarCoordinate (n + 2) +
        ccmActualHeadQuantilePolarCoordinate (n + 3)) / 2) =
      (ccmActualHeadQuantilePolarCoordinate (n + 3) ^ (2 : ℕ) -
        ccmActualHeadQuantilePolarCoordinate (n + 2) ^ (2 : ℕ)) / 2
  rw [← ccmActualHeadQuantilePolarCoordinate_succ_sub_eq_atomWeight]
  ring

private theorem routeP_quantile_second_term (n : ℕ) :
    criticalMellinAtomWeight n *
        ccmActualHeadQuantilePolarCentroid n ^ (2 : ℕ) =
      (ccmActualHeadQuantilePolarCoordinate (n + 1) ^ (3 : ℕ) -
        ccmActualHeadQuantilePolarCoordinate n ^ (3 : ℕ)) / 3 -
        criticalMellinAtomWeight n ^ (3 : ℕ) / 12 := by
  unfold ccmActualHeadQuantilePolarCentroid
  rw [← ccmActualHeadQuantilePolarCoordinate_succ_sub_eq_atomWeight]
  ring

private theorem routeP_quantile_second_sum (K : ℕ) :
    (∑ n ∈ Finset.range (K + 1),
      criticalMellinAtomWeight (n + 2) *
        ccmActualHeadQuantilePolarCentroid (n + 2) ^ (2 : ℕ)) =
      ((2 + ccmActualHeadParabolicMass K) ^ (3 : ℕ) - 8) / 3 -
        routePWidthCubePrefix K / 3 := by
  simp_rw [routeP_quantile_second_term]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div]
  have htel := Finset.sum_range_sub
    (fun n : ℕ => ccmActualHeadQuantilePolarCoordinate (n + 2) ^ (3 : ℕ)) (K + 1)
  rw [htel, routeP_quantile_coordinate_terminal,
    routeP_quantile_coordinate_two]
  unfold routePWidthCubePrefix
  rw [← Finset.sum_div]
  ring

theorem routeP_quantile_normalized_variance_closed (K : ℕ) :
    ccmActualHeadParabolicNormalizedCentroidVariance K
        ccmActualHeadQuantilePolarCentroid =
      ccmActualHeadParabolicMass K ^ (3 : ℕ) / 12 -
        routePWidthCubePrefix K / 3 := by
  have hm : ccmActualHeadParabolicMass K ≠ 0 :=
    (ccmActualHeadParabolicMass_pos K).ne'
  unfold ccmActualHeadParabolicNormalizedCentroidVariance
    ccmActualHeadParabolicCentroidVariance
  rw [routeP_quantile_first_sum, routeP_quantile_second_sum]
  field_simp
  ring

noncomputable def routePSqrtChebyshevMoment (K : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (K + 1),
    ArithmeticFunction.vonMangoldt (n + 2) * Real.sqrt ((n + 2 : ℕ) : ℝ)

theorem routeP_normalized_history_eq_arithmetic_null (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect K =
      4 * routePSqrtChebyshevMoment K +
        4 * routePWidthCubePrefix K / 3 -
        (2 * Chebyshev.psi ((K + 2 : ℕ) : ℝ) +
          ccmActualHeadMatchedCentroidChebyshevExcess K) ^ (2 : ℕ) /
          ccmActualHeadParabolicMass K -
        ccmActualHeadParabolicMass K ^ (3 : ℕ) / 12 := by
  let m := ccmActualHeadParabolicMass K
  let p := Chebyshev.psi ((K + 2 : ℕ) : ℝ)
  let e := ccmActualHeadMatchedCentroidChebyshevExcess K
  let q := routePWidthCubePrefix K
  let A := routePSqrtChebyshevMoment K
  have hm : m ≠ 0 := (ccmActualHeadParabolicMass_pos K).ne'
  have hfirst :
      (∑ n ∈ Finset.range (K + 1),
        criticalMellinAtomWeight (n + 2) * routePIdealCentroid (n + 2)) =
        2 * p := by
    unfold p
    rw [← centroidAtomExcess_vonMangoldt_shift_two K, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [← centroidAtomExcess_weight_mul_sqrt (show 0 < n + 2 by omega)]
    unfold routePIdealCentroid
    ring
  have hsecond :
      (∑ n ∈ Finset.range (K + 1),
        criticalMellinAtomWeight (n + 2) * routePIdealCentroid (n + 2) ^ (2 : ℕ)) =
        4 * A := by
    unfold A routePSqrtChebyshevMoment
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [← centroidAtomExcess_weight_mul_sqrt (show 0 < n + 2 by omega)]
    unfold routePIdealCentroid
    ring
  have hideal :
      ccmActualHeadParabolicNormalizedCentroidVariance K routePIdealCentroid =
        4 * A - (2 * p) ^ (2 : ℕ) / m := by
    unfold ccmActualHeadParabolicNormalizedCentroidVariance
      ccmActualHeadParabolicCentroidVariance
    rw [hfirst, hsecond]
    change (m * (4 * A) - (2 * p) ^ (2 : ℕ)) / m =
      4 * A - (2 * p) ^ (2 : ℕ) / m
    field_simp [hm]
  unfold ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect
  calc
    ccmActualHeadParabolicNormalizedCentroidVariance K ccmActualHeadMatchedPolarCentroid -
        ccmActualHeadParabolicNormalizedCentroidVariance K ccmActualHeadQuantilePolarCentroid =
      (ccmActualHeadParabolicNormalizedCentroidVariance K ccmActualHeadMatchedPolarCentroid -
        ccmActualHeadParabolicNormalizedCentroidVariance K routePIdealCentroid) +
      (ccmActualHeadParabolicNormalizedCentroidVariance K routePIdealCentroid -
        ccmActualHeadParabolicNormalizedCentroidVariance K ccmActualHeadQuantilePolarCentroid) := by ring
    _ = (q - (4 * p * e + e ^ (2 : ℕ)) / m) +
        ((4 * A - (2 * p) ^ (2 : ℕ) / m) - (m ^ (3 : ℕ) / 12 - q / 3)) := by
      rw [routeP_matched_variance_correction, hideal,
        routeP_quantile_normalized_variance_closed]
    _ = 4 * A + 4 * q / 3 - (2 * p + e) ^ (2 : ℕ) / m -
        m ^ (3 : ℕ) / 12 := by
      field_simp
      ring

end RHTower
