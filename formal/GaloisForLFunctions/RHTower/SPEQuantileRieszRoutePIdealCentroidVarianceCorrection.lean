import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePTerminalCentroidExcessSummability
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantileParabolicNormalizedVarianceFlow

/-!
# Exact matched-to-ideal centroid variance correction

Even though each literal matched-centroid excess is summable, barycentric
recentering amplifies its contribution to the mass-normalized variance.
This is a finite source-faithful identity; no asymptotic sign is inferred here.
-/

open scoped BigOperators Chebyshev
open ArithmeticFunction

namespace RHTower

noncomputable def routePIdealCentroid (n : ℕ) : ℝ := 2 * Real.sqrt (n : ℝ)

noncomputable def routePWidthCubePrefix (K : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (K + 1), criticalMellinAtomWeight (n + 2) ^ (3 : ℕ) / 4

theorem routeP_matched_variance_correction (K : ℕ) :
    ccmActualHeadParabolicNormalizedCentroidVariance K ccmActualHeadMatchedPolarCentroid -
      ccmActualHeadParabolicNormalizedCentroidVariance K routePIdealCentroid =
        routePWidthCubePrefix K -
          (4 * Chebyshev.psi ((K + 2 : ℕ) : ℝ) *
              ccmActualHeadMatchedCentroidChebyshevExcess K +
            ccmActualHeadMatchedCentroidChebyshevExcess K ^ (2 : ℕ)) /
            ccmActualHeadParabolicMass K := by
  let m := ccmActualHeadParabolicMass K
  let p := Chebyshev.psi ((K + 2 : ℕ) : ℝ)
  let e := ccmActualHeadMatchedCentroidChebyshevExcess K
  let q := routePWidthCubePrefix K
  have hm : m ≠ 0 := (ccmActualHeadParabolicMass_pos K).ne'
  have h1 :
      (∑ n ∈ Finset.range (K + 1),
        criticalMellinAtomWeight (n + 2) *
          ccmActualHeadMatchedPolarCentroid (n + 2)) = 2 * p + e := by
    unfold e ccmActualHeadMatchedCentroidChebyshevExcess p
    ring
  have h2 :
      (∑ n ∈ Finset.range (K + 1),
        criticalMellinAtomWeight (n + 2) *
          routePIdealCentroid (n + 2)) = 2 * p := by
    unfold p
    rw [← centroidAtomExcess_vonMangoldt_shift_two K, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [← centroidAtomExcess_weight_mul_sqrt (show 0 < n + 2 by omega)]
    unfold routePIdealCentroid
    ring
  have h3 :
      (∑ n ∈ Finset.range (K + 1),
        criticalMellinAtomWeight (n + 2) *
          ccmActualHeadMatchedPolarCentroid (n + 2) ^ (2 : ℕ)) -
        (∑ n ∈ Finset.range (K + 1),
          criticalMellinAtomWeight (n + 2) *
            routePIdealCentroid (n + 2) ^ (2 : ℕ)) = q := by
    rw [← Finset.sum_sub_distrib]
    unfold q routePWidthCubePrefix
    apply Finset.sum_congr rfl
    intro n hn
    have hs := ccmActualHeadMatchedPolarCentroid_sq (n + 2)
      (show 0 < n + 2 by omega)
    have hr : Real.sqrt ((n + 2 : ℕ) : ℝ) ^ (2 : ℕ) = ((n + 2 : ℕ) : ℝ) :=
      Real.sq_sqrt (by positivity)
    unfold routePIdealCentroid
    calc
      criticalMellinAtomWeight (n + 2) *
          ccmActualHeadMatchedPolarCentroid (n + 2) ^ (2 : ℕ) -
          criticalMellinAtomWeight (n + 2) *
            (2 * Real.sqrt ((n + 2 : ℕ) : ℝ)) ^ (2 : ℕ) =
        criticalMellinAtomWeight (n + 2) *
          (ccmActualHeadMatchedPolarCentroid (n + 2) ^ (2 : ℕ) -
            (2 * Real.sqrt ((n + 2 : ℕ) : ℝ)) ^ (2 : ℕ)) := by ring
      _ = criticalMellinAtomWeight (n + 2) ^ (3 : ℕ) / 4 := by
        have hideal : (2 * Real.sqrt ((n + 2 : ℕ) : ℝ)) ^ (2 : ℕ) =
            4 * ((n + 2 : ℕ) : ℝ) := by nlinarith only [hr]
        rw [hs, hideal]
        ring
  unfold ccmActualHeadParabolicNormalizedCentroidVariance
    ccmActualHeadParabolicCentroidVariance
  change (m * _ - _ ^ (2 : ℕ)) / m -
    (m * _ - _ ^ (2 : ℕ)) / m = q - (4 * p * e + e ^ (2 : ℕ)) / m
  rw [h1, h2]
  have h4 :
      (∑ n ∈ Finset.range (K + 1),
        criticalMellinAtomWeight (n + 2) *
          ccmActualHeadMatchedPolarCentroid (n + 2) ^ (2 : ℕ)) =
        (∑ n ∈ Finset.range (K + 1),
          criticalMellinAtomWeight (n + 2) *
            routePIdealCentroid (n + 2) ^ (2 : ℕ)) + q := by linarith only [h3]
  rw [h4]
  field_simp
  ring

end RHTower
