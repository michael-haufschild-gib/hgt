import GaloisForLFunctions.RHTower.SPEQuantileRieszPrimePowerHistoryVariance

/-!
# Translation-gauge blindness of the SP-E prime-power history

The finite SP-E source history is a difference of weighted centroid variances.
Those variances are exactly invariant under an independent common translation of
either cell profile.  Hence an affine repair which supplies only a headwise
common centroid shift is invisible to the complete prime-power history.  A
Route-P/SP-E graph estimate must control relative displacement across cells;
the common translation mode cannot supply its missing sign or bound.

This is a source-level no-go, not a variance sign or an RH implication.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Weighted centroid variance is exactly blind to a common translation of every cell. -/
theorem ccmActualHeadParabolicCentroidVariance_add_constant
    (K : ℕ) (c : ℕ → ℝ) (a : ℝ) :
    ccmActualHeadParabolicCentroidVariance K (fun n => c n + a) =
      ccmActualHeadParabolicCentroidVariance K c := by
  have hfirst :
      (∑ n ∈ Finset.range (K + 1),
        criticalMellinAtomWeight (n + 2) * (c (n + 2) + a)) =
      (∑ n ∈ Finset.range (K + 1),
        criticalMellinAtomWeight (n + 2) * c (n + 2)) +
        a * ccmActualHeadParabolicMass K := by
    unfold ccmActualHeadParabolicMass
    calc
      _ = (∑ n ∈ Finset.range (K + 1),
          (criticalMellinAtomWeight (n + 2) * c (n + 2) +
            a * criticalMellinAtomWeight (n + 2))) := by
          apply Finset.sum_congr rfl
          intro n hn
          ring
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hsecond :
      (∑ n ∈ Finset.range (K + 1),
        criticalMellinAtomWeight (n + 2) * (c (n + 2) + a) ^ (2 : ℕ)) =
      (∑ n ∈ Finset.range (K + 1),
        criticalMellinAtomWeight (n + 2) * c (n + 2) ^ (2 : ℕ)) +
        2 * a * (∑ n ∈ Finset.range (K + 1),
          criticalMellinAtomWeight (n + 2) * c (n + 2)) +
        a ^ (2 : ℕ) * ccmActualHeadParabolicMass K := by
    unfold ccmActualHeadParabolicMass
    calc
      _ = (∑ n ∈ Finset.range (K + 1),
          (criticalMellinAtomWeight (n + 2) * c (n + 2) ^ (2 : ℕ) +
            (2 * a) * (criticalMellinAtomWeight (n + 2) * c (n + 2)) +
            a ^ (2 : ℕ) * criticalMellinAtomWeight (n + 2))) := by
          apply Finset.sum_congr rfl
          intro n hn
          ring
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            Finset.mul_sum, Finset.mul_sum]
  unfold ccmActualHeadParabolicCentroidVariance
  rw [hfirst, hsecond]
  ring

/-- The complete prime-power history is unchanged by independent common translations of the
matched and quantile finite cell profiles. -/
theorem speQuantileRieszPrimePowerHistory_eq_translatedCentroidVarianceDifference
    (K : ℕ) (matchedShift quantileShift : ℝ) :
    ∑ n ∈ (Finset.range K).filter (fun n => IsPrimePow (n + 3)),
      speQuantileRieszPrimePowerHistoryCurvature n =
      ccmActualHeadParabolicCentroidVariance K
          (fun n => ccmActualHeadMatchedPolarCentroid n + matchedShift) -
        ccmActualHeadParabolicCentroidVariance K
          (fun n => ccmActualHeadQuantilePolarCentroid n + quantileShift) := by
  rw [ccmActualHeadParabolicCentroidVariance_add_constant,
    ccmActualHeadParabolicCentroidVariance_add_constant,
    speQuantileRieszPrimePowerHistory_eq_centroidVarianceDifference]

end RHTower
