import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePTranslationGauge
import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantileParabolicNormalizedVarianceFlow

/-!
# Canonical centroid gauge fixing for the finite Route-P SP-E carrier

The common-centroid translation mode of the five-channel Route-P carrier is
gauge.  This leaf chooses it canonically: at every finite physical head, shift
the matched and quantile centroid profiles by minus the weighted matched
centroid mean.  The translated centroid column then has zero weighted sum,
while the complete strict-cross P current is unchanged exactly.

This removes one genuine gauge direction before the unresolved ordered
two-Julia graph estimate.  It does not bound the remaining relative-
displacement covariance, construct the cofinal graph domain, or imply RH.
-/

open Complex Matrix
open scoped BigOperators

noncomputable section

namespace RHTower

/-- The weighted sum of a finite profile about its own literal centroid mean vanishes exactly. -/
theorem ccmActualHeadParabolicWeightedCenteredCentroidSum_eq_zero
    (K : ℕ) (c : ℕ → ℝ) :
    ∑ n ∈ Finset.range (K + 1),
      criticalMellinAtomWeight (n + 2) *
        (c (n + 2) - ccmActualHeadParabolicCentroidMean K c) = 0 := by
  have hmass : ccmActualHeadParabolicMass K ≠ 0 :=
    (ccmActualHeadParabolicMass_pos K).ne'
  have hsplit :
      (∑ n ∈ Finset.range (K + 1),
        criticalMellinAtomWeight (n + 2) *
          (c (n + 2) - ccmActualHeadParabolicCentroidMean K c)) =
        (∑ n ∈ Finset.range (K + 1),
          criticalMellinAtomWeight (n + 2) * c (n + 2)) -
        ccmActualHeadParabolicCentroidMean K c * ccmActualHeadParabolicMass K := by
    unfold ccmActualHeadParabolicMass
    calc
      _ = ∑ n ∈ Finset.range (K + 1),
          (criticalMellinAtomWeight (n + 2) * c (n + 2) -
            ccmActualHeadParabolicCentroidMean K c *
              criticalMellinAtomWeight (n + 2)) := by
          apply Finset.sum_congr rfl
          intro n hn
          ring
      _ = _ := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hsplit, ccmActualHeadParabolicCentroidMean]
  field_simp [hmass]
  ring

/-- Canonically gauge-fixed five-profile packet of the finite physical head. -/
def speQuantileRieszStrictCrossFiveChannelCenteredProfile (K : ℕ) :
    Matrix (Fin (K + 1)) (Fin 5) ℂ :=
  speQuantileRieszStrictCrossFiveChannelCentroidTranslatedProfile
    (fun i => (i : ℕ) + 2)
    (-ccmActualHeadParabolicCentroidMean K ccmActualHeadMatchedPolarCentroid)

/-- The gauge-fixed centroid column has zero aggregate exactly. -/
theorem speQuantileRieszStrictCrossFiveChannelCenteredProfile_column_two_sum_eq_zero
    (K : ℕ) :
    ∑ i : Fin (K + 1),
      speQuantileRieszStrictCrossFiveChannelCenteredProfile K i 2 = 0 := by
  let g : ℕ → ℂ := fun n =>
    ((criticalMellinAtomWeight (n + 2) *
      (ccmActualHeadMatchedPolarCentroid (n + 2) -
        ccmActualHeadParabolicCentroidMean K ccmActualHeadMatchedPolarCentroid) : ℝ) : ℂ)
  change (∑ i : Fin (K + 1), g i) = 0
  rw [Fin.sum_univ_eq_sum_range g (K + 1)]
  dsimp only [g]
  exact_mod_cast
    ccmActualHeadParabolicWeightedCenteredCentroidSum_eq_zero K
      ccmActualHeadMatchedPolarCentroid

/-- Gauge fixing preserves the complete finite P strict-cross current exactly. -/
theorem speQuantileRieszStrictCrossFiveChannelCenteredProfile_current_eq
    (K : ℕ) :
    speQuantileRieszStrictCrossFiveChannelCenteredProfile K *
        speQuantileRieszStrictCrossFiveChannelKreinForm *
        (speQuantileRieszStrictCrossFiveChannelCenteredProfile K)ᵀ =
      speQuantileRieszStrictCrossFiveChannelProfile
          (fun i : Fin (K + 1) => (i : ℕ) + 2) *
        speQuantileRieszStrictCrossFiveChannelKreinForm *
        (speQuantileRieszStrictCrossFiveChannelProfile
          (fun i : Fin (K + 1) => (i : ℕ) + 2))ᵀ := by
  exact speQuantileRieszStrictCrossFiveChannelCentroidTranslated_current_invariant _ _

end RHTower
