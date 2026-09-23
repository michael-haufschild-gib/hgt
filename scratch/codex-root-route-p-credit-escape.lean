import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePChebyshevAbelLattice
import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePIdealCentroidVarianceEscape
import GaloisForLFunctions.RHTower.SPEQuantileRieszPrimePowerHistoryVariance

open Filter Topology

namespace RHTower

theorem routeP_centroid_excess_ge_two (K : ℕ) :
    centroidAtomExcess 2 ≤ ccmActualHeadMatchedCentroidChebyshevExcess K := by
  rw [ccmActualHeadMatchedCentroidChebyshevExcess_eq_atomPrefix]
  exact Finset.single_le_sum
    (fun n _ => centroidAtomExcess_nonneg_all n)
    (by simp : 2 ∈ Finset.range (K + 3))

theorem routeP_history_sub_credit_le_geometric_escape (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect K -
        4 * routePWeightedChebyshevNullCredit K ≤
      4 * (∑' n : ℕ, routePWidthCubeAtom n) / 3 -
        2 * Real.sqrt ((K + 2 : ℕ) : ℝ) * centroidAtomExcess 2 := by
  rw [routeP_normalized_history_eq_credit_sub_two_square_debts]
  have hm : 0 < ccmActualHeadParabolicMass K := ccmActualHeadParabolicMass_pos K
  have hr : 0 ≤ Real.sqrt ((K + 2 : ℕ) : ℝ) := Real.sqrt_nonneg _
  have he := routeP_centroid_excess_ge_two K
  have hq := routePWidthCubePrefix_le_tsum K
  have hfirst : 0 ≤
      (2 * (Chebyshev.psi ((K + 2 : ℕ) : ℝ) - ((K + 2 : ℕ) : ℝ)) +
          ccmActualHeadMatchedCentroidChebyshevExcess K -
          Real.sqrt ((K + 2 : ℕ) : ℝ) *
            (ccmActualHeadParabolicMass K -
              2 * Real.sqrt ((K + 2 : ℕ) : ℝ))) ^ (2 : ℕ) /
        ccmActualHeadParabolicMass K :=
    div_nonneg (sq_nonneg _) hm.le
  have hsecond : 0 ≤
      (4 * Real.sqrt ((K + 2 : ℕ) : ℝ) +
        ccmActualHeadParabolicMass K) / 12 *
        (ccmActualHeadParabolicMass K -
          2 * Real.sqrt ((K + 2 : ℕ) : ℝ)) ^ (2 : ℕ) := by
    positivity
  nlinarith only [hfirst, hsecond, hq, he, hr]

theorem routeP_history_sub_credit_tendsto_atBot :
    Tendsto
      (fun K : ℕ =>
        ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect K -
          4 * routePWeightedChebyshevNullCredit K)
      atTop atBot := by
  let Q : ℝ := ∑' n : ℕ, routePWidthCubeAtom n
  let E : ℝ := centroidAtomExcess 2
  have hE : 0 < E := centroidAtomExcess_two_pos
  have hroot : Tendsto
      (fun K : ℕ => Real.sqrt ((K + 2 : ℕ) : ℝ)) atTop atTop := by
    exact Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
  have hbound : Tendsto
      (fun K : ℕ => 4 * Q / 3 +
        Real.sqrt ((K + 2 : ℕ) : ℝ) * (-2 * E)) atTop atBot := by
    apply tendsto_atBot_add_const_left
    exact hroot.atTop_mul_const_of_neg' (by dsimp [E]; linarith)
  apply tendsto_atBot_mono (f := fun K : ℕ =>
    4 * Q / 3 + Real.sqrt ((K + 2 : ℕ) : ℝ) * (-2 * E))
  · intro K
    have h := routeP_history_sub_credit_le_geometric_escape K
    dsimp [Q, E]
    nlinarith only [h]
  · exact hbound

theorem routeP_prime_power_history_div_mass_eq_normalized_defect (K : ℕ) :
    (∑ n ∈ (Finset.range K).filter (fun n => IsPrimePow (n + 3)),
      speQuantileRieszPrimePowerHistoryCurvature n) /
        ccmActualHeadParabolicMass K =
      ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect K := by
  rw [speQuantileRieszPrimePowerHistory_eq_centroidVarianceDifference]
  unfold ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect
    ccmActualHeadParabolicNormalizedCentroidVariance
  rw [sub_div]

theorem routeP_prime_power_history_sub_credit_tendsto_atBot :
    Tendsto
      (fun K : ℕ =>
        (∑ n ∈ (Finset.range K).filter (fun n => IsPrimePow (n + 3)),
          speQuantileRieszPrimePowerHistoryCurvature n) /
            ccmActualHeadParabolicMass K -
          4 * routePWeightedChebyshevNullCredit K)
      atTop atBot := by
  simpa only [routeP_prime_power_history_div_mass_eq_normalized_defect] using
    routeP_history_sub_credit_tendsto_atBot

end RHTower
