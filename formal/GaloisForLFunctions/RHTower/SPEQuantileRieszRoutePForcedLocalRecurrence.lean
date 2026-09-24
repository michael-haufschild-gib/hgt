import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePLocalFluxOrientation
import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePSourceIntegerHistoryNoGo

/-!
# Source-forced local Route-P recurrence

The normalized physical history is cofinally unbounded below and its exact
successor difference is the one-atom flux. Hence negative flux recurs at
arbitrarily late cutoffs. The eventual local orientation law then forces a
positive centered matched-to-quantile displacement at arbitrarily late
prime-power admissions.

This excludes eventual one-sided displacement as a debt-payment mechanism.
It supplies no positive global history bound or meromorphic graph intertwiner.
-/

open Filter

namespace RHTower

noncomputable section

/-- Unbounded negative history excursions force arbitrarily late negative
literal one-atom fluxes. -/
theorem routeP_cofinal_negative_normalized_variance_flux (M : ℕ) :
    ∃ K : ℕ, M ≤ K ∧
      ccmActualHeadMatchedQuantileParabolicNormalizedVarianceFlux K < 0 := by
  by_contra h
  have hnonneg : ∀ K : ℕ, M ≤ K →
      0 ≤ ccmActualHeadMatchedQuantileParabolicNormalizedVarianceFlux K := by
    intro K hMK
    by_contra hneg
    exact h ⟨K, hMK, lt_of_not_ge hneg⟩
  have hmono : ∀ K : ℕ, M ≤ K →
      ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect M ≤
        ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect K := by
    intro K hMK
    induction K, hMK using Nat.le_induction with
    | base => exact le_refl _
    | succ K hMK ih =>
        have hstep :=
          ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect_succ_sub_eq_flux K
        have hflux := hnonneg K hMK
        linarith
  obtain ⟨K, hMK, hbelow⟩ :=
    routeP_normalized_history_cofinally_unbounded_below
      (ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect M) M
  exact (not_lt_of_ge (hmono K hMK)) hbelow

/-- At arbitrarily late prime-power admissions, the new displacement exceeds
the preceding physical-head mean displacement. -/
theorem routeP_cofinal_positive_centered_displacement_at_primePower (M : ℕ) :
    ∃ K : ℕ, M ≤ K ∧ IsPrimePow (K + 3) ∧
      0 < ccmActualHeadMatchedQuantileParabolicCenteredDisplacement K := by
  obtain ⟨K₀, hK₀⟩ :=
    eventually_atTop.mp routeP_eventually_positive_local_flux_orientation_factor
  obtain ⟨K, hMK, hflux⟩ :=
    routeP_cofinal_negative_normalized_variance_flux (max M K₀)
  have hM : M ≤ K := (le_max_left M K₀).trans hMK
  have hK₀K : K₀ ≤ K := (le_max_right M K₀).trans hMK
  have hfactor := hK₀ K hK₀K
  have hprime : IsPrimePow (K + 3) := by
    by_contra hnot
    have hz :=
      ccmActualHeadMatchedQuantileParabolicNormalizedVarianceFlux_eq_zero_of_not_isPrimePow
        K hnot
    linarith
  have hweight : 0 ≤ criticalMellinAtomWeight (K + 3) :=
    criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _
  have hmass : 0 < ccmActualHeadParabolicMass K :=
    ccmActualHeadParabolicMass_pos K
  have hmass' : 0 < ccmActualHeadParabolicMass (K + 1) :=
    ccmActualHeadParabolicMass_pos (K + 1)
  have hcoeff : 0 ≤ criticalMellinAtomWeight (K + 3) *
      ccmActualHeadParabolicMass K / ccmActualHeadParabolicMass (K + 1) := by
    positivity
  rw [ccmActualHeadMatchedQuantileParabolicNormalizedVarianceFlux_eq_centered_signed_increment]
    at hflux
  have hproduct : 0 <
      (criticalMellinAtomWeight (K + 3) *
        ccmActualHeadParabolicMass K / ccmActualHeadParabolicMass (K + 1)) *
      (2 * ccmActualHeadMatchedQuantileParabolicCenteredMatchedOffset K +
        ccmActualHeadMatchedQuantileParabolicCenteredDisplacement K) *
      ccmActualHeadMatchedQuantileParabolicCenteredDisplacement K := by
    nlinarith only [hflux]
  have hnonnegFactor : 0 ≤
      (criticalMellinAtomWeight (K + 3) *
        ccmActualHeadParabolicMass K / ccmActualHeadParabolicMass (K + 1)) *
      (2 * ccmActualHeadMatchedQuantileParabolicCenteredMatchedOffset K +
        ccmActualHeadMatchedQuantileParabolicCenteredDisplacement K) :=
    mul_nonneg hcoeff hfactor.le
  have hpositive : 0 < ccmActualHeadMatchedQuantileParabolicCenteredDisplacement K := by
    by_contra hnot
    have hnonpos := le_of_not_gt hnot
    have hcontra := mul_nonpos_of_nonneg_of_nonpos hnonnegFactor hnonpos
    linarith
  exact ⟨K, hM, hprime, hpositive⟩

end
end RHTower
