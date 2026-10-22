import GaloisForLFunctions.RHTower.SPEQuantileRieszParabolicPhysicalWall
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantilePolarCovarianceHardCore
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantilePolarParabolicCompletedCenteredBoundary

/-!
# Literal SP-E physical-wall covariance hard core

The completed SP-E Riesz readout contains the finite strict-cross current together with two
physical-wall gauge terms and the completed terminal interaction.  The strict current is itself
the signed displacement--centroid covariance minus its quadratic debt.  This module composes the
two source identities without dropping a terminal, gauge, or debt term.

The resulting exact finite quantity is a cutoff-dependent global adjacent-gap sum, not a local
gap energy.  A cofinal bound for this complete equation remains open.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- **Completed physical SP-E hard-core law.** After multiplication by its literal completed
source mass, the Riesz readout is exactly the global adjacent-gap Abel current, the full positive
displacement debt, the retained terminal interaction/form, and both physical-wall gauge terms.
This is the source-faithful finite object whose simultaneous cofinal control is required by
SP-E. -/
theorem completedParabolic_physicalWall_eq_adjacentGapKernel
    (M : ℕ) :
    let K := M - 3
    let T := Real.log M
    let C := ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal K T
    let B := ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K T
    B 0 * speQuantileRieszParabolicReadout M C =
      2 * (∑ r ∈ Finset.range K,
        (ccmActualHeadMatchedPolarUpperCoordinate (r + 2) -
          ccmActualHeadMatchedPolarLowerCoordinate (r + 3)) *
          ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel K r) +
        ccmActualHeadMatchedQuantileParabolicDisplacementDebtSum K +
        (2 * ccmParabolicPairing (ccmActualHeadQuantileParabolicAggregate K)
            (ccmActualHeadQuantileParabolicTerminal K T) +
          ccmParabolicForm (ccmActualHeadQuantileParabolicTerminal K T)) +
        (Real.sqrt (M : ℝ) * B 0 - B 1) * C 1 + B 2 * C 0 := by
  dsimp only
  rw [completedParabolic_physicalWall_decomposition_eq_finiteCross_sub_terminal,
    ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary_eq_neg_two_mul_covariance_sub_debt,
    ccmActualHeadMatchedQuantileParabolicCovariance_eq_adjacentMatchedGapKernel]
  ring

/-- At every nondegenerate SP-E aperture, the literal terminal-completed source boundary has
strictly positive mass.  Thus the complete source identity below is a genuine normalization,
not a division by a target-selected or vanishing factor. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary_log_zero_pos
    {M : ℕ} (hM : 3 ≤ M) :
    let K := M - 3
    let T := Real.log M
    0 < ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K T 0 := by
  dsimp only
  rw [ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary_zero,
    ccmActualHeadQuantilePolarCoordinate_two]
  have hMreal : (1 : ℝ) < M := by exact_mod_cast (show 1 < M by omega)
  have hlog : 0 < Real.log M := Real.log_pos hMreal
  have hexp : 1 < Real.exp (Real.log M / 2) :=
    Real.one_lt_exp_iff.mpr (by linarith)
  unfold ccmActualHeadPolarMassCoordinate
  nlinarith [ccmActualHeadParabolicMass_pos (M - 3)]

/-- **Unnormalized literal completed SP-E source law.**  Multiplying the unsquared completed
transport by its own positive source-boundary mass exposes, without division, the exact global
covariance--debt--terminal--gauge relation. -/
theorem completedSPESourceTransport_mul_boundaryMass_eq_covariance_debt_gauges
    {M : ℕ} (hM : 3 ≤ M) :
    let K := M - 3
    let T := Real.log M
    let C := ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal K T
    let B := ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K T
    B 0 *
        (speCompletedQuantileRieszTransport M -
          (∑ n ∈ Finset.range (K + 1),
            ccmMatchedPrimePolarQuadratureDefect (speQuantileRieszProfile M) (n + 2)) +
          2 * (Real.sqrt M - 2 / 3)) =
      2 * (∑ r ∈ Finset.range K,
        (ccmActualHeadMatchedPolarUpperCoordinate (r + 2) -
          ccmActualHeadMatchedPolarLowerCoordinate (r + 3)) *
          ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel K r) +
        ccmActualHeadMatchedQuantileParabolicDisplacementDebtSum K +
        (2 * ccmParabolicPairing (ccmActualHeadQuantileParabolicAggregate K)
            (ccmActualHeadQuantileParabolicTerminal K T) +
          ccmParabolicForm (ccmActualHeadQuantileParabolicTerminal K T)) +
        (Real.sqrt (M : ℝ) * B 0 - B 1) * C 1 + B 2 * C 0 := by
  dsimp only
  rw [speCompletedQuantileRieszTransport_eq_matchedQuadratureDefect_add_completedParabolic hM]
  have h := completedParabolic_physicalWall_eq_adjacentGapKernel M
  linarith

/-- **Literal completed SP-E source law.**  The unsquared, coefficient-faithful SP-E transport
is exactly its matched quadrature defect, the retained lower physical correction, and one
positive-boundary-mass-normalized source relation.  That relation contains every global adjacent
covariance-gap contribution, the full displacement debt, the terminal interaction and form, and
both physical-wall gauge residues.  Hence the route's unresolved content is a single signed
covariance--debt--gauge cancellation, not a missing local transport identity. -/
theorem speCompletedQuantileRieszTransport_eq_quadrature_sub_lower_add_covariance_debt_gauges
    {M : ℕ} (hM : 3 ≤ M) :
    let K := M - 3
    let T := Real.log M
    let C := ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal K T
    let B := ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K T
    speCompletedQuantileRieszTransport M =
      (∑ n ∈ Finset.range (K + 1),
        ccmMatchedPrimePolarQuadratureDefect (speQuantileRieszProfile M) (n + 2)) -
        2 * (Real.sqrt M - 2 / 3) +
      (2 * (∑ r ∈ Finset.range K,
        (ccmActualHeadMatchedPolarUpperCoordinate (r + 2) -
          ccmActualHeadMatchedPolarLowerCoordinate (r + 3)) *
          ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel K r) +
        ccmActualHeadMatchedQuantileParabolicDisplacementDebtSum K +
        (2 * ccmParabolicPairing (ccmActualHeadQuantileParabolicAggregate K)
            (ccmActualHeadQuantileParabolicTerminal K T) +
          ccmParabolicForm (ccmActualHeadQuantileParabolicTerminal K T)) +
        (Real.sqrt (M : ℝ) * B 0 - B 1) * C 1 + B 2 * C 0) / B 0 := by
  dsimp only
  have hsource := completedSPESourceTransport_mul_boundaryMass_eq_covariance_debt_gauges hM
  have hpos := ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary_log_zero_pos hM
  have hne := hpos.ne'
  field_simp [hne]
  linarith [hsource]

end RHTower

end
