import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePClockDiagonalNoGo

/-!
# SP-E covariance as a Route-P Julia determinant cocycle

The complete SP-E covariance coefficient at cutoff `K` and adjacent history index `r` is the
oriented area of its two literal prefix mass--centroid vectors.  This is not a scalarization:
the determinant retains both the cutoff prefix and the history prefix.  The forced Route-P
Julia--Krein block has determinant `-1`, so it transports this source Pluecker cocycle by an
exact orientation reversal.

Consequently the full strict-cross source current is an exact sum of Route-P Julia determinant
amplitudes against the literal adjacent source gaps, minus the unreduced nonnegative debt.  This
does not yet construct the noncommutative history-action intertwiner, identify the determinant
line with the physical P-G186 Gram incidence, or prove a cofinal bound.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- First mass moment of the literal finite SP-E prefix in matched-cell centroid coordinates. -/
def speQuantileRieszCovariancePrefixCentroidMass (K : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (K + 1),
    criticalMellinAtomWeight (i + 2) * ccmActualHeadMatchedPolarCentroid (i + 2)

/-- The two-prefix Pluecker carrier: first column is the history prefix `r`, second column the
current cutoff prefix `K`. -/
def speQuantileRieszCovariancePrefixPlucker (K r : ℕ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![(ccmActualHeadParabolicMass r : ℂ), (ccmActualHeadParabolicMass K : ℂ);
    (speQuantileRieszCovariancePrefixCentroidMass r : ℂ),
      (speQuantileRieszCovariancePrefixCentroidMass K : ℂ)]

/-- A literal SP-E covariance-gap coefficient is exactly its prefix Pluecker determinant. -/
theorem speQuantileRieszCovariancePrefixPlucker_det (K r : ℕ) :
    (speQuantileRieszCovariancePrefixPlucker K r).det =
      (ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel K r : ℂ) := by
  unfold speQuantileRieszCovariancePrefixPlucker
  rw [Matrix.det_fin_two]
  change
    (ccmActualHeadParabolicMass r : ℂ) *
        (speQuantileRieszCovariancePrefixCentroidMass K : ℂ) -
      (ccmActualHeadParabolicMass K : ℂ) *
        (speQuantileRieszCovariancePrefixCentroidMass r : ℂ) =
      (ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel K r : ℂ)
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
  unfold ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel
    speQuantileRieszCovariancePrefixCentroidMass ccmActualHeadParabolicMass
  ring_nf

/-- The forced P Julia--Krein block reverses, but preserves in magnitude, every literal SP-E
prefix covariance determinant. -/
theorem routePJuliaKrein_mul_speQuantileRieszCovariancePrefixPlucker_det (K r : ℕ) :
    (routePPrimitiveBurnolJuliaKreinBlock *
      speQuantileRieszCovariancePrefixPlucker K r).det =
      -(ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel K r : ℂ) := by
  rw [Matrix.det_mul, routePPrimitiveBurnolJuliaKreinBlock_det,
    speQuantileRieszCovariancePrefixPlucker_det]
  ring

/-- **Determinant-cocycle covariance transport.** The complete source covariance is the negative
sum of P Julia determinant amplitudes against every literal oriented adjacent gap. -/
theorem ccmActualHeadMatchedQuantileParabolicCovariance_eq_neg_sum_routePJuliaPlucker (K : ℕ) :
    (ccmActualHeadMatchedQuantileParabolicDisplacementCentroidCovariance K : ℂ) =
      -(∑ r ∈ Finset.range K,
        (ccmActualHeadMatchedPolarUpperCoordinate (r + 2) -
          ccmActualHeadMatchedPolarLowerCoordinate (r + 3) : ℂ) *
          (routePPrimitiveBurnolJuliaKreinBlock *
            speQuantileRieszCovariancePrefixPlucker K r).det) := by
  rw [ccmActualHeadMatchedQuantileParabolicCovariance_eq_adjacentMatchedGapKernel]
  push_cast
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [routePJuliaKrein_mul_speQuantileRieszCovariancePrefixPlucker_det]
  ring

/-- **Strict-cross P determinant transport.** The whole literal SP-E strict-cross source current
equals twice its Route-P Julia Pluecker transport, with the full quadratic displacement debt
retained exactly. -/
theorem ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary_eq_routePJuliaPlucker_sub_debt
    (K : ℕ) :
    (ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
        (ccmActualHeadMatchedQuantileParabolicSourceBoundary K) : ℂ) =
      2 * (∑ r ∈ Finset.range K,
        (ccmActualHeadMatchedPolarUpperCoordinate (r + 2) -
          ccmActualHeadMatchedPolarLowerCoordinate (r + 3) : ℂ) *
          (routePPrimitiveBurnolJuliaKreinBlock *
            speQuantileRieszCovariancePrefixPlucker K r).det) -
        (ccmActualHeadMatchedQuantileParabolicDisplacementDebtSum K : ℂ) := by
  rw [ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary_eq_neg_two_mul_covariance_sub_debt,
    Complex.ofReal_sub, Complex.ofReal_mul]
  push_cast
  rw [ccmActualHeadMatchedQuantileParabolicCovariance_eq_neg_sum_routePJuliaPlucker]
  ring

end

end RHTower
