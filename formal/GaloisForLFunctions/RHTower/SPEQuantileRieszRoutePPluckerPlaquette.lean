import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePPluckerCocycle

/-!
# SP-E covariance Pluecker plaquette in the Route-P determinant line

The cutoff/history-dependent SP-E covariance coefficient is not merely a scalar that changes with
the cutoff. Its mixed finite difference is an exact two-atom exterior increment: the product of
the two newly appended literal atom weights times their matched-centroid separation. Thus the
prefix determinant carries a bivariate curvature law before any cofinal limit or scalar trace
regularization is taken.

The forced Route-P Julia--Krein block reverses this plaquette in its actual determinant line.
This supplies a source-side ordered curvature datum for the still-open graph-closed,
coefficient-faithful non-Bessel transport. It does not claim an intertwiner into P-G186 incidence,
a co-Poisson realization, or an RH consequence.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- **Literal SP-E covariance plaquette.** Appending atom `K + 3` to the cutoff and atom `r + 3`
to the history gives exactly their weighted centroid separation. -/
theorem ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel_plaquette
    (K r : ℕ) :
    ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel (K + 1) (r + 1) -
        ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel (K + 1) r -
        ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel K (r + 1) +
        ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel K r =
      criticalMellinAtomWeight (K + 3) * criticalMellinAtomWeight (r + 3) *
        (ccmActualHeadMatchedPolarCentroid (K + 3) -
          ccmActualHeadMatchedPolarCentroid (r + 3)) := by
  unfold ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel
    ccmActualHeadParabolicMass
  simp only [Finset.sum_range_succ]
  ring

/-- **Route-P Julia determinant plaquette.** The literal P Julia block preserves the complete
source cutoff/history curvature with its forced orientation reversal. -/
theorem routePJuliaKrein_speQuantileRieszCovariancePrefixPlucker_plaquette
    (K r : ℕ) :
    (routePPrimitiveBurnolJuliaKreinBlock *
      speQuantileRieszCovariancePrefixPlucker (K + 1) (r + 1)).det -
        (routePPrimitiveBurnolJuliaKreinBlock *
          speQuantileRieszCovariancePrefixPlucker (K + 1) r).det -
        (routePPrimitiveBurnolJuliaKreinBlock *
          speQuantileRieszCovariancePrefixPlucker K (r + 1)).det +
        (routePPrimitiveBurnolJuliaKreinBlock *
          speQuantileRieszCovariancePrefixPlucker K r).det =
      -((criticalMellinAtomWeight (K + 3) * criticalMellinAtomWeight (r + 3) *
        (ccmActualHeadMatchedPolarCentroid (K + 3) -
          ccmActualHeadMatchedPolarCentroid (r + 3)) : ℝ) : ℂ) := by
  rw [routePJuliaKrein_mul_speQuantileRieszCovariancePrefixPlucker_det,
    routePJuliaKrein_mul_speQuantileRieszCovariancePrefixPlucker_det,
    routePJuliaKrein_mul_speQuantileRieszCovariancePrefixPlucker_det,
    routePJuliaKrein_mul_speQuantileRieszCovariancePrefixPlucker_det]
  push_cast
  have h := congrArg (fun x : ℝ => (x : ℂ))
    (ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel_plaquette K r)
  push_cast at h
  linear_combination -h

end

end RHTower
