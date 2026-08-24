import GaloisForLFunctions.HTGeometry.GeneralizedSchurKernelRankProfile
import GaloisForLFunctions.RHTower.SuzukiShiftedXiInfiniteBlaschkeIsometry
import GaloisForLFunctions.RHTower.SuzukiShiftedXiLeakageNormBounds

/-!
# Exact infinite shifted-Xi cancellation rank

For every nonnegative shift, including exceptional shifts with common numerator and denominator
zeros, the literal full-divisor generalized-Schur kernel has an `r`-dimensional negative subspace
exactly when the numerator adjoint restricted to the denominator model space has rank at least `r`.
No coprimality or nonexceptionality condition is used.
-/

open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Literal full-divisor generalized-Schur kernel of the shifted-Xi numerator and denominator. -/
def xiShiftInfiniteGeneralizedSchurKernel
    {omega : ℝ} (homega : 0 ≤ omega) (z w : ℂ) : ℂ :=
  generalizedSchurKernel
    (xiShiftInfiniteSchurNumerator homega)
    (xiShiftPoleBlaschkeMultiplier homega) z w

/-- Exact arbitrary-rank profile of the infinite shifted-Xi generalized-Schur kernel, valid at
exceptional shifts: common-divisor cancellation is encoded by restricted adjoint rank. -/
theorem xiShiftInfiniteGeneralizedSchurKernel_negativeDimension_iff_rankAtLeast
    {omega : ℝ} (homega : 0 ≤ omega) (r : ℕ) :
    HasFiniteKernelNegativeDimension
        (fun z w : Metric.ball (0 : ℂ) 1 =>
          xiShiftInfiniteGeneralizedSchurKernel homega z.1 w.1) r ↔
      RestrictedAdjointRankAtLeast
        (hardyMultiplierModelSpace (xiShiftPoleBlaschkeMultiplier homega))
        (hardyMul (xiShiftInfiniteSchurNumerator homega)) r := by
  simpa only [xiShiftInfiniteGeneralizedSchurKernel] using
    generalizedSchurKernel_negativeDimension_iff_rankAtLeast
      (xiShiftInfiniteSchurNumerator homega)
      (xiShiftPoleBlaschkeMultiplier homega)
      (by rw [xiShiftInfiniteSchurNumerator_bd])
      (xiShiftPoleBlaschkeMultiplier_isometry homega) r

end

end RHTower
