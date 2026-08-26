import GaloisForLFunctions.HTGeometry.SmirnovToeplitzNPlus

/-!
# Inner-symbol cancellation in `N⁺` Toeplitz kernels

A unit-boundary analytic factor on the right of a Toeplitz symbol can be moved to the reflected
Smirnov function.  Forward local `L¹` admission is unchanged.  This is the exact cancellation
needed after taking the square root of only the outer factor of a bounded analytic gauge.
-/

open Complex MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Cancel a bounded analytic unit-boundary factor from the right of an `N⁺` symbol. -/
def SmirnovToeplitzNPlusElement.cancel_right_unitBoundary
    {U : ℝ → ℂ} (theta : DiskMultiplier)
    (hthetaUnit : ∀ᵐ x ∂volume, ‖diskMultiplierLineBoundary theta x‖ = 1)
    (F : SmirnovToeplitzNPlusElement
      (smirnovToeplitzSymbolMul U (diskMultiplierLineBoundary theta))) :
    SmirnovToeplitzNPlusElement U where
  toSmirnovToeplitzKernelElement :=
    { forward := F.toKernelElement.forward
      reflected := F.toKernelElement.reflected.mul
        (DiskSmirnovBoundary.ofMultiplier theta)
      boundary_relation := by
        filter_upwards [F.toKernelElement.boundary_relation,
          F.toKernelElement.reflected.boundary_mul_ae
            (DiskSmirnovBoundary.ofMultiplier theta),
          DiskSmirnovBoundary.boundary_ofMultiplier_ae theta,
          hthetaUnit] with x hF hmul htheta hunit
        rw [hmul, hF, htheta]
        simp only [smirnovToeplitzSymbolMul, map_mul]
        have hthetaConj :
            (starRingEnd ℂ) (diskMultiplierLineBoundary theta x) *
                diskMultiplierLineBoundary theta x = 1 := by
          rw [Complex.conj_mul', hunit]
          norm_num
        rw [show
          ((starRingEnd ℂ) (U x) *
              (starRingEnd ℂ) (diskMultiplierLineBoundary theta x)) *
                (starRingEnd ℂ) (F.toKernelElement.forward.boundary x) *
                  diskMultiplierLineBoundary theta x =
            (starRingEnd ℂ) (U x) *
              ((starRingEnd ℂ) (diskMultiplierLineBoundary theta x) *
                diskMultiplierLineBoundary theta x) *
              (starRingEnd ℂ) (F.toKernelElement.forward.boundary x) by ring,
          hthetaConj]
        ring
      forward_nonzero := F.toKernelElement.forward_nonzero }
  forward_locallyIntegrable := F.forward_locallyIntegrable

end

end GaloisForLFunctions.HTGeometry
