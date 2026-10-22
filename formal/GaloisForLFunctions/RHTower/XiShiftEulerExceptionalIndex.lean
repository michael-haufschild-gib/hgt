import GaloisForLFunctions.RHTower.Suzuki.SuzukiShiftedXiInfiniteKernelIdentification
import GaloisForLFunctions.RHTower.XiShiftEulerRegionIndex

/-!
# Exceptional-shift Euler Pick index

This leaf transfers the source-exact infinite shifted-Xi cancellation rank to the ordinary
Euler-convergence sampling half-plane. It proves the nonlocal correlation law without excluding
exceptional common numerator/denominator zeros.
-/

open Complex Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Exact cancellation-aware finite negative-dimension profile on the literal Euler sampling
region, valid at every positive shift. -/
theorem eulerXiShiftPick_negativeDimension_iff_rankAtLeast
    {omega : ℝ} (homega : 0 < omega) (r : ℕ) :
    HasFiniteKernelNegativeDimension
        (fun z w : xiShiftEulerUpperSet omega =>
          eulerXiShiftPick omega z.1 w.1) r ↔
      RestrictedAdjointRankAtLeast
        (hardyMultiplierModelSpace
          (xiShiftPoleBlaschkeMultiplier homega.le))
        (hardyMul (xiShiftInfiniteSchurNumerator homega.le)) r := by
  have hlocal := xiShiftRegularUpperKernel_openRegion_negativeDimension_iff
    omega (xiShiftEulerUpperSet omega)
    (isOpen_xiShiftEulerUpperSet omega)
    (xiShiftEulerUpperSet_subset_upperHalfPlane homega)
    (suzukiCanonicalE_ne_zero_of_mem_xiShiftEulerUpperSet homega)
    (xiShiftEulerUpperSet_nonempty omega) r
  rw [← xiShiftRegularUpperKernel_negativeDimension_iff_rankAtLeast
    homega.le r]
  simpa only [eulerXiShiftPick_eq_upperHalfPlaneSchurKernel] using hlocal

/-- At every positive shift, including exceptional shifts, all finite Euler Pick matrices are
positive-semidefinite exactly when the cancelled restricted leakage has no rank-one direction. -/
theorem eulerXiShiftPick_firstFailingCorrelationOrder_eq_top_iff_not_rankAtLeast_one
    {omega : ℝ} (homega : 0 < omega) :
    kernelFirstFailingCorrelationOrder
        (fun z w : xiShiftEulerUpperSet omega =>
          eulerXiShiftPick omega z.1 w.1) = ⊤ ↔
      ¬ RestrictedAdjointRankAtLeast
        (hardyMultiplierModelSpace
          (xiShiftPoleBlaschkeMultiplier homega.le))
        (hardyMul (xiShiftInfiniteSchurNumerator homega.le)) 1 := by
  rw [kernelFirstFailingCorrelationOrder_eq_top_iff,
    hasNegativeKernelPacket_iff_negativeDimension_one,
    eulerXiShiftPick_negativeDimension_iff_rankAtLeast homega 1]

/-- Any surviving cancelled divisor direction is invisible to one-node tests but appears in a
finite Euler-region correlation packet of order at least two. -/
theorem eulerXiShiftPick_nonlocal_negative_correlation
    {omega : ℝ} (homega : 0 < omega)
    (hrank : RestrictedAdjointRankAtLeast
      (hardyMultiplierModelSpace
        (xiShiftPoleBlaschkeMultiplier homega.le))
      (hardyMul (xiShiftInfiniteSchurNumerator homega.le)) 1) :
    (2 : WithTop ℕ) ≤ kernelFirstFailingCorrelationOrder
        (fun z w : xiShiftEulerUpperSet omega =>
          eulerXiShiftPick omega z.1 w.1) ∧
      kernelFirstFailingCorrelationOrder
        (fun z w : xiShiftEulerUpperSet omega =>
          eulerXiShiftPick omega z.1 w.1) ≠ ⊤ := by
  refine ⟨two_le_eulerXiShiftPick_firstFailingCorrelationOrder homega, ?_⟩
  intro htop
  have hnrank :=
    (eulerXiShiftPick_firstFailingCorrelationOrder_eq_top_iff_not_rankAtLeast_one
      homega).mp htop
  exact hnrank hrank

end

end RHTower

