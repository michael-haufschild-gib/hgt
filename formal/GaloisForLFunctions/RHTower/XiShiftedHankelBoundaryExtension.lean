import GaloisForLFunctions.HTGeometry.HankelBoundaryExtension
import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryFlux

/-!
# Positive-semidefinite extension rigidity for shifted Xi Hankel blocks

The universal Hankel extension law is specialized here to the actual integral-differentiated Xi
moment flow.  At a singular shifted-Xi block, one more PSD block forces the first omitted Xi
pairing—and therefore the null-quadratic derivative—to vanish.  Conversely, a nonzero omitted
pairing is an explicit witness that the next shifted-Xi block is indefinite.
-/

open Matrix

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- A shifted-Xi null polynomial that survives one PSD extension has zero first omitted pairing. -/
theorem xiShiftedHankelFirstOmittedCoupling_eq_zero_of_posSemidef_succ_of_kernel
    (y : ℝ) (n : ℕ) (c : Fin n → ℝ)
    (hpsd : (xiShiftedMomentHankelMatrix y (n + 1)).PosSemidef)
    (hc : xiShiftedMomentHankelMatrix y n *ᵥ c = 0) :
    xiShiftedHankelFirstOmittedCoupling y n c = 0 := by
  exact hankelFirstOmittedCoupling_eq_zero_of_posSemidef_succ_of_kernel
    (fun k => (xiShiftedReciprocalMoment y k).re) n c hpsd hc

/-- Nonzero shifted-Xi boundary coupling certifies failure of the next block's PSD condition. -/
theorem xiShiftedMomentHankelMatrix_succ_not_posSemidef_of_kernel_of_coupling_ne_zero
    (y : ℝ) (n : ℕ) (c : Fin n → ℝ)
    (hc : xiShiftedMomentHankelMatrix y n *ᵥ c = 0)
    (hboundary : xiShiftedHankelFirstOmittedCoupling y n c ≠ 0) :
    ¬ (xiShiftedMomentHankelMatrix y (n + 1)).PosSemidef := by
  exact finiteHankelMatrix_succ_not_posSemidef_of_kernel_of_coupling_ne_zero
    (fun k => (xiShiftedReciprocalMoment y k).re) n c hc hboundary

/-- If a singular shifted-Xi block admits one PSD extension, its null quadratic is stationary
under the exact shift flow. -/
theorem hasDerivAt_xiShiftedMomentHankelQuadratic_zero_of_posSemidef_succ_of_kernel
    {y : ℝ} (hy : 0 < y) (n : ℕ) (c : Fin n → ℝ)
    (hpsd : (xiShiftedMomentHankelMatrix y (n + 1)).PosSemidef)
    (hc : xiShiftedMomentHankelMatrix y n *ᵥ c = 0) :
    HasDerivAt (fun t => xiShiftedMomentHankelQuadratic t n c) 0 y := by
  refine (hasDerivAt_xiShiftedMomentHankelQuadratic_of_kernel hy n c hc).congr_deriv ?_
  rw [xiShiftedHankelTerminalMomentVector, dotProduct_hankelTerminalMomentVector]
  change -2 * (c ⬝ᵥ hankelTerminalBasis n) *
    (((n : ℝ) - 1 / 2) * xiShiftedHankelFirstOmittedCoupling y n c) = 0
  rw [xiShiftedHankelFirstOmittedCoupling_eq_zero_of_posSemidef_succ_of_kernel
    y n c hpsd hc]
  ring

end

end RHTower
