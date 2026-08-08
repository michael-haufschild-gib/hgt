import GaloisForLFunctions.HTGeometry.HankelBoundaryFlux
import GaloisForLFunctions.RHTower.XiShiftedHankelTerminalFlux

/-!
# Exact boundary flux for the shifted reciprocal Xi Hankel flow

This module specializes the null-vector terminal-flux law to the actual integral-differentiated Xi
moment flow.  At a singular block, the derivative of its null quadratic depends on no interior
entry: it is exactly the leading null-polynomial coefficient times the first omitted Xi moment
pairing.
-/

open Matrix
open scoped BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Matrix form of the shifted reciprocal Xi Hankel quadratic. -/
def xiShiftedMomentHankelQuadratic
    (y : ℝ) (n : ℕ) (c : Fin n → ℝ) : ℝ :=
  c ⬝ᵥ (xiShiftedMomentHankelMatrix y n *ᵥ c)

/-- The matrix quadratic agrees with the original double-sum disproof functional. -/
theorem xiShiftedMomentHankelQuadratic_eq
    (y : ℝ) (n : ℕ) (c : Fin n → ℝ) :
    xiShiftedMomentHankelQuadratic y n c =
      xiShiftedReciprocalHankelQuadratic y c := by
  simp only [xiShiftedMomentHankelQuadratic, xiShiftedReciprocalHankelQuadratic,
    dotProduct, Matrix.mulVec, xiShiftedMomentHankelMatrix, finiteHankelMatrix,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Entrywise differentiability gives the derivative of the complete finite quadratic form. -/
theorem hasDerivAt_xiShiftedMomentHankelQuadratic
    {y : ℝ} (hy : 0 < y) (n : ℕ) (c : Fin n → ℝ) :
    HasDerivAt (fun t => xiShiftedMomentHankelQuadratic t n c)
      (c ⬝ᵥ (xiShiftedHankelTransportMatrix y n *ᵥ c)) y := by
  simp only [xiShiftedMomentHankelQuadratic, dotProduct, Matrix.mulVec]
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.const_mul
  apply HasDerivAt.fun_sum
  intro j _
  exact (hasDerivAt_xiShiftedMomentHankelMatrix_entry hy n i j).mul_const (c j)

/-- The first omitted Xi moment column paired with the current coefficient vector. -/
def xiShiftedHankelFirstOmittedCoupling
    (y : ℝ) (n : ℕ) (c : Fin n → ℝ) : ℝ :=
  hankelFirstOmittedCoupling
    (fun k => (xiShiftedReciprocalMoment y k).re) n c

/-- **Actual Xi null-vector flux.** On a kernel vector of the shifted-Xi block, the derivative of
the quadratic is exactly the rank-two terminal boundary pairing. -/
theorem hasDerivAt_xiShiftedMomentHankelQuadratic_of_kernel
    {y : ℝ} (hy : 0 < y) (n : ℕ) (c : Fin n → ℝ)
    (hc : xiShiftedMomentHankelMatrix y n *ᵥ c = 0) :
    HasDerivAt (fun t => xiShiftedMomentHankelQuadratic t n c)
      (-2 * (c ⬝ᵥ hankelTerminalBasis n) *
        (xiShiftedHankelTerminalMomentVector y n ⬝ᵥ c)) y := by
  refine (hasDerivAt_xiShiftedMomentHankelQuadratic hy n c).congr_deriv ?_
  rw [xiShiftedHankelTransportMatrix]
  have h := dotProduct_finiteHankelDerivativeMatrix_mulVec_of_kernel
    (fun k => (xiShiftedReciprocalMoment y k).re) n c hc
  rw [finiteHankelDerivativeMatrix_eq_transport_sub_terminalFlux] at h
  simpa [xiShiftedMomentHankelMatrix, xiShiftedHankelTerminalMomentVector] using h

/-- **Monic first-crossing coordinate.** For a block of size `n+1`, the Xi null-quadratic
derivative is `-(2n+1)` times leading coefficient times first omitted coupling. -/
theorem hasDerivAt_xiShiftedMomentHankelQuadratic_of_kernel_succ
    {y : ℝ} (hy : 0 < y) (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0) :
    HasDerivAt (fun t => xiShiftedMomentHankelQuadratic t (n + 1) c)
      (-(2 * (n : ℝ) + 1) * c (Fin.last n) *
        xiShiftedHankelFirstOmittedCoupling y (n + 1) c) y := by
  refine (hasDerivAt_xiShiftedMomentHankelQuadratic hy (n + 1) c).congr_deriv ?_
  rw [xiShiftedHankelTransportMatrix]
  have h := dotProduct_finiteHankelDerivativeMatrix_mulVec_of_kernel_succ
    (fun k => (xiShiftedReciprocalMoment y k).re) n c hc
  rw [finiteHankelDerivativeMatrix_eq_transport_sub_terminalFlux] at h
  simpa [xiShiftedMomentHankelMatrix, xiShiftedHankelTerminalMomentVector,
    xiShiftedHankelFirstOmittedCoupling] using h

end

end RHTower
