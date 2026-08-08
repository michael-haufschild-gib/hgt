import GaloisForLFunctions.HTGeometry.HankelTerminalFlux
import GaloisForLFunctions.RHTower.SquaredXiCompleteMonotonicity

/-!
# Terminal-flux transport for shifted reciprocal Xi moments

The integral Lipschitz theorem for shifted reciprocal Xi moments supplies the exact recursion

`d/dy Re m_k(y) = -(k+1) Re m_(k+1)(y)`.

Specializing the generic finite Hankel transport law shows that every fixed Xi moment block evolves
by a weighted-shift Lyapunov flow plus one symmetric rank-two terminal leakage.  No finite-section
bulk defect remains.
-/

open Matrix

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Finite Hankel block of real shifted reciprocal Xi moments. -/
def xiShiftedMomentHankelMatrix (y : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  finiteHankelMatrix (fun k => (xiShiftedReciprocalMoment y k).re) n

/-- Terminal moment vector for the shifted Xi block. -/
def xiShiftedHankelTerminalMomentVector (y : ℝ) (n : ℕ) : Fin n → ℝ :=
  hankelTerminalMomentVector (fun k => (xiShiftedReciprocalMoment y k).re) n

theorem xiShiftedMomentHankelMatrix_isHermitian (y : ℝ) (n : ℕ) :
    (xiShiftedMomentHankelMatrix y n).IsHermitian :=
  finiteHankelMatrix_isHermitian _ _

/-- Exact algebraic Lyapunov/terminal-flux matrix for the Xi moment block. -/
def xiShiftedHankelTransportMatrix (y : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  -(hankelWeightedUpperShift n * xiShiftedMomentHankelMatrix y n) -
      xiShiftedMomentHankelMatrix y n * (hankelWeightedUpperShift n)ᵀ -
    (realOuterProduct (hankelTerminalBasis n)
        (xiShiftedHankelTerminalMomentVector y n) +
      realOuterProduct (xiShiftedHankelTerminalMomentVector y n)
        (hankelTerminalBasis n))

/-- **Actual Xi Lyapunov law.**  Every entry derivative of the shifted Xi Hankel block equals the
weighted-shift transport plus symmetric terminal flux. -/
theorem hasDerivAt_xiShiftedMomentHankelMatrix_entry
    {y : ℝ} (hy : 0 < y) (n : ℕ) (i j : Fin n) :
    HasDerivAt (fun t => xiShiftedMomentHankelMatrix t n i j)
      (xiShiftedHankelTransportMatrix y n i j) y := by
  apply hasDerivAt_finiteHankelMatrix_entry_of_momentRecursion
  intro k
  exact hasDerivAt_re_xiShiftedReciprocalMoment hy k

/-- Entrywise derivative formula without matrix notation. -/
theorem deriv_xiShiftedMomentHankelMatrix_entry
    {y : ℝ} (hy : 0 < y) (n : ℕ) (i j : Fin n) :
    deriv (fun t => xiShiftedMomentHankelMatrix t n i j) y =
      xiShiftedHankelTransportMatrix y n i j :=
  (hasDerivAt_xiShiftedMomentHankelMatrix_entry hy n i j).deriv

end

end RHTower
