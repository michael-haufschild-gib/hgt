import GaloisForLFunctions.RHTower.MobiusThetaInternalJetSourceToXiLanding
import GaloisForLFunctions.RHTower.XiHedenmalmThetaJetSource
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Local full-rank theorem for internally promoted theta sources

The internally promoted source family contains every local multiplicity direction, without using a
divisor point in its construction.  After a divisor point is chosen only for evaluation, arrange
the successive spectral jets of source orders `r, r - 1, ..., 1` into an `r × r` matrix, where `r`
is the analytic multiplicity.  The source-to-Xi landing makes this matrix upper triangular.  Its
diagonal is the first nonzero Xi jet, so its determinant is exactly that jet to the `r`-th power.

This is a source-side local spanning theorem: no multiplicity direction is lost by internal
promotion.  It does not assert the global closed-graph/Hodge estimate needed by Route R.
-/

open Complex Real MeasureTheory Set
open scoped BigOperators

noncomputable section
namespace RHTower

/-- At a divisor point of multiplicity `r`, row `i` is the source order `r - i`, and column `j`
records its `j`-th spectral jet.  Entries are kept as explicit theta-source moments. -/
def thetaInternalJetLocalMomentMatrix (rho : XiDivisorSupport) :
    Matrix (Fin (xiSupportMultiplicity rho))
      (Fin (xiSupportMultiplicity rho)) ℂ :=
  fun i j =>
    ∫ x : ℝ, thetaCuspFourierLaplaceJetIntegrand
      (xiSupportMultiplicity rho - i.val + j.val)
      (xiSpectralPointSupport rho) x

/-- Each local matrix entry is the corresponding Xi jet, by the unconditional theta-source
landing theorem. -/
theorem thetaInternalJetLocalMomentMatrix_apply
    (rho : XiDivisorSupport) (i j : Fin (xiSupportMultiplicity rho)) :
    thetaInternalJetLocalMomentMatrix rho i j =
      iteratedDeriv (xiSupportMultiplicity rho - i.val + j.val) XiC
        (xiSpectralPointSupport rho) := by
  rw [thetaInternalJetLocalMomentMatrix]
  exact (iteratedDeriv_XiC_eq_integral_thetaCuspFourierLaplaceJet
    (xiSupportMultiplicity rho - i.val + j.val)
    (xiSpectralPointSupport_mem_thetaCuspFourierLaplaceStrip rho)).symm

/-- Strictly lower entries vanish: their source order lies below the analytic multiplicity. -/
theorem thetaInternalJetLocalMomentMatrix_blockTriangular
    (rho : XiDivisorSupport) :
    (thetaInternalJetLocalMomentMatrix rho).BlockTriangular id := by
  intro i j hji
  rw [thetaInternalJetLocalMomentMatrix_apply]
  apply iteratedDeriv_XiC_eq_zero_before_supportMultiplicity rho
  change j.val < i.val at hji
  have hlt := Nat.add_lt_add_left hji
    (xiSupportMultiplicity rho - i.val)
  rw [Nat.sub_add_cancel (Nat.le_of_lt i.isLt)] at hlt
  exact hlt

/-- Every diagonal entry is the first nonzero Xi jet. -/
theorem thetaInternalJetLocalMomentMatrix_diag
    (rho : XiDivisorSupport) (i : Fin (xiSupportMultiplicity rho)) :
    thetaInternalJetLocalMomentMatrix rho i i =
      iteratedDeriv (xiSupportMultiplicity rho) XiC
        (xiSpectralPointSupport rho) := by
  rw [thetaInternalJetLocalMomentMatrix_apply]
  congr 2
  exact Nat.sub_add_cancel (Nat.le_of_lt i.isLt)

/-- **Exact local source determinant.**  The determinant of the complete internal source-jet
matrix is the first nonzero Xi jet raised to the analytic multiplicity. -/
theorem det_thetaInternalJetLocalMomentMatrix
    (rho : XiDivisorSupport) :
    (thetaInternalJetLocalMomentMatrix rho).det =
      (iteratedDeriv (xiSupportMultiplicity rho) XiC
        (xiSpectralPointSupport rho)) ^ xiSupportMultiplicity rho := by
  rw [Matrix.det_of_upperTriangular
    (thetaInternalJetLocalMomentMatrix_blockTriangular rho)]
  simp_rw [thetaInternalJetLocalMomentMatrix_diag]
  simp

/-- The local source-jet matrix is nonsingular at every Xi divisor point, including points of
arbitrary multiplicity. -/
theorem det_thetaInternalJetLocalMomentMatrix_ne_zero
    (rho : XiDivisorSupport) :
    (thetaInternalJetLocalMomentMatrix rho).det ≠ 0 := by
  rw [det_thetaInternalJetLocalMomentMatrix]
  exact pow_ne_zero _
    (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho)

/-- **Unconditional local full-rank source theorem.**  The internally promoted source orders
`r, r - 1, ..., 1` are linearly independent through all `r` local spectral jet directions at a
divisor point of multiplicity `r`. -/
theorem thetaInternalJetLocalMomentMatrix_linearIndependent
    (rho : XiDivisorSupport) :
    LinearIndependent ℂ (fun i => thetaInternalJetLocalMomentMatrix rho i) :=
  Matrix.linearIndependent_rows_of_det_ne_zero
    (det_thetaInternalJetLocalMomentMatrix_ne_zero rho)

end RHTower
