import GaloisForLFunctions.RHTower.EulerPositiveFisherFourUnit
import GaloisForLFunctions.HTGeometry.InfiniteFisherOneCornerCodiagonalContraction

/-!
# Physical full-Euler Fisher lower boundary

The direct positive-integer Euler state and its centered Fisher tangent define
an actual rank-two Hilbert--Schmidt connection on `ℓ²(ℕ+)`.  Its single lower
logarithmic cutoff corner is the concrete source field required by the
cofinal CCM incidence problem.

This file proves, without scalarizing the corner, that:

* the complete pointed connection has exactly the direct Euler Fisher energy;
* its energy tends to four at the critical boundary;
* every sharp Euler lower corner is carried unitarily to the affine
  squarefree-times-square lower corner, with both rank-one summands intact;
* the Hilbert--Schmidt energy of that corner is preserved exactly.

All statements are unconditional.
-/

open Complex Filter Set
open scoped Topology

noncomputable section
namespace RHTower

open ContinuousLinearMap
open GaloisForLFunctions.HTGeometry

/-- Actual pointed Fisher connection of the normalized positive Euler Gibbs
state. -/
def eulerPositivePointedFisherConnection
    (sigma : ℝ) (hsigma : 1 < sigma) :
    EulerPositiveL2 →L[ℂ] EulerPositiveL2 :=
  pointedFisherConnection
    (eulerPositiveStateLp sigma hsigma)
    (eulerPositiveCriticalFisherTangentLp sigma hsigma)

/-- The direct full-Euler pointed connection carries exactly the projective
Fisher energy of its tangent. -/
theorem hsNormSq_eulerPositivePointedFisherConnection
    {sigma : ℝ} (hsigma : 1 < sigma) :
    hsNormSq (eulerPositivePointedFisherConnection sigma hsigma) =
      eulerPositiveCriticalProjectiveFisherEnergy sigma := by
  rw [eulerPositivePointedFisherConnection,
    hsNormSq_pointedFisherConnection_of_unit_of_orthogonal
      (eulerPositiveStateLp sigma hsigma)
      (eulerPositiveCriticalFisherTangentLp sigma hsigma)
      (norm_eulerPositiveStateLp hsigma)
      (inner_eulerPositiveState_fisherTangent_eq_zero hsigma),
    norm_eulerPositiveCriticalFisherTangentLp_sq hsigma]

/-- **Physical connection four-unit law.**  The Hilbert--Schmidt energy of
the actual positive-integer pointed connection tends to four. -/
theorem tendsto_hsNormSq_eulerPositivePointedFisherConnection :
    Tendsto
      (fun sigma : ℝ =>
        if hsigma : 1 < sigma then
          hsNormSq (eulerPositivePointedFisherConnection sigma hsigma)
        else 0)
      (nhdsWithin 1 (Ioi 1)) (nhds 4) := by
  apply tendsto_eulerPositiveCriticalProjectiveFisherEnergy.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  change 1 < sigma at hsigma
  rw [dif_pos hsigma,
    hsNormSq_eulerPositivePointedFisherConnection hsigma]

/-- One oriented sharp logarithmic cutoff corner of the actual full-Euler
pointed connection. -/
def eulerPositiveFisherLowerBoundary
    (sigma T : ℝ) (hsigma : 1 < sigma) :
    EulerPositiveL2 →L[ℂ] EulerPositiveL2 :=
  cutoffLowerBoundary
    (lpCoordinateProjection (eulerPositiveLogCutoffSet T))
    (eulerPositivePointedFisherConnection sigma hsigma)

/-- The global squarefree-times-square unitary transports the actual
positive-Euler lower corner to the affine joint lower corner.  This is an
operator equality retaining both pointed-connection summands. -/
theorem dyadicSquarefreeSquareUnitary_eulerPositiveFisherLowerBoundary
    {sigma T : ℝ} (hsigma : 1 < sigma) :
    lpReindexConjugate dyadicSquarefreeSquareEquiv
        (eulerPositiveFisherLowerBoundary sigma T hsigma) =
      cutoffLowerBoundary
        (lpCoordinateProjection (dyadicSquarefreeAffineCutoffSet T))
        (pointedFisherConnection
          (dyadicSquarefreeSquareUnitary
            (eulerPositiveStateLp sigma hsigma))
          (dyadicSquarefreeSquareUnitary
            (eulerPositiveCriticalFisherTangentLp sigma hsigma))) := by
  exact dyadicSquarefreeSquareUnitary_fisherLowerBoundary T
    (eulerPositiveStateLp sigma hsigma)
    (eulerPositiveCriticalFisherTangentLp sigma hsigma)

/-- The affine joint presentation preserves the complete
Hilbert--Schmidt energy of every physical full-Euler lower corner. -/
theorem hsNormSq_dyadicSquarefree_eulerPositiveFisherLowerBoundary
    {sigma T : ℝ} (hsigma : 1 < sigma) :
    hsNormSq
        (cutoffLowerBoundary
          (lpCoordinateProjection (dyadicSquarefreeAffineCutoffSet T))
          (pointedFisherConnection
            (dyadicSquarefreeSquareUnitary
              (eulerPositiveStateLp sigma hsigma))
            (dyadicSquarefreeSquareUnitary
              (eulerPositiveCriticalFisherTangentLp sigma hsigma)))) =
      hsNormSq (eulerPositiveFisherLowerBoundary sigma T hsigma) := by
  exact hsNormSq_dyadicSquarefreeAffine_fisherLowerBoundary T
    (eulerPositiveStateLp sigma hsigma)
    (eulerPositiveCriticalFisherTangentLp sigma hsigma)

/-- **Physical infinite source-codiagonal contraction.**  Every contraction
on the full positive-integer Euler Hilbert space produces a joined lower-corner
reporter whose pairing with the actual Euler Fisher source costs at most half
of that source corner's Hilbert--Schmidt energy.  The contraction may mix both
sharp-cutoff sectors; no commutation, finite-rank, or compactness hypothesis is
used. -/
theorem norm_sq_hsInner_eulerPositiveFisherLowerBoundary_joinedReporter_le_half
    {sigma T : ℝ} (hsigma : 1 < sigma)
    (D : EulerPositiveL2 →L[ℂ] EulerPositiveL2)
    (hD : ‖D‖ ≤ 1) :
    ‖hsInner
        (eulerPositiveFisherLowerBoundary sigma T hsigma)
        (infiniteFisherOneCornerJoinedReporter
          (lpCoordinateProjection (eulerPositiveLogCutoffSet T))
          D
          (eulerPositiveStateLp sigma hsigma))‖ ^ (2 : ℕ) ≤
      (1 / 2 : ℝ) *
        hsNormSq (eulerPositiveFisherLowerBoundary sigma T hsigma) := by
  apply norm_sq_hsInner_infiniteFisherOneCornerJoinedReporter_le_half
  · exact
      ((pointedFisherConnection_isHilbertSchmidt
          (eulerPositiveStateLp sigma hsigma)
          (eulerPositiveCriticalFisherTangentLp sigma hsigma)).comp_right
        (lpCoordinateProjection (eulerPositiveLogCutoffSet T))).comp_left
        (1 - lpCoordinateProjection (eulerPositiveLogCutoffSet T))
  · exact lpCoordinateProjection_idempotent _
  · exact lpCoordinateProjection_selfAdjoint _
  · exact norm_eulerPositiveStateLp hsigma
  · exact hD

end RHTower
