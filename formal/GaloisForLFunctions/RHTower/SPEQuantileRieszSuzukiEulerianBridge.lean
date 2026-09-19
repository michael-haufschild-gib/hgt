import GaloisForLFunctions.RHTower.SPEQuantileRieszSourceTransport
import GaloisForLFunctions.RHTower.SuzukiEulerianOutgoingChargeRigidity

/-!
# Exact SP-E--Suzuki Eulerian charge bridge

The labelled SP-E quantile--Riesz current and the Suzuki Eulerian discrepancy are not independent
sources of cancellation.  After their literal normalizations they share the completed outgoing
charge, with only Suzuki's already bounded polar--lattice residual left over.  This module records
the exact equality and the two quantitative transfers without taking a prime or polar absolute
value before the source has been assembled.
-/

namespace RHTower

open GaloisForLFunctions.RHTower

noncomputable section

/-- The normalized labelled SP-E transport is exactly the completed outgoing charge. -/
theorem speCompletedQuantileRieszTransport_div_two_mul_eq_completedOutgoingCharge
    {M : ℕ} (hM : 2 ≤ M) :
    speCompletedQuantileRieszTransport M / (2 * (M : ℝ)) =
      unitRieszCoherentCompletedOutgoingCharge M := by
  have hMR : (M : ℝ) ≠ 0 := by positivity
  calc
    speCompletedQuantileRieszTransport M / (2 * (M : ℝ)) =
        (speCompletedQuantileRieszTransport M / (M : ℝ)) / 2 := by
          field_simp [hMR]
    _ = criticalMellinChebyshevResolventSource (Real.log M) / 2 := by
      rw [speCompletedQuantileRieszTransport_div_eq_resolvent_source hM]
    _ = unitRieszCoherentCompletedOutgoingCharge M := by
      exact (unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half hM).symm

/-- Exact literal-source comparison: the Suzuki Eulerian discrepancy is negative normalized
SP-E transport plus its source-free polar--lattice residual. -/
theorem suzukiEulerianCompletedOutgoingDiscrepancy_eq_neg_speTransport_add_residual
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiEulerianCompletedOutgoingDiscrepancy N =
      -speCompletedQuantileRieszTransport (N + 1) / (2 * ((N + 1 : ℕ) : ℝ)) +
        suzukiEulerianCompletedOutgoingResidual N := by
  rw [suzukiEulerianCompletedOutgoingDiscrepancy_eq_neg_charge_add_residual hN,
    ← speCompletedQuantileRieszTransport_div_two_mul_eq_completedOutgoingCharge (by omega)]
  rw [neg_div]

/-- SP-E controls the Suzuki discrepancy with only the explicitly bounded source-free residual. -/
theorem abs_suzukiEulerianCompletedOutgoingDiscrepancy_le_abs_speTransport_add
    {N : ℕ} (hN : 2 ≤ N) :
    |suzukiEulerianCompletedOutgoingDiscrepancy N| ≤
      |speCompletedQuantileRieszTransport (N + 1) / (2 * ((N + 1 : ℕ) : ℝ))| +
        5 + |suzukiEulerianCoherentBoundaryAnchor| := by
  rw [suzukiEulerianCompletedOutgoingDiscrepancy_eq_neg_speTransport_add_residual hN]
  calc
    |-speCompletedQuantileRieszTransport (N + 1) / (2 * ((N + 1 : ℕ) : ℝ)) +
        suzukiEulerianCompletedOutgoingResidual N| ≤
        |speCompletedQuantileRieszTransport (N + 1) / (2 * ((N + 1 : ℕ) : ℝ))| +
          |suzukiEulerianCompletedOutgoingResidual N| := by
      simpa only [neg_div, abs_neg] using abs_add_le
        (-speCompletedQuantileRieszTransport (N + 1) / (2 * ((N + 1 : ℕ) : ℝ)))
        (suzukiEulerianCompletedOutgoingResidual N)
    _ ≤ |speCompletedQuantileRieszTransport (N + 1) / (2 * ((N + 1 : ℕ) : ℝ))| +
        (5 + |suzukiEulerianCoherentBoundaryAnchor|) :=
      by linarith [abs_suzukiEulerianCompletedOutgoingResidual_le N]
    _ = _ := by ring

/-- Conversely, the literal SP-E transport is controlled by the Suzuki discrepancy up to exactly
the same source-free residual.  Hence these routes have one common unbounded arithmetic charge. -/
theorem abs_speTransport_le_abs_suzukiEulerianCompletedOutgoingDiscrepancy_add
    {N : ℕ} (hN : 2 ≤ N) :
    |speCompletedQuantileRieszTransport (N + 1) / (2 * ((N + 1 : ℕ) : ℝ))| ≤
      |suzukiEulerianCompletedOutgoingDiscrepancy N| +
        5 + |suzukiEulerianCoherentBoundaryAnchor| := by
  have hsource :=
    suzukiEulerianCompletedOutgoingDiscrepancy_eq_neg_speTransport_add_residual hN
  have hrewrite : speCompletedQuantileRieszTransport (N + 1) /
      (2 * ((N + 1 : ℕ) : ℝ)) =
      suzukiEulerianCompletedOutgoingResidual N -
        suzukiEulerianCompletedOutgoingDiscrepancy N := by
    have hsource' : suzukiEulerianCompletedOutgoingDiscrepancy N =
        -(speCompletedQuantileRieszTransport (N + 1) /
          (2 * ((N + 1 : ℕ) : ℝ))) +
          suzukiEulerianCompletedOutgoingResidual N := by
      simpa only [neg_div] using hsource
    linarith
  rw [hrewrite]
  calc
    |suzukiEulerianCompletedOutgoingResidual N -
        suzukiEulerianCompletedOutgoingDiscrepancy N| ≤
        |suzukiEulerianCompletedOutgoingResidual N| +
          |suzukiEulerianCompletedOutgoingDiscrepancy N| := abs_sub _ _
    _ ≤ _ := by
      linarith [abs_suzukiEulerianCompletedOutgoingResidual_le N]

end

end RHTower
