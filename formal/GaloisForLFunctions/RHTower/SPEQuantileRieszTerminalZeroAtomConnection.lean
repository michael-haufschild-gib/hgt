import GaloisForLFunctions.RHTower.SPEQuantileRieszPhysicalWallMovingOffsetTransport
import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarCovarianceExteriorProducer

/-!
# Literal terminal connection at zero SP-E admissions

At an integer which is not a prime power, neither the signed exterior covariance nor the full
ordered quadratic displacement debt changes.  The strict-cross matched--quantile source is thus
exactly stationary.  The canonical completed source nevertheless moves: its entire increment is
the increment of the literal terminal completion, which is exactly the physical endpoint quartic.

This identifies a source-defined discrete terminal connection.  At each zero atom it cancels the
moving physical-wall offset transport exactly, and its increment has the same linear lower bound
as the endpoint quartic.  This is a finite identity, not a cofinal bound or an SP-E/P landing:
prime-power updates and the source-selected two-port realization remain open.
-/

noncomputable section

namespace RHTower

/-- At a zero von-Mangoldt admission, every newly created ordered displacement-debt pair has a
zero factor.  Thus the full nonnegative debt is stationary, independently of the signed
covariance channel. -/
theorem ccmActualHeadMatchedQuantileParabolicDisplacementDebtSum_succ_eq_of_not_isPrimePow
    (K : ℕ) (hK : ¬ IsPrimePow (K + 3)) :
    ccmActualHeadMatchedQuantileParabolicDisplacementDebtSum (K + 1) =
      ccmActualHeadMatchedQuantileParabolicDisplacementDebtSum K := by
  have hweight : criticalMellinAtomWeight (K + 3) = 0 :=
    criticalMellinAtomWeight_eq_zero_of_not_isPrimePow hK
  have hright (m : ℕ) :
      ccmActualHeadMatchedQuantileParabolicDisplacementDebt (m + 2) (K + 3) = 0 := by
    unfold ccmActualHeadMatchedQuantileParabolicDisplacementDebt
    rw [hweight]
    ring
  have hleft (n : ℕ) :
      ccmActualHeadMatchedQuantileParabolicDisplacementDebt (K + 3) (n + 2) = 0 := by
    unfold ccmActualHeadMatchedQuantileParabolicDisplacementDebt
    rw [hweight]
    ring
  classical
  have hinner (m : ℕ) (hm : m ∈ Finset.range (K + 1)) :
      (∑ n ∈ (Finset.range (K + 2)).erase m,
        ccmActualHeadMatchedQuantileParabolicDisplacementDebt (m + 2) (n + 2)) =
        ∑ n ∈ (Finset.range (K + 1)).erase m,
          ccmActualHeadMatchedQuantileParabolicDisplacementDebt (m + 2) (n + 2) := by
    have hset : (Finset.range (K + 2)).erase m =
        insert (K + 1) ((Finset.range (K + 1)).erase m) := by
      have hm' : m < K + 1 := Finset.mem_range.mp hm
      ext n
      simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_insert]
      omega
    rw [hset, Finset.sum_insert]
    · simpa [Nat.add_assoc] using hright m
    · simp
  have hlast :
      (∑ n ∈ (Finset.range (K + 2)).erase (K + 1),
        ccmActualHeadMatchedQuantileParabolicDisplacementDebt ((K + 1) + 2) (n + 2)) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simpa [Nat.add_assoc] using hleft n
  unfold ccmActualHeadMatchedQuantileParabolicDisplacementDebtSum
  rw [show K + 2 = (K + 1) + 1 by omega, Finset.sum_range_succ]
  rw [hlast]
  simp only [add_zero]
  apply Finset.sum_congr rfl
  intro m hm
  exact hinner m hm

/-- **Debt-admission law.**  Adding one literal head creates exactly its two ordered debt
interactions with retained history.  The formula retains both orientations, so it is valid at
prime powers as well as at zero atoms. -/
theorem ccmActualHeadMatchedQuantileParabolicDisplacementDebtSum_succ_sub
    (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicDisplacementDebtSum (K + 1) -
      ccmActualHeadMatchedQuantileParabolicDisplacementDebtSum K =
      ∑ m ∈ Finset.range (K + 1),
        (ccmActualHeadMatchedQuantileParabolicDisplacementDebt (m + 2) (K + 3) +
          ccmActualHeadMatchedQuantileParabolicDisplacementDebt (K + 3) (m + 2)) := by
  classical
  have hinner (m : ℕ) (hm : m ∈ Finset.range (K + 1)) :
      (∑ n ∈ (Finset.range (K + 2)).erase m,
        ccmActualHeadMatchedQuantileParabolicDisplacementDebt (m + 2) (n + 2)) =
        (∑ n ∈ (Finset.range (K + 1)).erase m,
          ccmActualHeadMatchedQuantileParabolicDisplacementDebt (m + 2) (n + 2)) +
          ccmActualHeadMatchedQuantileParabolicDisplacementDebt (m + 2) (K + 3) := by
    have hset : (Finset.range (K + 2)).erase m =
        insert (K + 1) ((Finset.range (K + 1)).erase m) := by
      have hm' : m < K + 1 := Finset.mem_range.mp hm
      ext n
      simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_insert]
      omega
    rw [hset, Finset.sum_insert]
    · ring
    · simp
  have hlast :
      (∑ n ∈ (Finset.range (K + 2)).erase (K + 1),
        ccmActualHeadMatchedQuantileParabolicDisplacementDebt ((K + 1) + 2) (n + 2)) =
        ∑ n ∈ Finset.range (K + 1),
          ccmActualHeadMatchedQuantileParabolicDisplacementDebt (K + 3) (n + 2) := by
    have hset : (Finset.range (K + 2)).erase (K + 1) = Finset.range (K + 1) := by
      ext n
      simp only [Finset.mem_erase, Finset.mem_range]
      omega
    rw [hset]

  unfold ccmActualHeadMatchedQuantileParabolicDisplacementDebtSum
  rw [show K + 2 = (K + 1) + 1 by omega, Finset.sum_range_succ, hlast]
  have hsum :
      (∑ m ∈ Finset.range (K + 1), ∑ n ∈ (Finset.range (K + 2)).erase m,
        ccmActualHeadMatchedQuantileParabolicDisplacementDebt (m + 2) (n + 2)) =
        ∑ m ∈ Finset.range (K + 1),
          ((∑ n ∈ (Finset.range (K + 1)).erase m,
            ccmActualHeadMatchedQuantileParabolicDisplacementDebt (m + 2) (n + 2)) +
            ccmActualHeadMatchedQuantileParabolicDisplacementDebt (m + 2) (K + 3)) := by
    apply Finset.sum_congr rfl
    intro m hm
    exact hinner m hm
  rw [hsum, Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

/-- The complete strict-cross source is stationary at every zero atom: both of its independent
channels, exterior covariance and displacement debt, are stationary. -/
theorem ccmActualHeadMatchedQuantileParabolicStrictCross_succ_eq_of_not_isPrimePow
    (K : ℕ) (hK : ¬ IsPrimePow (K + 3)) :
    ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal (K + 1))
        (ccmActualHeadMatchedQuantileParabolicSourceBoundary (K + 1)) =
      ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
        (ccmActualHeadMatchedQuantileParabolicSourceBoundary K) := by
  rw [ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary_eq_neg_two_mul_covariance_sub_debt,
    ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary_eq_neg_two_mul_covariance_sub_debt,
    ccmActualHeadMatchedQuantileParabolicDisplacementCentroidCovariance_succ_eq_of_not_isPrimePow K hK,
    ccmActualHeadMatchedQuantileParabolicDisplacementDebtSum_succ_eq_of_not_isPrimePow K hK]

/-- The literal terminal interaction and form at the canonical physical clock.  It is the unique
term removed from the strict-cross source to obtain the completed source current. -/
def speQuantileRieszCanonicalTerminalConnection (K : ℕ) : ℝ :=
  2 * ccmParabolicPairing (ccmActualHeadQuantileParabolicAggregate K)
      (ccmActualHeadQuantileParabolicTerminal K (Real.log ((K : ℝ) + 3))) +
    ccmParabolicForm
      (ccmActualHeadQuantileParabolicTerminal K (Real.log ((K : ℝ) + 3)))

/-- The canonical completed current is the strict-cross source less its literal terminal
connection. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent_eq_strictCross_sub_terminalConnection
    (K : ℕ) :
    ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent K =
      ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
          (ccmActualHeadMatchedQuantileParabolicSourceBoundary K) -
        speQuantileRieszCanonicalTerminalConnection K := by
  unfold ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent
    speQuantileRieszCanonicalTerminalConnection
  exact ccmActualHeadMatchedCompletedQuantileParabolic_pairing_eq_finite_sub_terminal K
    (Real.log ((K : ℝ) + 3))

/-- One-step transport of the literal completed source at the moving physical wall.  The offset
is not frozen: each endpoint is evaluated at its own physical-wall offset. -/
def speQuantileRieszPhysicalWallDynamicSourceTransport (K : ℕ) : ℝ :=
  ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent
      (speQuantileRieszPhysicalWallOffset (K + 1)) (K + 1) -
    ccmActualHeadMatchedCompletedQuantileParabolicSourceRelativeOffsetCurrent
      (speQuantileRieszPhysicalWallOffset K) K

/-- **All-head discrete connection law.**  Physical moving-wall transport plus the literal
terminal-connection increment is exactly the update of the strict-cross covariance--debt source.
Thus the terminal is the covariant correction which transports the physical completed current
back to its full signed arithmetic history; no correction is selected externally. -/
theorem speQuantileRieszPhysicalWallDynamicSourceTransport_add_terminalConnectionIncrement_eq_strictCross_increment
    (K : ℕ) :
    speQuantileRieszPhysicalWallDynamicSourceTransport K +
      (speQuantileRieszCanonicalTerminalConnection (K + 1) -
        speQuantileRieszCanonicalTerminalConnection K) =
      ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal (K + 1))
          (ccmActualHeadMatchedQuantileParabolicSourceBoundary (K + 1)) -
        ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
          (ccmActualHeadMatchedQuantileParabolicSourceBoundary K) := by
  unfold speQuantileRieszPhysicalWallDynamicSourceTransport
  rw [speQuantileRieszPhysicalWallOffset_current_eq_canonical,
    speQuantileRieszPhysicalWallOffset_current_eq_canonical,
    ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent_eq_strictCross_sub_terminalConnection,
    ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent_eq_strictCross_sub_terminalConnection]
  ring

/-- The all-head connection curvature is exactly the increment of the existing signed
covariance--debt hard core. -/
theorem speQuantileRieszPhysicalWallDynamicSourceTransport_add_terminalConnectionIncrement_eq_covarianceDebt_increment
    (K : ℕ) :
    speQuantileRieszPhysicalWallDynamicSourceTransport K +
      (speQuantileRieszCanonicalTerminalConnection (K + 1) -
        speQuantileRieszCanonicalTerminalConnection K) =
      -2 * (ccmActualHeadMatchedQuantileParabolicDisplacementCentroidCovariance (K + 1) -
        ccmActualHeadMatchedQuantileParabolicDisplacementCentroidCovariance K) -
        (ccmActualHeadMatchedQuantileParabolicDisplacementDebtSum (K + 1) -
          ccmActualHeadMatchedQuantileParabolicDisplacementDebtSum K) := by
  rw [speQuantileRieszPhysicalWallDynamicSourceTransport_add_terminalConnectionIncrement_eq_strictCross_increment,
    ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary_eq_neg_two_mul_covariance_sub_debt,
    ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary_eq_neg_two_mul_covariance_sub_debt]
  ring

/-- **Literal prime-power curvature law.**  The unresolved all-head connection curvature is one
signed exterior interaction of the admitted source atom with retained history, minus its two
ordered nonnegative debt interactions.  No term is omitted, and no prime-power hypothesis is
needed for this exact finite identity. -/
theorem speQuantileRieszPhysicalWallDynamicSourceTransport_add_terminalConnectionIncrement_eq_exteriorHistory_sub_debtAdmission
    (K : ℕ) :
    speQuantileRieszPhysicalWallDynamicSourceTransport K +
      (speQuantileRieszCanonicalTerminalConnection (K + 1) -
        speQuantileRieszCanonicalTerminalConnection K) =
      -2 * criticalMellinAtomWeight (K + 3) *
        (ccmActualHeadTwoMomentExteriorPairing
            (ccmActualHeadMatchedQuantileAtomExteriorDirection (K + 3))
            (ccmActualHeadMatchedQuantileCentroidDisplacementMomentVector K) +
          ccmActualHeadMatchedPolarCentroid (K + 3) *
            ccmActualHeadTwoMomentExteriorPairing
              (ccmActualHeadMatchedQuantileDisplacementMomentVector K)
              (ccmActualHeadMatchedQuantileAtomExteriorDirection (K + 3))) -
        ∑ m ∈ Finset.range (K + 1),
          (ccmActualHeadMatchedQuantileParabolicDisplacementDebt (m + 2) (K + 3) +
            ccmActualHeadMatchedQuantileParabolicDisplacementDebt (K + 3) (m + 2)) := by
  rw [speQuantileRieszPhysicalWallDynamicSourceTransport_add_terminalConnectionIncrement_eq_covarianceDebt_increment,
    ccmActualHeadMatchedQuantileParabolicDisplacementCentroidCovariance_succ_sub_eq_exteriorHistory,
    ccmActualHeadMatchedQuantileParabolicDisplacementDebtSum_succ_sub]
  ring

/-- **Zero-atom terminal-connection law.**  Once the strict-cross history is stationary, the
literal terminal completion carries exactly the increasing endpoint-quartic increment. -/
theorem speQuantileRieszCanonicalTerminalConnection_succ_sub_eq_endpointQuartic_succ_sub_of_not_isPrimePow
    (K : ℕ) (hK : ¬ IsPrimePow (K + 3)) :
    speQuantileRieszCanonicalTerminalConnection (K + 1) -
      speQuantileRieszCanonicalTerminalConnection K =
      ccmActualHeadMatchedCompletedQuantileParabolicCanonicalEndpointQuartic (K + 1) -
        ccmActualHeadMatchedCompletedQuantileParabolicCanonicalEndpointQuartic K := by
  have hcurrent :=
    ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent_succ_sub_eq_endpointQuartic_sub_of_not_isPrimePow
      K hK
  rw [ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent_eq_strictCross_sub_terminalConnection,
    ccmActualHeadMatchedCompletedQuantileParabolicCanonicalClockCurrent_eq_strictCross_sub_terminalConnection,
    ccmActualHeadMatchedQuantileParabolicStrictCross_succ_eq_of_not_isPrimePow K hK] at hcurrent
  linarith

/-- The terminal connection cannot be treated as an asymptotically negligible gauge: at every
zero atom after the initial head, its exact increment has a linear lower bound. -/
theorem speQuantileRieszCanonicalTerminalConnection_succ_sub_lower_of_not_isPrimePow
    (K : ℕ) (hK : ¬ IsPrimePow (K + 3)) (hKone : 1 ≤ K) :
    (2 / 9 : ℝ) * (K + 3) ≤
      speQuantileRieszCanonicalTerminalConnection (K + 1) -
        speQuantileRieszCanonicalTerminalConnection K := by
  rw [speQuantileRieszCanonicalTerminalConnection_succ_sub_eq_endpointQuartic_succ_sub_of_not_isPrimePow K hK]
  exact ccmActualHeadMatchedCompletedQuantileParabolicCanonicalEndpointQuartic_succ_sub_lower_at_head K hKone

/-- **Physical moving-wall cancellation.**  The literal terminal connection increment cancels
the dynamic transport forced by changing from a stationary source-relative clock to the physical
wall.  This is an exact finite identity at every zero atom, with no target-selected correction. -/
theorem speQuantileRieszPhysicalWall_dynamicOffset_transport_add_terminalConnectionIncrement_eq_zero_of_not_isPrimePow
    (K : ℕ) (hK : ¬ IsPrimePow (K + 3)) :
    ((Real.exp (speQuantileRieszPhysicalWallOffset K / 2) *
          ccmActualHeadQuantilePolarCoordinate (K + 4) - 2) ^ 4 -
        (Real.exp (speQuantileRieszPhysicalWallOffset (K + 1) / 2) *
          ccmActualHeadQuantilePolarCoordinate (K + 4) - 2) ^ 4) / 12 +
      (speQuantileRieszCanonicalTerminalConnection (K + 1) -
        speQuantileRieszCanonicalTerminalConnection K) = 0 := by
  rw [speQuantileRieszPhysicalWall_dynamicOffset_transport_eq_endpointQuartic_sub_of_not_isPrimePow K hK,
    speQuantileRieszCanonicalTerminalConnection_succ_sub_eq_endpointQuartic_succ_sub_of_not_isPrimePow K hK]
  ring

end RHTower
