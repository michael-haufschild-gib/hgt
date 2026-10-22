import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantilePolarParabolicCompletedSourceBoundary
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadOutgoingQuantileStieltjesCrossing
import GaloisForLFunctions.RHTower.SPEQuantileRieszEndpointRayLaplacePort
import GaloisForLFunctions.RHTower.SPEQuantileRieszParabolicBridge

/-!
# Source-determined terminal error gate for the SP-E/P two-port

The literal SP-E terminal interval starts at quantile boundary `N`, while the native
threshold-centred completed error is indexed by the time head through `N + 1`.  The missing atom
is not bookkeeping: it gives the exact sign gate of the terminal physical-wall interval.

For the actual finite head `N = K + 3`, the terminal mass coordinate is
`threshold - completedError - atomWeight N`.  Hence the completed error plus that literal atom
selects, with no assumed sign, which of the two already constructed P ports carries the terminal:
the positive-scale P eigenray or the finite reflected-wall ray.  Both branches retain their exact
endpoint length and remain source terms; neither is estimated away.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- **Actual-terminal mass law.**  The mass coordinate of the completed codiagonal at its
literal time endpoint is the threshold-centred completed error with the necessarily retained
`K + 3` atom correction.  This is the exact off-by-one relation between the physical terminal
and the time-clock discrepancy. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal_zero_eq_threshold_sub_error_sub_atom
    (K : ℕ) :
    ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal K
        (Real.log (K + 3)) 0 =
      2 * (1 - Real.exp (-(Real.log (K + 3) / 2))) -
        criticalMellinCompletedError (Real.log (K + 3)) -
          criticalMellinAtomWeight (K + 3) := by
  have hN : (0 : ℝ) < K + 3 := by positivity
  have hcast : (K : ℝ) + 3 = ((K + 3 : ℕ) : ℝ) := by norm_num
  have hterminal := quantileTerminalMass_eq_completedError_sub_threshold
    (Real.log (K + 3))
  rw [hcast, Real.exp_log (by positivity : (0 : ℝ) < (K + 3 : ℕ)), Nat.floor_natCast,
    ccmOutgoingPrimeCumulative_succ] at hterminal
  rw [ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal_zero,
    ccmActualHeadQuantilePolarCoordinate_eq_two_add_cumulative]
  rw [hcast]
  unfold ccmActualHeadPolarMassCoordinate
  linarith

/-- The terminal begins on or before the physical SP-E wall exactly when the completed error
plus its indispensable current atom clears the threshold.  This is the source gate for the
positive P eigenray port. -/
theorem ccmOutgoingPrimeQuantileBoundary_le_log_iff_completedError_add_atom_ge_threshold
    (K : ℕ) :
    ccmOutgoingPrimeQuantileBoundary (K + 3) ≤ Real.log (K + 3) ↔
      2 * (1 - Real.exp (-(Real.log (K + 3) / 2))) ≤
        criticalMellinCompletedError (Real.log (K + 3)) +
          criticalMellinAtomWeight (K + 3) := by
  have hCeq :=
    ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal_zero_eq_threshold_sub_error_sub_atom K
  rw [ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal_zero] at hCeq
  constructor
  · intro h
    have hcoordinate :
        ccmActualHeadPolarMassCoordinate
            (ccmOutgoingPrimeQuantileBoundary (K + 3)) ≤
          ccmActualHeadPolarMassCoordinate (Real.log (K + 3)) := by
      unfold ccmActualHeadPolarMassCoordinate
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (Real.exp_le_exp).mpr (by linarith)
    rw [ccmActualHeadPolarMassCoordinate_quantileBoundary] at hcoordinate
    have hzero : ccmActualHeadQuantilePolarCoordinate (K + 3) -
        ccmActualHeadPolarMassCoordinate (Real.log (K + 3)) ≤ 0 := by
      linarith
    rw [hCeq] at hzero
    linarith
  · intro h
    have hzero : ccmActualHeadQuantilePolarCoordinate (K + 3) -
        ccmActualHeadPolarMassCoordinate (Real.log (K + 3)) ≤ 0 := by
      rw [hCeq]
      linarith
    have hcoordinate :
        ccmActualHeadPolarMassCoordinate
            (ccmOutgoingPrimeQuantileBoundary (K + 3)) ≤
          ccmActualHeadPolarMassCoordinate (Real.log (K + 3)) := by
      rw [ccmActualHeadPolarMassCoordinate_quantileBoundary]
      exact sub_nonpos.mp hzero
    unfold ccmActualHeadPolarMassCoordinate at hcoordinate
    have hexp :
        Real.exp (ccmOutgoingPrimeQuantileBoundary (K + 3) / 2) ≤
          Real.exp (Real.log (K + 3) / 2) := by
      linarith
    linarith [(Real.exp_le_exp.mp hexp)]

/-- The complementary source gate: the terminal begins on or beyond the physical wall exactly
when completed error plus the literal current atom is below threshold.  This selects the compact
reflected P port. -/
theorem ccmLog_le_outgoingPrimeQuantileBoundary_iff_completedError_add_atom_le_threshold
    (K : ℕ) :
    Real.log (K + 3) ≤ ccmOutgoingPrimeQuantileBoundary (K + 3) ↔
      criticalMellinCompletedError (Real.log (K + 3)) +
          criticalMellinAtomWeight (K + 3) ≤
        2 * (1 - Real.exp (-(Real.log (K + 3) / 2))) := by
  have hCeq :=
    ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal_zero_eq_threshold_sub_error_sub_atom K
  rw [ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal_zero] at hCeq
  constructor
  · intro h
    have hcoordinate :
        ccmActualHeadPolarMassCoordinate (Real.log (K + 3)) ≤
          ccmActualHeadPolarMassCoordinate
            (ccmOutgoingPrimeQuantileBoundary (K + 3)) := by
      unfold ccmActualHeadPolarMassCoordinate
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (Real.exp_le_exp).mpr (by linarith)
    rw [ccmActualHeadPolarMassCoordinate_quantileBoundary] at hcoordinate
    have hzero : 0 ≤ ccmActualHeadQuantilePolarCoordinate (K + 3) -
        ccmActualHeadPolarMassCoordinate (Real.log (K + 3)) := by
      linarith
    rw [hCeq] at hzero
    linarith
  · intro h
    have hzero : 0 ≤ ccmActualHeadQuantilePolarCoordinate (K + 3) -
        ccmActualHeadPolarMassCoordinate (Real.log (K + 3)) := by
      rw [hCeq]
      linarith
    have hcoordinate :
        ccmActualHeadPolarMassCoordinate (Real.log (K + 3)) ≤
          ccmActualHeadPolarMassCoordinate
            (ccmOutgoingPrimeQuantileBoundary (K + 3)) := by
      rw [ccmActualHeadPolarMassCoordinate_quantileBoundary]
      exact sub_nonneg.mp hzero
    unfold ccmActualHeadPolarMassCoordinate at hcoordinate
    have hexp : Real.exp (Real.log (K + 3) / 2) ≤
        Real.exp (ccmOutgoingPrimeQuantileBoundary (K + 3) / 2) := by
      linarith
    linarith [(Real.exp_le_exp.mp hexp)]

/-- **Positive terminal P port.**  When the source error gate places the literal terminal before
the physical wall, the full terminal parabolic Riesz readout is exactly the positive-scale
Route-P cubic eigenray port.  The displayed nonnegative interval length is part of the result. -/
theorem speQuantileRieszActualTerminal_eq_positiveEndpointPort_of_errorGate
    (K : ℕ)
    (hgate :
      2 * (1 - Real.exp (-(Real.log (K + 3) / 2))) ≤
        criticalMellinCompletedError (Real.log (K + 3)) +
          criticalMellinAtomWeight (K + 3)) :
    0 ≤ Real.log (K + 3) - ccmOutgoingPrimeQuantileBoundary (K + 3) ∧
      speQuantileRieszParabolicReadout (K + 3)
          (ccmActualHeadQuantileParabolicTerminal K (Real.log (K + 3))) =
        2 * ((K + 3 : ℕ) : ℝ) * Real.sqrt ((K + 3 : ℕ) : ℝ) *
          ∫ s in (1 : ℝ)..(3 / 2 : ℝ),
            ∫ u in (0 : ℝ)..Real.log (K + 3) -
                ccmOutgoingPrimeQuantileBoundary (K + 3),
              primeGammaCauchyCubicRayFeature s u := by
  have hwall :=
    ccmOutgoingPrimeQuantileBoundary_le_log_iff_completedError_add_atom_ge_threshold K |>.mpr
      hgate
  have hN : 0 < K + 3 := by omega
  have hcast : (K : ℝ) + 3 = ((K + 3 : ℕ) : ℝ) := by norm_num
  constructor
  · linarith
  · rw [hcast]
    rw [speQuantileRieszParabolicReadout_terminal]
    simpa only [hcast, sub_self] using
      speQuantileRieszWeightedIntervalIntegral_eq_endpointRayTwoPort hN
        (ccmOutgoingPrimeQuantileBoundary (K + 3)) (Real.log ((K + 3 : ℕ) : ℝ))

/-- **Reflected terminal P port.**  When the complementary error gate places the literal
terminal beyond the physical wall, its full oriented readout is exactly the compact reflected
Route-P ray port.  The source interval is retained with its positive reflected length. -/
theorem speQuantileRieszActualTerminal_eq_reflectedEndpointPort_of_errorGate
    (K : ℕ)
    (hgate : criticalMellinCompletedError (Real.log (K + 3)) +
        criticalMellinAtomWeight (K + 3) ≤
      2 * (1 - Real.exp (-(Real.log (K + 3) / 2)))) :
    0 ≤ ccmOutgoingPrimeQuantileBoundary (K + 3) - Real.log (K + 3) ∧
      speQuantileRieszParabolicReadout (K + 3)
          (ccmActualHeadQuantileParabolicTerminal K (Real.log (K + 3))) =
        2 * ((K + 3 : ℕ) : ℝ) * Real.sqrt ((K + 3 : ℕ) : ℝ) *
          ∫ s in (1 : ℝ)..(3 / 2 : ℝ),
            ∫ u in (0 : ℝ)..ccmOutgoingPrimeQuantileBoundary (K + 3) -
                Real.log (K + 3),
              primeGammaCauchyCubicRayFeature (-s) u := by
  have hwall :=
    ccmLog_le_outgoingPrimeQuantileBoundary_iff_completedError_add_atom_le_threshold K |>.mpr
      hgate
  have hcast : (K : ℝ) + 3 = ((K + 3 : ℕ) : ℝ) := by norm_num
  constructor
  · linarith
  · rw [hcast]
    rw [speQuantileRieszParabolicReadout_terminal]
    calc
      (∫ h in ccmOutgoingPrimeQuantileBoundary (K + 3)..Real.log ((K + 3 : ℕ) : ℝ),
          Real.exp (h / 2) * speQuantileRieszProfile (K + 3) h) =
          -(∫ h in Real.log ((K + 3 : ℕ) : ℝ)..
            ccmOutgoingPrimeQuantileBoundary (K + 3),
            Real.exp (h / 2) * speQuantileRieszProfile (K + 3) h) := by
              rw [intervalIntegral.integral_symm]
      _ = _ := by
        rw [speQuantileRieszWeightedWallRemainder_eq_reflectedEndpointPort
          (M := K + 3) (by omega)]
        ring

end RHTower
