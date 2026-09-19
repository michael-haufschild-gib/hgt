import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarParabolicSourceRelativeOffsetClock
import GaloisForLFunctions.RHTower.SPEQuantileRieszEndpointRayLaplacePort
import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePPluckerPlaquette

/-!
# Active SP-E quantile cells as literal Route-P endpoint ports

The literal SP-E source is supported exactly at prime powers.  Its outgoing quantile boundary is
therefore stationary at inactive natural-number indices; treating every raw index as a distinct
P port would collapse zero-mass labels and is not source faithful.  This file makes the exact
replacement precise without quotienting any nonzero source coordinate.

At an active prime-power index, the quantile boundary advances strictly.  Below the physical
wall, the corresponding reversed endpoint interval is a nonzero literal P indicator port.  The
mixed SP-E Pluecker plaquette is positive exactly on ordered pairs of such active atoms and is
identically zero whenever either atom is inactive.  Thus every source coordinate capable of
carrying the two-history curvature has a distinct nondegenerate P cell port; no raw zero-mass
label is silently discarded.

This is a coefficient-domain result only.  It does not identify the resulting interval ports
with P-G186's full off-diagonal incidence, nor construct the required signed-word/history
intertwiner or cofinal graph-closed transport.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Every prime-power source atom advances the literal outgoing quantile boundary strictly. -/
theorem ccmOutgoingPrimeQuantileBoundary_lt_succ_of_isPrimePow
    (n : ℕ) (hn : IsPrimePow n) :
    ccmOutgoingPrimeQuantileBoundary n <
      ccmOutgoingPrimeQuantileBoundary (n + 1) := by
  unfold ccmOutgoingPrimeQuantileBoundary
  rw [ccmOutgoingPrimeCumulative_succ]
  have hmass : 0 < criticalMellinAtomWeight n := criticalMellinAtomWeight_pos hn
  have hcum : 0 ≤ ccmOutgoingPrimeCumulative n := ccmOutgoingPrimeCumulative_nonneg n
  gcongr
  linarith

/-- Literal P endpoint port of one source quantile cell, retaining both of its physical
endpoints before any Rayleigh or scalar readout. -/
def speQuantileRieszRoutePActiveQuantileCellEndpointPort (M n : ℕ) : ℝ → ℂ :=
  primeGammaCauchyCubicPositiveIntervalPort
      (Real.log M - ccmOutgoingPrimeQuantileBoundary n) -
    primeGammaCauchyCubicPositiveIntervalPort
      (Real.log M - ccmOutgoingPrimeQuantileBoundary (n + 1))

/-- Below the physical wall, one literal source cell is exactly the indicator of its reversed
P interval.  This is an equality of P functions, not an equality after integration. -/
theorem speQuantileRieszRoutePActiveQuantileCellEndpointPort_eq_indicator
    (M n : ℕ)
    (hwall : ccmOutgoingPrimeQuantileBoundary (n + 1) ≤ Real.log M) :
    speQuantileRieszRoutePActiveQuantileCellEndpointPort M n =
      (Ioc (Real.log M - ccmOutgoingPrimeQuantileBoundary (n + 1))
        (Real.log M - ccmOutgoingPrimeQuantileBoundary n)).indicator (fun _ => (1 : ℂ)) := by
  ext u
  unfold speQuantileRieszRoutePActiveQuantileCellEndpointPort
    primeGammaCauchyCubicPositiveIntervalPort
  have hmono := ccmOutgoingPrimeQuantileBoundary_mono_step n
  have hnext : 0 ≤ Real.log M - ccmOutgoingPrimeQuantileBoundary (n + 1) := by
    linarith
  have hU : Real.log M - ccmOutgoingPrimeQuantileBoundary (n + 1) ≤
      Real.log M - ccmOutgoingPrimeQuantileBoundary n := by linarith
  by_cases hu1 : u ∈ Ioc (0 : ℝ) (Real.log M - ccmOutgoingPrimeQuantileBoundary n)
  · by_cases hu2 : u ∈ Ioc (0 : ℝ)
      (Real.log M - ccmOutgoingPrimeQuantileBoundary (n + 1))
    · have hnot : u ∉ Ioc (Real.log M - ccmOutgoingPrimeQuantileBoundary (n + 1))
          (Real.log M - ccmOutgoingPrimeQuantileBoundary n) := by
        intro hu
        exact (not_lt_of_ge hu2.2) hu.1
      simp [hu1, hu2, hnot]
    · have hleft : Real.log M - ccmOutgoingPrimeQuantileBoundary (n + 1) < u := by
        by_contra h
        exact hu2 ⟨hu1.1, le_of_not_gt h⟩
      have hu : u ∈ Ioc (Real.log M - ccmOutgoingPrimeQuantileBoundary (n + 1))
          (Real.log M - ccmOutgoingPrimeQuantileBoundary n) := ⟨hleft, hu1.2⟩
      simp [hu1, hu2, hu]
  · by_cases hu2 : u ∈ Ioc (0 : ℝ)
      (Real.log M - ccmOutgoingPrimeQuantileBoundary (n + 1))
    · exfalso
      apply hu1
      exact ⟨hu2.1, hu2.2.trans hU⟩
    · have hnot : u ∉ Ioc (Real.log M - ccmOutgoingPrimeQuantileBoundary (n + 1))
          (Real.log M - ccmOutgoingPrimeQuantileBoundary n) := by
        intro hu
        apply hu1
        exact ⟨by linarith [hnext, hu.1], hu.2⟩
      simp [hu1, hu2, hnot]

/-- Every active source cell below the wall remains a nonzero literal P function. -/
theorem speQuantileRieszRoutePActiveQuantileCellEndpointPort_ne_zero_of_isPrimePow
    (M n : ℕ) (hn : IsPrimePow n)
    (hwall : ccmOutgoingPrimeQuantileBoundary (n + 1) ≤ Real.log M) :
    speQuantileRieszRoutePActiveQuantileCellEndpointPort M n ≠ 0 := by
  intro hzero
  have hstrict := ccmOutgoingPrimeQuantileBoundary_lt_succ_of_isPrimePow n hn
  let u : ℝ := (Real.log M - ccmOutgoingPrimeQuantileBoundary (n + 1) +
    (Real.log M - ccmOutgoingPrimeQuantileBoundary n)) / 2
  have hu : u ∈ Ioc (Real.log M - ccmOutgoingPrimeQuantileBoundary (n + 1))
      (Real.log M - ccmOutgoingPrimeQuantileBoundary n) := by
    dsimp [u]
    constructor <;> linarith
  have hvalue := congrFun hzero u
  rw [speQuantileRieszRoutePActiveQuantileCellEndpointPort_eq_indicator M n hwall] at hvalue
  simp [hu] at hvalue

/-- The source two-history plaquette vanishes identically when its new cutoff atom is inactive. -/
theorem ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel_plaquette_eq_zero_of_not_isPrimePow_left
    (K r : ℕ) (hK : ¬ IsPrimePow (K + 3)) :
    ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel (K + 1) (r + 1) -
      ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel (K + 1) r -
        ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel K (r + 1) +
          ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel K r = 0 := by
  rw [ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel_plaquette,
    criticalMellinAtomWeight_eq_zero_of_not_isPrimePow hK]
  ring

/-- The source two-history plaquette vanishes identically when its retained history atom is
inactive. -/
theorem ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel_plaquette_eq_zero_of_not_isPrimePow_right
    (K r : ℕ) (hr : ¬ IsPrimePow (r + 3)) :
    ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel (K + 1) (r + 1) -
      ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel (K + 1) r -
        ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel K (r + 1) +
          ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel K r = 0 := by
  rw [ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel_plaquette,
    criticalMellinAtomWeight_eq_zero_of_not_isPrimePow hr]
  ring

/-- **Exact active-support classification.** On an ordered source pair, the literal SP-E
two-history curvature is strictly positive exactly when both source atoms are prime powers. -/
theorem ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel_plaquette_pos_iff_active
    (K r : ℕ) (hrK : r < K) :
    0 < ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel (K + 1) (r + 1) -
      ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel (K + 1) r -
        ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel K (r + 1) +
          ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel K r ↔
      IsPrimePow (K + 3) ∧ IsPrimePow (r + 3) := by
  constructor
  · intro hpos
    constructor
    · by_contra hK
      rw [ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel_plaquette_eq_zero_of_not_isPrimePow_left
        K r hK] at hpos
      exact (lt_irrefl (0 : ℝ)) hpos
    · by_contra hr
      rw [ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel_plaquette_eq_zero_of_not_isPrimePow_right
        K r hr] at hpos
      exact (lt_irrefl (0 : ℝ)) hpos
  · rintro ⟨hK, hr⟩
    rw [ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel_plaquette]
    apply mul_pos (mul_pos (criticalMellinAtomWeight_pos hK)
      (criticalMellinAtomWeight_pos hr))
    apply sub_pos.mpr
    apply strictMono_ccmActualHeadMatchedPolarCentroid_shift_two
    omega

end RHTower
