import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantilePolarParabolicSourceRelativeOffsetClock
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

At zero ordinate clock, it also identifies the literal P-G186 primitive Burnol column at every
active `(prime, depth)` label with its exact arithmetic-amplitude-weighted SP-E cubic ray, and
identifies pairwise half-line entries with the corresponding cubic Cauchy edge.  This is not a
full P-G186 incidence map: it does not construct the required signed-word/history intertwiner,
match the SP-E plaquette coefficients to that history, or assemble a cofinal graph-closed
transport.
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

/-- At zero ordinate clock, a literal P-G186 primitive Burnol column is exactly its arithmetic
amplitude times the SP-E cubic generator ray.  This is an equality of actual half-line columns,
not merely of their scalar pairings. -/
theorem routePPrimitiveBurnolWindowFeature_zero_eq_speQuantileRieszCubicRay
    (pe : Nat.Primes × ℕ) (L : ℝ) :
    routePPrimitiveBurnolWindowFeature pe 0 L =
      finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe) *
        (primeGammaCauchyCubicRayFeature (xiGammaEulerPrimitiveLogFrequency pe) L : ℂ) := by
  calc
    routePPrimitiveBurnolWindowFeature pe 0 L =
        finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe) *
          xiWardResolvedRadialGeneratorMode
            ((xiGammaEulerPrimitiveLogFrequency pe : ℂ) + Complex.I * (0 : ℂ)) L :=
      routePPrimitiveBurnolWindowFeature_eq_resolvedRadialGeneratorMode pe 0 L
    _ = finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe) *
          xiWardResolvedRadialGeneratorMode (xiGammaEulerPrimitiveLogFrequency pe : ℂ) L := by
      congr 2
      norm_num
    _ = finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe) *
          (primeGammaCauchyCubicRayFeature (xiGammaEulerPrimitiveLogFrequency pe) L : ℂ) := by
      rw [primeGammaCauchyCubicRayFeature_eq_xiWardResolvedRadialGeneratorMode]

/-- Every active SP-E prime-power atom has a literal P primitive `(prime, depth)` label whose
zero-clock P-G186 column is the corresponding cubic generator ray with its exact arithmetic
amplitude. -/
theorem isPrimePow_exists_routePPrimitiveBurnolZeroClockRay
    (n : ℕ) (hn : IsPrimePow n) :
    ∃ pe : Nat.Primes × ℕ,
      xiGammaEulerValuationNat pe = n ∧
      xiGammaEulerPrimitiveLogFrequency pe = Real.log n ∧
      ∀ L : ℝ,
        routePPrimitiveBurnolWindowFeature pe 0 L =
          finiteVonMangoldtDepthOneAmplitude n *
            (primeGammaCauchyCubicRayFeature (Real.log n) L : ℂ) := by
  rcases (isPrimePow_iff_pow_succ n).mp hn with ⟨p, k, hp, hpow⟩
  let p' : Nat.Primes := ⟨p, Nat.prime_iff.mpr hp⟩
  refine ⟨(p', k), ?_, ?_, ?_⟩
  · simpa [xiGammaEulerValuationNat, p'] using hpow
  · rw [xiGammaEulerPrimitiveLogFrequency]
    congr 1
    simp [xiGammaEulerValuationNat, p', hpow]
  · intro L
    rw [routePPrimitiveBurnolWindowFeature_zero_eq_speQuantileRieszCubicRay]
    simp [xiGammaEulerValuationNat, xiGammaEulerPrimitiveLogFrequency, p', hpow]

/-- **Actual finite incidence bridge.** Any pair of active SP-E prime-power labels admits
literal zero-clock P-G186 primitive columns whose exact half-line pairing is their
von-Mangoldt-amplitude-weighted real cubic Cauchy edge.  No pair is collapsed to a diagonal or
scalar surrogate. -/
theorem isPrimePow_pair_exists_routePPrimitiveBurnol_zero_clock_entry
    (m n : ℕ) (hm : IsPrimePow m) (hn : IsPrimePow n) :
    ∃ pe tau : Nat.Primes × ℕ,
      xiGammaEulerValuationNat pe = m ∧
      xiGammaEulerValuationNat tau = n ∧
      (∫ L : ℝ in Ioi 0,
        star (routePPrimitiveBurnolWindowFeature pe 0 L) *
          routePPrimitiveBurnolWindowFeature tau 0 L) =
        finiteVonMangoldtDepthOneAmplitude m *
          (primeGammaCauchyCubicEdge (Real.log m) (Real.log n) : ℂ) *
            star (finiteVonMangoldtDepthOneAmplitude n) := by
  obtain ⟨pe, hpe, hpeLog, _⟩ := isPrimePow_exists_routePPrimitiveBurnolZeroClockRay m hm
  obtain ⟨tau, htau, htauLog, _⟩ := isPrimePow_exists_routePPrimitiveBurnolZeroClockRay n hn
  refine ⟨pe, tau, hpe, htau, ?_⟩
  rw [integral_star_routePPrimitiveBurnolWindowFeature_mul]
  rw [hpe, htau, hpeLog, htauLog]
  simp only [sub_self]
  rw [routePBaseCauchyCubicKernel_one_zero_eq_primeGammaCauchyCubicEdge]

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
