import GaloisForLFunctions.RHTower.Sieve.MaynardCommonModePhaseExtraction
import GaloisForLFunctions.RHTower.Sieve.MaynardLowOrdinateDerivativeReceiver

/-!
# Exact derivative reserve in Route T's common-mode phase window

The phase-extraction window lies below the derivative-count seam for every Route-T large value
with `alpha >= 3/4`.  Its reserve is small—set by the long-factor deficit—so the fixed
`T^(1/25)` bookkeeping used elsewhere is insufficient.  This file proves arbitrary positive
polylog absorption and retains half of that exact reserve in the canonical derivative receiver.
It does not claim a phase-aware selection theorem; that is the remaining analytic obstacle.
-/

noncomputable section
namespace RHTower.Sieve

open Filter Topology

/-- Every fixed-polylog cost in the low-ordinate derivative receiver is eventually smaller than
an arbitrary prescribed positive power. -/
theorem eventually_maynardLowOrdinateDerivative_cost_absorbed
    (eta : ℝ) (heta : 0 < eta) (q : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ C U : ℝ, ∀ E : ℕ,
      0 ≤ C → C ≤ 600 * Real.log T →
      1 ≤ U → U ≤ maynardLowOrdinateComplementWidthConstant * T ^ (8 : ℕ) →
      E ≤ maynardLowOrdinateComplementPolylogExponent →
      (2 * (C ^ 2 * (12 * maynardLowOrdinateComplementWidthConstant ^ 2 *
          (1 + Real.log U) ^ (E + 2)))) * (Real.log T) ^ q ≤
        T ^ eta := by
  let W : ℝ := maynardLowOrdinateComplementWidthConstant
  let E0 : ℕ := maynardLowOrdinateComplementPolylogExponent + 2
  let B0 : ℝ := 9 + |Real.log W|
  let K0 : ℝ := 24 * 600 ^ 2 * W ^ 2 * B0 ^ E0
  let eps : ℝ := eta / 2
  have heps : 0 < eps := by
    dsimp only [eps]
    linarith
  have hW : 1 ≤ W := maynardLowOrdinateComplementWidthConstant_one_le
  have hWpos : 0 < W := zero_lt_one.trans_le hW
  have hB0 : 1 ≤ B0 := by
    dsimp only [B0]
    linarith [abs_nonneg (Real.log W)]
  have hK0 : 0 < K0 := by
    dsimp only [K0]
    positivity
  have hconst : ∀ᶠ T : ℝ in atTop, K0 ≤ T ^ eps :=
    (tendsto_rpow_atTop heps).eventually_ge_atTop K0
  filter_upwards [RHTower.burnolEventually_log_pow_le_rpow heps (q + E0 + 2),
    hconst, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Filter.eventually_ge_atTop (1 : ℝ)] with T hlogPow hconstT hlogT hT
  intro C U E hC0 hC hU hUscale hE
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hlog0 : 0 ≤ Real.log T := zero_le_one.trans hlogT
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have hT8pos : 0 < T ^ (8 : ℕ) := pow_pos hTpos _
  have hlogU : Real.log U ≤ Real.log W + 8 * Real.log T := by
    calc
      Real.log U ≤ Real.log (W * T ^ (8 : ℕ)) :=
        Real.log_le_log hUpos hUscale
      _ = Real.log W + Real.log (T ^ (8 : ℕ)) := by
        rw [Real.log_mul hWpos.ne' hT8pos.ne']
      _ = Real.log W + 8 * Real.log T := by
        rw [Real.log_pow]
        norm_num
  have hbase : 1 + Real.log U ≤ B0 * Real.log T := by
    have hlogW : Real.log W ≤ |Real.log W| * Real.log T := by
      calc
        Real.log W ≤ |Real.log W| := le_abs_self _
        _ ≤ |Real.log W| * Real.log T := by
          nlinarith [abs_nonneg (Real.log W)]
    dsimp only [B0]
    nlinarith
  have hbase1 : 1 ≤ 1 + Real.log U := by
    linarith [Real.log_nonneg hU]
  have hBLog1 : 1 ≤ B0 * Real.log T :=
    one_le_mul_of_one_le_of_one_le hB0 hlogT
  have hE2 : E + 2 ≤ E0 := by
    dsimp only [E0]
    omega
  have hpowBase : (1 + Real.log U) ^ (E + 2) ≤
      (B0 * Real.log T) ^ E0 := by
    calc
      (1 + Real.log U) ^ (E + 2) ≤ (B0 * Real.log T) ^ (E + 2) :=
        pow_le_pow_left₀ (zero_le_one.trans hbase1) hbase _
      _ ≤ (B0 * Real.log T) ^ E0 := pow_le_pow_right₀ hBLog1 hE2
  have hCsq : C ^ 2 ≤ (600 * Real.log T) ^ 2 :=
    pow_le_pow_left₀ hC0 hC 2
  have hpoly :
      (2 * (C ^ 2 * (12 * W ^ 2 *
          (1 + Real.log U) ^ (E + 2)))) * (Real.log T) ^ q ≤
        K0 * (Real.log T) ^ (q + E0 + 2) := by
    calc
      (2 * (C ^ 2 * (12 * W ^ 2 *
          (1 + Real.log U) ^ (E + 2)))) * (Real.log T) ^ q ≤
        (2 * ((600 * Real.log T) ^ 2 *
          (12 * W ^ 2 * (B0 * Real.log T) ^ E0))) *
            (Real.log T) ^ q := by gcongr
      _ = K0 * (Real.log T) ^ (q + E0 + 2) := by
        dsimp only [K0]
        rw [show (600 * Real.log T) ^ 2 =
          600 ^ 2 * (Real.log T) ^ 2 by rw [mul_pow]]
        rw [show (B0 * Real.log T) ^ E0 =
          B0 ^ E0 * (Real.log T) ^ E0 by rw [mul_pow]]
        rw [show (Real.log T) ^ (q + E0 + 2) =
          (Real.log T) ^ q * (Real.log T) ^ E0 *
            (Real.log T) ^ 2 by rw [pow_add, pow_add]]
        ring
  have hpowNonneg : 0 ≤ T ^ eps := Real.rpow_nonneg hTpos.le _
  calc
    (2 * (C ^ 2 * (12 * W ^ 2 *
        (1 + Real.log U) ^ (E + 2)))) * (Real.log T) ^ q ≤
      K0 * (Real.log T) ^ (q + E0 + 2) := hpoly
    _ ≤ T ^ eps * T ^ eps :=
      mul_le_mul hconstT hlogPow (pow_nonneg hlog0 _) hpowNonneg
    _ = T ^ eta := by
      rw [← Real.rpow_add hTpos]
      dsimp only [eps]
      congr 1
      ring

/-- The phase window's reserve pays arbitrary fixed logarithmic receiver costs with half the
reserve left over. -/
theorem eventually_routeT_phaseExtraction_derivative_cost_absorbed (q : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ C U : ℝ, ∀ E : ℕ,
      0 ≤ C → C ≤ 600 * Real.log T →
      1 ≤ U → U ≤ maynardLowOrdinateComplementWidthConstant * T ^ (8 : ℕ) →
      E ≤ maynardLowOrdinateComplementPolylogExponent →
      (2 * (C ^ 2 * (12 * maynardLowOrdinateComplementWidthConstant ^ 2 *
          (1 + Real.log U) ^ (E + 2)))) * (Real.log T) ^ q ≤
        T ^ (routeTPhaseExtractionDerivativeReserve / 2) := by
  exact eventually_maynardLowOrdinateDerivative_cost_absorbed
    (routeTPhaseExtractionDerivativeReserve / 2)
    (half_pos routeT_phaseExtraction_derivativeReserve_pos) q

/-- Canonical derivative excision is strictly inside the first receiver throughout the common-mode
phase window, after paying the exact arbitrary-polylog budget. -/
theorem routeT_phaseExtraction_derivativeComplement_normalized_first
    {R Q T mu tau alpha s : ℝ} {q : ℕ}
    (hT : 1 ≤ T) (hQ : 0 ≤ Q)
    (hmu0 : 0 ≤ mu) (hmu : mu < routeTPhaseExtractionReferenceMu)
    (halphaLo : 3 / 4 ≤ alpha) (halphaHi : alpha ≤ 1)
    (htau : tau ≤ mu) (hs : 0 ≤ s)
    (hcount : R ≤ Q *
      (T ^ maynardDerivativeComplementHeightExponent tau alpha s +
        T ^ maynardDerivativeComplementLengthExponent tau alpha))
    (hcost : (2 * Q) * (Real.log T) ^ q ≤
      T ^ (routeTPhaseExtractionDerivativeReserve / 2)) :
    R * (Real.log T) ^ q ≤
      T ^ (mu * (1 - alpha) - routeTPhaseExtractionDerivativeReserve / 2) := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT
  obtain ⟨hheight, hlength⟩ :=
    routeT_phaseExtraction_derivativeComplement_margin
      hmu0 hmu halphaLo halphaHi htau hs
  have hheightPow := Real.rpow_le_rpow_of_exponent_le hT hheight
  have hlengthPow := Real.rpow_le_rpow_of_exponent_le hT hlength
  have hraw : R ≤ (2 * Q) *
      T ^ (mu * (1 - alpha) - routeTPhaseExtractionDerivativeReserve) := by
    calc
      R ≤ Q *
          (T ^ maynardDerivativeComplementHeightExponent tau alpha s +
            T ^ maynardDerivativeComplementLengthExponent tau alpha) := hcount
      _ ≤ Q *
          (T ^ (mu * (1 - alpha) - routeTPhaseExtractionDerivativeReserve) +
            T ^ (mu * (1 - alpha) - routeTPhaseExtractionDerivativeReserve)) := by
          gcongr
      _ = (2 * Q) *
          T ^ (mu * (1 - alpha) - routeTPhaseExtractionDerivativeReserve) := by ring
  have hpow0 : 0 ≤ T ^
      (mu * (1 - alpha) - routeTPhaseExtractionDerivativeReserve) :=
    Real.rpow_nonneg hT0.le _
  calc
    R * (Real.log T) ^ q ≤
        ((2 * Q) * T ^
          (mu * (1 - alpha) - routeTPhaseExtractionDerivativeReserve)) *
          (Real.log T) ^ q :=
      mul_le_mul_of_nonneg_right hraw (pow_nonneg hlog0 q)
    _ = ((2 * Q) * (Real.log T) ^ q) *
        T ^ (mu * (1 - alpha) - routeTPhaseExtractionDerivativeReserve) := by ring
    _ ≤ T ^ (routeTPhaseExtractionDerivativeReserve / 2) *
        T ^ (mu * (1 - alpha) - routeTPhaseExtractionDerivativeReserve) :=
      mul_le_mul_of_nonneg_right hcost hpow0
    _ = T ^ (mu * (1 - alpha) - routeTPhaseExtractionDerivativeReserve / 2) := by
      rw [← Real.rpow_add hT0]
      congr 1
      ring

end RHTower.Sieve
