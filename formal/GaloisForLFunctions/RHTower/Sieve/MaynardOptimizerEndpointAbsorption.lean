import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedCellFibreHuxley
import GaloisForLFunctions.RHTower.Sieve.MaynardFixedPolylogEndpointAbsorption

/-!
# Endpoint absorption for optimizer-scale Huxley

Optimizer crossing only gives `Y <= T`, rather than the old `Y <= T^(1367/2160)`.  The same
Route-T endpoint shift still dominates every fixed polylogarithm at this larger scale.  One
hundredth of the global endpoint deficit pays the complete Huxley energy constant.
-/


noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex Filter Topology

/-- Fixed-polylog base comparison for any polynomial length exponent. -/
theorem log_maynardFixedPolylogBase_le_edge_of_scale
    (A : ℝ) {T mu : ℝ} (hT : 0 < T) (hlogT : 1 ≤ Real.log T)
    {N : ℕ} (hN : 1 ≤ N) (hmu : mu ≤ 19 / 9)
    (hNscale : (N : ℝ) ≤ T ^ mu) :
    Real.log (1 + Real.log (maynardRaisedWidthConstant * (N : ℝ))) ≤
      (maynardRaisedWidthConstant + 1) *
        routeTContourEdgeLogEnvelope A (3 * T) := by
  let E : ℝ := maynardLongPolylogEnvelope N
  let B : ℝ := 1 + Real.log (maynardRaisedWidthConstant * (N : ℝ))
  have hwidth1 : 1 ≤ maynardRaisedWidthConstant := maynardRaisedWidthConstant_one_le
  have hwidth0 : 0 < maynardRaisedWidthConstant := zero_lt_one.trans_le hwidth1
  have hNR1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNR0 : (0 : ℝ) < N := zero_lt_one.trans_le hNR1
  have hprod1 : 1 ≤ maynardRaisedWidthConstant * (N : ℝ) :=
    one_le_mul_of_one_le_of_one_le hwidth1 hNR1
  have hB1 : 1 ≤ B := by
    dsimp only [B]
    linarith [Real.log_nonneg hprod1]
  have hE1 : 1 ≤ E := by
    dsimp only [E]
    exact one_le_maynardLongPolylogEnvelope N
  have hNtop : (N : ℝ) ≤ ((2 * (N + 1) : ℕ) : ℝ) := by
    exact_mod_cast (by omega : N ≤ 2 * (N + 1))
  have hlogN : Real.log (N : ℝ) ≤ Real.log (((2 * (N + 1) : ℕ) : ℝ)) :=
    Real.log_le_log hNR0 hNtop
  have hlogWidth : Real.log maynardRaisedWidthConstant ≤
      maynardRaisedWidthConstant - 1 :=
    Real.log_le_sub_one_of_pos hwidth0
  have hBE : B ≤ maynardRaisedWidthConstant * E := by
    have hsplit : Real.log (maynardRaisedWidthConstant * (N : ℝ)) =
        Real.log maynardRaisedWidthConstant + Real.log (N : ℝ) := by
      rw [Real.log_mul hwidth0.ne' hNR0.ne']
    have hfirst : B ≤ maynardRaisedWidthConstant + E - 1 := by
      dsimp only [B, E, maynardLongPolylogEnvelope]
      rw [hsplit]
      linarith
    have hsecond : maynardRaisedWidthConstant + E - 1 ≤
        maynardRaisedWidthConstant * E := by
      linarith [mul_nonneg (sub_nonneg.mpr hwidth1) (sub_nonneg.mpr hE1)]
    exact hfirst.trans hsecond
  have hlogE : Real.log E ≤ routeTContourEdgeLogEnvelope A (3 * T) := by
    dsimp only [E]
    exact log_maynardLongPolylogEnvelope_le_routeTContourEdgeLogEnvelope
      hN hT hlogT hmu hNscale
  have hlogBE : Real.log B ≤
      Real.log maynardRaisedWidthConstant + Real.log E := by
    have hlog := Real.log_le_log (zero_lt_one.trans_le hB1) hBE
    rw [Real.log_mul hwidth0.ne' (zero_lt_one.trans_le hE1).ne'] at hlog
    exact hlog
  have hedge1 : 1 ≤ routeTContourEdgeLogEnvelope A (3 * T) :=
    one_le_routeTContourEdgeLogEnvelope A (by positivity)
  have hwidthEdge : Real.log maynardRaisedWidthConstant ≤
      maynardRaisedWidthConstant * routeTContourEdgeLogEnvelope A (3 * T) := by
    calc
      Real.log maynardRaisedWidthConstant ≤ maynardRaisedWidthConstant :=
        Real.log_le_self (le_trans (by norm_num) hwidth1)
      _ ≤ maynardRaisedWidthConstant * routeTContourEdgeLogEnvelope A (3 * T) := by
        nlinarith
  calc
    Real.log B ≤ Real.log maynardRaisedWidthConstant + Real.log E := hlogBE
    _ ≤ maynardRaisedWidthConstant * routeTContourEdgeLogEnvelope A (3 * T) +
        routeTContourEdgeLogEnvelope A (3 * T) := add_le_add hwidthEdge hlogE
    _ = (maynardRaisedWidthConstant + 1) *
        routeTContourEdgeLogEnvelope A (3 * T) := by ring

/-- Logarithm of the complete optimizer-scale energy cost. -/
theorem log_maynardOptimizerHuxleyCost_le_edge
    (A C : ℝ) (hC : 0 < C)
    {T mu : ℝ} (hT : 0 < T) (hlogT : 1 ≤ Real.log T)
    {N e : ℕ} (hN : 1 ≤ N) (hmu : mu ≤ 19 / 9)
    (hNscale : (N : ℝ) ≤ T ^ mu)
    (he : e ≤ maynardFixedPolylogExponentBound) :
    Real.log (C *
        (1 + Real.log (maynardRaisedWidthConstant * (N : ℝ))) ^ e) ≤
      (|Real.log C| +
        (maynardFixedPolylogExponentBound : ℝ) *
          (maynardRaisedWidthConstant + 1)) *
        routeTContourEdgeLogEnvelope A (3 * T) := by
  let B : ℝ := 1 + Real.log (maynardRaisedWidthConstant * (N : ℝ))
  let E : ℝ := routeTContourEdgeLogEnvelope A (3 * T)
  have hwidth1 : 1 ≤ maynardRaisedWidthConstant := maynardRaisedWidthConstant_one_le
  have hNR1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hprod1 : 1 ≤ maynardRaisedWidthConstant * (N : ℝ) :=
    one_le_mul_of_one_le_of_one_le hwidth1 hNR1
  have hB1 : 1 ≤ B := by
    dsimp only [B]
    linarith [Real.log_nonneg hprod1]
  have hlogB0 : 0 ≤ Real.log B := Real.log_nonneg hB1
  have hlogB : Real.log B ≤ (maynardRaisedWidthConstant + 1) * E := by
    simpa only [B, E] using
      log_maynardFixedPolylogBase_le_edge_of_scale A hT hlogT hN hmu hNscale
  have hE1 : 1 ≤ E := by
    dsimp only [E]
    exact one_le_routeTContourEdgeLogEnvelope A (by positivity)
  have hCterm : Real.log C ≤ |Real.log C| * E := by
    have habs : Real.log C ≤ |Real.log C| := le_abs_self _
    have hmul : |Real.log C| ≤ |Real.log C| * E := by
      nlinarith [abs_nonneg (Real.log C)]
    exact habs.trans hmul
  have hecast : (e : ℝ) ≤ (maynardFixedPolylogExponentBound : ℝ) := by
    exact_mod_cast he
  have heterm : (e : ℝ) * Real.log B ≤
      (maynardFixedPolylogExponentBound : ℝ) *
        ((maynardRaisedWidthConstant + 1) * E) := by
    exact mul_le_mul hecast hlogB hlogB0 (Nat.cast_nonneg _)
  have hlogeq : Real.log (C * B ^ e) = Real.log C + (e : ℝ) * Real.log B := by
    rw [Real.log_mul hC.ne' (pow_ne_zero _ (zero_lt_one.trans_le hB1).ne'),
      Real.log_pow]
  rw [show 1 + Real.log (maynardRaisedWidthConstant * (N : ℝ)) = B by rfl,
    hlogeq]
  calc
    Real.log C + (e : ℝ) * Real.log B ≤
        |Real.log C| * E +
          (maynardFixedPolylogExponentBound : ℝ) *
            ((maynardRaisedWidthConstant + 1) * E) := add_le_add hCterm heterm
    _ = (|Real.log C| +
        (maynardFixedPolylogExponentBound : ℝ) *
          (maynardRaisedWidthConstant + 1)) * E := by ring

/-- Complete optimizer-scale fixed-polylog cost is paid by one hundredth of endpoint deficit. -/
theorem eventually_maynardOptimizerHuxleyCost_absorbed (A : ℝ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ N e : ℕ, 1 ≤ N → (N : ℝ) ≤ T →
      e ≤ maynardFixedPolylogExponentBound →
      2 * (6121 : ℝ) ^ 2 * maynardRaisedWidthConstant *
          (1 + Real.log (maynardRaisedWidthConstant * (N : ℝ))) ^ e *
          maynardEnergyEnvelopeConstant ≤
        T ^ (routeTEndpointGlobalDeficit A T / 100) := by
  let C : ℝ := 2 * (6121 : ℝ) ^ 2 * maynardRaisedWidthConstant *
    maynardEnergyEnvelopeConstant
  let K : ℝ := |Real.log C| +
    (maynardFixedPolylogExponentBound : ℝ) * (maynardRaisedWidthConstant + 1)
  let c0 : ℝ := (7 / 6000 : ℝ)
  have hC : 0 < C := by
    dsimp only [C]
    exact mul_pos
      (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos (by norm_num)))
        (lt_of_lt_of_le zero_lt_one maynardRaisedWidthConstant_one_le))
      maynardEnergyEnvelopeConstant_pos
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    exact add_nonneg (abs_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _)
        (add_nonneg (le_trans (by norm_num) maynardRaisedWidthConstant_one_le) zero_le_one))
  have hc0 : 0 < c0 := by norm_num
  have hthree : Tendsto (fun T : ℝ => 3 * T) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) tendsto_id
  have hfactor0 : 0 ≤ 2 * K / c0 :=
    div_nonneg (mul_nonneg (by norm_num) hK0) hc0.le
  have habsorbRaw := eventually_const_mul_routeTContourEdgeLogEnvelope_le_shiftGain
    A (2 * K / c0) hfactor0
  have habsorb := hthree.eventually habsorbRaw
  filter_upwards [habsorb, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop 3] with T habsorbT hlogT hT
  intro N e hN hNscale he
  have hT0 : 0 < T := by linarith
  have hlog3T : Real.log (3 * T) ≤ 2 * Real.log T := by
    have hthreeSq : 3 * T ≤ T ^ (2 : ℕ) := by nlinarith
    have hlog := Real.log_le_log (by positivity : 0 < 3 * T) hthreeSq
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    exact hlog
  have hshift0 : 0 ≤ routeTContourShiftEnvelope A (3 * T) :=
    (routeTContourShiftEnvelope_pos A (by positivity)).le
  have htransfer : routeTContourShiftEnvelope A (3 * T) * Real.log (3 * T) ≤
      2 * routeTContourShiftEnvelope A (3 * T) * Real.log T := by
    calc
      routeTContourShiftEnvelope A (3 * T) * Real.log (3 * T) ≤
          routeTContourShiftEnvelope A (3 * T) * (2 * Real.log T) :=
        mul_le_mul_of_nonneg_left hlog3T hshift0
      _ = 2 * routeTContourShiftEnvelope A (3 * T) * Real.log T := by ring
  have hKedge : K * routeTContourEdgeLogEnvelope A (3 * T) ≤
      c0 * routeTContourShiftEnvelope A (3 * T) * Real.log T := by
    have hboth := habsorbT.trans htransfer
    have htwice :
        2 * ((K * routeTContourEdgeLogEnvelope A (3 * T)) / c0) ≤
          2 * (routeTContourShiftEnvelope A (3 * T) * Real.log T) := by
      calc
        2 * ((K * routeTContourEdgeLogEnvelope A (3 * T)) / c0) =
            2 * K / c0 * routeTContourEdgeLogEnvelope A (3 * T) := by
          field_simp [hc0.ne']
        _ ≤ 2 * routeTContourShiftEnvelope A (3 * T) * Real.log T := hboth
        _ = 2 * (routeTContourShiftEnvelope A (3 * T) * Real.log T) := by ring
    have hdiv : (K * routeTContourEdgeLogEnvelope A (3 * T)) / c0 ≤
        routeTContourShiftEnvelope A (3 * T) * Real.log T := by linarith
    have hmul := (div_le_iff₀ hc0).mp hdiv
    calc
      K * routeTContourEdgeLogEnvelope A (3 * T) ≤
          (routeTContourShiftEnvelope A (3 * T) * Real.log T) * c0 := hmul
      _ = c0 * routeTContourShiftEnvelope A (3 * T) * Real.log T := by ring
  have hlogcost := log_maynardOptimizerHuxleyCost_le_edge
    A C hC hT0 hlogT hN (by norm_num : (1 : ℝ) ≤ 19 / 9)
      (by simpa using hNscale) he
  have hlogtarget :
      Real.log (C *
        (1 + Real.log (maynardRaisedWidthConstant * (N : ℝ))) ^ e) ≤
        (routeTEndpointGlobalDeficit A T / 100) * Real.log T := by
    calc
      Real.log (C *
          (1 + Real.log (maynardRaisedWidthConstant * (N : ℝ))) ^ e) ≤
          K * routeTContourEdgeLogEnvelope A (3 * T) := by
        simpa only [K] using hlogcost
      _ ≤ c0 * routeTContourShiftEnvelope A (3 * T) * Real.log T := hKedge
      _ = (routeTEndpointGlobalDeficit A T / 100) * Real.log T := by
        dsimp only [c0, routeTEndpointGlobalDeficit, routeTEndpointCommonDeficit]
        ring
  have hbase : 0 < 1 + Real.log (maynardRaisedWidthConstant * (N : ℝ)) := by
    have hwidthN : 1 ≤ maynardRaisedWidthConstant * (N : ℝ) := by
      apply one_le_mul_of_one_le_of_one_le maynardRaisedWidthConstant_one_le
      exact_mod_cast hN
    linarith [Real.log_nonneg hwidthN]
  have hcost0 : 0 < C *
      (1 + Real.log (maynardRaisedWidthConstant * (N : ℝ))) ^ e := by positivity
  have hcost : C *
      (1 + Real.log (maynardRaisedWidthConstant * (N : ℝ))) ^ e ≤
        T ^ (routeTEndpointGlobalDeficit A T / 100) := by
    rw [← Real.exp_log hcost0, Real.rpow_def_of_pos hT0]
    apply Real.exp_le_exp.mpr
    simpa only [mul_comm] using hlogtarget
  simpa [C, mul_assoc, mul_comm, mul_left_comm] using hcost

/-- Lowering amplitude by one percent of its gap pays optimizer and endpoint costs while staying
below the universal Route-T adjacent-power cap at the original amplitude. -/
theorem maynard_optimizer_amplitude_reserve_transfer
    {alpha alpha0 d : ℝ}
    (halphaLo : 997 / 1000 ≤ alpha) (halphaHi : alpha < 1)
    (_hd : 0 ≤ d) (hdGap : d ≤ 1 - alpha)
    (halpha0 : alpha0 = alpha - (1 - alpha) / 100) :
    (19 / 10 : ℝ) * (1 - alpha0) / alpha0 + d / 100 ≤
      2 * (1 - alpha) / alpha := by
  have halpha : 0 < alpha := by linarith
  have hgap : 0 < 1 - alpha := by linarith
  have halpha0pos : 0 < alpha0 := by rw [halpha0]; linarith
  have hdCost : d / 100 ≤ (1 - alpha) / 100 := by
    exact div_le_div_of_nonneg_right hdGap (by norm_num)
  have hgap0eq : 1 - alpha0 = (101 / 100 : ℝ) * (1 - alpha) := by
    rw [halpha0]
    ring
  have hcoeff : (1919 / 1000 : ℝ) / alpha0 + 1 / 100 ≤ 2 / alpha := by
    rw [show (1919 / 1000 : ℝ) / alpha0 + 1 / 100 =
      ((1919 / 1000 : ℝ) + alpha0 / 100) / alpha0 by
        field_simp [halpha0pos.ne']]
    rw [div_le_div_iff₀ halpha0pos halpha]
    rw [halpha0]
    nlinarith
  have hmain : (19 / 10 : ℝ) * (1 - alpha0) / alpha0 +
      (1 - alpha) / 100 ≤ 2 * (1 - alpha) / alpha := by
    have hmul := mul_le_mul_of_nonneg_left hcoeff hgap.le
    calc
      (19 / 10 : ℝ) * (1 - alpha0) / alpha0 + (1 - alpha) / 100 =
          (1 - alpha) * ((1919 / 1000 : ℝ) / alpha0 + 1 / 100) := by
        rw [hgap0eq]
        ring
      _ ≤ (1 - alpha) * (2 / alpha) := hmul
      _ = 2 * (1 - alpha) / alpha := by ring
  linarith

/-- The transferred optimizer reserve lands in Route T's exact first/second dichotomy. -/
theorem routeT_optimizer_amplitude_reserve_first_or_second
    {mu alpha alpha0 d : ℝ}
    (hmuLo : 4 / 3 ≤ mu) (hmuHi : mu ≤ 19 / 9)
    (halphaLo : 997 / 1000 ≤ alpha)
    (halphaHi : alpha ≤ 1 - maynardLongGlobalAmplitudeDeficit)
    (hd : 0 ≤ d) (hdGap : d ≤ 1 - alpha)
    (halpha0 : alpha0 = alpha - (1 - alpha) / 100) :
    (19 / 10 : ℝ) * (1 - alpha0) / alpha0 + d / 100 ≤
        mu * (1 - alpha) ∨
      (19 / 10 : ℝ) * (1 - alpha0) / alpha0 + d / 100 ≤
        1 + mu * (1 + routeTGapMomentNu - 2 * alpha) := by
  have halphaLt : alpha < 1 := by
    have hd0 := maynardLongGlobalAmplitudeDeficit_pos
    linarith
  have htransfer := maynard_optimizer_amplitude_reserve_transfer
    halphaLo halphaLt hd hdGap halpha0
  rcases routeT_adjacent_optimizer_first_or_second
    hmuLo hmuHi (by linarith : 3 / 4 ≤ alpha) halphaHi with hfirst | hsecond
  · exact Or.inl (htransfer.trans hfirst)
  · exact Or.inr (htransfer.trans hsecond)

/-- **Moving-endpoint crossing dichotomy.**  Retaining the exact crossing length removes the
fixed-deficit hypothesis.  Either its width plus one percent reserve fits the first target, or
crossing geometry forces `mu < 1.87`, where the second target has a fixed positive margin. -/
theorem routeT_exact_crossing_first_or_second_unbounded
    {mu alpha alpha0 beta r d : ℝ}
    (hmuLo : 4 / 3 ≤ mu)
    (halphaLo : 997 / 1000 ≤ alpha) (halphaHi : alpha < 1)
    (halpha0 : alpha0 = alpha - (1 - alpha) / 100)
    (hbetaHi : beta ≤ 5 / 12)
    (hr : r < maynardHuxleyOptimizer alpha0 + beta)
    (_hd : 0 ≤ d) (hdGap : d ≤ 1 - alpha) :
    2 * r * (1 - alpha) + d / 100 ≤ mu * (1 - alpha) ∨
      2 * r * (1 - alpha) + d / 100 ≤
        1 + mu * (1 + routeTGapMomentNu - 2 * alpha) := by
  have hgap : 0 < 1 - alpha := by linarith
  have halpha0Lo : 99 / 100 ≤ alpha0 := by rw [halpha0]; linarith
  have htheta : maynardHuxleyOptimizer alpha0 ≤ 25 / 49 := by
    dsimp only [maynardHuxleyOptimizer]
    rw [div_le_iff₀ (by linarith : 0 < 4 * alpha0 - 2)]
    nlinarith
  have hrUpper : r < 545 / 588 := by
    have hfixed : (25 / 49 : ℝ) + 5 / 12 = 545 / 588 := by norm_num
    linarith
  have hdCost : d / 100 ≤ (1 - alpha) / 100 :=
    div_le_div_of_nonneg_right hdGap (by norm_num)
  by_cases hfirst : 2 * r + 1 / 100 ≤ mu
  · left
    have hmul := mul_le_mul_of_nonneg_right hfirst hgap.le
    nlinarith
  · right
    have hmuUpper : mu < 187 / 100 := by
      have : mu < 2 * r + 1 / 100 := lt_of_not_ge hfirst
      linarith
    let q := 1 + routeTGapMomentNu - 2 * alpha
    have hdlong := maynardLongGlobalAmplitudeDeficit_lt_one_millionth
    have hqneg : q < 0 := by
      dsimp only [q, routeTGapMomentNu]
      have hdpos := maynardLongGlobalAmplitudeDeficit_pos
      linarith
    have hqlo : (-501 / 1000 : ℝ) ≤ q := by
      dsimp only [q, routeTGapMomentNu]
      linarith
    have hmulQ : (187 / 100 : ℝ) * (-501 / 1000) ≤ mu * q := by
      have hlo := mul_le_mul_of_nonneg_left hqlo (by norm_num : (0 : ℝ) ≤ 187 / 100)
      have hhi := mul_le_mul_of_nonpos_right hmuUpper.le hqneg.le
      exact hlo.trans hhi
    have hlhs : 2 * r * (1 - alpha) + d / 100 ≤ 57 / 10000 := by
      have hrle : r ≤ 545 / 588 := hrUpper.le
      have hgapLe : 1 - alpha ≤ 3 / 1000 := by linarith
      have hr0 : 0 ≤ r := by
        have hmu0 : 0 < mu := by linarith
        by_contra hneg
        have : r < 0 := lt_of_not_ge hneg
        nlinarith
      have hmulR := mul_le_mul hrle hgapLe hgap.le
        (by norm_num : (0 : ℝ) ≤ 545 / 588)
      nlinarith
    have hrhs : 63 / 1000 ≤ 1 + mu * q := by
      nlinarith [hmulQ]
    dsimp only [q] at hrhs
    exact hlhs.trans (by linarith)

/-- Compatibility wrapper on Maynard's historical height range. -/
theorem routeT_exact_crossing_first_or_second
    {mu alpha alpha0 beta r d : ℝ}
    (hmuLo : 4 / 3 ≤ mu) (_hmuHi : mu ≤ 19 / 9)
    (halphaLo : 997 / 1000 ≤ alpha) (halphaHi : alpha < 1)
    (halpha0 : alpha0 = alpha - (1 - alpha) / 100)
    (hbetaHi : beta ≤ 5 / 12)
    (hr : r < maynardHuxleyOptimizer alpha0 + beta)
    (hd : 0 ≤ d) (hdGap : d ≤ 1 - alpha) :
    2 * r * (1 - alpha) + d / 100 ≤ mu * (1 - alpha) ∨
      2 * r * (1 - alpha) + d / 100 ≤
        1 + mu * (1 + routeTGapMomentNu - 2 * alpha) := by
  exact routeT_exact_crossing_first_or_second_unbounded
    hmuLo halphaLo halphaHi halpha0 hbetaHi hr hd hdGap

/-- A fixed logarithmic factor and the canonical raised-polynomial factor are
absorbed by one contour-edge envelope.  This is the reusable logarithmic form
needed when the endpoint reserve is split between analysis and finite entropy. -/
theorem log_maynardOptimizerFixedLogCost_le_edge
    (A C : ℝ) (hC : 0 < C) (q : ℕ)
    {T mu : ℝ} (hT : 0 < T) (hlogT : 1 ≤ Real.log T)
    {N e : ℕ} (hN : 1 ≤ N) (hmu : mu ≤ 19 / 9)
    (hNscale : (N : ℝ) ≤ T ^ mu)
    (he : e ≤ maynardFixedPolylogExponentBound) :
    Real.log (C * (Real.log T) ^ q *
        (1 + Real.log (maynardRaisedWidthConstant * (N : ℝ))) ^ e) ≤
      (|Real.log C| + q +
        (maynardFixedPolylogExponentBound : ℝ) *
          (maynardRaisedWidthConstant + 1)) *
        routeTContourEdgeLogEnvelope A (3 * T) := by
  let B : ℝ := 1 + Real.log (maynardRaisedWidthConstant * (N : ℝ))
  let E : ℝ := routeTContourEdgeLogEnvelope A (3 * T)
  have hlogT0 : 0 < Real.log T := by linarith
  have hwidth1 : 1 ≤ maynardRaisedWidthConstant := maynardRaisedWidthConstant_one_le
  have hNR1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hprod1 : 1 ≤ maynardRaisedWidthConstant * (N : ℝ) :=
    one_le_mul_of_one_le_of_one_le hwidth1 hNR1
  have hB1 : 1 ≤ B := by
    dsimp only [B]
    linarith [Real.log_nonneg hprod1]
  have hlogB0 : 0 ≤ Real.log B := Real.log_nonneg hB1
  have hbase := log_maynardOptimizerHuxleyCost_le_edge
    A C hC hT hlogT hN hmu hNscale he
  have hloglog0 : 0 ≤ Real.log (Real.log T) := Real.log_nonneg hlogT
  have hloglog : Real.log (Real.log T) ≤ E := by
    simpa only [E] using log_log_le_routeTContourEdgeLogEnvelope_three A hT.le hlogT
  have hqterm : (q : ℝ) * Real.log (Real.log T) ≤ (q : ℝ) * E :=
    mul_le_mul_of_nonneg_left hloglog (Nat.cast_nonneg q)
  have hbase' : Real.log (C * B ^ e) ≤
      (|Real.log C| +
        (maynardFixedPolylogExponentBound : ℝ) *
          (maynardRaisedWidthConstant + 1)) * E := by
    simpa only [B, E] using hbase
  have hcost0 : 0 < C * B ^ e := by positivity
  have hlogeq : Real.log (C * (Real.log T) ^ q * B ^ e) =
      Real.log (C * B ^ e) + (q : ℝ) * Real.log (Real.log T) := by
    rw [show C * (Real.log T) ^ q * B ^ e = (C * B ^ e) * (Real.log T) ^ q by ring,
      Real.log_mul hcost0.ne' (pow_ne_zero _ hlogT0.ne'), Real.log_pow]
  rw [show 1 + Real.log (maynardRaisedWidthConstant * (N : ℝ)) = B by rfl,
    hlogeq]
  calc
    Real.log (C * B ^ e) + (q : ℝ) * Real.log (Real.log T) ≤
        (|Real.log C| +
          (maynardFixedPolylogExponentBound : ℝ) *
            (maynardRaisedWidthConstant + 1)) * E + (q : ℝ) * E :=
      add_le_add hbase' hqterm
    _ = (|Real.log C| + q +
        (maynardFixedPolylogExponentBound : ℝ) *
          (maynardRaisedWidthConstant + 1)) * E := by ring

/-- Any fixed logarithmic cost is absorbed by `1 / m` of the moving Route-T
endpoint deficit.  The denominator is explicit so independent costs can be
budgeted before a global finite-colour sum. -/
theorem eventually_maynardOptimizerFixedLogCost_absorbed
    (A C : ℝ) (hC : 0 < C) (q m : ℕ) (hm : 0 < m) :
    ∀ᶠ T : ℝ in atTop,
      ∀ N e : ℕ, 1 ≤ N → (N : ℝ) ≤ T →
      e ≤ maynardFixedPolylogExponentBound →
      C * (Real.log T) ^ q *
          (1 + Real.log (maynardRaisedWidthConstant * (N : ℝ))) ^ e ≤
        T ^ (routeTEndpointGlobalDeficit A T / m) := by
  let K : ℝ := |Real.log C| + q +
    (maynardFixedPolylogExponentBound : ℝ) * (maynardRaisedWidthConstant + 1)
  let c0 : ℝ := 7 / (60 * (m : ℝ))
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    exact add_nonneg
      (add_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
      (mul_nonneg (Nat.cast_nonneg _)
        (add_nonneg (le_trans (by norm_num) maynardRaisedWidthConstant_one_le) zero_le_one))
  have hc0 : 0 < c0 := by
    dsimp only [c0]
    positivity
  have hthree : Tendsto (fun T : ℝ => 3 * T) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) tendsto_id
  have hfactor0 : 0 ≤ 2 * K / c0 :=
    div_nonneg (mul_nonneg (by norm_num) hK0) hc0.le
  have habsorbRaw := eventually_const_mul_routeTContourEdgeLogEnvelope_le_shiftGain
    A (2 * K / c0) hfactor0
  have habsorb := hthree.eventually habsorbRaw
  filter_upwards [habsorb, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop 3] with T habsorbT hlogT hT
  intro N e hN hNscale he
  have hT0 : 0 < T := by linarith
  have hlog3T : Real.log (3 * T) ≤ 2 * Real.log T := by
    have hthreeSq : 3 * T ≤ T ^ (2 : ℕ) := by nlinarith
    have hlog := Real.log_le_log (by positivity : 0 < 3 * T) hthreeSq
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    exact hlog
  have hshift0 : 0 ≤ routeTContourShiftEnvelope A (3 * T) :=
    (routeTContourShiftEnvelope_pos A (by positivity)).le
  have htransfer : routeTContourShiftEnvelope A (3 * T) * Real.log (3 * T) ≤
      2 * routeTContourShiftEnvelope A (3 * T) * Real.log T := by
    calc
      routeTContourShiftEnvelope A (3 * T) * Real.log (3 * T) ≤
          routeTContourShiftEnvelope A (3 * T) * (2 * Real.log T) :=
        mul_le_mul_of_nonneg_left hlog3T hshift0
      _ = 2 * routeTContourShiftEnvelope A (3 * T) * Real.log T := by ring
  have hKedge : K * routeTContourEdgeLogEnvelope A (3 * T) ≤
      c0 * routeTContourShiftEnvelope A (3 * T) * Real.log T := by
    have hboth := habsorbT.trans htransfer
    have htwice :
        2 * ((K * routeTContourEdgeLogEnvelope A (3 * T)) / c0) ≤
          2 * (routeTContourShiftEnvelope A (3 * T) * Real.log T) := by
      calc
        2 * ((K * routeTContourEdgeLogEnvelope A (3 * T)) / c0) =
            2 * K / c0 * routeTContourEdgeLogEnvelope A (3 * T) := by
          field_simp [hc0.ne']
        _ ≤ 2 * routeTContourShiftEnvelope A (3 * T) * Real.log T := hboth
        _ = 2 * (routeTContourShiftEnvelope A (3 * T) * Real.log T) := by ring
    have hdiv : (K * routeTContourEdgeLogEnvelope A (3 * T)) / c0 ≤
        routeTContourShiftEnvelope A (3 * T) * Real.log T := by linarith
    have hmul := (div_le_iff₀ hc0).mp hdiv
    calc
      K * routeTContourEdgeLogEnvelope A (3 * T) ≤
          (routeTContourShiftEnvelope A (3 * T) * Real.log T) * c0 := hmul
      _ = c0 * routeTContourShiftEnvelope A (3 * T) * Real.log T := by ring
  have hlogcost := log_maynardOptimizerFixedLogCost_le_edge
    A C hC q hT0 hlogT hN (by norm_num : (1 : ℝ) ≤ 19 / 9)
      (by simpa using hNscale) he
  have hlogtarget :
      Real.log (C * (Real.log T) ^ q *
        (1 + Real.log (maynardRaisedWidthConstant * (N : ℝ))) ^ e) ≤
        (routeTEndpointGlobalDeficit A T / m) * Real.log T := by
    calc
      Real.log (C * (Real.log T) ^ q *
          (1 + Real.log (maynardRaisedWidthConstant * (N : ℝ))) ^ e) ≤
          K * routeTContourEdgeLogEnvelope A (3 * T) := by
        simpa only [K] using hlogcost
      _ ≤ c0 * routeTContourShiftEnvelope A (3 * T) * Real.log T := hKedge
      _ = (routeTEndpointGlobalDeficit A T / m) * Real.log T := by
        dsimp only [c0, routeTEndpointGlobalDeficit, routeTEndpointCommonDeficit]
        field_simp [show (m : ℝ) ≠ 0 by exact_mod_cast hm.ne']
        ring
  have hbase : 0 < 1 + Real.log (maynardRaisedWidthConstant * (N : ℝ)) := by
    have hwidthN : 1 ≤ maynardRaisedWidthConstant * (N : ℝ) := by
      apply one_le_mul_of_one_le_of_one_le maynardRaisedWidthConstant_one_le
      exact_mod_cast hN
    linarith [Real.log_nonneg hwidthN]
  have hcost0 : 0 < C * (Real.log T) ^ q *
      (1 + Real.log (maynardRaisedWidthConstant * (N : ℝ))) ^ e := by positivity
  rw [← Real.exp_log hcost0, Real.rpow_def_of_pos hT0]
  apply Real.exp_le_exp.mpr
  simpa only [mul_comm] using hlogtarget

end RHTower.Sieve
