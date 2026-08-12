import GaloisForLFunctions.RHTower.Sieve.MaynardFixedPolylogAmplitudeCount
import GaloisForLFunctions.RHTower.Sieve.RouteTEndpointAmplitudeExclusion

/-!
# Endpoint absorption of fixed Maynard polylogarithms

The common Route-T endpoint deficit has vanishing power, but its logarithmic gain dominates every
fixed `log log` cost.  This module proves that domination uniformly over all selected factors and
raising orders, including an arbitrary fixed extra log power for label entropy.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex Filter Topology

theorem log_log_le_routeTContourEdgeLogEnvelope_three
    (A : ℝ) {T : ℝ} (hT : 0 ≤ T) (hlogT : 1 ≤ Real.log T) :
    Real.log (Real.log T) ≤ routeTContourEdgeLogEnvelope A (3 * T) := by
  let Z : ℝ := routeTLogHeightEnvelope (4 * (3 * T + 1))
  let W : ℝ := 1 + Real.log Z
  have harg : T ≤ 4 * (3 * T + 1) + 2 := by linarith
  have hTpos : 0 < T := by
    have hTne : T ≠ 0 := by
      intro hzero
      subst T
      norm_num at hlogT
    exact lt_of_le_of_ne hT (Ne.symm hTne)
  have hlogArg : Real.log T ≤ Real.log (4 * (3 * T + 1) + 2) :=
    Real.log_le_log hTpos harg
  have hlogTZ : Real.log T ≤ Z := by
    dsimp only [Z, routeTLogHeightEnvelope]
    linarith
  have hloglog : Real.log (Real.log T) ≤ Real.log Z :=
    Real.log_le_log (by linarith) hlogTZ
  have hZ1 : 1 ≤ Z := by
    dsimp only [Z]
    exact routeTLogHeightEnvelope_one_le (by positivity)
  have hW1 : 1 ≤ W := by
    dsimp only [W]
    linarith [Real.log_nonneg hZ1]
  have hWedge : W ≤ routeTContourEdgeLogEnvelope A (3 * T) := by
    unfold routeTContourEdgeLogEnvelope
    dsimp only [W, Z]
    have hB : 2 ≤ routeTZeroFreeBudgetEnvelopeConstant A + 2 := by
      linarith [routeTZeroFreeBudgetEnvelopeConstant_pos A]
    have hW1' : 1 ≤
        1 + Real.log (routeTLogHeightEnvelope (4 * (3 * T + 1))) := by
      simpa only [W, Z] using hW1
    calc
      1 + Real.log (routeTLogHeightEnvelope (4 * (3 * T + 1))) ≤
          1600 * (1 + Real.log
            (routeTLogHeightEnvelope (4 * (3 * T + 1)))) ^ 2 := by nlinarith
      _ ≤ 400 * (routeTZeroFreeBudgetEnvelopeConstant A + 2) ^ 2 *
          (1 + Real.log
            (routeTLogHeightEnvelope (4 * (3 * T + 1)))) ^ 2 := by
        have hBsq : 4 ≤ (routeTZeroFreeBudgetEnvelopeConstant A + 2) ^ 2 := by
          nlinarith
        have hcoeff : (1600 : ℝ) ≤
            400 * (routeTZeroFreeBudgetEnvelopeConstant A + 2) ^ 2 := by
          nlinarith
        exact mul_le_mul_of_nonneg_right
          hcoeff
          (sq_nonneg (1 + Real.log
            (routeTLogHeightEnvelope (4 * (3 * T + 1)))))
  calc
    Real.log (Real.log T) ≤ Real.log Z := hloglog
    _ ≤ W := by dsimp only [W]; linarith
    _ ≤ routeTContourEdgeLogEnvelope A (3 * T) := hWedge

theorem log_maynardFixedPolylogBase_le_edge
    (A : ℝ) {T : ℝ} (hT : 0 < T) (hlogT : 1 ≤ Real.log T)
    {N : ℕ} (hN : 1 ≤ N)
    (hNscale : (N : ℝ) ≤ T ^ (1367 / 2160 : ℝ)) :
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
      nlinarith [mul_nonneg (sub_nonneg.mpr hwidth1) (sub_nonneg.mpr hE1)]
    exact hfirst.trans hsecond
  have hlogE : Real.log E ≤ routeTContourEdgeLogEnvelope A (3 * T) := by
    dsimp only [E]
    exact log_maynardLongPolylogEnvelope_le_routeTContourEdgeLogEnvelope
      hN hT hlogT (by norm_num : (1367 / 2160 : ℝ) ≤ 19 / 9) hNscale
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

theorem log_maynardFixedPolylogTotalCost_le_edge
    (A C : ℝ) (hC : 0 < C) (q : ℕ)
    {T : ℝ} (hT : 0 < T) (hlogT : 1 ≤ Real.log T)
    {N e : ℕ} (hN : 1 ≤ N)
    (hNscale : (N : ℝ) ≤ T ^ (1367 / 2160 : ℝ))
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
  have hlogB : Real.log B ≤ (maynardRaisedWidthConstant + 1) * E := by
    simpa only [B, E] using
      log_maynardFixedPolylogBase_le_edge A hT hlogT hN hNscale
  have hloglog0 : 0 ≤ Real.log (Real.log T) := Real.log_nonneg hlogT
  have hloglog : Real.log (Real.log T) ≤ E := by
    simpa only [E] using
      log_log_le_routeTContourEdgeLogEnvelope_three A hT.le hlogT
  have hE1 : 1 ≤ E := by
    dsimp only [E]
    exact one_le_routeTContourEdgeLogEnvelope A (by positivity)
  have hCterm : Real.log C ≤ |Real.log C| * E := by
    have habs : Real.log C ≤ |Real.log C| := le_abs_self _
    have hmul : |Real.log C| ≤ |Real.log C| * E := by
      nlinarith [abs_nonneg (Real.log C)]
    exact habs.trans hmul
  have hqterm : (q : ℝ) * Real.log (Real.log T) ≤ (q : ℝ) * E :=
    mul_le_mul_of_nonneg_left hloglog (Nat.cast_nonneg q)
  have hecast : (e : ℝ) ≤ (maynardFixedPolylogExponentBound : ℝ) := by
    exact_mod_cast he
  have heterm : (e : ℝ) * Real.log B ≤
      (maynardFixedPolylogExponentBound : ℝ) *
        ((maynardRaisedWidthConstant + 1) * E) := by
    exact mul_le_mul hecast hlogB hlogB0 (Nat.cast_nonneg _)
  have hlogeq :
      Real.log (C * (Real.log T) ^ q * B ^ e) =
        Real.log C + (q : ℝ) * Real.log (Real.log T) +
          (e : ℝ) * Real.log B := by
    rw [Real.log_mul (mul_ne_zero hC.ne' (pow_ne_zero _ hlogT0.ne'))
        (pow_ne_zero _ (zero_lt_one.trans_le hB1).ne'),
      Real.log_mul hC.ne' (pow_ne_zero _ hlogT0.ne'),
      Real.log_pow, Real.log_pow]
  rw [show 1 + Real.log (maynardRaisedWidthConstant * (N : ℝ)) = B by rfl,
    hlogeq]
  calc
    Real.log C + (q : ℝ) * Real.log (Real.log T) + (e : ℝ) * Real.log B ≤
        |Real.log C| * E + (q : ℝ) * E +
          (maynardFixedPolylogExponentBound : ℝ) *
            ((maynardRaisedWidthConstant + 1) * E) :=
      add_le_add (add_le_add hCterm hqterm) heterm
    _ = (|Real.log C| + q +
        (maynardFixedPolylogExponentBound : ℝ) *
          (maynardRaisedWidthConstant + 1)) * E := by ring

theorem eventually_maynardFixedPolylogTotalCost_absorbed
    (A C : ℝ) (hC : 0 < C) (q : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ N : ℕ, 1 ≤ N → (N : ℝ) ≤ T ^ (1367 / 2160 : ℝ) →
      ∀ e : ℕ, e ≤ maynardFixedPolylogExponentBound →
        C * (Real.log T) ^ q *
            (1 + Real.log (maynardRaisedWidthConstant * (N : ℝ))) ^ e ≤
          T ^ ((73 / 1080 : ℝ) * routeTEndpointGlobalDeficit A T) := by
  let K : ℝ := |Real.log C| + q +
    (maynardFixedPolylogExponentBound : ℝ) * (maynardRaisedWidthConstant + 1)
  let c0 : ℝ := (73 / 1080 : ℝ) * (7 / 60 : ℝ)
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    exact add_nonneg
      (add_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
      (mul_nonneg (Nat.cast_nonneg _)
        (add_nonneg (le_trans (by norm_num) maynardRaisedWidthConstant_one_le) zero_le_one))
  have hc0 : 0 < c0 := by dsimp only [c0]; norm_num
  have hthree : Tendsto (fun T : ℝ => 3 * T) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) tendsto_id
  have hfactor0 : 0 ≤ 2 * K / c0 :=
    div_nonneg (mul_nonneg (by norm_num) hK0) (le_of_lt hc0)
  have habsorbRaw := eventually_const_mul_routeTContourEdgeLogEnvelope_le_shiftGain
    A (2 * K / c0) hfactor0
  have habsorb := hthree.eventually habsorbRaw
  filter_upwards [habsorb, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop 3] with T habsorbT hlogT hT
  intro N hN hNscale e he
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
  have hlogcost := log_maynardFixedPolylogTotalCost_le_edge
    A C hC q hT0 hlogT hN hNscale he
  have hlogtarget :
      Real.log (C * (Real.log T) ^ q *
        (1 + Real.log (maynardRaisedWidthConstant * (N : ℝ))) ^ e) ≤
        ((73 / 1080 : ℝ) * routeTEndpointGlobalDeficit A T) * Real.log T := by
    calc
      Real.log (C * (Real.log T) ^ q *
          (1 + Real.log (maynardRaisedWidthConstant * (N : ℝ))) ^ e) ≤
          K * routeTContourEdgeLogEnvelope A (3 * T) := by simpa only [K] using hlogcost
      _ ≤ c0 * routeTContourShiftEnvelope A (3 * T) * Real.log T := hKedge
      _ = ((73 / 1080 : ℝ) * routeTEndpointGlobalDeficit A T) * Real.log T := by
        dsimp only [c0, routeTEndpointGlobalDeficit, routeTEndpointCommonDeficit]
        ring
  have hcost0 : 0 < C * (Real.log T) ^ q *
      (1 + Real.log (maynardRaisedWidthConstant * (N : ℝ))) ^ e := by
    have hwidthN : 1 ≤ maynardRaisedWidthConstant * (N : ℝ) := by
      apply one_le_mul_of_one_le_of_one_le maynardRaisedWidthConstant_one_le
      exact_mod_cast hN
    have hbase : 0 < 1 + Real.log (maynardRaisedWidthConstant * (N : ℝ)) := by
      linarith [Real.log_nonneg hwidthN]
    positivity
  rw [← Real.exp_log hcost0, Real.rpow_def_of_pos hT0]
  apply Real.exp_le_exp.mpr
  simpa only [mul_comm] using hlogtarget

/-- The worst Maynard height ratio leaves slope `73/1080`; a common endpoint deficit therefore
supplies at least that much fixed-polylog reserve. -/
theorem maynard_fixedPolylog_huxley_reserve_of_endpoint_deficit
    {mu alpha d : ℝ} (hmu : 4 / 3 ≤ mu) (hd : 0 ≤ d)
    (halpha : alpha ≤ 1 - d) :
    (73 / 1080 : ℝ) * d ≤
      (mu - 2 * (1367 / 2160 : ℝ)) * (1 - alpha) := by
  have hslope : (73 / 1080 : ℝ) ≤
      mu - 2 * (1367 / 2160 : ℝ) := by linarith
  have hgap : d ≤ 1 - alpha := by linarith
  exact (mul_le_mul_of_nonneg_left hgap (by norm_num)).trans
    (mul_le_mul_of_nonneg_right hslope (by linarith))

/-- **Uniform moving-endpoint fibre reserve.**  Every literal selected factor and permitted
raising order has its exact fixed-polylog Huxley cost absorbed at the lower endpoint boundary.
No choice-dependent constant or auxiliary `rho` remains. -/
theorem eventually_maynard_fixedPolylog_fibre_reserve (A : ℝ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X : ℕ} (label : HeathBrownSelectionLabel L X 60)
        (ell : ℕ), 0 < ell → ell ≤ 51 →
      ((((groupedDyadicLower
        (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)) ≤
          T ^ (1367 / 2160 : ℝ) →
      ∀ mu alpha : ℝ, 4 / 3 ≤ mu →
        alpha ≤ 1 - routeTEndpointGlobalDeficit A T →
        2 * (6121 : ℝ) ^ 2 * maynardRaisedWidthConstant *
            (1 + Real.log
              (maynardRaisedWidthConstant *
                ((((groupedDyadicLower
                  (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)))) ^
              (2 * (Fintype.card (HeathBrownSelectedFactor label) * ell) +
                (2 ^ (2 * ((Fintype.card
                  (HeathBrownSelectedFactor label) + 1) * ell)) - 1)) ≤
          T ^ ((mu - 2 * (1367 / 2160 : ℝ)) * (1 - alpha)) := by
  let C : ℝ := 2 * (6121 : ℝ) ^ 2 * maynardRaisedWidthConstant
  have hC : 0 < C := by
    dsimp only [C]
    exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos (by norm_num)))
      (lt_of_lt_of_le zero_lt_one maynardRaisedWidthConstant_one_le)
  filter_upwards [eventually_maynardFixedPolylogTotalCost_absorbed A C hC 0,
    eventually_gt_atTop (1 : ℝ)] with T habsorb hT
  intro L X label ell hell hell51 hYhi mu alpha hmu halpha
  let N : ℕ := (groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell
  let e : ℕ :=
    2 * (Fintype.card (HeathBrownSelectedFactor label) * ell) +
      (2 ^ (2 * ((Fintype.card (HeathBrownSelectedFactor label) + 1) * ell)) - 1)
  have hN : 1 ≤ N := by
    dsimp only [N]
    exact Nat.one_le_pow ell _ (one_le_groupedDyadicLower _)
  have hNscale : (N : ℝ) ≤ T ^ (1367 / 2160 : ℝ) := by
    simpa only [N] using hYhi
  have he : e ≤ maynardFixedPolylogExponentBound := by
    dsimp only [e]
    exact heathBrownSelected_fixedPolylogExponent_le label hell51
  have hcost := habsorb N hN hNscale e he
  have hd : 0 ≤ routeTEndpointGlobalDeficit A T :=
    (routeTEndpointGlobalDeficit_pos A (by linarith)).le
  have hexp := maynard_fixedPolylog_huxley_reserve_of_endpoint_deficit
    hmu hd halpha
  have hpow := Real.rpow_le_rpow_of_exponent_le hT.le hexp
  have hcost' : C *
      (1 + Real.log (maynardRaisedWidthConstant * (N : ℝ))) ^ e ≤
      T ^ ((73 / 1080 : ℝ) * routeTEndpointGlobalDeficit A T) := by
    simpa only [pow_zero, mul_one] using hcost
  simpa only [C, N, e] using hcost'.trans hpow

end RHTower.Sieve
