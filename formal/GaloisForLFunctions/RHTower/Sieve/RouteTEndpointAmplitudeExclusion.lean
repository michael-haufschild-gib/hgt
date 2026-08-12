import GaloisForLFunctions.RHTower.Sieve.RouteTMoebiusEndpoint
import GaloisForLFunctions.RHTower.Sieve.MaynardPerronRelevantAggregate

/-!
# Route-T exclusion of every endpoint-long atom

An explicit contour-shift envelope supplies one common deficit for all three literal
Heath--Brown atom kinds.  The same spare tenth-power that absorbs the Möbius contour coefficient
also absorbs the unique logarithmic atom's exact `log log` slack.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex Filter Topology

/-- Common endpoint deficit, chosen below the actual Möbius contour shift and eventually below
the fixed zeta/log derivative deficit. -/
def routeTEndpointCommonDeficit (A T : ℝ) : ℝ :=
  routeTContourShiftEnvelope A (3 * T) / 6

theorem routeTEndpointCommonDeficit_pos
    (A : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    0 < routeTEndpointCommonDeficit A T := by
  unfold routeTEndpointCommonDeficit
  exact div_pos (routeTContourShiftEnvelope_pos A (by positivity)) (by norm_num)

/-- The explicit common deficit eventually lies below the fixed zeta/log derivative deficit. -/
theorem eventually_routeTEndpointCommonDeficit_le_zetaLog (A : ℝ) :
    ∀ᶠ T : ℝ in atTop,
      routeTEndpointCommonDeficit A T ≤ maynardEndpointDerivativeDeficit / 2 := by
  have hthree : Tendsto (fun T : ℝ => 3 * T) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) tendsto_id
  have hzero : Tendsto (fun T : ℝ => routeTContourShiftEnvelope A (3 * T))
      atTop (𝓝 0) := (tendsto_routeTContourShiftEnvelope_zero A).comp hthree
  have hsmall := hzero.eventually (eventually_lt_nhds
    (show (0 : ℝ) < 3 * maynardEndpointDerivativeDeficit by
      positivity [maynardEndpointDerivativeDeficit_pos]))
  filter_upwards [hsmall] with T hT
  unfold routeTEndpointCommonDeficit
  linarith

/-- The explicit common deficit eventually lies below the actual common Möbius deficit. -/
theorem eventually_routeTEndpointCommonDeficit_le_moebius
    {A delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ T : ℝ in atTop,
      routeTEndpointCommonDeficit A T ≤ routeTEndpointMoebiusDeficit A delta T := by
  obtain ⟨b, hb⟩ := eventually_atTop.1
    (eventually_routeTContourShiftEnvelope_le (A := A) hdelta)
  filter_upwards [eventually_ge_atTop (b / 3)] with T hT
  have h := hb (3 * T) (by linarith)
  unfold routeTEndpointCommonDeficit routeTEndpointMoebiusDeficit
  linarith

/-- The logarithm of the uniform Maynard polylog envelope fits inside one Route-T edge envelope.
This is a direct comparison on the `log log` scale, not an `o(log T)` weakening. -/
theorem log_maynardLongPolylogEnvelope_le_routeTContourEdgeLogEnvelope
    {A T mu : ℝ} {X : ℕ} (hX : 1 ≤ X) (hT : 0 < T)
    (hlogT : 1 ≤ Real.log T) (hmu : mu ≤ 19 / 9)
    (hXscale : (X : ℝ) ≤ T ^ mu) :
    Real.log (maynardLongPolylogEnvelope X) ≤
      routeTContourEdgeLogEnvelope A (3 * T) := by
  let Z : ℝ := routeTLogHeightEnvelope (4 * (3 * T + 1))
  let W : ℝ := 1 + Real.log Z
  have hE := maynardLongPolylogEnvelope_le_eight_log hX hT hlogT hmu hXscale
  have hE0 : 0 < maynardLongPolylogEnvelope X :=
    lt_of_lt_of_le zero_lt_one (one_le_maynardLongPolylogEnvelope X)
  have hlogT0 : 0 < Real.log T := by linarith
  have hlogE : Real.log (maynardLongPolylogEnvelope X) ≤
      Real.log (8 * Real.log T) := Real.log_le_log hE0 hE
  have harg0 : 0 < 4 * (3 * T + 1) + 2 := by positivity
  have harg : T ≤ 4 * (3 * T + 1) + 2 := by linarith
  have hlogArg : Real.log T ≤ Real.log (4 * (3 * T + 1) + 2) :=
    Real.log_le_log hT harg
  have hZlogT : Real.log T ≤ Z := by
    dsimp only [Z, routeTLogHeightEnvelope]
    linarith
  have hZ0 : 0 < Z := hlogT0.trans_le hZlogT
  have hloglog : Real.log (Real.log T) ≤ Real.log Z :=
    Real.log_le_log hlogT0 hZlogT
  have hlog8 : Real.log 8 < 3 := by
    have hlog2 := Real.log_lt_sub_one_of_pos
      (by norm_num : (0 : ℝ) < 2) (by norm_num)
    calc
      Real.log 8 = Real.log ((2 : ℝ) ^ (3 : ℕ)) := by norm_num
      _ = 3 * Real.log 2 := by rw [Real.log_pow]; norm_num
      _ < 3 := by linarith
  have hsplit : Real.log (8 * Real.log T) =
      Real.log 8 + Real.log (Real.log T) := by
    rw [Real.log_mul (by norm_num) hlogT0.ne']
  have hW1 : 1 ≤ W := by
    dsimp only [W]
    linarith [Real.log_nonneg (by linarith : 1 ≤ Z)]
  have hlog8T : Real.log (8 * Real.log T) ≤ 3 * W := by
    rw [hsplit]
    dsimp only [W]
    linarith
  have hB : 2 ≤ routeTZeroFreeBudgetEnvelopeConstant A + 2 := by
    linarith [routeTZeroFreeBudgetEnvelopeConstant_pos A]
  have hBsq : 4 ≤ (routeTZeroFreeBudgetEnvelopeConstant A + 2) ^ (2 : ℕ) := by
    nlinarith
  have hWsq : 3 * W ≤ 1600 * W ^ (2 : ℕ) := by
    nlinarith
  calc
    Real.log (maynardLongPolylogEnvelope X) ≤ Real.log (8 * Real.log T) := hlogE
    _ ≤ 3 * W := hlog8T
    _ ≤ 1600 * W ^ (2 : ℕ) := hWsq
    _ ≤ 400 * (routeTZeroFreeBudgetEnvelopeConstant A + 2) ^ (2 : ℕ) *
        W ^ (2 : ℕ) := by
      exact mul_le_mul_of_nonneg_right (by nlinarith [hBsq]) (sq_nonneg W)
    _ = routeTContourEdgeLogEnvelope A (3 * T) := by
      rfl

/-- The unique logarithmic atom's complete amplitude slack is eventually at most one quarter of
the common endpoint deficit times the exact box logarithmic length. -/
theorem eventually_routeT_endpoint_slack_mass_le (A : ℝ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, 4 / 3 ≤ mu → mu ≤ 19 / 9 →
        (X : ℝ) ≤ T ^ mu →
        ∀ L : ℕ, ∀ box : HeathBrownBoxChoice L X 60, 1 ≤ box.q →
          IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
          ∑ i : HeathBrownBoxFactorIndex 60 box.m,
              heathBrownFactorAmplitudeSlack (heathBrownBoxFactorKind 60 box.m i)
                (heathBrownBoxFactorExponent box.a box.b box.q i) *
                Real.log
                  (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ)) ≤
            (routeTEndpointCommonDeficit A T / 4) *
              Real.log
                ((groupedDyadicLower
                  (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) := by
  obtain ⟨a, ha⟩ := eventually_atTop.1
    (eventually_const_mul_routeTContourEdgeLogEnvelope_le_shiftGain
      A 4320 (by norm_num))
  filter_upwards [eventually_ge_atTop (a / 3),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop 3] with T hTa hlogT hT3
  intro X hX mu hmu_lo hmu_hi hXscale L box hq helig
  let total : ℝ := heathBrownBoxTotalExponent L X 60 T box
  let D : ℝ :=
    ((groupedDyadicLower
      (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ)
  have hT0 : 0 < T := by linarith
  have htotal : mu / 120 ≤ total := by
    simpa [IsHeathBrownBoxEligible, total] using helig
  have htotalMin : (1 / 90 : ℝ) ≤ total := by linarith
  have hD : D = T ^ total := by
    dsimp [D, total]
    simpa [heathBrownBoxTotalExponent, groupedDyadicLower] using
      (cast_prod_twoPow_eq_rpow_sum_dyadicLogExponent (by linarith : 1 < T)
        (heathBrownBoxFactorExponent box.a box.b box.q)
        (Finset.univ : Finset (HeathBrownBoxFactorIndex 60 box.m)))
  have hlogD : Real.log D = total * Real.log T := by
    rw [hD, Real.log_rpow hT0]
  have hlogDlower : (1 / 90 : ℝ) * Real.log T ≤ Real.log D := by
    rw [hlogD]
    exact mul_le_mul_of_nonneg_right htotalMin (Real.log_nonneg (by linarith))
  have hslack :
      (∑ i : HeathBrownBoxFactorIndex 60 box.m,
          heathBrownFactorAmplitudeSlack (heathBrownBoxFactorKind 60 box.m i)
            (heathBrownBoxFactorExponent box.a box.b box.q i) *
            Real.log
              (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ))) ≤
        routeTContourEdgeLogEnvelope A (3 * T) := by
    rw [sum_heathBrownBoxFactorAmplitudeSlack_mul_log box.a box.b hq]
    exact (log_heathBrown_log_trivialConstant_le_log_polylogEnvelope box hX hq).trans
      (log_maynardLongPolylogEnvelope_le_routeTContourEdgeLogEnvelope
        hX hT0 hlogT hmu_hi hXscale)
  have habsorb := ha (3 * T) (by linarith)
  have hlog3T : Real.log (3 * T) ≤ 2 * Real.log T := by
    have hthree : 3 * T ≤ T ^ (2 : ℕ) := by nlinarith
    have hlog := Real.log_le_log (by positivity : 0 < 3 * T) hthree
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    exact hlog
  have henv0 : 0 ≤ routeTContourShiftEnvelope A (3 * T) :=
    (routeTContourShiftEnvelope_pos A (by positivity)).le
  have hedge : routeTContourEdgeLogEnvelope A (3 * T) ≤
      routeTContourShiftEnvelope A (3 * T) * Real.log T / 2160 := by
    have htransfer : routeTContourShiftEnvelope A (3 * T) * Real.log (3 * T) ≤
        2 * routeTContourShiftEnvelope A (3 * T) * Real.log T := by
      calc
        routeTContourShiftEnvelope A (3 * T) * Real.log (3 * T) ≤
            routeTContourShiftEnvelope A (3 * T) * (2 * Real.log T) :=
          mul_le_mul_of_nonneg_left hlog3T henv0
        _ = 2 * routeTContourShiftEnvelope A (3 * T) * Real.log T := by ring
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hlogDlower
    (show 0 ≤ routeTContourShiftEnvelope A (3 * T) / 24 by positivity)
  calc
    (∑ i : HeathBrownBoxFactorIndex 60 box.m,
        heathBrownFactorAmplitudeSlack (heathBrownBoxFactorKind 60 box.m i)
          (heathBrownBoxFactorExponent box.a box.b box.q i) *
          Real.log
            (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ))) ≤
        routeTContourEdgeLogEnvelope A (3 * T) := hslack
    _ ≤ routeTContourShiftEnvelope A (3 * T) * Real.log T / 2160 := hedge
    _ ≤ (routeTContourShiftEnvelope A (3 * T) / 24) * Real.log D := by
      nlinarith
    _ = (routeTEndpointCommonDeficit A T / 4) *
        Real.log
          ((groupedDyadicLower
            (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) := by
      simp only [routeTEndpointCommonDeficit, D]
      ring

/-- Global box-amplitude deficit left after the `19/20` endpoint mass law and the exact quarter-
deficit logarithmic slack payment. -/
def routeTEndpointGlobalDeficit (A T : ℝ) : ℝ :=
  (7 / 10 : ℝ) * routeTEndpointCommonDeficit A T

theorem routeTEndpointGlobalDeficit_pos
    (A : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    0 < routeTEndpointGlobalDeficit A T := by
  unfold routeTEndpointGlobalDeficit
  positivity [routeTEndpointCommonDeficit_pos A hT]

/-- **Every endpoint-long atom is excluded.**  Möbius, zeta, and logarithm factors share one
explicit vanishing deficit, and the complete literal box loses `7/10` of it globally. -/
theorem exists_eventually_routeT_endpoint_box_amplitude_exclusion :
    ∃ (A C C' delta : ℝ), 0 ≤ C ∧ 0 ≤ C' ∧ 0 < delta ∧
      ∀ᶠ T : ℝ in atTop,
        ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, 4 / 3 ≤ mu → mu ≤ 19 / 9 →
          (X : ℝ) ≤ T ^ mu →
          ∀ L : ℕ, 1 ≤ L → (L : ℝ) ≤ T ^ (mu / 60) →
            ∀ box : HeathBrownBoxChoice L X 60,
              IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
              ∀ c y alpha : ℝ, 0 ≤ c → T ≤ y → y ≤ 2 * T →
                ((groupedDyadicLower
                  (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^
                    (alpha - c) ≤
                  ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q
                    ((c : ℂ) + (y : ℝ) * Complex.I)‖ →
                alpha ≤ 1 - routeTEndpointGlobalDeficit A T := by
  obtain ⟨A, C, C', delta, hC, hC', hdelta, hmobius⟩ :=
    exists_eventually_maynard_endpoint_moebius_amplitude_deficit
  refine ⟨A, C, C', delta, hC, hC', hdelta, ?_⟩
  filter_upwards [hmobius,
    eventually_maynard_endpoint_zeta_log_amplitude_deficit,
    eventually_routeTEndpointCommonDeficit_le_zetaLog A,
    eventually_routeTEndpointCommonDeficit_le_moebius hdelta,
    eventually_routeT_endpoint_slack_mass_le A,
    eventually_gt_atTop (1 : ℝ)]
      with T hmob hzeta hcommonZeta hcommonMob hslack hT
  intro X hX mu hmu_lo hmu_hi hXscale L hL hcut box helig c y alpha hc hylo hyhi hlarge
  let s : ℂ := (c : ℂ) + (y : ℝ) * Complex.I
  let D : ℝ :=
    ((groupedDyadicLower
      (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ)
  have hq : 1 ≤ box.q :=
    heathBrownBox_log_exponent_pos_of_large_core box s (by simpa only [s] using hlarge)
  have hD0 : 0 < D := by
    dsimp only [D]
    exact_mod_cast (show 0 < groupedDyadicLower
      (heathBrownBoxFactorExponent box.a box.b box.q) by
        exact lt_of_lt_of_le Nat.zero_lt_one
          (one_le_groupedDyadicLower
            (heathBrownBoxFactorExponent box.a box.b box.q)))
  have hthreshold : 0 < D ^ (alpha - c) := Real.rpow_pos_of_pos hD0 _
  have hcorePos : 0 < ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q s‖ :=
    hthreshold.trans_le (by simpa only [D, s] using hlarge)
  have hprod :
      (∏ i : PositiveHeathBrownBoxFactorIndex box,
        heathBrownBoxFactorValue L X 60 box s i) =
        heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q s :=
    prod_positive_heathBrownBoxFactorValue_eq_core box hL hX hq s
  have hfactorPos : ∀ i : PositiveHeathBrownBoxFactorIndex box,
      0 < ‖heathBrownBoxFactorValue L X 60 box s i‖ := by
    intro i
    by_contra hi
    have hi0 : ‖heathBrownBoxFactorValue L X 60 box s i‖ = 0 :=
      le_antisymm (le_of_not_gt hi) (norm_nonneg _)
    have hvalue0 : heathBrownBoxFactorValue L X 60 box s i = 0 := norm_eq_zero.mp hi0
    have hprod0 : (∏ r : PositiveHeathBrownBoxFactorIndex box,
        heathBrownBoxFactorValue L X 60 box s r) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hvalue0
    rw [hprod] at hprod0
    rw [hprod0, norm_zero] at hcorePos
    exact (lt_irrefl 0) hcorePos
  have hDelta : 0 ≤ routeTEndpointCommonDeficit A T :=
    (routeTEndpointCommonDeficit_pos A (by linarith)).le
  have hlong : ∀ j : PositiveHeathBrownBoxFactorIndex box,
      (∑ i : PositiveHeathBrownBoxFactorIndex box,
          dyadicLogExponent T
            (heathBrownBoxFactorExponent box.a box.b box.q i)) /
            (40 * 60 : ℕ) ≤
        dyadicLogExponent T
          (heathBrownBoxFactorExponent box.a box.b box.q j) →
      maynardAmplitude c
          (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ))
          ‖heathBrownBoxFactorValue L X 60 box s j‖ ≤
        1 - routeTEndpointCommonDeficit A T := by
    intro j hj
    have hV := hfactorPos j
    have htotal :
        heathBrownBoxTotalExponent L X 60 T box / (40 * 60 : ℕ) ≤
          dyadicLogExponent T
            (heathBrownBoxFactorExponent box.a box.b box.q j) := by
      rw [← sum_positive_dyadicLogExponent_eq_heathBrownBoxTotalExponent box]
      exact hj
    cases hkind : heathBrownBoxFactorKind 60 box.m j with
    | moebius =>
        have hm := hmob L X hL mu hmu_lo hmu_hi hcut box helig j hkind hj
          c y hc hylo hyhi (by simpa only [s] using hV)
        linarith
    | zeta =>
        have hz := hzeta X hX mu hmu_lo hmu_hi hXscale L box helig j
          (Or.inl hkind) htotal c y hc hylo hyhi (by simpa only [s] using hV)
        linarith
    | log =>
        have hz := hzeta X hX mu hmu_lo hmu_hi hXscale L box helig j
          (Or.inr hkind) htotal c y hc hylo hyhi (by simpa only [s] using hV)
        linarith
  have hslackMass := hslack X hX mu hmu_lo hmu_hi hXscale L box hq helig
  have hbox := maynard_heathBrownBox_endpoint_long_deficits_trimmed
    (k := 60) (by norm_num) box hL hX hT hc hDelta hlong hslackMass
      (by simpa only [s] using hlarge)
  unfold routeTEndpointGlobalDeficit
  linarith

/-- **Near-one Perron endpoint is empty.**  If the aggregate threshold is strong enough to select
a box at amplitude `alpha`, then no ordinate in the endpoint band can exceed the explicit Route-T
global deficit boundary. -/
theorem exists_eventually_no_perronRelevant_aggregate_near_one :
    ∃ (A C C' delta : ℝ), 0 ≤ C ∧ 0 ≤ C' ∧ 0 < delta ∧
      ∀ᶠ T : ℝ in atTop,
        ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, 4 / 3 ≤ mu → mu ≤ 19 / 9 →
          (X : ℝ) ≤ T ^ mu →
          ∀ L : ℕ, 1 ≤ L → X < (L + 1) ^ 60 →
            (L : ℝ) ≤ T ^ (mu / 60) →
            ∀ c y alpha V : ℝ, 0 ≤ c → T ≤ y → y ≤ 2 * T →
              1 - routeTEndpointGlobalDeficit A T < alpha → 0 < V →
              V ≤ ‖heathBrownPerronRelevantEligibleDyadicAggregate
                L X 60 T (mu / 120)
                  ((c : ℂ) + (y : ℝ) * Complex.I)‖ →
              (∀ box : HeathBrownBoxChoice L X 60,
                IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
                IsHeathBrownBoxPerronRelevant X 60 box →
                  heathBrownEligibleBoxCost L X 60 *
                    (groupedDyadicLower
                      (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
                        (alpha - c) ≤ V) →
              False := by
  obtain ⟨A, C, C', delta, hC, hC', hdelta, hboxExclude⟩ :=
    exists_eventually_routeT_endpoint_box_amplitude_exclusion
  refine ⟨A, C, C', delta, hC, hC', hdelta, ?_⟩
  filter_upwards [hboxExclude] with T hbox
  intro X hX mu hmu_lo hmu_hi hXscale L hL hXL hcut
    c y alpha V hc hylo hyhi halpha hV haggregate hreserve
  obtain ⟨box, helig, hrel, hterm⟩ :=
    exists_large_perronRelevant_eligible_heathBrownBox
      L X 60 (by norm_num) T (mu / 120)
        ((c : ℂ) + (y : ℝ) * Complex.I) hV haggregate
  have hterm' : V ≤ heathBrownEligibleBoxCost L X 60 *
      ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q
        ((c : ℂ) + (y : ℝ) * Complex.I)‖ := by
    dsimp [heathBrownBoxTerm] at hterm
    rw [norm_heathBrownDyadicTermProduct_eq_choose_mul_core] at hterm
    have hchoose : ((Nat.choose 60 box.m : ℕ) : ℝ) ≤ (2 ^ 60 : ℝ) := by
      exact_mod_cast Nat.choose_le_two_pow 60 box.m
    calc
      V ≤ (Fintype.card (HeathBrownBoxChoice L X 60) : ℝ) *
          (((Nat.choose 60 box.m : ℕ) : ℝ) *
            ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q
              ((c : ℂ) + (y : ℝ) * Complex.I)‖) := hterm
      _ ≤ (Fintype.card (HeathBrownBoxChoice L X 60) : ℝ) *
          ((2 ^ 60 : ℝ) *
            ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q
              ((c : ℂ) + (y : ℝ) * Complex.I)‖) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_right hchoose (norm_nonneg _)
        · exact Nat.cast_nonneg _
      _ = heathBrownEligibleBoxCost L X 60 *
          ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q
            ((c : ℂ) + (y : ℝ) * Complex.I)‖ := by
        change _ =
          (((Fintype.card (HeathBrownBoxChoice L X 60) : ℕ) : ℝ) * (2 ^ 60 : ℝ)) *
            ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q
              ((c : ℂ) + (y : ℝ) * Complex.I)‖
        exact (mul_assoc _ _ _).symm
  have hscaled := (hreserve box helig hrel).trans hterm'
  have hcostPos := heathBrownEligibleBoxCost_pos L X 60 (by norm_num)
  have hcore :
      (groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^ (alpha - c) ≤
        ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q
          ((c : ℂ) + (y : ℝ) * Complex.I)‖ :=
    (mul_le_mul_iff_right₀ hcostPos).mp hscaled
  have hbound := hbox X hX mu hmu_lo hmu_hi hXscale L hL hcut box helig
    c y alpha hc hylo hyhi hcore
  linarith

end RHTower.Sieve
