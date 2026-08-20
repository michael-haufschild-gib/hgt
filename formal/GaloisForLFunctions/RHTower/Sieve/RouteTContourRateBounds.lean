import GaloisForLFunctions.RHTower.Sieve.RouteTMoebiusTwistAllHeights
import GaloisForLFunctions.RHTower.Sieve.PolylogRpowDomination
import GaloisForLFunctions.RHTower.Sieve.RouteTZetaAsymptotics
import GaloisForLFunctions.RHTower.Sieve.RouteTZetaZeroFreeMonotonicity

/-!
# The Route-T contour data at heights below the doubled cutoff

Every quantity of the Route-T rectangle is monotone in the contour height, so on the whole range
`routeTInverseBaseHeight ≤ S ≤ 2N` it is controlled by its value at `S = 2N`, where the
polylogarithmic envelopes of `Sieve/RouteTZetaAsymptotics` apply.  The three facts the rate
argument needs are: the contour displacement times `log N` beats every fixed power `(log N)^{1/20}`,
the edge constant is below `exp((log N)^{1/20})`, and the reciprocal width exceeds `1/log N`, so
the abscissa `1 + 1/log N` still lies inside the zero-free rectangle.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The left abscissa never drops below one half: the displacement is at most `1/320`. -/
theorem routeTContourLeft_ge_half (A δ T : ℝ) : (1 : ℝ) / 2 ≤ routeTContourLeft A δ T := by
  have hshift := routeTContourShift_le_delta_twentieth A δ T
  have hD := routeTInverseDelta_le_sixteenth A T
  unfold routeTContourLeft
  linarith

/-- The log-height envelope at a height below the doubled cutoff is at most five logarithms. -/
theorem routeTLogHeightEnvelope_le_five_log {N S : ℝ} (hN0 : 0 < N) (hN : 3 ≤ Real.log N)
    (hS0 : 0 ≤ S) (hS : S ≤ 2 * N) :
    routeTLogHeightEnvelope (4 * routeTInverseHeight S) ≤ 5 * Real.log N := by
  have hNe : Real.exp 3 ≤ N := by
    have h := Real.exp_le_exp.2 hN
    rwa [Real.exp_log hN0] at h
  have he3 : (20 : ℝ) ≤ Real.exp 3 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h3 : Real.exp 3 = Real.exp 1 * (Real.exp 1 * Real.exp 1) := by
      rw [← Real.exp_add, ← Real.exp_add]
      norm_num
    rw [h3]
    nlinarith [Real.exp_pos (1 : ℝ)]
  have hN20 : (20 : ℝ) ≤ N := le_trans he3 hNe
  have harg : 4 * routeTInverseHeight S + 2 ≤ N ^ 2 := by
    unfold routeTInverseHeight
    nlinarith [hN20, hS]
  have hpos : (0 : ℝ) < 4 * routeTInverseHeight S + 2 := by
    unfold routeTInverseHeight
    linarith
  have hlog : Real.log (4 * routeTInverseHeight S + 2) ≤ Real.log (N ^ 2) :=
    Real.log_le_log hpos harg
  have hsq : Real.log (N ^ 2) = 2 * Real.log N := by
    rw [Real.log_pow]
    push_cast
    ring
  unfold routeTLogHeightEnvelope
  rw [hsq] at hlog
  linarith

/-- The log-height envelope is at least one. -/
theorem one_le_routeTLogHeightEnvelope {t : ℝ} (ht : -1 ≤ t) :
    (1 : ℝ) ≤ routeTLogHeightEnvelope t := by
  unfold routeTLogHeightEnvelope
  have : (0 : ℝ) ≤ Real.log (t + 2) := Real.log_nonneg (by linarith)
  linarith

end

end RHTower.Sieve

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- A polylogarithm in `5L` is a polylogarithm in `L`. -/
theorem five_log_polylog_le {L : ℝ} (hL : 1 ≤ L) :
    (5 * L) ^ ((9 : ℝ) / 10) * (1 + Real.log (5 * L)) ^ 2
      ≤ (5 : ℝ) ^ ((9 : ℝ) / 10) * (1 + Real.log 5) ^ 2
          * (L ^ ((9 : ℝ) / 10) * (1 + |Real.log L|) ^ 2) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hlogL : (0 : ℝ) ≤ Real.log L := Real.log_nonneg hL
  have habs : |Real.log L| = Real.log L := abs_of_nonneg hlogL
  have hlog5 : (0 : ℝ) ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  have hpow : (5 * L) ^ ((9 : ℝ) / 10) = (5 : ℝ) ^ ((9 : ℝ) / 10) * L ^ ((9 : ℝ) / 10) :=
    Real.mul_rpow (by norm_num) hL0.le
  have hlogmul : Real.log (5 * L) = Real.log 5 + Real.log L :=
    Real.log_mul (by norm_num) (ne_of_gt hL0)
  have hsplit : (1 + Real.log (5 * L)) ≤ (1 + Real.log 5) * (1 + Real.log L) := by
    rw [hlogmul]
    nlinarith [hlog5, hlogL]
  have hsq : (1 + Real.log (5 * L)) ^ 2 ≤ ((1 + Real.log 5) * (1 + Real.log L)) ^ 2 := by
    have h0 : (0 : ℝ) ≤ 1 + Real.log (5 * L) := by
      rw [hlogmul]; linarith
    nlinarith [hsplit, h0]
  have hpowpos : (0 : ℝ) < L ^ ((9 : ℝ) / 10) := Real.rpow_pos_of_pos hL0 _
  have h5pos : (0 : ℝ) < (5 : ℝ) ^ ((9 : ℝ) / 10) := Real.rpow_pos_of_pos (by norm_num) _
  have hexp : ((1 + Real.log 5) * (1 + Real.log L)) ^ 2
      = (1 + Real.log 5) ^ 2 * (1 + Real.log L) ^ 2 := by ring
  rw [hexp] at hsq
  calc (5 * L) ^ ((9 : ℝ) / 10) * (1 + Real.log (5 * L)) ^ 2
      = ((5 : ℝ) ^ ((9 : ℝ) / 10) * L ^ ((9 : ℝ) / 10)) * (1 + Real.log (5 * L)) ^ 2 := by
        rw [hpow]
    _ ≤ ((5 : ℝ) ^ ((9 : ℝ) / 10) * L ^ ((9 : ℝ) / 10))
          * ((1 + Real.log 5) ^ 2 * (1 + Real.log L) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = (5 : ℝ) ^ ((9 : ℝ) / 10) * (1 + Real.log 5) ^ 2
          * (L ^ ((9 : ℝ) / 10) * (1 + |Real.log L|) ^ 2) := by rw [habs]; ring

set_option maxHeartbeats 1000000 in
/-- **The Route-T contour data below the doubled cutoff.**  The displacement beats `(log N)^{1/20}`
after multiplication by `log N`, the edge constant stays below `exp((log N)^{1/20})`, and the
reciprocal width exceeds `1/log N`. -/
theorem eventually_routeT_contour_rate_data (A δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℝ in atTop, ∀ S : ℝ, routeTInverseBaseHeight ≤ S → S ≤ 2 * N →
      10 * (Real.log N) ^ ((1 : ℝ) / 20) ≤ routeTContourShift A δ S * Real.log N
      ∧ routeTContourEdgeBound A S ≤ Real.exp ((Real.log N) ^ ((1 : ℝ) / 20))
      ∧ 1 / Real.log N ≤ routeTInverseDelta A S := by
  have hD := routeTZeroFreeDeltaEnvelopeConstant_pos A
  have hEA := routeTZeroFreeBudgetEnvelopeConstant_pos A
  have hlog5 : (0 : ℝ) ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  -- the three polylogarithmic thresholds, in the variable `L = log N`
  have hP1 : ∀ᶠ L : ℝ in atTop,
      200 * routeTZeroFreeDeltaEnvelopeConstant A
          * ((5 * L) ^ ((9 : ℝ) / 10) * (1 + Real.log (5 * L)) ^ 2)
        ≤ L ^ ((19 : ℝ) / 20) := by
    have hdom := eventually_const_mul_rpow_polylog_le_rpow
      (C := 200 * routeTZeroFreeDeltaEnvelopeConstant A
        * ((5 : ℝ) ^ ((9 : ℝ) / 10) * (1 + Real.log 5) ^ 2))
      (α := (9 : ℝ) / 10) (β := (19 : ℝ) / 20) 2 (by norm_num)
    filter_upwards [hdom, eventually_ge_atTop (1 : ℝ)] with L hdomL hL
    have hfive := five_log_polylog_le hL
    have hc : (0 : ℝ) ≤ 200 * routeTZeroFreeDeltaEnvelopeConstant A := by linarith
    calc 200 * routeTZeroFreeDeltaEnvelopeConstant A
            * ((5 * L) ^ ((9 : ℝ) / 10) * (1 + Real.log (5 * L)) ^ 2)
        ≤ 200 * routeTZeroFreeDeltaEnvelopeConstant A
            * ((5 : ℝ) ^ ((9 : ℝ) / 10) * (1 + Real.log 5) ^ 2
                * (L ^ ((9 : ℝ) / 10) * (1 + |Real.log L|) ^ 2)) :=
          mul_le_mul_of_nonneg_left hfive hc
      _ = 200 * routeTZeroFreeDeltaEnvelopeConstant A
            * ((5 : ℝ) ^ ((9 : ℝ) / 10) * (1 + Real.log 5) ^ 2)
            * L ^ ((9 : ℝ) / 10) * (1 + |Real.log L|) ^ 2 := by ring
      _ ≤ L ^ ((19 : ℝ) / 20) := hdomL
  have hP2 : ∀ᶠ L : ℝ in atTop,
      400 * (routeTZeroFreeBudgetEnvelopeConstant A + 2 * Real.log (5 * L)) ^ 2
        ≤ L ^ ((1 : ℝ) / 20) := by
    have hdom := eventually_const_mul_rpow_polylog_le_rpow
      (C := 400 * (routeTZeroFreeBudgetEnvelopeConstant A + 2 * Real.log 5 + 2) ^ 2)
      (α := (0 : ℝ)) (β := (1 : ℝ) / 20) 2 (by norm_num)
    filter_upwards [hdom, eventually_ge_atTop (1 : ℝ)] with L hdomL hL
    have hL0 : (0 : ℝ) < L := by linarith
    have hlogL : (0 : ℝ) ≤ Real.log L := Real.log_nonneg hL
    have habs : |Real.log L| = Real.log L := abs_of_nonneg hlogL
    have hlogmul : Real.log (5 * L) = Real.log 5 + Real.log L :=
      Real.log_mul (by norm_num) (ne_of_gt hL0)
    have hstep : routeTZeroFreeBudgetEnvelopeConstant A + 2 * Real.log (5 * L)
        ≤ (routeTZeroFreeBudgetEnvelopeConstant A + 2 * Real.log 5 + 2)
            * (1 + Real.log L) := by
      rw [hlogmul]
      nlinarith [hlogL, hlog5, hEA]
    have h0 : (0 : ℝ) ≤ routeTZeroFreeBudgetEnvelopeConstant A + 2 * Real.log (5 * L) := by
      rw [hlogmul]; linarith
    have hsq : (routeTZeroFreeBudgetEnvelopeConstant A + 2 * Real.log (5 * L)) ^ 2
        ≤ ((routeTZeroFreeBudgetEnvelopeConstant A + 2 * Real.log 5 + 2)
            * (1 + Real.log L)) ^ 2 := by nlinarith [hstep, h0]
    rw [Real.rpow_zero, mul_one, habs] at hdomL
    nlinarith [hsq, hdomL]
  have hP3 : ∀ᶠ L : ℝ in atTop, 200 * L ^ ((1 : ℝ) / 20) ≤ δ * L := by
    have hdom := eventually_const_mul_rpow_polylog_le_rpow
      (C := 200 / δ) (α := (1 : ℝ) / 20) (β := (1 : ℝ)) 0 (by norm_num)
    filter_upwards [hdom, eventually_ge_atTop (1 : ℝ)] with L hdomL hL
    have hL0 : (0 : ℝ) < L := by linarith
    rw [pow_zero, mul_one, Real.rpow_one] at hdomL
    rw [div_mul_eq_mul_div, div_le_iff₀ hδ] at hdomL
    linarith
  have hP4 : ∀ᶠ L : ℝ in atTop, (1 : ℝ) ≤ L ^ ((1 : ℝ) / 20) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    have h1 : ((1 : ℝ)) ^ ((1 : ℝ) / 20) ≤ L ^ ((1 : ℝ) / 20) :=
      Real.rpow_le_rpow (by norm_num) hL (by norm_num)
    rwa [Real.one_rpow] at h1
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (3 : ℝ),
    Real.tendsto_log_atTop.eventually hP1, Real.tendsto_log_atTop.eventually hP2,
    Real.tendsto_log_atTop.eventually hP3, Real.tendsto_log_atTop.eventually hP4]
    with N hN0 hL3 hp1 hp2 hp3 hp4
  intro S hSbase hS2N
  set L : ℝ := Real.log N with hLdef
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hL0 : (0 : ℝ) < L := by linarith
  have hbase := routeTInverseBaseHeight_ge
  have hS0 : (0 : ℝ) ≤ S := by linarith
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hSlo : 8 * Real.pi + 1 ≤ routeTInverseHeight S := by
    unfold routeTInverseHeight
    linarith
  have h2Nlo : 8 * Real.pi + 1 ≤ routeTInverseHeight (2 * N) := by
    unfold routeTInverseHeight
    linarith
  have hST : routeTInverseHeight S ≤ routeTInverseHeight (2 * N) := by
    unfold routeTInverseHeight
    linarith
  -- the envelope at the top of the range
  have hEnv := routeTLogHeightEnvelope_le_five_log (N := N) (S := 2 * N) hN0 hL3
    (by linarith) le_rfl
  have hEnv1 : (1 : ℝ) ≤ routeTLogHeightEnvelope (4 * routeTInverseHeight (2 * N)) :=
    one_le_routeTLogHeightEnvelope (by unfold routeTInverseHeight; linarith)
  set E : ℝ := routeTLogHeightEnvelope (4 * routeTInverseHeight (2 * N)) with hEdef
  have hE5L : E ≤ 5 * L := hEnv
  have hE1 : (1 : ℝ) ≤ E := hEnv1
  -- the polylogarithmic factor is monotone
  have hmono : E ^ ((9 : ℝ) / 10) * (1 + Real.log E) ^ 2
      ≤ (5 * L) ^ ((9 : ℝ) / 10) * (1 + Real.log (5 * L)) ^ 2 := by
    have h1 : E ^ ((9 : ℝ) / 10) ≤ (5 * L) ^ ((9 : ℝ) / 10) :=
      Real.rpow_le_rpow (by linarith) hE5L (by norm_num)
    have hlogE : (0 : ℝ) ≤ Real.log E := Real.log_nonneg hE1
    have h2 : Real.log E ≤ Real.log (5 * L) := Real.log_le_log (by linarith) hE5L
    have h3 : (1 + Real.log E) ^ 2 ≤ (1 + Real.log (5 * L)) ^ 2 := by nlinarith
    have h4 : (0 : ℝ) ≤ E ^ ((9 : ℝ) / 10) := Real.rpow_nonneg (by linarith) _
    nlinarith [h1, h3, h4, sq_nonneg (1 + Real.log E)]
  -- lower bound for the width at the top of the range
  have hlow := routeTZeroFreeDelta_polylog_lower (A := A) h2Nlo
  have hanti : routeTZeroFreeDelta A (routeTInverseHeight (2 * N))
      ≤ routeTZeroFreeDelta A (routeTInverseHeight S) :=
    routeTZeroFreeDelta_antitone hSlo hST
  have hdenpos : (0 : ℝ) < routeTZeroFreeDeltaEnvelopeConstant A
      * E ^ ((9 : ℝ) / 10) * (1 + Real.log E) ^ 2 := by
    have h4 : (0 : ℝ) < E ^ ((9 : ℝ) / 10) := Real.rpow_pos_of_pos (by linarith) _
    have hlogE : (0 : ℝ) ≤ Real.log E := Real.log_nonneg hE1
    positivity
  have hdenle : routeTZeroFreeDeltaEnvelopeConstant A
      * E ^ ((9 : ℝ) / 10) * (1 + Real.log E) ^ 2 ≤ L ^ ((19 : ℝ) / 20) / 200 := by
    have hstep : routeTZeroFreeDeltaEnvelopeConstant A
        * (E ^ ((9 : ℝ) / 10) * (1 + Real.log E) ^ 2)
        ≤ routeTZeroFreeDeltaEnvelopeConstant A
            * ((5 * L) ^ ((9 : ℝ) / 10) * (1 + Real.log (5 * L)) ^ 2) :=
      mul_le_mul_of_nonneg_left hmono hD.le
    have := hp1
    nlinarith [hstep, this]
  have hpow19 : L ^ ((19 : ℝ) / 20) * L ^ ((1 : ℝ) / 20) = L := by
    rw [← Real.rpow_add hL0]
    norm_num
  have hpow20 : (0 : ℝ) < L ^ ((1 : ℝ) / 20) := Real.rpow_pos_of_pos hL0 _
  have hpow19pos : (0 : ℝ) < L ^ ((19 : ℝ) / 20) := Real.rpow_pos_of_pos hL0 _
  have hfin : 1 / (routeTZeroFreeDeltaEnvelopeConstant A
      * E ^ ((9 : ℝ) / 10) * (1 + Real.log E) ^ 2)
      ≤ routeTInverseDelta A S := by
    have h0 : 1 / (routeTZeroFreeDeltaEnvelopeConstant A
        * E ^ ((9 : ℝ) / 10) * (1 + Real.log E) ^ 2)
        ≤ routeTZeroFreeDelta A (routeTInverseHeight (2 * N)) := by
      simpa only [hEdef] using hlow
    unfold routeTInverseDelta
    linarith [h0, hanti]
  have hwidthL : 200 * L ^ ((1 : ℝ) / 20) ≤ routeTInverseDelta A S * L := by
    set den : ℝ := routeTZeroFreeDeltaEnvelopeConstant A
      * E ^ ((9 : ℝ) / 10) * (1 + Real.log E) ^ 2 with hdendef
    have hone : 1 ≤ routeTInverseDelta A S * den := (div_le_iff₀ hdenpos).1 hfin
    have hprod : 200 * L ^ ((1 : ℝ) / 20) * den ≤ L := by
      have hstep : 200 * L ^ ((1 : ℝ) / 20) * den
          ≤ 200 * L ^ ((1 : ℝ) / 20) * (L ^ ((19 : ℝ) / 20) / 200) := by
        have hc : (0 : ℝ) ≤ 200 * L ^ ((1 : ℝ) / 20) := by positivity
        exact mul_le_mul_of_nonneg_left hdenle hc
      have heq : 200 * L ^ ((1 : ℝ) / 20) * (L ^ ((19 : ℝ) / 20) / 200)
          = L ^ ((19 : ℝ) / 20) * L ^ ((1 : ℝ) / 20) := by ring
      rw [heq, hpow19] at hstep
      exact hstep
    have hΔ0 : 0 < routeTInverseDelta A S := routeTInverseDelta_pos A S
    have hstep1 : routeTInverseDelta A S * (200 * L ^ ((1 : ℝ) / 20) * den)
        ≤ routeTInverseDelta A S * L := mul_le_mul_of_nonneg_left hprod hΔ0.le
    have heq2 : routeTInverseDelta A S * (200 * L ^ ((1 : ℝ) / 20) * den)
        = 200 * L ^ ((1 : ℝ) / 20) * (routeTInverseDelta A S * den) := by ring
    have hstep2 : 200 * L ^ ((1 : ℝ) / 20)
        ≤ 200 * L ^ ((1 : ℝ) / 20) * (routeTInverseDelta A S * den) := by
      have h := mul_le_mul_of_nonneg_left hone
        (show (0 : ℝ) ≤ 200 * L ^ ((1 : ℝ) / 20) by positivity)
      simpa using h
    rw [heq2] at hstep1
    linarith
  have hshiftL : 10 * L ^ ((1 : ℝ) / 20) ≤ routeTContourShift A δ S * L := by
    have h1 : 10 * L ^ ((1 : ℝ) / 20) ≤ routeTInverseDelta A S / 20 * L := by
      linarith [hwidthL]
    have h2 : 10 * L ^ ((1 : ℝ) / 20) ≤ δ / 2 * L := by linarith [hp3]
    unfold routeTContourShift
    rcases le_total (routeTInverseDelta A S / 20) (δ / 2) with h | h
    · rw [min_eq_left h]; exact h1
    · rw [min_eq_right h]; exact h2
  -- (2) the edge constant
  have hedge : routeTContourEdgeBound A S ≤ Real.exp (L ^ ((1 : ℝ) / 20)) := by
    have hbmono : routeTZeroFreeBudget A (routeTInverseHeight S)
        ≤ routeTZeroFreeBudget A (routeTInverseHeight (2 * N)) :=
      routeTZeroFreeBudget_mono hSlo hST
    have hbupper := routeTZeroFreeBudget_logHeight_upper (A := A) h2Nlo
    have hbge := routeTZeroFreeBudget_ge A (routeTInverseHeight S)
    have hlogE : Real.log E ≤ Real.log (5 * L) := Real.log_le_log (by linarith) hE5L
    have hchain : routeTZeroFreeBudget A (routeTInverseHeight S)
        ≤ routeTZeroFreeBudgetEnvelopeConstant A + 2 * Real.log (5 * L) := by
      have : routeTZeroFreeBudget A (routeTInverseHeight (2 * N))
          ≤ routeTZeroFreeBudgetEnvelopeConstant A + 2 * Real.log E := by
        simpa only [hEdef] using hbupper
      linarith
    have hsq : 400 * routeTZeroFreeBudget A (routeTInverseHeight S) ^ 2
        ≤ 400 * (routeTZeroFreeBudgetEnvelopeConstant A + 2 * Real.log (5 * L)) ^ 2 := by
      have hb0 : (0 : ℝ) ≤ routeTZeroFreeBudget A (routeTInverseHeight S) := by linarith
      have hmm := mul_self_le_mul_self hb0 hchain
      nlinarith [hmm]
    unfold routeTContourEdgeBound
    exact Real.exp_le_exp.2 (by linarith [hsq, hp2])
  -- (3) the abscissa fits inside the rectangle
  have hinv : 1 / L ≤ routeTInverseDelta A S := by
    rw [div_le_iff₀ hL0]
    nlinarith [hwidthL, hp4]
  exact ⟨hshiftL, hedge, hinv⟩

end

end RHTower.Sieve
