import GaloisForLFunctions.RHTower.Sieve.RouteTContourRateBounds

/-!
# Route-T contour data on Menon's polynomial frequency range

Menon's degree-three Heath--Brown argument uses a Mobius atom of length `N` at ordinates as
large as `N^(24 : ℕ)`.  The all-height Route-T contour already applies there.  This file proves the
uniform rate data needed to retain the same super-polylogarithmic saving on that full range.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- On the range `S <= 2 N^(24 : ℕ)`, the Route-T log-height envelope is still bounded by a fixed
multiple of `log N`. -/
theorem routeTLogHeightEnvelope_le_sixtyFour_log_of_le_pow_twentyFour
    {N S : ℝ} (hN0 : 0 < N) (hN : 3 ≤ Real.log N)
    (hS0 : 0 ≤ S) (hS : S ≤ 2 * N ^ (24 : ℕ)) :
    routeTLogHeightEnvelope (4 * routeTInverseHeight S) ≤ 64 * Real.log N := by
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
  have hN20 : (20 : ℝ) ≤ N := he3.trans hNe
  have hN24 : (1 : ℝ) ≤ N ^ (24 : ℕ) := one_le_pow₀ (by linarith)
  have hN2 : (400 : ℝ) ≤ N ^ (2 : ℕ) := by nlinarith
  have harg : 4 * routeTInverseHeight S + 2 ≤ N ^ (26 : ℕ) := by
    have hfirst : 4 * routeTInverseHeight S + 2 ≤ 32 * N ^ (24 : ℕ) + 18 := by
      unfold routeTInverseHeight
      nlinarith
    have hmiddle : 32 * N ^ (24 : ℕ) + 18 ≤ 400 * N ^ (24 : ℕ) := by
      nlinarith
    have hlast : 400 * N ^ (24 : ℕ) ≤ N ^ (2 : ℕ) * N ^ (24 : ℕ) :=
      mul_le_mul_of_nonneg_right hN2 (pow_nonneg hN0.le 24)
    calc
      4 * routeTInverseHeight S + 2 ≤ 32 * N ^ (24 : ℕ) + 18 := hfirst
      _ ≤ 400 * N ^ (24 : ℕ) := hmiddle
      _ ≤ N ^ (2 : ℕ) * N ^ (24 : ℕ) := hlast
      _ = N ^ (26 : ℕ) := by ring
  have hpos : (0 : ℝ) < 4 * routeTInverseHeight S + 2 := by
    unfold routeTInverseHeight
    linarith
  have hlog : Real.log (4 * routeTInverseHeight S + 2) ≤ Real.log (N ^ (26 : ℕ)) :=
    Real.log_le_log hpos harg
  have hpow : Real.log (N ^ (26 : ℕ)) = 26 * Real.log N := by
    rw [Real.log_pow]
    norm_num
  unfold routeTLogHeightEnvelope
  rw [hpow] at hlog
  nlinarith

/-- A fixed dilation of `L` has the same polylogarithmic order as `L`. -/
private theorem sixtyFour_log_polylog_le {L : ℝ} (hL : 1 ≤ L) :
    (64 * L) ^ ((9 : ℝ) / 10) * (1 + Real.log (64 * L)) ^ 2
      ≤ (64 : ℝ) ^ ((9 : ℝ) / 10) * (1 + Real.log 64) ^ 2
          * (L ^ ((9 : ℝ) / 10) * (1 + |Real.log L|) ^ 2) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hlogL : (0 : ℝ) ≤ Real.log L := Real.log_nonneg hL
  have habs : |Real.log L| = Real.log L := abs_of_nonneg hlogL
  have hlog64 : (0 : ℝ) ≤ Real.log 64 := Real.log_nonneg (by norm_num)
  have hpow : (64 * L) ^ ((9 : ℝ) / 10) =
      (64 : ℝ) ^ ((9 : ℝ) / 10) * L ^ ((9 : ℝ) / 10) :=
    Real.mul_rpow (by norm_num) hL0.le
  have hlogmul : Real.log (64 * L) = Real.log 64 + Real.log L :=
    Real.log_mul (by norm_num) (ne_of_gt hL0)
  have hsplit : 1 + Real.log (64 * L) ≤
      (1 + Real.log 64) * (1 + Real.log L) := by
    rw [hlogmul]
    nlinarith
  have hsq : (1 + Real.log (64 * L)) ^ 2 ≤
      ((1 + Real.log 64) * (1 + Real.log L)) ^ 2 := by
    have h0 : (0 : ℝ) ≤ 1 + Real.log (64 * L) := by
      rw [hlogmul]
      linarith
    nlinarith
  have hexp : ((1 + Real.log 64) * (1 + Real.log L)) ^ 2 =
      (1 + Real.log 64) ^ 2 * (1 + Real.log L) ^ 2 := by ring
  rw [hexp] at hsq
  calc
    (64 * L) ^ ((9 : ℝ) / 10) * (1 + Real.log (64 * L)) ^ 2 =
        ((64 : ℝ) ^ ((9 : ℝ) / 10) * L ^ ((9 : ℝ) / 10)) *
          (1 + Real.log (64 * L)) ^ 2 := by rw [hpow]
    _ ≤ ((64 : ℝ) ^ ((9 : ℝ) / 10) * L ^ ((9 : ℝ) / 10)) *
          ((1 + Real.log 64) ^ 2 * (1 + Real.log L) ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = (64 : ℝ) ^ ((9 : ℝ) / 10) * (1 + Real.log 64) ^ 2 *
          (L ^ ((9 : ℝ) / 10) * (1 + |Real.log L|) ^ 2) := by
      rw [habs]
      ring

set_option maxHeartbeats 1000000 in
/-- Route-T displacement, edge, and width data uniformly for
`routeTInverseBaseHeight <= S <= 2 N^(24 : ℕ)`. -/
theorem eventually_routeT_contour_rate_data_pow_twentyFour
    (A delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ N : ℝ in atTop, ∀ S : ℝ,
      routeTInverseBaseHeight ≤ S → S ≤ 2 * N ^ (24 : ℕ) →
      10 * (Real.log N) ^ ((1 : ℝ) / 20) ≤
          routeTContourShift A delta S * Real.log N
      ∧ routeTContourEdgeBound A S ≤
          Real.exp ((Real.log N) ^ ((1 : ℝ) / 20))
      ∧ 1 / Real.log N ≤ routeTInverseDelta A S := by
  have hD := routeTZeroFreeDeltaEnvelopeConstant_pos A
  have hEA := routeTZeroFreeBudgetEnvelopeConstant_pos A
  have hlog64 : (0 : ℝ) ≤ Real.log 64 := Real.log_nonneg (by norm_num)
  have hP1 : ∀ᶠ L : ℝ in atTop,
      200 * routeTZeroFreeDeltaEnvelopeConstant A *
          ((64 * L) ^ ((9 : ℝ) / 10) * (1 + Real.log (64 * L)) ^ 2)
        ≤ L ^ ((19 : ℝ) / 20) := by
    have hdom := eventually_const_mul_rpow_polylog_le_rpow
      (C := 200 * routeTZeroFreeDeltaEnvelopeConstant A *
        ((64 : ℝ) ^ ((9 : ℝ) / 10) * (1 + Real.log 64) ^ 2))
      (α := (9 : ℝ) / 10) (β := (19 : ℝ) / 20) 2 (by norm_num)
    filter_upwards [hdom, eventually_ge_atTop (1 : ℝ)] with L hdomL hL
    have hsixtyFour := sixtyFour_log_polylog_le hL
    have hc : (0 : ℝ) ≤ 200 * routeTZeroFreeDeltaEnvelopeConstant A := by linarith
    calc
      200 * routeTZeroFreeDeltaEnvelopeConstant A *
          ((64 * L) ^ ((9 : ℝ) / 10) * (1 + Real.log (64 * L)) ^ 2)
          ≤ 200 * routeTZeroFreeDeltaEnvelopeConstant A *
            ((64 : ℝ) ^ ((9 : ℝ) / 10) * (1 + Real.log 64) ^ 2 *
              (L ^ ((9 : ℝ) / 10) * (1 + |Real.log L|) ^ 2)) :=
            mul_le_mul_of_nonneg_left hsixtyFour hc
      _ = 200 * routeTZeroFreeDeltaEnvelopeConstant A *
            ((64 : ℝ) ^ ((9 : ℝ) / 10) * (1 + Real.log 64) ^ 2) *
              L ^ ((9 : ℝ) / 10) * (1 + |Real.log L|) ^ 2 := by ring
      _ ≤ L ^ ((19 : ℝ) / 20) := hdomL
  have hP2 : ∀ᶠ L : ℝ in atTop,
      400 * (routeTZeroFreeBudgetEnvelopeConstant A + 2 * Real.log (64 * L)) ^ 2
        ≤ L ^ ((1 : ℝ) / 20) := by
    have hdom := eventually_const_mul_rpow_polylog_le_rpow
      (C := 400 * (routeTZeroFreeBudgetEnvelopeConstant A + 2 * Real.log 64 + 2) ^ 2)
      (α := (0 : ℝ)) (β := (1 : ℝ) / 20) 2 (by norm_num)
    filter_upwards [hdom, eventually_ge_atTop (1 : ℝ)] with L hdomL hL
    have hL0 : (0 : ℝ) < L := by linarith
    have hlogL : (0 : ℝ) ≤ Real.log L := Real.log_nonneg hL
    have habs : |Real.log L| = Real.log L := abs_of_nonneg hlogL
    have hlogmul : Real.log (64 * L) = Real.log 64 + Real.log L :=
      Real.log_mul (by norm_num) (ne_of_gt hL0)
    have hstep : routeTZeroFreeBudgetEnvelopeConstant A + 2 * Real.log (64 * L)
        ≤ (routeTZeroFreeBudgetEnvelopeConstant A + 2 * Real.log 64 + 2) *
            (1 + Real.log L) := by
      rw [hlogmul]
      nlinarith
    have h0 : (0 : ℝ) ≤
        routeTZeroFreeBudgetEnvelopeConstant A + 2 * Real.log (64 * L) := by
      rw [hlogmul]
      linarith
    have hsq : (routeTZeroFreeBudgetEnvelopeConstant A + 2 * Real.log (64 * L)) ^ 2
        ≤ ((routeTZeroFreeBudgetEnvelopeConstant A + 2 * Real.log 64 + 2) *
            (1 + Real.log L)) ^ 2 := by nlinarith
    rw [Real.rpow_zero, mul_one, habs] at hdomL
    nlinarith
  have hP3 : ∀ᶠ L : ℝ in atTop,
      200 * L ^ ((1 : ℝ) / 20) ≤ delta * L := by
    have hdom := eventually_const_mul_rpow_polylog_le_rpow
      (C := 200 / delta) (α := (1 : ℝ) / 20) (β := (1 : ℝ)) 0 (by norm_num)
    filter_upwards [hdom, eventually_ge_atTop (1 : ℝ)] with L hdomL hL
    rw [pow_zero, mul_one, Real.rpow_one] at hdomL
    rw [div_mul_eq_mul_div, div_le_iff₀ hdelta] at hdomL
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
  intro S hSbase hSupper
  set L : ℝ := Real.log N with hLdef
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hL0 : (0 : ℝ) < L := by linarith
  have hbase := routeTInverseBaseHeight_ge
  have hS0 : (0 : ℝ) ≤ S := by linarith
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hSlo : 8 * Real.pi + 1 ≤ routeTInverseHeight S := by
    unfold routeTInverseHeight
    linarith
  have hTop0 : (0 : ℝ) ≤ 2 * N ^ (24 : ℕ) := by positivity
  have hToplo : 8 * Real.pi + 1 ≤
      routeTInverseHeight (2 * N ^ (24 : ℕ)) := by
    unfold routeTInverseHeight
    linarith
  have hST : routeTInverseHeight S ≤
      routeTInverseHeight (2 * N ^ (24 : ℕ)) := by
    unfold routeTInverseHeight
    linarith
  have hEnv := routeTLogHeightEnvelope_le_sixtyFour_log_of_le_pow_twentyFour
    (N := N) (S := 2 * N ^ (24 : ℕ)) hN0 hL3 hTop0 le_rfl
  have hEnv1 : (1 : ℝ) ≤
      routeTLogHeightEnvelope (4 * routeTInverseHeight (2 * N ^ (24 : ℕ))) :=
    one_le_routeTLogHeightEnvelope (by unfold routeTInverseHeight; linarith)
  set E : ℝ :=
    routeTLogHeightEnvelope (4 * routeTInverseHeight (2 * N ^ (24 : ℕ))) with hEdef
  have hE64L : E ≤ 64 * L := hEnv
  have hE1 : (1 : ℝ) ≤ E := hEnv1
  have hmono : E ^ ((9 : ℝ) / 10) * (1 + Real.log E) ^ 2
      ≤ (64 * L) ^ ((9 : ℝ) / 10) * (1 + Real.log (64 * L)) ^ 2 := by
    have h1 : E ^ ((9 : ℝ) / 10) ≤ (64 * L) ^ ((9 : ℝ) / 10) :=
      Real.rpow_le_rpow (by linarith) hE64L (by norm_num)
    have hlogE : (0 : ℝ) ≤ Real.log E := Real.log_nonneg hE1
    have h2 : Real.log E ≤ Real.log (64 * L) :=
      Real.log_le_log (by linarith) hE64L
    have h3 : (1 + Real.log E) ^ 2 ≤ (1 + Real.log (64 * L)) ^ 2 := by
      nlinarith
    have h4 : (0 : ℝ) ≤ E ^ ((9 : ℝ) / 10) := Real.rpow_nonneg (by linarith) _
    nlinarith [h1, h3, h4, sq_nonneg (1 + Real.log E)]
  have hlow := routeTZeroFreeDelta_polylog_lower (A := A) hToplo
  have hanti : routeTZeroFreeDelta A (routeTInverseHeight (2 * N ^ (24 : ℕ)))
      ≤ routeTZeroFreeDelta A (routeTInverseHeight S) :=
    routeTZeroFreeDelta_antitone hSlo hST
  have hdenpos : (0 : ℝ) < routeTZeroFreeDeltaEnvelopeConstant A *
      E ^ ((9 : ℝ) / 10) * (1 + Real.log E) ^ 2 := by
    have h4 : (0 : ℝ) < E ^ ((9 : ℝ) / 10) := Real.rpow_pos_of_pos (by linarith) _
    have hlogE : (0 : ℝ) ≤ Real.log E := Real.log_nonneg hE1
    positivity
  have hdenle : routeTZeroFreeDeltaEnvelopeConstant A *
      E ^ ((9 : ℝ) / 10) * (1 + Real.log E) ^ 2
      ≤ L ^ ((19 : ℝ) / 20) / 200 := by
    have hstep : routeTZeroFreeDeltaEnvelopeConstant A *
        (E ^ ((9 : ℝ) / 10) * (1 + Real.log E) ^ 2)
        ≤ routeTZeroFreeDeltaEnvelopeConstant A *
          ((64 * L) ^ ((9 : ℝ) / 10) * (1 + Real.log (64 * L)) ^ 2) :=
      mul_le_mul_of_nonneg_left hmono hD.le
    nlinarith
  have hpow19 : L ^ ((19 : ℝ) / 20) * L ^ ((1 : ℝ) / 20) = L := by
    rw [← Real.rpow_add hL0]
    norm_num
  have hfin : 1 / (routeTZeroFreeDeltaEnvelopeConstant A *
      E ^ ((9 : ℝ) / 10) * (1 + Real.log E) ^ 2)
      ≤ routeTInverseDelta A S := by
    have h0 : 1 / (routeTZeroFreeDeltaEnvelopeConstant A *
        E ^ ((9 : ℝ) / 10) * (1 + Real.log E) ^ 2)
        ≤ routeTZeroFreeDelta A (routeTInverseHeight (2 * N ^ (24 : ℕ))) := by
      simpa only [hEdef] using hlow
    unfold routeTInverseDelta
    linarith
  have hwidthL : 200 * L ^ ((1 : ℝ) / 20) ≤ routeTInverseDelta A S * L := by
    set den : ℝ := routeTZeroFreeDeltaEnvelopeConstant A *
      E ^ ((9 : ℝ) / 10) * (1 + Real.log E) ^ 2 with hdendef
    have hone : 1 ≤ routeTInverseDelta A S * den := (div_le_iff₀ hdenpos).1 hfin
    have hprod : 200 * L ^ ((1 : ℝ) / 20) * den ≤ L := by
      have hstep : 200 * L ^ ((1 : ℝ) / 20) * den
          ≤ 200 * L ^ ((1 : ℝ) / 20) * (L ^ ((19 : ℝ) / 20) / 200) :=
        mul_le_mul_of_nonneg_left hdenle (by positivity)
      have heq : 200 * L ^ ((1 : ℝ) / 20) * (L ^ ((19 : ℝ) / 20) / 200)
          = L ^ ((19 : ℝ) / 20) * L ^ ((1 : ℝ) / 20) := by ring
      rw [heq, hpow19] at hstep
      exact hstep
    have hDelta0 : 0 < routeTInverseDelta A S := routeTInverseDelta_pos A S
    have hstep1 : routeTInverseDelta A S *
        (200 * L ^ ((1 : ℝ) / 20) * den) ≤ routeTInverseDelta A S * L :=
      mul_le_mul_of_nonneg_left hprod hDelta0.le
    have heq2 : routeTInverseDelta A S *
        (200 * L ^ ((1 : ℝ) / 20) * den) =
          200 * L ^ ((1 : ℝ) / 20) * (routeTInverseDelta A S * den) := by ring
    have hstep2 : 200 * L ^ ((1 : ℝ) / 20) ≤
        200 * L ^ ((1 : ℝ) / 20) * (routeTInverseDelta A S * den) := by
      simpa using mul_le_mul_of_nonneg_left hone
        (show (0 : ℝ) ≤ 200 * L ^ ((1 : ℝ) / 20) by positivity)
    rw [heq2] at hstep1
    linarith
  have hshiftL : 10 * L ^ ((1 : ℝ) / 20) ≤ routeTContourShift A delta S * L := by
    have h1 : 10 * L ^ ((1 : ℝ) / 20) ≤ routeTInverseDelta A S / 20 * L := by
      linarith
    have h2 : 10 * L ^ ((1 : ℝ) / 20) ≤ delta / 2 * L := by
      linarith
    unfold routeTContourShift
    rcases le_total (routeTInverseDelta A S / 20) (delta / 2) with h | h
    · rw [min_eq_left h]
      exact h1
    · rw [min_eq_right h]
      exact h2
  have hedge : routeTContourEdgeBound A S ≤ Real.exp (L ^ ((1 : ℝ) / 20)) := by
    have hbmono : routeTZeroFreeBudget A (routeTInverseHeight S)
        ≤ routeTZeroFreeBudget A (routeTInverseHeight (2 * N ^ (24 : ℕ))) :=
      routeTZeroFreeBudget_mono hSlo hST
    have hbupper := routeTZeroFreeBudget_logHeight_upper (A := A) hToplo
    have hbge := routeTZeroFreeBudget_ge A (routeTInverseHeight S)
    have hlogE : Real.log E ≤ Real.log (64 * L) :=
      Real.log_le_log (by linarith) hE64L
    have hchain : routeTZeroFreeBudget A (routeTInverseHeight S)
        ≤ routeTZeroFreeBudgetEnvelopeConstant A + 2 * Real.log (64 * L) := by
      have htop : routeTZeroFreeBudget A (routeTInverseHeight (2 * N ^ (24 : ℕ)))
          ≤ routeTZeroFreeBudgetEnvelopeConstant A + 2 * Real.log E := by
        simpa only [hEdef] using hbupper
      linarith
    have hsq : 400 * routeTZeroFreeBudget A (routeTInverseHeight S) ^ 2
        ≤ 400 * (routeTZeroFreeBudgetEnvelopeConstant A + 2 * Real.log (64 * L)) ^ 2 := by
      have hb0 : (0 : ℝ) ≤ routeTZeroFreeBudget A (routeTInverseHeight S) := by
        linarith
      have hmm := mul_self_le_mul_self hb0 hchain
      nlinarith
    unfold routeTContourEdgeBound
    exact Real.exp_le_exp.2 (by linarith)
  have hinv : 1 / L ≤ routeTInverseDelta A S := by
    rw [div_le_iff₀ hL0]
    nlinarith
  exact ⟨hshiftL, hedge, hinv⟩

end

end RHTower.Sieve
