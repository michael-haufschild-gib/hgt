import GaloisForLFunctions.RHTower.Sieve.RouteTZetaAsymptotics

/-!
# Route T zero-free edge absorbs every fixed polylogarithm

The explicit Route-T displacement has size approximately
`log(T)^(-9/10) / log(log(T))^(2 : ℕ)`.  Consequently its exponential gain has logarithm
`delta(T) * log T`, which diverges like a positive tenth power modulo iterated logarithms.
This file proves the exact corpus-level statement needed by the zero-density layer cake:
`T ^ (-c * delta(T))` beats every fixed power of `1 + log T`.
-/

open Filter Topology

namespace RHTower.Sieve

noncomputable section

theorem routeTContourEdgeLogEnvelope_one_le
    (A : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    1 ≤ routeTContourEdgeLogEnvelope A T := by
  have hCpos : 0 < routeTZeroFreeBudgetEnvelopeConstant A + 2 := by
    linarith [routeTZeroFreeBudgetEnvelopeConstant_pos A]
  have hC0 := routeTZeroFreeBudgetEnvelopeConstant_pos A
  have hC : 1 ≤ routeTZeroFreeBudgetEnvelopeConstant A + 2 := by linarith
  have hZ : 1 ≤ routeTLogHeightEnvelope (4 * (T + 1)) :=
    routeTLogHeightEnvelope_one_le (by positivity)
  have hL : 1 ≤ 1 + Real.log (routeTLogHeightEnvelope (4 * (T + 1))) := by
    linarith [Real.log_nonneg hZ]
  unfold routeTContourEdgeLogEnvelope
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ hC))
    (one_le_pow₀ hL)

/-- Route T's zero-free displacement times logarithmic height diverges. -/
theorem tendsto_routeTContourShiftEnvelope_mul_log_atTop (A : ℝ) :
    Tendsto (fun T : ℝ => routeTContourShiftEnvelope A T * Real.log T)
      atTop atTop := by
  apply tendsto_atTop.2
  intro b
  let K : ℝ := max b 0
  have hK : 0 ≤ K := by exact le_max_right _ _
  have habsorb :=
    eventually_const_mul_routeTContourEdgeLogEnvelope_le_shiftGain A K hK
  filter_upwards [habsorb, eventually_ge_atTop (0 : ℝ)] with T habsorbT hT
  have hcost : 1 ≤ routeTContourEdgeLogEnvelope A T :=
    routeTContourEdgeLogEnvelope_one_le A hT
  calc
    b ≤ K := le_max_left _ _
    _ = K * 1 := by ring
    _ ≤ K * routeTContourEdgeLogEnvelope A T :=
      mul_le_mul_of_nonneg_left hcost hK
    _ ≤ routeTContourShiftEnvelope A T * Real.log T := habsorbT

theorem eventually_log_one_add_log_le_routeTContourEdgeLogEnvelope (A : ℝ) :
    ∀ᶠ T : ℝ in atTop,
      Real.log (1 + Real.log T) ≤ routeTContourEdgeLogEnvelope A T := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hTpos : 0 < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  let Z : ℝ := routeTLogHeightEnvelope (4 * (T + 1))
  have harg : T ≤ 4 * (T + 1) + 2 := by linarith
  have hargpos : 0 < 4 * (T + 1) + 2 := by positivity
  have hlogarg : Real.log T ≤ Real.log (4 * (T + 1) + 2) :=
    Real.log_le_log hTpos harg
  have hbaseZ : 1 + Real.log T ≤ Z := by
    dsimp only [Z, routeTLogHeightEnvelope]
    linarith
  have hbasepos : 0 < 1 + Real.log T := by linarith
  have hZpos : 0 < Z := lt_of_lt_of_le hbasepos hbaseZ
  have hlogZ : Real.log (1 + Real.log T) ≤ Real.log Z :=
    Real.log_le_log hbasepos hbaseZ
  have hC0 := routeTZeroFreeBudgetEnvelopeConstant_pos A
  have hC : 1 ≤ routeTZeroFreeBudgetEnvelopeConstant A + 2 := by linarith
  have hZone : 1 ≤ Z := by
    dsimp only [Z]
    exact routeTLogHeightEnvelope_one_le (by positivity)
  have hL : 1 ≤ 1 + Real.log Z := by linarith [Real.log_nonneg hZone]
  have hcoef : 1 ≤
      400 * (routeTZeroFreeBudgetEnvelopeConstant A + 2) ^ 2 *
        (1 + Real.log Z) := by
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ hC)) hL
  calc
    Real.log (1 + Real.log T) ≤ Real.log Z := hlogZ
    _ ≤ 1 + Real.log Z := by linarith
    _ = 1 * (1 + Real.log Z) := by ring
    _ ≤ (400 * (routeTZeroFreeBudgetEnvelopeConstant A + 2) ^ 2 *
          (1 + Real.log Z)) * (1 + Real.log Z) :=
      mul_le_mul_of_nonneg_right hcoef (by linarith)
    _ = routeTContourEdgeLogEnvelope A T := by
      dsimp only [Z]
      unfold routeTContourEdgeLogEnvelope
      ring

/-- Every fixed polylogarithm is eventually bounded by any positive fraction of Route T's
zero-free exponential gain. -/
theorem eventually_one_add_log_pow_le_exp_routeTShiftGain
    (A c : ℝ) (hc : 0 < c) (n : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      (1 + Real.log T) ^ n ≤
        Real.exp (c * routeTContourShiftEnvelope A T * Real.log T) := by
  let K : ℝ := (n : ℝ) / c
  have hK : 0 ≤ K := by positivity
  have habsorb :=
    eventually_const_mul_routeTContourEdgeLogEnvelope_le_shiftGain A K hK
  filter_upwards [habsorb,
    eventually_log_one_add_log_le_routeTContourEdgeLogEnvelope A,
    eventually_ge_atTop (1 : ℝ)] with T habsorbT hlogcost hT
  have hbase : 0 < 1 + Real.log T := by
    linarith [Real.log_nonneg hT]
  have hexponent :
      (n : ℝ) * Real.log (1 + Real.log T) ≤
        c * routeTContourShiftEnvelope A T * Real.log T := by
    calc
      (n : ℝ) * Real.log (1 + Real.log T) ≤
          (n : ℝ) * routeTContourEdgeLogEnvelope A T :=
        mul_le_mul_of_nonneg_left hlogcost (Nat.cast_nonneg n)
      _ = c * (K * routeTContourEdgeLogEnvelope A T) := by
        dsimp only [K]
        field_simp [hc.ne']
      _ ≤ c * (routeTContourShiftEnvelope A T * Real.log T) :=
        mul_le_mul_of_nonneg_left habsorbT hc.le
      _ = c * routeTContourShiftEnvelope A T * Real.log T := by ring
  rw [← Real.exp_log (pow_pos hbase n)]
  apply Real.exp_le_exp.mpr
  rw [Real.log_pow]
  exact hexponent

/-- Route T's edge power beats every fixed polylogarithm. -/
theorem tendsto_one_add_log_pow_mul_routeTShiftPower_zero
    (A : ℝ) {c : ℝ} (hc : 0 < c) (n : ℕ) :
    Tendsto (fun T : ℝ =>
      (1 + Real.log T) ^ n *
        T ^ (-c * routeTContourShiftEnvelope A T)) atTop (𝓝 0) := by
  have hgain : Tendsto
      (fun T : ℝ => (c / 2) *
        (routeTContourShiftEnvelope A T * Real.log T)) atTop atTop :=
    (tendsto_routeTContourShiftEnvelope_mul_log_atTop A).const_mul_atTop
      (by positivity)
  have hupper : Tendsto (fun T : ℝ =>
      Real.exp (-((c / 2) *
        (routeTContourShiftEnvelope A T * Real.log T)))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hgain
  have habsorb :=
    eventually_one_add_log_pow_le_exp_routeTShiftGain A (c / 2) (by positivity) n
  have hcomparison : ∀ᶠ T : ℝ in atTop,
      (1 + Real.log T) ^ n *
          T ^ (-c * routeTContourShiftEnvelope A T) ≤
        Real.exp (-((c / 2) *
          (routeTContourShiftEnvelope A T * Real.log T))) := by
    filter_upwards [habsorb, eventually_gt_atTop (0 : ℝ)] with T habsorbT hT
    rw [Real.rpow_def_of_pos hT]
    have hmul := mul_le_mul_of_nonneg_right habsorbT
      (Real.exp_pos (Real.log T * (-c * routeTContourShiftEnvelope A T))).le
    calc
      (1 + Real.log T) ^ n *
          Real.exp (Real.log T * (-c * routeTContourShiftEnvelope A T)) ≤
        Real.exp ((c / 2) * routeTContourShiftEnvelope A T * Real.log T) *
          Real.exp (Real.log T * (-c * routeTContourShiftEnvelope A T)) := hmul
      _ = Real.exp (-((c / 2) *
          (routeTContourShiftEnvelope A T * Real.log T))) := by
        rw [← Real.exp_add]
        congr 1
        ring
  refine squeeze_zero' ?_ hcomparison hupper
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hbase : 0 ≤ 1 + Real.log T := by linarith [Real.log_nonneg hT]
  exact mul_nonneg (pow_nonneg hbase _) (Real.rpow_nonneg (by positivity) _)

end

end RHTower.Sieve
