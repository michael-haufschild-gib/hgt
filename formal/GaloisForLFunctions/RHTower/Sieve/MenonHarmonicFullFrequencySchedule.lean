import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicPrimeScaledBound
import GaloisForLFunctions.RHTower.Sieve.TwoRangeHighBound

/-!
# Menon's Route-T schedule through the full physical frequency range

The existing two-range specialization stops at a subpower frequency.  Menon's final prime ladder
starts at `exp ((log x)^(19/20))`, so the same zero-free-region estimate remains logarithmically
negligible all the way to physical frequency `|w| <= x`.  This file records the scalar schedule
needed for that full-frequency specialization.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- Route-T width at the full physical-frequency endpoint `2 * pi * x`. -/
def menonHarmonicFullFrequencyMu (A delta x : ℝ) : ℝ :=
  min delta (routeTWidthPolylogLower A (2 * Real.pi * x)) / 2

theorem menonHarmonicFullFrequencyMu_nonneg {A delta : ℝ} (hdelta : 0 ≤ delta) (x : ℝ) :
    0 ≤ menonHarmonicFullFrequencyMu A delta x := by
  rw [menonHarmonicFullFrequencyMu]
  have hwidth := (routeTWidthPolylogLower_pos A (2 * Real.pi * x)).le
  linarith [le_min hdelta hwidth]

private theorem eventually_one_add_logConstLogSq_le_rpow {C K ε : ℝ}
    (hC : 0 ≤ C) (hK : 0 < K) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      1 + C * (1 + Real.log (K * Real.log x)) ^ 2 ≤ (Real.log x) ^ ε := by
  have hconst : Tendsto (fun x : ℝ =>
      (1 + 2 * C * (1 + Real.log K) ^ 2) * (Real.log x) ^ (-ε)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_log_of_neg (c := -ε) (by linarith)).const_mul
      (1 + 2 * C * (1 + Real.log K) ^ 2)
  have hll : Tendsto (fun x : ℝ =>
      (2 * C) * ((Real.log x) ^ (-ε) * (Real.log (Real.log x)) ^ 2)) atTop (𝓝 0) := by
    simpa using (tendsto_logRpow_mul_logLogPow (e := -ε) (by linarith) 2).const_mul (2 * C)
  have hlim : Tendsto (fun x : ℝ =>
      (Real.log x) ^ (-ε) * (1 + C * (1 + Real.log (K * Real.log x)) ^ 2))
      atTop (𝓝 0) := by
    have hsum : Tendsto (fun x : ℝ =>
        (1 + 2 * C * (1 + Real.log K) ^ 2) * (Real.log x) ^ (-ε)
          + 2 * C * ((Real.log x) ^ (-ε) * (Real.log (Real.log x)) ^ 2))
        atTop (𝓝 0) := by
      simpa using hconst.add hll
    refine squeeze_zero' ?_ ?_ hsum
    · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
      have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx
      exact mul_nonneg (Real.rpow_nonneg hlogx.le _) (by positivity)
    · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
        Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hx hlog1
      have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx
      have hpow : (0 : ℝ) ≤ (Real.log x) ^ (-ε) := Real.rpow_nonneg hlogx.le _
      have hsplit : Real.log (K * Real.log x) = Real.log K + Real.log (Real.log x) :=
        Real.log_mul (ne_of_gt hK) (ne_of_gt hlogx)
      have hsq : (1 + Real.log (K * Real.log x)) ^ 2
          ≤ 2 * (1 + Real.log K) ^ 2 + 2 * (Real.log (Real.log x)) ^ 2 := by
        rw [hsplit]
        nlinarith [sq_nonneg ((1 + Real.log K) - Real.log (Real.log x))]
      have hstep : 1 + C * (1 + Real.log (K * Real.log x)) ^ 2
          ≤ (1 + 2 * C * (1 + Real.log K) ^ 2)
            + 2 * C * (Real.log (Real.log x)) ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hsq hC]
      calc
        (Real.log x) ^ (-ε) * (1 + C * (1 + Real.log (K * Real.log x)) ^ 2)
            ≤ (Real.log x) ^ (-ε) *
                ((1 + 2 * C * (1 + Real.log K) ^ 2)
                  + 2 * C * (Real.log (Real.log x)) ^ 2) :=
              mul_le_mul_of_nonneg_left hstep hpow
        _ = (1 + 2 * C * (1 + Real.log K) ^ 2) * (Real.log x) ^ (-ε)
              + 2 * C * ((Real.log x) ^ (-ε) * (Real.log (Real.log x)) ^ 2) := by ring
  filter_upwards [Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) hlim,
    Filter.eventually_gt_atTop (1 : ℝ)] with x hsmall hx
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx
  have hpow : (0 : ℝ) < (Real.log x) ^ ε := Real.rpow_pos_of_pos hlogx _
  have hid : (Real.log x) ^ ε * (Real.log x) ^ (-ε) = 1 := by
    rw [← Real.rpow_add hlogx]
    simp
  have hmul := mul_le_mul_of_nonneg_left hsmall hpow.le
  rw [mul_one, ← mul_assoc, hid, one_mul] at hmul
  exact hmul

/-- Elementary height bounds at the physical endpoint `2 * pi * x`. -/
theorem eventually_menonHarmonicFullFrequency_height_bounds :
    ∀ᶠ x : ℝ in atTop,
      1 ≤ |2 * Real.pi * x|
        ∧ routeTLogHeightEnvelope (4 * (3 * |2 * Real.pi * x| / 2 + 1))
            ≤ 30 * Real.log x
        ∧ (0 : ℝ) ≤ Real.log (3 * (2 * Real.pi * x) / 2)
        ∧ Real.log (3 * (2 * Real.pi * x) / 2) ≤ 12 * Real.log x := by
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
    Filter.eventually_ge_atTop (1 : ℝ)] with x hx hlog1 hxge
  have hx0 : (0 : ℝ) < x := by linarith
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  have htau0 : (0 : ℝ) < 2 * Real.pi * x := by positivity
  have htauAbs : |2 * Real.pi * x| = 2 * Real.pi * x := abs_of_pos htau0
  have htau1 : 1 ≤ |2 * Real.pi * x| := by rw [htauAbs]; nlinarith [Real.pi_gt_three]
  have hlogTwoPi : Real.log (2 * Real.pi) ≤ 7 := by
    have hlog := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)
    nlinarith
  have hlogTau : Real.log |2 * Real.pi * x| ≤ 7 + Real.log x := by
    rw [htauAbs, Real.log_mul (by positivity : (2 * Real.pi : ℝ) ≠ 0) (ne_of_gt hx0)]
    linarith
  have henv0 := routeTLogHeightEnvelope_le htau1
  have henv : routeTLogHeightEnvelope (4 * (3 * |2 * Real.pi * x| / 2 + 1))
      ≤ 30 * Real.log x := by linarith
  have harg0 : (1 : ℝ) ≤ 3 * (2 * Real.pi * x) / 2 := by
    nlinarith [Real.pi_gt_three]
  have hlogArg0 : (0 : ℝ) ≤ Real.log (3 * (2 * Real.pi * x) / 2) := Real.log_nonneg harg0
  have hlogThreePi : Real.log (3 * Real.pi) ≤ 11 := by
    have hlog := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 3 * Real.pi)
    nlinarith
  have hargEq : 3 * (2 * Real.pi * x) / 2 = (3 * Real.pi) * x := by ring
  have hlogArg : Real.log (3 * (2 * Real.pi * x) / 2) ≤ 12 * Real.log x := by
    rw [hargEq, Real.log_mul (by positivity : (3 * Real.pi : ℝ) ≠ 0) (ne_of_gt hx0)]
    linarith
  exact ⟨htau1, henv, hlogArg0, hlogArg⟩

/-- The full-frequency Route-T height cost is eventually at most `(log x)^2`. -/
theorem eventually_menonHarmonicFullFrequency_heightCost_le_logSq {A b A₃ : ℝ}
    (hb : 0 < b) (hA₃ : 0 < A₃) :
    ∀ᶠ x : ℝ in atTop,
      1 / twoRangeT₀ b A₃ x
          + Real.log (3 * (2 * Real.pi * x) / 2)
              / routeTWidthPolylogLower A (2 * Real.pi * x)
        ≤ (Real.log x) ^ (2 : ℝ) := by
  have hC : (0 : ℝ) < routeTZeroFreeDeltaEnvelopeConstant A :=
    routeTZeroFreeDeltaEnvelopeConstant_pos A
  filter_upwards [eventually_menonHarmonicFullFrequency_height_bounds,
    eventually_one_add_logConstLogSq_le_rpow
      (C := 3600 * routeTZeroFreeDeltaEnvelopeConstant A) (K := 30)
      (ε := (1 : ℝ) / 10) (by positivity) (by norm_num) (by norm_num),
    Filter.eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hbd hsmall hx hlog1
  obtain ⟨htau1, hZ, hlogS0, hlogS⟩ := hbd
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx
  let Z : ℝ := 30 * Real.log x
  have hZ1 : (1 : ℝ) ≤ Z := by dsimp only [Z]; linarith
  have hinv := inv_routeTWidthPolylogLower_le (A := A) (τ := 2 * Real.pi * x)
    (Z := Z) htau1 (by simpa only [Z] using hZ) hZ1
  have hZpow : Z ^ ((9 : ℝ) / 10) ≤ 30 * (Real.log x) ^ ((9 : ℝ) / 10) := by
    dsimp only [Z]
    rw [Real.mul_rpow (by norm_num) hlogx.le]
    have h30 : (30 : ℝ) ^ ((9 : ℝ) / 10) ≤ 30 := by
      calc
        (30 : ℝ) ^ ((9 : ℝ) / 10) ≤ (30 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 30 := Real.rpow_one 30
    exact mul_le_mul_of_nonneg_right h30 (Real.rpow_nonneg hlogx.le _)
  have hsq0 : (0 : ℝ) ≤ (1 + Real.log Z) ^ 2 := sq_nonneg _
  have hinv' : 1 / routeTWidthPolylogLower A (2 * Real.pi * x)
      ≤ 300 * routeTZeroFreeDeltaEnvelopeConstant A
          * (Real.log x) ^ ((9 : ℝ) / 10) * (1 + Real.log Z) ^ 2 := by
    refine hinv.trans ?_
    have hmul := mul_le_mul_of_nonneg_left hZpow
      (show (0 : ℝ) ≤ 10 * routeTZeroFreeDeltaEnvelopeConstant A by positivity)
    have hmul' : 10 * routeTZeroFreeDeltaEnvelopeConstant A * Z ^ ((9 : ℝ) / 10)
        ≤ 300 * routeTZeroFreeDeltaEnvelopeConstant A *
          (Real.log x) ^ ((9 : ℝ) / 10) := by
      nlinarith
    exact mul_le_mul_of_nonneg_right hmul' hsq0
  have hquot : Real.log (3 * (2 * Real.pi * x) / 2)
        / routeTWidthPolylogLower A (2 * Real.pi * x)
      ≤ 3600 * routeTZeroFreeDeltaEnvelopeConstant A
          * (1 + Real.log Z) ^ 2 * (Real.log x) ^ ((19 : ℝ) / 10) := by
    rw [div_eq_mul_inv]
    have hwidth0 : (0 : ℝ) < routeTWidthPolylogLower A (2 * Real.pi * x) :=
      routeTWidthPolylogLower_pos _ _
    have hinv0 : (0 : ℝ) ≤ 1 / routeTWidthPolylogLower A (2 * Real.pi * x) :=
      (one_div_pos.mpr hwidth0).le
    have hlog12 : (0 : ℝ) ≤ 12 * Real.log x := mul_nonneg (by norm_num) hlogx.le
    have hmul := mul_le_mul hlogS hinv'
      hinv0 hlog12
    rw [one_div] at hmul
    have hpow : Real.log x * (Real.log x) ^ ((9 : ℝ) / 10) =
        (Real.log x) ^ ((19 : ℝ) / 10) := by
      rw [show ((19 : ℝ) / 10) = 1 + 9 / 10 by norm_num,
        Real.rpow_add hlogx, Real.rpow_one]
    calc
      Real.log (3 * (2 * Real.pi * x) / 2) *
          (routeTWidthPolylogLower A (2 * Real.pi * x))⁻¹
          ≤ 12 * Real.log x *
              (300 * routeTZeroFreeDeltaEnvelopeConstant A *
                (Real.log x) ^ ((9 : ℝ) / 10) * (1 + Real.log Z) ^ 2) := hmul
      _ = 3600 * routeTZeroFreeDeltaEnvelopeConstant A *
            (1 + Real.log Z) ^ 2 * (Real.log x) ^ ((19 : ℝ) / 10) := by
        rw [← hpow]
        ring
  have ht0one : (1 : ℝ) ≤ twoRangeT₀ b A₃ x := by
    rw [twoRangeT₀]
    exact Real.one_le_rpow hlog1 (by linarith)
  have hdisc : 1 / twoRangeT₀ b A₃ x ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
  have hpow19 : (1 : ℝ) ≤ (Real.log x) ^ ((19 : ℝ) / 10) :=
    Real.one_le_rpow hlog1 (by norm_num)
  have hmain : 1 / twoRangeT₀ b A₃ x
        + Real.log (3 * (2 * Real.pi * x) / 2)
            / routeTWidthPolylogLower A (2 * Real.pi * x)
      ≤ (1 + 3600 * routeTZeroFreeDeltaEnvelopeConstant A *
          (1 + Real.log Z) ^ 2) * (Real.log x) ^ ((19 : ℝ) / 10) := by
    nlinarith [hdisc, hquot, hpow19]
  have hfinal : (1 + 3600 * routeTZeroFreeDeltaEnvelopeConstant A *
        (1 + Real.log Z) ^ 2) * (Real.log x) ^ ((19 : ℝ) / 10)
      ≤ (Real.log x) ^ (2 : ℝ) := by
    have hsmall' : 1 + 3600 * routeTZeroFreeDeltaEnvelopeConstant A *
        (1 + Real.log Z) ^ 2 ≤ (Real.log x) ^ ((1 : ℝ) / 10) := by
      simpa only [Z] using hsmall
    have hmul := mul_le_mul_of_nonneg_right hsmall'
      (Real.rpow_nonneg hlogx.le ((19 : ℝ) / 10))
    refine hmul.trans_eq ?_
    rw [← Real.rpow_add hlogx]
    norm_num
  exact hmain.trans hfinal

/-- At full physical frequency the Route-T width times Menon's final prime logarithm still grows
like a positive power of `log x`. -/
theorem eventually_menonHarmonicFullFrequencyMu_mul_twoRangeQ_ge {A delta a : ℝ}
    (hdelta : 0 < delta) (ha : 9 / 10 < a) :
    ∀ᶠ x : ℝ in atTop,
      (Real.log x) ^ ((a - 9 / 10) / 2)
        ≤ menonHarmonicFullFrequencyMu A delta x * twoRangeQ a x := by
  have hC : (0 : ℝ) < routeTZeroFreeDeltaEnvelopeConstant A :=
    routeTZeroFreeDeltaEnvelopeConstant_pos A
  let ε : ℝ := (a - 9 / 10) / 2
  have hε : 0 < ε := by dsimp only [ε]; linarith
  have hdec : Tendsto (fun x : ℝ => 2 * (Real.log x) ^ (-(9 / 10 + ε)))
      atTop (𝓝 0) := by
    simpa using (tendsto_rpow_log_of_neg (c := -(9 / 10 + ε)) (by linarith)).const_mul 2
  filter_upwards [eventually_menonHarmonicFullFrequency_height_bounds,
    eventually_one_add_logConstLogSq_le_rpow
      (C := 600 * routeTZeroFreeDeltaEnvelopeConstant A) (K := 30) (ε := ε)
      (by positivity) (by norm_num) hε,
    Tendsto.eventually_le_const hdelta hdec,
    Filter.eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with
      x hbd hsmall hdeltaSmall hx hlog1
  obtain ⟨htau1, hZ, -, -⟩ := hbd
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx
  let Z : ℝ := 30 * Real.log x
  have hZ1 : (1 : ℝ) ≤ Z := by dsimp only [Z]; linarith
  have hwidthLower := routeTWidthPolylogLower_ge (A := A) (τ := 2 * Real.pi * x)
    (Z := Z) htau1 (by simpa only [Z] using hZ) hZ1
  have hZpow : Z ^ ((9 : ℝ) / 10) ≤ 30 * (Real.log x) ^ ((9 : ℝ) / 10) := by
    dsimp only [Z]
    rw [Real.mul_rpow (by norm_num) hlogx.le]
    have h30 : (30 : ℝ) ^ ((9 : ℝ) / 10) ≤ 30 := by
      calc
        (30 : ℝ) ^ ((9 : ℝ) / 10) ≤ (30 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 30 := Real.rpow_one 30
    exact mul_le_mul_of_nonneg_right h30 (Real.rpow_nonneg hlogx.le _)
  have hsq0 : (0 : ℝ) ≤ (1 + Real.log Z) ^ 2 := sq_nonneg _
  have hden : 20 * routeTZeroFreeDeltaEnvelopeConstant A * Z ^ ((9 : ℝ) / 10)
        * (1 + Real.log Z) ^ 2
      ≤ (Real.log x) ^ (9 / 10 + ε) := by
    have hstep : 20 * routeTZeroFreeDeltaEnvelopeConstant A * Z ^ ((9 : ℝ) / 10)
          * (1 + Real.log Z) ^ 2
        ≤ 600 * routeTZeroFreeDeltaEnvelopeConstant A
            * (Real.log x) ^ ((9 : ℝ) / 10) * (1 + Real.log Z) ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hZpow
        (show (0 : ℝ) ≤ 20 * routeTZeroFreeDeltaEnvelopeConstant A by positivity)
      have hmul' : 20 * routeTZeroFreeDeltaEnvelopeConstant A * Z ^ ((9 : ℝ) / 10)
          ≤ 600 * routeTZeroFreeDeltaEnvelopeConstant A *
            (Real.log x) ^ ((9 : ℝ) / 10) := by
        nlinarith
      exact mul_le_mul_of_nonneg_right hmul' hsq0
    have hsmall' : 600 * routeTZeroFreeDeltaEnvelopeConstant A *
        (1 + Real.log Z) ^ 2 ≤ (Real.log x) ^ ε := by
      have := hsmall
      simpa only [Z] using (le_trans (by linarith :
        600 * routeTZeroFreeDeltaEnvelopeConstant A *
          (1 + Real.log (30 * Real.log x)) ^ 2
            ≤ 1 + 600 * routeTZeroFreeDeltaEnvelopeConstant A *
              (1 + Real.log (30 * Real.log x)) ^ 2) this)
    have hmul := mul_le_mul_of_nonneg_left hsmall'
      (Real.rpow_nonneg hlogx.le ((9 : ℝ) / 10))
    have hid : (Real.log x) ^ ((9 : ℝ) / 10) * (Real.log x) ^ ε =
        (Real.log x) ^ (9 / 10 + ε) := by rw [← Real.rpow_add hlogx]
    refine hstep.trans ?_
    calc
      600 * routeTZeroFreeDeltaEnvelopeConstant A *
            (Real.log x) ^ ((9 : ℝ) / 10) * (1 + Real.log Z) ^ 2
          = (Real.log x) ^ ((9 : ℝ) / 10) *
              (600 * routeTZeroFreeDeltaEnvelopeConstant A * (1 + Real.log Z) ^ 2) := by ring
      _ ≤ (Real.log x) ^ ((9 : ℝ) / 10) * (Real.log x) ^ ε := hmul
      _ = (Real.log x) ^ (9 / 10 + ε) := hid
  have hpowpos : (0 : ℝ) < (Real.log x) ^ (9 / 10 + ε) :=
    Real.rpow_pos_of_pos hlogx _
  have hdenpos : (0 : ℝ) < 10 * routeTZeroFreeDeltaEnvelopeConstant A *
      Z ^ ((9 : ℝ) / 10) * (1 + Real.log Z) ^ 2 := by
    have hZ0 : (0 : ℝ) < Z := by dsimp only [Z]; positivity
    have hlogZ : (0 : ℝ) ≤ Real.log Z := Real.log_nonneg hZ1
    positivity
  have hwidth : 2 * (Real.log x) ^ (-(9 / 10 + ε))
      ≤ routeTWidthPolylogLower A (2 * Real.pi * x) := by
    refine (show 2 * (Real.log x) ^ (-(9 / 10 + ε))
      ≤ 1 / (10 * routeTZeroFreeDeltaEnvelopeConstant A * Z ^ ((9 : ℝ) / 10)
        * (1 + Real.log Z) ^ 2) by
          rw [Real.rpow_neg hlogx.le, ← one_div, mul_one_div,
            div_le_div_iff₀ hpowpos hdenpos]
          linarith).trans hwidthLower
  have hmin : 2 * (Real.log x) ^ (-(9 / 10 + ε))
      ≤ min delta (routeTWidthPolylogLower A (2 * Real.pi * x)) := by
    refine le_min ?_ hwidth
    rw [Real.rpow_neg hlogx.le] at hdeltaSmall ⊢
    linarith
  have hmu : (Real.log x) ^ (-(9 / 10 + ε))
      ≤ menonHarmonicFullFrequencyMu A delta x := by
    rw [menonHarmonicFullFrequencyMu]
    linarith
  have hq0 : (0 : ℝ) < twoRangeQ a x := by
    rw [twoRangeQ]
    exact Real.rpow_pos_of_pos hlogx _
  have hmul := mul_le_mul_of_nonneg_right hmu hq0.le
  refine (le_of_eq ?_).trans hmul
  rw [twoRangeQ, ← Real.rpow_add hlogx]
  dsimp only [ε]
  congr 1
  ring

/-- Menon's full-frequency Route-T relative majorant beats forty logarithms. -/
theorem tendsto_logPow_forty_mul_menonHarmonicFullFrequencyRelMajorant
    {A delta Ctot : ℝ} (hdelta : 0 < delta) (hCtot : 0 < Ctot) :
    Tendsto (fun x : ℝ => (Real.log x) ^ (40 : ℝ) *
      relScaledMajorant Ctot (twoRangeWidth 2 100 x) (twoRangeLx 2 x)
        ((Real.log x) ^ (2 : ℝ)) (menonHarmonicFullFrequencyMu A delta x)
        (twoRangeQ ((19 : ℝ) / 20) x) (twoRangeT₀ 2 100 x)
        (twoRangeXmin ((19 : ℝ) / 20) x)) atTop (𝓝 0) := by
  have hmuq := eventually_menonHarmonicFullFrequencyMu_mul_twoRangeQ_ge
    (A := A) (delta := delta) (a := (19 : ℝ) / 20) hdelta (by norm_num)
  have hexpq : Tendsto (fun x : ℝ =>
      (Real.log x) ^ (2 * (2 : ℝ) + 2 * 100 + 4 + 40) *
        Real.exp (-(menonHarmonicFullFrequencyMu A delta x *
          twoRangeQ ((19 : ℝ) / 20) x))) atTop (𝓝 0) := by
    exact tendsto_rpow_log_mul_exp_neg_of_ge (by norm_num) hmuq
  have hxmin : Tendsto (fun x : ℝ =>
      (Real.log x) ^ ((2 : ℝ) + 40) /
        Real.sqrt (twoRangeXmin ((19 : ℝ) / 20) x)) atTop (𝓝 0) := by
    refine (tendsto_logRpow_mul_expSaving
      (d := (19 : ℝ) / 20) (s := (1 : ℝ) / 2)
      (by norm_num) (by norm_num) ((2 : ℝ) + 40)).congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    have hc0 : (0 : ℝ) < cardLength ((19 : ℝ) / 20) x := cardLength_pos _ _
    have hsqrt : Real.sqrt (twoRangeXmin ((19 : ℝ) / 20) x) =
        Real.exp ((Real.log x) ^ ((19 : ℝ) / 20) / 2) := by
      rw [twoRangeXmin, sqrt_eq_exp_half_log hc0, log_cardLength]
    have hexp : Real.exp (-((1 : ℝ) / 2 * (Real.log x) ^ ((19 : ℝ) / 20))) =
        (Real.exp ((Real.log x) ^ ((19 : ℝ) / 20) / 2))⁻¹ := by
      rw [← Real.exp_neg]
      congr 1
      ring
    rw [hsqrt, hexp]
    exact (div_eq_mul_inv _ _).symm
  refine tendsto_logRpow_mul_relScaledMajorant
    (b := (2 : ℝ)) (A₃ := (100 : ℝ)) (Ctot := Ctot) (e := (40 : ℝ))
    (Hmaj := fun x => (Real.log x) ^ (2 : ℝ))
    (μ := fun x => menonHarmonicFullFrequencyMu A delta x)
    (q := fun x => twoRangeQ ((19 : ℝ) / 20) x)
    (xmin := fun x => twoRangeXmin ((19 : ℝ) / 20) x)
    (by norm_num) (by norm_num) hCtot.le (by norm_num) (by norm_num) (by norm_num)
    ?_ (Filter.Eventually.of_forall fun x => twoRangeXmin_pos ((19 : ℝ) / 20) x)
    hexpq hxmin
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
  exact ⟨Real.rpow_nonneg (Real.log_pos hx).le _, le_rfl⟩

end

end RHTower.Sieve
