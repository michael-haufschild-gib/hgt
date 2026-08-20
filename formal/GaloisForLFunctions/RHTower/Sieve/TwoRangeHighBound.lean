import GaloisForLFunctions.RHTower.Sieve.TwoRangeRouteT
import GaloisForLFunctions.RHTower.Sieve.AnnulusBoundUniform
import GaloisForLFunctions.RHTower.Sieve.MoebiusWindowPartition
import GaloisForLFunctions.RHTower.Sieve.WidthEnvelopeBounds

/-!
# The high blocks on the large half of the annulus

This is the hypothesis `hbound'` of
`Sieve/MoebiusTwoRangeWindow.integral_Icc_normSq_logPoly_moebius_le_twoRange`: a pointwise bound for
every block of the *high* designated range, valid on the whole exceptional half of the annulus and
with a relative size that beats every fixed power of the logarithm.

Everything is one application of `Sieve/AnnulusBoundUniform.exists_annulus_bound_uniform` with the
fourteen slots filled by `Sieve/TwoRangeRouteT`, restricted to `annulusLarge` by
`Sieve/MoebiusWindowPartition.annulusLarge_subset_annulus`.  The only two analytic facts left are
about the Route-T contour itself:

* its height cost `Hmaj` is at most `(log x)²` — the width surrogate is a reciprocal `9/10`-th power
  of `log` up to a square of `log log`, and the height is `log x`;
* its width times its frequency, `μ·q`, exceeds `(log x)^{(a−9/10)/2}` — this is the *only* place
  where `a > 9/10` is used, and it is what makes `e^{−μq}` beat every power of the logarithm.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The disc radius and the Route-T height are the same quantity up to `2π`. -/
theorem two_pi_mul_twoRangeDisc (b A₃ x : ℝ) :
    2 * Real.pi * twoRangeDisc b A₃ x = twoRangeT₀ b A₃ x := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [twoRangeDisc, twoRangeT₀]
  field_simp

/-- **A square of `log log` is beaten by any positive power of `log`.** -/
theorem eventually_one_add_logLogSq_le_rpow {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, 1 + C * (1 + Real.log (3 * Real.log x)) ^ 2 ≤ (Real.log x) ^ ε := by
  have hconst : Tendsto (fun x : ℝ =>
      (1 + 2 * C * (1 + Real.log 3) ^ 2) * (Real.log x) ^ (-ε)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_log_of_neg (c := -ε) (by linarith)).const_mul
      (1 + 2 * C * (1 + Real.log 3) ^ 2)
  have hll : Tendsto (fun x : ℝ =>
      (2 * C) * ((Real.log x) ^ (-ε) * (Real.log (Real.log x)) ^ 2)) atTop (𝓝 0) := by
    simpa using (tendsto_logRpow_mul_logLogPow (e := -ε) (by linarith) 2).const_mul (2 * C)
  have hlim : Tendsto (fun x : ℝ =>
      (Real.log x) ^ (-ε) * (1 + C * (1 + Real.log (3 * Real.log x)) ^ 2)) atTop (𝓝 0) := by
    have hsum : Tendsto (fun x : ℝ =>
        (1 + 2 * C * (1 + Real.log 3) ^ 2) * (Real.log x) ^ (-ε)
          + 2 * C * ((Real.log x) ^ (-ε) * (Real.log (Real.log x)) ^ 2)) atTop (𝓝 0) := by
      simpa using hconst.add hll
    refine squeeze_zero' ?_ ?_ hsum
    · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx1
      have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
      have h1 : (0 : ℝ) ≤ (Real.log x) ^ (-ε) := Real.rpow_nonneg hlogx.le _
      have h2 : (0 : ℝ) ≤ 1 + C * (1 + Real.log (3 * Real.log x)) ^ 2 := by
        have := mul_nonneg hC (sq_nonneg (1 + Real.log (3 * Real.log x)))
        linarith
      exact mul_nonneg h1 h2
    · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
        Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hx1 hlog1
      have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
      have hpow : (0 : ℝ) ≤ (Real.log x) ^ (-ε) := Real.rpow_nonneg hlogx.le _
      have hsplit : Real.log (3 * Real.log x) = Real.log 3 + Real.log (Real.log x) :=
        Real.log_mul (by norm_num) (ne_of_gt hlogx)
      have hsq : (1 + Real.log (3 * Real.log x)) ^ 2
          ≤ 2 * (1 + Real.log 3) ^ 2 + 2 * (Real.log (Real.log x)) ^ 2 := by
        rw [hsplit]
        nlinarith [sq_nonneg ((1 + Real.log 3) - Real.log (Real.log x))]
      have hstep : 1 + C * (1 + Real.log (3 * Real.log x)) ^ 2
          ≤ (1 + 2 * C * (1 + Real.log 3) ^ 2) + 2 * C * (Real.log (Real.log x)) ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hsq hC]
      calc (Real.log x) ^ (-ε) * (1 + C * (1 + Real.log (3 * Real.log x)) ^ 2)
          ≤ (Real.log x) ^ (-ε)
              * ((1 + 2 * C * (1 + Real.log 3) ^ 2) + 2 * C * (Real.log (Real.log x)) ^ 2) :=
            mul_le_mul_of_nonneg_left hstep hpow
        _ = (1 + 2 * C * (1 + Real.log 3) ^ 2) * (Real.log x) ^ (-ε)
              + 2 * C * ((Real.log x) ^ (-ε) * (Real.log (Real.log x)) ^ 2) := by ring
  filter_upwards [Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) hlim,
    Filter.eventually_gt_atTop (1 : ℝ)] with x hsm hx1
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hpow : (0 : ℝ) < (Real.log x) ^ ε := Real.rpow_pos_of_pos hlogx ε
  have hid : (Real.log x) ^ ε * (Real.log x) ^ (-ε) = 1 := by
    rw [← Real.rpow_add hlogx]
    simp
  have := mul_le_mul_of_nonneg_left hsm hpow.le
  rw [mul_one, ← mul_assoc, hid, one_mul] at this
  exact this

/-- **The Route-T height is below the outer scale.** -/
theorem twoRangeTop_two_pi_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ᶠ x : ℝ in atTop, 2 * Real.pi * twoRangeTop β x ≤ x := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsq := tendsto_rpow_log_div_sqrt (1 : ℝ)
  filter_upwards [one_le_twoRangeCut hβ0 hβ1, Filter.eventually_gt_atTop (1 : ℝ),
    Filter.eventually_ge_atTop (16 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
    (tendsto_cardLength hβ0).eventually_ge_atTop (1 : ℝ),
    Tendsto.eventually_le_const (show (0 : ℝ) < 1 / (4 * Real.pi) by positivity) hsq]
    with x hcut hx1 hx16 hlog1 hh1 hsmall
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hsqrt : (4 : ℝ) ≤ Real.sqrt x := by
    rw [show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx16
  have hsq0 : (0 : ℝ) < Real.sqrt x := by linarith
  have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  -- `4π log x ≤ √x`
  have hkey : 4 * Real.pi * Real.log x ≤ Real.sqrt x := by
    rw [Real.rpow_one] at hsmall
    rw [div_le_iff₀ hsq0] at hsmall
    have := mul_le_mul_of_nonneg_left hsmall (by positivity : (0 : ℝ) ≤ 4 * Real.pi)
    have hid : 4 * Real.pi * (1 / (4 * Real.pi) * Real.sqrt x) = Real.sqrt x := by
      field_simp
    rw [hid] at this
    linarith
  -- the cutoff is at most `√x + 1`
  have hcutle : twoRangeCut β x ≤ Real.sqrt x + 1 := by
    have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
    have hfl : ((twoRangeLength β x : ℕ) : ℝ) ≤ Real.sqrt x + cardLength β x := by
      rw [twoRangeLength]
      exact Nat.floor_le (by positivity)
    rw [twoRangeCut, div_le_iff₀ hh0]
    nlinarith [hfl, hh1, hsq0]
  have hll : Real.log (Real.log x) ≤ Real.log x := by
    have := Real.log_le_sub_one_of_pos hlogx
    linarith
  have hll0 : (0 : ℝ) ≤ Real.log (Real.log x) := Real.log_nonneg hlog1
  have hcut0 : (0 : ℝ) ≤ twoRangeCut β x := by linarith [hcut]
  have htop : twoRangeTop β x ≤ (Real.sqrt x + 1) * Real.log x := by
    rw [twoRangeTop]
    nlinarith [hcutle, hll, hll0, hcut0]
  have htop0 : (0 : ℝ) ≤ twoRangeTop β x := by
    rw [twoRangeTop]
    exact mul_nonneg hcut0 hll0
  nlinarith [htop, hkey, hsqrt, hxx, hpi, hlogx, hsq0]

/-- The height envelope of the Route-T window, in the logarithm of the outer scale. -/
theorem routeTHeight_twoRangeTop_bounds {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ᶠ x : ℝ in atTop,
      1 ≤ |2 * Real.pi * twoRangeTop β x|
        ∧ routeTLogHeightEnvelope (4 * (3 * |2 * Real.pi * twoRangeTop β x| / 2 + 1))
            ≤ 3 * Real.log x
        ∧ (0 : ℝ) ≤ Real.log (3 * (2 * Real.pi * twoRangeTop β x) / 2)
        ∧ Real.log (3 * (2 * Real.pi * twoRangeTop β x) / 2) ≤ 2 * Real.log x := by
  filter_upwards [one_le_twoRangeTop hβ0 hβ1, twoRangeTop_two_pi_le hβ0 hβ1,
    Filter.eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (10 : ℝ)] with x hT1 hTx hx1 hlog10
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hτ0 : (6 : ℝ) ≤ 2 * Real.pi * twoRangeTop β x := by nlinarith [hT1, hpi3]
  have hτabs : |2 * Real.pi * twoRangeTop β x| = 2 * Real.pi * twoRangeTop β x :=
    abs_of_pos (by linarith)
  have hτ1 : 1 ≤ |2 * Real.pi * twoRangeTop β x| := by rw [hτabs]; linarith
  refine ⟨hτ1, ?_, ?_, ?_⟩
  · have henv := routeTLogHeightEnvelope_le (τ := 2 * Real.pi * twoRangeTop β x) hτ1
    have hlogτ : Real.log |2 * Real.pi * twoRangeTop β x| ≤ Real.log x := by
      rw [hτabs]
      exact Real.log_le_log (by linarith) hTx
    linarith [henv, hlogτ, hlog10]
  · refine Real.log_nonneg ?_
    linarith
  · have hle : 3 * (2 * Real.pi * twoRangeTop β x) / 2 ≤ 2 * x := by linarith
    have hstep : Real.log (3 * (2 * Real.pi * twoRangeTop β x) / 2) ≤ Real.log (2 * x) :=
      Real.log_le_log (by linarith) hle
    have hsplit : Real.log (2 * x) = Real.log 2 + Real.log x :=
      Real.log_mul (by norm_num) (by linarith)
    have hl2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    linarith

/-- **The height cost of the Route-T contour is at most `(log x)²`.** -/
theorem twoRangeHmaj_bounds {A b A₃ β : ℝ} (hb : 0 < b) (hA₃ : 0 < A₃) (hβ0 : 0 < β)
    (hβ1 : β < 1) :
    ∀ᶠ x : ℝ in atTop,
      0 ≤ twoRangeHmaj A b A₃ β x ∧ twoRangeHmaj A b A₃ β x ≤ (Real.log x) ^ (2 : ℝ) := by
  have hC : (0 : ℝ) < routeTZeroFreeDeltaEnvelopeConstant A :=
    routeTZeroFreeDeltaEnvelopeConstant_pos A
  filter_upwards [routeTHeight_twoRangeTop_bounds (β := β) hβ0 hβ1,
    eventually_one_add_logLogSq_le_rpow
      (C := 60 * routeTZeroFreeDeltaEnvelopeConstant A) (ε := (1 : ℝ) / 10)
      (by positivity) (by norm_num),
    Filter.eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hbd hsmall hx1 hlog1
  obtain ⟨hτ1, hZ, hlogS0, hlogS⟩ := hbd
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  set Z : ℝ := 3 * Real.log x with hZdef
  have hZ1 : (1 : ℝ) ≤ Z := by rw [hZdef]; linarith
  have hwidth0 : (0 : ℝ) < routeTWidthPolylogLower A (2 * Real.pi * twoRangeTop β x) :=
    routeTWidthPolylogLower_pos _ _
  have hinv := inv_routeTWidthPolylogLower_le (A := A)
    (τ := 2 * Real.pi * twoRangeTop β x) (Z := Z) hτ1 hZ hZ1
  -- the disc term
  have hT₀1 : (1 : ℝ) ≤ twoRangeT₀ b A₃ x := by
    rw [twoRangeT₀]
    exact Real.one_le_rpow hlog1 (by linarith)
  have hdisc1 : 1 / (2 * Real.pi * twoRangeDisc b A₃ x) ≤ 1 := by
    rw [two_pi_mul_twoRangeDisc]
    rw [div_le_one (by linarith)]
    linarith
  have hdisc0 : (0 : ℝ) ≤ 1 / (2 * Real.pi * twoRangeDisc b A₃ x) := by
    rw [two_pi_mul_twoRangeDisc]
    positivity
  -- the width term
  have hZpow : Z ^ ((9 : ℝ) / 10) ≤ 3 * (Real.log x) ^ ((9 : ℝ) / 10) := by
    rw [hZdef, Real.mul_rpow (by norm_num) hlogx.le]
    have h3 : (3 : ℝ) ^ ((9 : ℝ) / 10) ≤ 3 := by
      calc (3 : ℝ) ^ ((9 : ℝ) / 10) ≤ (3 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 3 := Real.rpow_one 3
    have hlp : (0 : ℝ) ≤ (Real.log x) ^ ((9 : ℝ) / 10) := Real.rpow_nonneg hlogx.le _
    nlinarith [h3, hlp]
  have hlogZ : Real.log Z = Real.log (3 * Real.log x) := by rw [hZdef]
  have hsq0 : (0 : ℝ) ≤ (1 + Real.log Z) ^ 2 := sq_nonneg _
  have hinner : 10 * routeTZeroFreeDeltaEnvelopeConstant A * Z ^ ((9 : ℝ) / 10)
        * (1 + Real.log Z) ^ 2
      ≤ 30 * routeTZeroFreeDeltaEnvelopeConstant A * (Real.log x) ^ ((9 : ℝ) / 10)
        * (1 + Real.log Z) ^ 2 := by
    have hstep : 10 * routeTZeroFreeDeltaEnvelopeConstant A * Z ^ ((9 : ℝ) / 10)
        ≤ 30 * routeTZeroFreeDeltaEnvelopeConstant A * (Real.log x) ^ ((9 : ℝ) / 10) := by
      nlinarith [hZpow, hC]
    exact mul_le_mul_of_nonneg_right hstep hsq0
  have hquot : Real.log (3 * (2 * Real.pi * twoRangeTop β x) / 2)
        / routeTWidthPolylogLower A (2 * Real.pi * twoRangeTop β x)
      ≤ 2 * Real.log x
        * (30 * routeTZeroFreeDeltaEnvelopeConstant A * (Real.log x) ^ ((9 : ℝ) / 10)
            * (1 + Real.log Z) ^ 2) := by
    have hrw : Real.log (3 * (2 * Real.pi * twoRangeTop β x) / 2)
        / routeTWidthPolylogLower A (2 * Real.pi * twoRangeTop β x)
        = Real.log (3 * (2 * Real.pi * twoRangeTop β x) / 2)
          * (1 / routeTWidthPolylogLower A (2 * Real.pi * twoRangeTop β x)) := by
      ring
    rw [hrw]
    refine mul_le_mul hlogS (le_trans hinv hinner) (by positivity) (by linarith)
  have hpow19 : Real.log x * (Real.log x) ^ ((9 : ℝ) / 10) = (Real.log x) ^ ((19 : ℝ) / 10) := by
    rw [show ((19 : ℝ) / 10) = 1 + 9 / 10 by norm_num, Real.rpow_add hlogx, Real.rpow_one]
  have h19 : (1 : ℝ) ≤ (Real.log x) ^ ((19 : ℝ) / 10) :=
    Real.one_le_rpow hlog1 (by norm_num)
  have hmain : twoRangeHmaj A b A₃ β x
      ≤ (1 + 60 * routeTZeroFreeDeltaEnvelopeConstant A * (1 + Real.log (3 * Real.log x)) ^ 2)
        * (Real.log x) ^ ((19 : ℝ) / 10) := by
    rw [twoRangeHmaj]
    have hid : 2 * Real.log x
        * (30 * routeTZeroFreeDeltaEnvelopeConstant A * (Real.log x) ^ ((9 : ℝ) / 10)
            * (1 + Real.log Z) ^ 2)
        = 60 * routeTZeroFreeDeltaEnvelopeConstant A * (1 + Real.log Z) ^ 2
            * (Real.log x ^ (1 : ℝ) * (Real.log x) ^ ((9 : ℝ) / 10)) := by
      rw [Real.rpow_one]
      ring
    rw [hid, Real.rpow_one, hpow19] at hquot
    rw [hlogZ] at hquot
    nlinarith [hdisc1, hquot, h19]
  have hfinal : (1 + 60 * routeTZeroFreeDeltaEnvelopeConstant A
        * (1 + Real.log (3 * Real.log x)) ^ 2) * (Real.log x) ^ ((19 : ℝ) / 10)
      ≤ (Real.log x) ^ (2 : ℝ) := by
    have hstep := mul_le_mul_of_nonneg_right hsmall (le_trans zero_le_one h19)
    refine hstep.trans (le_of_eq ?_)
    rw [← Real.rpow_add hlogx]
    norm_num
  refine ⟨?_, le_trans hmain hfinal⟩
  rw [twoRangeHmaj]
  have hq0 : (0 : ℝ) ≤ Real.log (3 * (2 * Real.pi * twoRangeTop β x) / 2)
      / routeTWidthPolylogLower A (2 * Real.pi * twoRangeTop β x) :=
    div_nonneg hlogS0 hwidth0.le
  linarith [hdisc0]

/-- **The Route-T contour's width times its frequency exceeds a power of the logarithm.**  This is
the only place where `a > 9/10` is used. -/
theorem twoRangeMu_mul_twoRangeQ_ge {A delta a β : ℝ} (hdelta : 0 < delta) (ha : 9 / 10 < a)
    (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ᶠ x : ℝ in atTop,
      (Real.log x) ^ ((a - 9 / 10) / 2) ≤ twoRangeMu A delta β x * twoRangeQ a x := by
  have hC : (0 : ℝ) < routeTZeroFreeDeltaEnvelopeConstant A :=
    routeTZeroFreeDeltaEnvelopeConstant_pos A
  set ε : ℝ := (a - 9 / 10) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hdec : Tendsto (fun x : ℝ => 2 * (Real.log x) ^ (-(9 / 10 + ε))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_log_of_neg (c := -(9 / 10 + ε)) (by linarith)).const_mul 2
  filter_upwards [routeTHeight_twoRangeTop_bounds (β := β) hβ0 hβ1,
    eventually_one_add_logLogSq_le_rpow
      (C := 60 * routeTZeroFreeDeltaEnvelopeConstant A) (ε := ε) (by positivity) hε,
    Tendsto.eventually_le_const hdelta hdec,
    Filter.eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hbd hsmall hδsm hx1 hlog1
  obtain ⟨hτ1, hZ, -, -⟩ := hbd
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  set Z : ℝ := 3 * Real.log x with hZdef
  have hZ1 : (1 : ℝ) ≤ Z := by rw [hZdef]; linarith
  have hge := routeTWidthPolylogLower_ge (A := A)
    (τ := 2 * Real.pi * twoRangeTop β x) (Z := Z) hτ1 hZ hZ1
  -- the width beats `2·(log x)^{−(9/10+ε)}`
  have hZpow : Z ^ ((9 : ℝ) / 10) ≤ 3 * (Real.log x) ^ ((9 : ℝ) / 10) := by
    rw [hZdef, Real.mul_rpow (by norm_num) hlogx.le]
    have h3 : (3 : ℝ) ^ ((9 : ℝ) / 10) ≤ 3 := by
      calc (3 : ℝ) ^ ((9 : ℝ) / 10) ≤ (3 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 3 := Real.rpow_one 3
    have hlp : (0 : ℝ) ≤ (Real.log x) ^ ((9 : ℝ) / 10) := Real.rpow_nonneg hlogx.le _
    nlinarith [h3, hlp]
  have hlogZ : Real.log Z = Real.log (3 * Real.log x) := by rw [hZdef]
  have hden : 20 * routeTZeroFreeDeltaEnvelopeConstant A * Z ^ ((9 : ℝ) / 10)
        * (1 + Real.log Z) ^ 2
      ≤ (Real.log x) ^ (9 / 10 + ε) := by
    have hsq0 : (0 : ℝ) ≤ (1 + Real.log Z) ^ 2 := sq_nonneg _
    have hstep : 20 * routeTZeroFreeDeltaEnvelopeConstant A * Z ^ ((9 : ℝ) / 10)
          * (1 + Real.log Z) ^ 2
        ≤ 60 * routeTZeroFreeDeltaEnvelopeConstant A * (Real.log x) ^ ((9 : ℝ) / 10)
          * (1 + Real.log Z) ^ 2 := by
      have h1 : 20 * routeTZeroFreeDeltaEnvelopeConstant A * Z ^ ((9 : ℝ) / 10)
          ≤ 60 * routeTZeroFreeDeltaEnvelopeConstant A * (Real.log x) ^ ((9 : ℝ) / 10) := by
        nlinarith [hZpow, hC]
      exact mul_le_mul_of_nonneg_right h1 hsq0
    have hpow0 : (0 : ℝ) < (Real.log x) ^ ((9 : ℝ) / 10) := Real.rpow_pos_of_pos hlogx _
    have hε0 : (0 : ℝ) < (Real.log x) ^ ε := Real.rpow_pos_of_pos hlogx ε
    have hcomb : 60 * routeTZeroFreeDeltaEnvelopeConstant A * (Real.log x) ^ ((9 : ℝ) / 10)
          * (1 + Real.log Z) ^ 2
        ≤ (Real.log x) ^ ((9 : ℝ) / 10) * (Real.log x) ^ ε := by
      rw [hlogZ] at *
      have := mul_le_mul_of_nonneg_left hsmall hpow0.le
      nlinarith [this, hpow0, sq_nonneg (1 + Real.log (3 * Real.log x)), hC]
    have hid : (Real.log x) ^ ((9 : ℝ) / 10) * (Real.log x) ^ ε = (Real.log x) ^ (9 / 10 + ε) := by
      rw [← Real.rpow_add hlogx]
    linarith [hstep, hcomb, hid.symm.le, hid.le]
  have hpowpos : (0 : ℝ) < (Real.log x) ^ (9 / 10 + ε) := Real.rpow_pos_of_pos hlogx _
  have hdenpos : (0 : ℝ) < 10 * routeTZeroFreeDeltaEnvelopeConstant A * Z ^ ((9 : ℝ) / 10)
      * (1 + Real.log Z) ^ 2 := by
    have h1 : (0 : ℝ) < Z ^ ((9 : ℝ) / 10) := Real.rpow_pos_of_pos (by linarith) _
    have h2 : (0 : ℝ) < (1 + Real.log Z) ^ 2 := by
      have : (0 : ℝ) ≤ Real.log Z := Real.log_nonneg hZ1
      positivity
    positivity
  have hwidth : 2 * (Real.log x) ^ (-(9 / 10 + ε))
      ≤ routeTWidthPolylogLower A (2 * Real.pi * twoRangeTop β x) := by
    refine le_trans ?_ hge
    rw [Real.rpow_neg hlogx.le, ← one_div, mul_one_div, div_le_div_iff₀ hpowpos hdenpos]
    linarith [hden]
  have hmin : 2 * (Real.log x) ^ (-(9 / 10 + ε))
      ≤ min delta (routeTWidthPolylogLower A (2 * Real.pi * twoRangeTop β x)) := by
    refine le_min ?_ hwidth
    rw [Real.rpow_neg hlogx.le] at hδsm ⊢
    linarith [hδsm]
  have hμ : (Real.log x) ^ (-(9 / 10 + ε)) ≤ twoRangeMu A delta β x := by
    rw [twoRangeMu]
    linarith [hmin]
  have hq0 : (0 : ℝ) < twoRangeQ a x := by
    rw [twoRangeQ]
    exact Real.rpow_pos_of_pos hlogx a
  have hstep := mul_le_mul_of_nonneg_right hμ hq0.le
  refine le_trans (le_of_eq ?_) hstep
  rw [twoRangeQ, ← Real.rpow_add hlogx]
  congr 1
  rw [hεdef]
  ring

/-- **A power of the logarithm against an exponential saving bounded below by a power.** -/
theorem tendsto_rpow_log_mul_exp_neg_of_ge {c s : ℝ} (hs : 0 < s) {f : ℝ → ℝ}
    (hf : ∀ᶠ x : ℝ in atTop, (Real.log x) ^ s ≤ f x) :
    Tendsto (fun x : ℝ => (Real.log x) ^ c * Real.exp (-(f x))) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ (tendsto_rpow_log_mul_exp_neg (c := c) (a := s) hs)
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx1
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have : (0 : ℝ) ≤ (Real.log x) ^ c := Real.rpow_nonneg hlogx.le c
    positivity
  · filter_upwards [hf, Filter.eventually_gt_atTop (1 : ℝ)] with x hfx hx1
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hnn : (0 : ℝ) ≤ (Real.log x) ^ c := Real.rpow_nonneg hlogx.le c
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hnn

/-- The relative size of a high block at the schedule. -/
def twoRangeHighRho (A delta Ctot a b c' β A₃ x : ℝ) : ℝ :=
  (4 / Real.log 2)
    * ((1 + highEta c' x)
        * relScaledMajorant Ctot (twoRangeWidth b A₃ x) (twoRangeLx b x)
            (twoRangeHmaj A b A₃ β x) (twoRangeMu A delta β x) (twoRangeQ a x)
            (twoRangeT₀ b A₃ x) (twoRangeXmin a x)
      + 7 * Real.exp 9 / ((highBase a x : ℕ) : ℝ))

/-- **The high blocks on the large half of the annulus.**  This is the hypothesis `hbound'` of
`Sieve/MoebiusTwoRangeWindow.integral_Icc_normSq_logPoly_moebius_le_twoRange`, together with the
fact that its relative size beats every admissible power of the logarithm. -/
theorem exists_twoRange_high_bound {a b c' β A₃ : ℝ}
    (ha : 9 / 10 < a) (hab : a < b) (hb1 : b < 1) (hc' : 0 < c')
    (hβ0 : 0 < β) (hβ1 : β < 1) (hA₃ : 0 < A₃) :
    ∃ A delta Ctot : ℝ, 0 < delta ∧ 0 < Ctot ∧
      (∀ᶠ x : ℝ in atTop, ∀ T : Set ℝ, ∀ j ∈ Finset.range (highSteps a b c' x),
        ∀ w ∈ annulusLarge T (twoRangeTop β x) (twoRangeDisc b A₃ x),
          ‖primeBlockPoly (geomBlock (primesRange (highBase a x) (highTop a b c' x))
              ((highBase a x : ℕ) : ℝ) (1 + highEta c' x) j) w‖
            ≤ twoRangeHighRho A delta Ctot a b c' β A₃ x
                * (((highBase a x : ℕ) : ℝ) * (1 + highEta c' x) ^ j))
      ∧ ∀ e : ℝ, 0 ≤ e → e < A₃ + 1 →
          Tendsto (fun x : ℝ =>
            (Real.log x) ^ e * twoRangeHighRho A delta Ctot a b c' β A₃ x) atTop (𝓝 0) := by
  obtain ⟨A, delta, Ctot, τ₀, hdelta, hCtot, hτ₀, hann⟩ := exists_annulus_bound_uniform
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hb0 : (0 : ℝ) < b := lt_trans ha0 hab
  refine ⟨A, delta, Ctot, hdelta, hCtot, ?_, ?_⟩
  · filter_upwards [highBlockTop_log_bounds (a := a) (b := b) (c' := c') hab.le hc',
      one_le_twoRangeWidth (b := b) (A₃ := A₃) hb0 hA₃,
      twoRangeDisc_ge (b := b) (A₃ := A₃) hb0 hA₃ τ₀,
      twoRangeDisc_le_top (b := b) (A₃ := A₃) (β := β) hb0 hA₃ hβ0 hβ1,
      Filter.eventually_gt_atTop (1 : ℝ)] with x hlogbd hD hdisc hdt hx1
    intro T j hj w hw
    have hz₀ : 1 ≤ highBase a x := by
      rw [highBase]
      exact Nat.one_le_ceil_iff.2 (Real.exp_pos _)
    have hη : (0 : ℝ) ≤ highEta c' x := (highEta_pos hx1).le
    have hsub := annulusLarge_subset_annulus T (twoRangeTop β x) (twoRangeDisc b A₃ x) hw
    have hkey := hann (highBase a x) (highTop a b c' x) (highSteps a b c' x) 0
      ((highBase a x : ℕ) : ℝ) (highEta c' x) (twoRangeWidth b A₃ x)
      (twoRangeDisc b A₃ x) (twoRangeTop β x) (twoRangeLx b x) (twoRangeQ a x)
      (twoRangeMu A delta β x) (twoRangeXmin a x) (twoRangeHmaj A b A₃ β x)
      hz₀ rfl hη rfl hD hdisc hdt
      (fun k hk => (hlogbd k hk).1) (twoRangeQ_nonneg hx1)
      (fun k hk => (hlogbd k hk).2.1) (twoRangeMu_nonneg hdelta.le x) (twoRangeMu_le x)
      (twoRangeXmin_pos a x) (fun k hk => (hlogbd k hk).2.2) (le_refl _)
      j hj w hsub
    rw [two_pi_mul_twoRangeDisc] at hkey
    rw [twoRangeHighRho]
    exact hkey
  · intro e he0 he1
    have he3 : e < 6 * b + 4 * A₃ + 2 := by linarith
    have hxpos : ∀ᶠ x : ℝ in atTop, 0 < twoRangeXmin a x :=
      Filter.Eventually.of_forall fun x => twoRangeXmin_pos a x
    have hexpq : Tendsto (fun x : ℝ =>
        (Real.log x) ^ (2 * b + 2 * A₃ + 4 + e)
          * Real.exp (-(twoRangeMu A delta β x * twoRangeQ a x))) atTop (𝓝 0) :=
      tendsto_rpow_log_mul_exp_neg_of_ge (c := 2 * b + 2 * A₃ + 4 + e)
        (s := (a - 9 / 10) / 2) (by linarith)
        (twoRangeMu_mul_twoRangeQ_ge (A := A) hdelta ha hβ0 hβ1)
    have hxmin : Tendsto (fun x : ℝ =>
        (Real.log x) ^ (b + e) / Real.sqrt (twoRangeXmin a x)) atTop (𝓝 0) := by
      refine (tendsto_logRpow_mul_expSaving (d := a) (s := (1 : ℝ) / 2) ha0
        (by norm_num) (b + e)).congr' ?_
      filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx1
      have hc0 : (0 : ℝ) < cardLength a x := cardLength_pos a x
      have hsq : Real.sqrt (twoRangeXmin a x) = Real.exp ((Real.log x) ^ a / 2) := by
        rw [twoRangeXmin, sqrt_eq_exp_half_log hc0, log_cardLength]
      have hexp : Real.exp (-(1 / 2 * (Real.log x) ^ a))
          = (Real.exp ((Real.log x) ^ a / 2))⁻¹ := by
        rw [← Real.exp_neg]
        congr 1
        ring
      rw [hsq, hexp]
      exact (div_eq_mul_inv _ _).symm
    have hrel := tendsto_logRpow_mul_relScaledMajorant (b := b) (A₃ := A₃) (Ctot := Ctot)
      (e := e) (Hmaj := fun x => twoRangeHmaj A b A₃ β x)
      (μ := fun x => twoRangeMu A delta β x) (q := fun x => twoRangeQ a x)
      (xmin := fun x => twoRangeXmin a x)
      hb0 hA₃ hCtot.le he1 he3 he0
      (twoRangeHmaj_bounds (A := A) hb0 hA₃ hβ0 hβ1) hxpos hexpq hxmin
    have hcard := tendsto_rpow_log_div_cardLength (β := a) ha0 e
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hg : Tendsto (fun x : ℝ =>
        (4 / Real.log 2) * (2 * ((Real.log x) ^ e
            * relScaledMajorant Ctot (twoRangeWidth b A₃ x) (twoRangeLx b x)
                (twoRangeHmaj A b A₃ β x) (twoRangeMu A delta β x) (twoRangeQ a x)
                (twoRangeT₀ b A₃ x) (twoRangeXmin a x))
          + 7 * Real.exp 9 * ((Real.log x) ^ e / cardLength a x))) atTop (𝓝 0) := by
      have h := ((hrel.const_mul (2 : ℝ)).add (hcard.const_mul (7 * Real.exp 9))).const_mul
        (4 / Real.log 2)
      simpa using h
    refine squeeze_zero' ?_ ?_ hg
    · filter_upwards [twoRangeHmaj_bounds (A := A) (b := b) (A₃ := A₃) (β := β) hb0 hA₃ hβ0 hβ1,
        Filter.eventually_gt_atTop (1 : ℝ)] with x hHm hx1
      have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
      have hpe : (0 : ℝ) ≤ (Real.log x) ^ e := Real.rpow_nonneg hlogx.le e
      have hLx0 : (0 : ℝ) ≤ twoRangeLx b x := by
        rw [twoRangeLx]
        have h1 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        have h2 : (0 : ℝ) ≤ (Real.log x) ^ b := Real.rpow_nonneg hlogx.le b
        linarith
      have hrel0 := relScaledMajorant_nonneg (Ctot := Ctot) (D := twoRangeWidth b A₃ x)
        (Lx := twoRangeLx b x) (Hmaj := twoRangeHmaj A b A₃ β x)
        (μ := twoRangeMu A delta β x) (q := twoRangeQ a x) (t₀ := twoRangeT₀ b A₃ x)
        (xmin := twoRangeXmin a x) hCtot.le (twoRangeWidth_pos hx1) hLx0 hHm.1
        (twoRangeT₀_pos hx1) (twoRangeXmin_pos a x)
      have hη : (0 : ℝ) < highEta c' x := highEta_pos hx1
      have hR0 : (0 : ℝ) < ((highBase a x : ℕ) : ℝ) := by
        have h1 := (highBase_bounds (a := a) hx1).1
        have h2 := cardLength_pos a x
        linarith
      have hrho : (0 : ℝ) ≤ twoRangeHighRho A delta Ctot a b c' β A₃ x := by
        rw [twoRangeHighRho]
        have h1 : (0 : ℝ) ≤ (1 + highEta c' x)
            * relScaledMajorant Ctot (twoRangeWidth b A₃ x) (twoRangeLx b x)
                (twoRangeHmaj A b A₃ β x) (twoRangeMu A delta β x) (twoRangeQ a x)
                (twoRangeT₀ b A₃ x) (twoRangeXmin a x) :=
          mul_nonneg (by linarith) hrel0
        have h2 : (0 : ℝ) ≤ 7 * Real.exp 9 / ((highBase a x : ℕ) : ℝ) := by positivity
        have h3 : (0 : ℝ) ≤ 4 / Real.log 2 := by positivity
        exact mul_nonneg h3 (by linarith)
      exact mul_nonneg hpe hrho
    · filter_upwards [twoRangeHmaj_bounds (A := A) (b := b) (A₃ := A₃) (β := β) hb0 hA₃ hβ0 hβ1,
        Filter.eventually_gt_atTop (1 : ℝ),
        Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) (tendsto_highEta hc')]
        with x hHm hx1 hη1
      have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
      have hpe : (0 : ℝ) ≤ (Real.log x) ^ e := Real.rpow_nonneg hlogx.le e
      have hLx0 : (0 : ℝ) ≤ twoRangeLx b x := by
        rw [twoRangeLx]
        have h1 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        have h2 : (0 : ℝ) ≤ (Real.log x) ^ b := Real.rpow_nonneg hlogx.le b
        linarith
      have hrel0 := relScaledMajorant_nonneg (Ctot := Ctot) (D := twoRangeWidth b A₃ x)
        (Lx := twoRangeLx b x) (Hmaj := twoRangeHmaj A b A₃ β x)
        (μ := twoRangeMu A delta β x) (q := twoRangeQ a x) (t₀ := twoRangeT₀ b A₃ x)
        (xmin := twoRangeXmin a x) hCtot.le (twoRangeWidth_pos hx1) hLx0 hHm.1
        (twoRangeT₀_pos hx1) (twoRangeXmin_pos a x)
      have hη : (0 : ℝ) < highEta c' x := highEta_pos hx1
      have hc0 : (0 : ℝ) < cardLength a x := cardLength_pos a x
      have hRc : cardLength a x ≤ ((highBase a x : ℕ) : ℝ) := (highBase_bounds (a := a) hx1).1
      have hR0 : (0 : ℝ) < ((highBase a x : ℕ) : ℝ) := by linarith
      -- the two factors
      have hfac1 : (1 + highEta c' x)
            * ((Real.log x) ^ e
              * relScaledMajorant Ctot (twoRangeWidth b A₃ x) (twoRangeLx b x)
                  (twoRangeHmaj A b A₃ β x) (twoRangeMu A delta β x) (twoRangeQ a x)
                  (twoRangeT₀ b A₃ x) (twoRangeXmin a x))
          ≤ 2 * ((Real.log x) ^ e
              * relScaledMajorant Ctot (twoRangeWidth b A₃ x) (twoRangeLx b x)
                  (twoRangeHmaj A b A₃ β x) (twoRangeMu A delta β x) (twoRangeQ a x)
                  (twoRangeT₀ b A₃ x) (twoRangeXmin a x)) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hpe hrel0)
      have hfac2 : (Real.log x) ^ e / ((highBase a x : ℕ) : ℝ)
          ≤ (Real.log x) ^ e / cardLength a x :=
        div_le_div_of_nonneg_left hpe hc0 hRc
      have hexpand : (Real.log x) ^ e * twoRangeHighRho A delta Ctot a b c' β A₃ x
          = (4 / Real.log 2)
            * ((1 + highEta c' x)
                * ((Real.log x) ^ e
                  * relScaledMajorant Ctot (twoRangeWidth b A₃ x) (twoRangeLx b x)
                      (twoRangeHmaj A b A₃ β x) (twoRangeMu A delta β x) (twoRangeQ a x)
                      (twoRangeT₀ b A₃ x) (twoRangeXmin a x))
              + 7 * Real.exp 9 * ((Real.log x) ^ e / ((highBase a x : ℕ) : ℝ))) := by
        rw [twoRangeHighRho]
        field_simp
      rw [hexpand]
      have hcoef : (0 : ℝ) ≤ 4 / Real.log 2 := by positivity
      have hstep : (1 + highEta c' x)
              * ((Real.log x) ^ e
                * relScaledMajorant Ctot (twoRangeWidth b A₃ x) (twoRangeLx b x)
                    (twoRangeHmaj A b A₃ β x) (twoRangeMu A delta β x) (twoRangeQ a x)
                    (twoRangeT₀ b A₃ x) (twoRangeXmin a x))
            + 7 * Real.exp 9 * ((Real.log x) ^ e / ((highBase a x : ℕ) : ℝ))
          ≤ 2 * ((Real.log x) ^ e
              * relScaledMajorant Ctot (twoRangeWidth b A₃ x) (twoRangeLx b x)
                  (twoRangeHmaj A b A₃ β x) (twoRangeMu A delta β x) (twoRangeQ a x)
                  (twoRangeT₀ b A₃ x) (twoRangeXmin a x))
            + 7 * Real.exp 9 * ((Real.log x) ^ e / cardLength a x) := by
        have h7 : (0 : ℝ) ≤ 7 * Real.exp 9 := by positivity
        nlinarith [hfac1, mul_le_mul_of_nonneg_left hfac2 h7]
      exact mul_le_mul_of_nonneg_left hstep hcoef

end

end RHTower.Sieve
