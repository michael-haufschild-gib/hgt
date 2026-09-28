import GaloisForLFunctions.RHTower.Sieve.TwoRangeHighBound

/-!
# The high blocks up to an arbitrary frequency top

The Route-T bound for the blocks of the high designated range depends on the top of the frequency
window only through three facts: the top is at least `1`, `2π` times it is at most the outer
scale, and it lies above the low-frequency disc.  This file restates the high-range bound for any
top with these properties, so that the window can be the full `(M/h)·ω` of an arbitrary
short-interval length `h`.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The width of the Route-T contour for a frequency top. -/
def topMu (A delta : ℝ) (top : ℝ → ℝ) (x : ℝ) : ℝ :=
  min delta (routeTWidthPolylogLower A (2 * Real.pi * top x)) / 2

/-- The height cost of the Route-T contour for a frequency top. -/
def topHmaj (A b A₃ : ℝ) (top : ℝ → ℝ) (x : ℝ) : ℝ :=
  1 / (2 * Real.pi * twoRangeDisc b A₃ x)
    + Real.log (3 * (2 * Real.pi * top x) / 2)
        / routeTWidthPolylogLower A (2 * Real.pi * top x)

theorem topMu_nonneg {A delta : ℝ} {top : ℝ → ℝ} (hdelta : 0 ≤ delta) (x : ℝ) :
    0 ≤ topMu A delta top x := by
  rw [topMu]
  have := (routeTWidthPolylogLower_pos A (2 * Real.pi * top x)).le
  have hmin : (0 : ℝ) ≤ min delta (routeTWidthPolylogLower A (2 * Real.pi * top x)) :=
    le_min hdelta this
  linarith

theorem topMu_le {A delta : ℝ} {top : ℝ → ℝ} (x : ℝ) :
    topMu A delta top x ≤ min delta (routeTWidthPolylogLower A (2 * Real.pi * top x)) / 2 :=
  le_refl _

/-- The height envelope of the Route-T window, in the logarithm of the outer scale. -/
theorem routeTHeight_top_bounds {top : ℝ → ℝ} (htop1 : ∀ᶠ x : ℝ in atTop, 1 ≤ top x)
    (htopx : ∀ᶠ x : ℝ in atTop, 2 * Real.pi * top x ≤ x) :
    ∀ᶠ x : ℝ in atTop,
      1 ≤ |2 * Real.pi * top x|
        ∧ routeTLogHeightEnvelope (4 * (3 * |2 * Real.pi * top x| / 2 + 1))
            ≤ 3 * Real.log x
        ∧ (0 : ℝ) ≤ Real.log (3 * (2 * Real.pi * top x) / 2)
        ∧ Real.log (3 * (2 * Real.pi * top x) / 2) ≤ 2 * Real.log x := by
  filter_upwards [htop1, htopx,
    Filter.eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (10 : ℝ)] with x hT1 hTx hx1 hlog10
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hτ0 : (6 : ℝ) ≤ 2 * Real.pi * top x := by nlinarith [hT1, hpi3]
  have hτabs : |2 * Real.pi * top x| = 2 * Real.pi * top x :=
    abs_of_pos (by linarith)
  have hτ1 : 1 ≤ |2 * Real.pi * top x| := by rw [hτabs]; linarith
  refine ⟨hτ1, ?_, ?_, ?_⟩
  · have henv := routeTLogHeightEnvelope_le (τ := 2 * Real.pi * top x) hτ1
    have hlogτ : Real.log |2 * Real.pi * top x| ≤ Real.log x := by
      rw [hτabs]
      exact Real.log_le_log (by linarith) hTx
    linarith [henv, hlogτ, hlog10]
  · refine Real.log_nonneg ?_
    linarith
  · have hle : 3 * (2 * Real.pi * top x) / 2 ≤ 2 * x := by linarith
    have hstep : Real.log (3 * (2 * Real.pi * top x) / 2) ≤ Real.log (2 * x) :=
      Real.log_le_log (by linarith) hle
    have hsplit : Real.log (2 * x) = Real.log 2 + Real.log x :=
      Real.log_mul (by norm_num) (by linarith)
    have hl2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    linarith


/-- **The height cost of the Route-T contour is at most `(log x)²`.** -/
theorem topHmaj_bounds {A b A₃ : ℝ} {top : ℝ → ℝ} (hb : 0 < b) (hA₃ : 0 < A₃)
    (htop1 : ∀ᶠ x : ℝ in atTop, 1 ≤ top x)
    (htopx : ∀ᶠ x : ℝ in atTop, 2 * Real.pi * top x ≤ x) :
    ∀ᶠ x : ℝ in atTop,
      0 ≤ topHmaj A b A₃ top x ∧ topHmaj A b A₃ top x ≤ (Real.log x) ^ (2 : ℝ) := by
  have hC : (0 : ℝ) < routeTZeroFreeDeltaEnvelopeConstant A :=
    routeTZeroFreeDeltaEnvelopeConstant_pos A
  filter_upwards [routeTHeight_top_bounds htop1 htopx,
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
  have hwidth0 : (0 : ℝ) < routeTWidthPolylogLower A (2 * Real.pi * top x) :=
    routeTWidthPolylogLower_pos _ _
  have hinv := inv_routeTWidthPolylogLower_le (A := A)
    (τ := 2 * Real.pi * top x) (Z := Z) hτ1 hZ hZ1
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
  have hquot : Real.log (3 * (2 * Real.pi * top x) / 2)
        / routeTWidthPolylogLower A (2 * Real.pi * top x)
      ≤ 2 * Real.log x
        * (30 * routeTZeroFreeDeltaEnvelopeConstant A * (Real.log x) ^ ((9 : ℝ) / 10)
            * (1 + Real.log Z) ^ 2) := by
    have hrw : Real.log (3 * (2 * Real.pi * top x) / 2)
        / routeTWidthPolylogLower A (2 * Real.pi * top x)
        = Real.log (3 * (2 * Real.pi * top x) / 2)
          * (1 / routeTWidthPolylogLower A (2 * Real.pi * top x)) := by
      ring
    rw [hrw]
    refine mul_le_mul hlogS (le_trans hinv hinner) (by positivity) (by linarith)
  have hpow19 : Real.log x * (Real.log x) ^ ((9 : ℝ) / 10) = (Real.log x) ^ ((19 : ℝ) / 10) := by
    rw [show ((19 : ℝ) / 10) = 1 + 9 / 10 by norm_num, Real.rpow_add hlogx, Real.rpow_one]
  have h19 : (1 : ℝ) ≤ (Real.log x) ^ ((19 : ℝ) / 10) :=
    Real.one_le_rpow hlog1 (by norm_num)
  have hmain : topHmaj A b A₃ top x
      ≤ (1 + 60 * routeTZeroFreeDeltaEnvelopeConstant A * (1 + Real.log (3 * Real.log x)) ^ 2)
        * (Real.log x) ^ ((19 : ℝ) / 10) := by
    rw [topHmaj]
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
  rw [topHmaj]
  have hq0 : (0 : ℝ) ≤ Real.log (3 * (2 * Real.pi * top x) / 2)
      / routeTWidthPolylogLower A (2 * Real.pi * top x) :=
    div_nonneg hlogS0 hwidth0.le
  linarith [hdisc0]


/-- **The Route-T contour's width times its frequency exceeds a power of the logarithm.**  This is
the only place where `a > 9/10` is used. -/
theorem topMu_mul_twoRangeQ_ge {A delta a : ℝ} {top : ℝ → ℝ} (hdelta : 0 < delta)
    (ha : 9 / 10 < a) (htop1 : ∀ᶠ x : ℝ in atTop, 1 ≤ top x)
    (htopx : ∀ᶠ x : ℝ in atTop, 2 * Real.pi * top x ≤ x) :
    ∀ᶠ x : ℝ in atTop,
      (Real.log x) ^ ((a - 9 / 10) / 2) ≤ topMu A delta top x * twoRangeQ a x := by
  have hC : (0 : ℝ) < routeTZeroFreeDeltaEnvelopeConstant A :=
    routeTZeroFreeDeltaEnvelopeConstant_pos A
  set ε : ℝ := (a - 9 / 10) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hdec : Tendsto (fun x : ℝ => 2 * (Real.log x) ^ (-(9 / 10 + ε))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_log_of_neg (c := -(9 / 10 + ε)) (by linarith)).const_mul 2
  filter_upwards [routeTHeight_top_bounds htop1 htopx,
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
    (τ := 2 * Real.pi * top x) (Z := Z) hτ1 hZ hZ1
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
      ≤ routeTWidthPolylogLower A (2 * Real.pi * top x) := by
    refine le_trans ?_ hge
    rw [Real.rpow_neg hlogx.le, ← one_div, mul_one_div, div_le_div_iff₀ hpowpos hdenpos]
    linarith [hden]
  have hmin : 2 * (Real.log x) ^ (-(9 / 10 + ε))
      ≤ min delta (routeTWidthPolylogLower A (2 * Real.pi * top x)) := by
    refine le_min ?_ hwidth
    rw [Real.rpow_neg hlogx.le] at hδsm ⊢
    linarith [hδsm]
  have hμ : (Real.log x) ^ (-(9 / 10 + ε)) ≤ topMu A delta top x := by
    rw [topMu]
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


/-- The relative size of a high block at the schedule. -/
def topHighRho (A delta Ctot a b c' A₃ : ℝ) (top : ℝ → ℝ) (x : ℝ) : ℝ :=
  (4 / Real.log 2)
    * ((1 + highEta c' x)
        * relScaledMajorant Ctot (twoRangeWidth b A₃ x) (twoRangeLx b x)
            (topHmaj A b A₃ top x) (topMu A delta top x) (twoRangeQ a x)
            (twoRangeT₀ b A₃ x) (twoRangeXmin a x)
      + 7 * Real.exp 9 / ((highBase a x : ℕ) : ℝ))


/-- **The high blocks on the large half of the annulus.**  This is the hypothesis `hbound'` of
`Sieve/MoebiusTwoRangeWindow.integral_Icc_normSq_logPoly_moebius_le_twoRange`, together with the
fact that its relative size beats every admissible power of the logarithm. -/
theorem exists_top_high_bound {a b c' A₃ : ℝ} {top : ℝ → ℝ}
    (ha : 9 / 10 < a) (hab : a < b) (hb1 : b < 1) (hc' : 0 < c')
    (hA₃ : 0 < A₃) (htop1 : ∀ᶠ x : ℝ in atTop, 1 ≤ top x)
    (htopx : ∀ᶠ x : ℝ in atTop, 2 * Real.pi * top x ≤ x)
    (hdisc : ∀ᶠ x : ℝ in atTop, twoRangeDisc b A₃ x ≤ top x) :
    ∃ A delta Ctot : ℝ, 0 < delta ∧ 0 < Ctot ∧
      (∀ᶠ x : ℝ in atTop, ∀ T : Set ℝ, ∀ j ∈ Finset.range (highSteps a b c' x),
        ∀ w ∈ annulusLarge T (top x) (twoRangeDisc b A₃ x),
          ‖primeBlockPoly (geomBlock (primesRange (highBase a x) (highTop a b c' x))
              ((highBase a x : ℕ) : ℝ) (1 + highEta c' x) j) w‖
            ≤ topHighRho A delta Ctot a b c' A₃ top x
                * (((highBase a x : ℕ) : ℝ) * (1 + highEta c' x) ^ j))
      ∧ ∀ e : ℝ, 0 ≤ e → e < A₃ + 1 →
          Tendsto (fun x : ℝ =>
            (Real.log x) ^ e * topHighRho A delta Ctot a b c' A₃ top x) atTop (𝓝 0) := by
  obtain ⟨A, delta, Ctot, τ₀, hdelta, hCtot, hτ₀, hann⟩ := exists_annulus_bound_uniform
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hb0 : (0 : ℝ) < b := lt_trans ha0 hab
  refine ⟨A, delta, Ctot, hdelta, hCtot, ?_, ?_⟩
  · filter_upwards [highBlockTop_log_bounds (a := a) (b := b) (c' := c') hab.le hc',
      one_le_twoRangeWidth (b := b) (A₃ := A₃) hb0 hA₃,
      twoRangeDisc_ge (b := b) (A₃ := A₃) hb0 hA₃ τ₀,
      hdisc,
      Filter.eventually_gt_atTop (1 : ℝ)] with x hlogbd hD hdisc hdt hx1
    intro T j hj w hw
    have hz₀ : 1 ≤ highBase a x := by
      rw [highBase]
      exact Nat.one_le_ceil_iff.2 (Real.exp_pos _)
    have hη : (0 : ℝ) ≤ highEta c' x := (highEta_pos hx1).le
    have hsub := annulusLarge_subset_annulus T (top x) (twoRangeDisc b A₃ x) hw
    have hkey := hann (highBase a x) (highTop a b c' x) (highSteps a b c' x) 0
      ((highBase a x : ℕ) : ℝ) (highEta c' x) (twoRangeWidth b A₃ x)
      (twoRangeDisc b A₃ x) (top x) (twoRangeLx b x) (twoRangeQ a x)
      (topMu A delta top x) (twoRangeXmin a x) (topHmaj A b A₃ top x)
      hz₀ rfl hη rfl hD hdisc hdt
      (fun k hk => (hlogbd k hk).1) (twoRangeQ_nonneg hx1)
      (fun k hk => (hlogbd k hk).2.1) (topMu_nonneg hdelta.le x) (topMu_le x)
      (twoRangeXmin_pos a x) (fun k hk => (hlogbd k hk).2.2) (le_refl _)
      j hj w hsub
    rw [two_pi_mul_twoRangeDisc] at hkey
    rw [topHighRho]
    exact hkey
  · intro e he0 he1
    have he3 : e < 6 * b + 4 * A₃ + 2 := by linarith
    have hxpos : ∀ᶠ x : ℝ in atTop, 0 < twoRangeXmin a x :=
      Filter.Eventually.of_forall fun x => twoRangeXmin_pos a x
    have hexpq : Tendsto (fun x : ℝ =>
        (Real.log x) ^ (2 * b + 2 * A₃ + 4 + e)
          * Real.exp (-(topMu A delta top x * twoRangeQ a x))) atTop (𝓝 0) :=
      tendsto_rpow_log_mul_exp_neg_of_ge (c := 2 * b + 2 * A₃ + 4 + e)
        (s := (a - 9 / 10) / 2) (by linarith)
        (topMu_mul_twoRangeQ_ge (A := A) hdelta ha htop1 htopx)
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
      (e := e) (Hmaj := fun x => topHmaj A b A₃ top x)
      (μ := fun x => topMu A delta top x) (q := fun x => twoRangeQ a x)
      (xmin := fun x => twoRangeXmin a x)
      hb0 hA₃ hCtot.le he1 he3 he0
      (topHmaj_bounds (A := A) hb0 hA₃ htop1 htopx) hxpos hexpq hxmin
    have hcard := tendsto_rpow_log_div_cardLength (β := a) ha0 e
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hg : Tendsto (fun x : ℝ =>
        (4 / Real.log 2) * (2 * ((Real.log x) ^ e
            * relScaledMajorant Ctot (twoRangeWidth b A₃ x) (twoRangeLx b x)
                (topHmaj A b A₃ top x) (topMu A delta top x) (twoRangeQ a x)
                (twoRangeT₀ b A₃ x) (twoRangeXmin a x))
          + 7 * Real.exp 9 * ((Real.log x) ^ e / cardLength a x))) atTop (𝓝 0) := by
      have h := ((hrel.const_mul (2 : ℝ)).add (hcard.const_mul (7 * Real.exp 9))).const_mul
        (4 / Real.log 2)
      simpa using h
    refine squeeze_zero' ?_ ?_ hg
    · filter_upwards [topHmaj_bounds (A := A) (b := b) (A₃ := A₃) hb0 hA₃ htop1 htopx,
        Filter.eventually_gt_atTop (1 : ℝ)] with x hHm hx1
      have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
      have hpe : (0 : ℝ) ≤ (Real.log x) ^ e := Real.rpow_nonneg hlogx.le e
      have hLx0 : (0 : ℝ) ≤ twoRangeLx b x := by
        rw [twoRangeLx]
        have h1 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        have h2 : (0 : ℝ) ≤ (Real.log x) ^ b := Real.rpow_nonneg hlogx.le b
        linarith
      have hrel0 := relScaledMajorant_nonneg (Ctot := Ctot) (D := twoRangeWidth b A₃ x)
        (Lx := twoRangeLx b x) (Hmaj := topHmaj A b A₃ top x)
        (μ := topMu A delta top x) (q := twoRangeQ a x) (t₀ := twoRangeT₀ b A₃ x)
        (xmin := twoRangeXmin a x) hCtot.le (twoRangeWidth_pos hx1) hLx0 hHm.1
        (twoRangeT₀_pos hx1) (twoRangeXmin_pos a x)
      have hη : (0 : ℝ) < highEta c' x := highEta_pos hx1
      have hR0 : (0 : ℝ) < ((highBase a x : ℕ) : ℝ) := by
        have h1 := (highBase_bounds (a := a) hx1).1
        have h2 := cardLength_pos a x
        linarith
      have hrho : (0 : ℝ) ≤ topHighRho A delta Ctot a b c' A₃ top x := by
        rw [topHighRho]
        have h1 : (0 : ℝ) ≤ (1 + highEta c' x)
            * relScaledMajorant Ctot (twoRangeWidth b A₃ x) (twoRangeLx b x)
                (topHmaj A b A₃ top x) (topMu A delta top x) (twoRangeQ a x)
                (twoRangeT₀ b A₃ x) (twoRangeXmin a x) :=
          mul_nonneg (by linarith) hrel0
        have h2 : (0 : ℝ) ≤ 7 * Real.exp 9 / ((highBase a x : ℕ) : ℝ) := by positivity
        have h3 : (0 : ℝ) ≤ 4 / Real.log 2 := by positivity
        exact mul_nonneg h3 (by linarith)
      exact mul_nonneg hpe hrho
    · filter_upwards [topHmaj_bounds (A := A) (b := b) (A₃ := A₃) hb0 hA₃ htop1 htopx,
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
        (Lx := twoRangeLx b x) (Hmaj := topHmaj A b A₃ top x)
        (μ := topMu A delta top x) (q := twoRangeQ a x) (t₀ := twoRangeT₀ b A₃ x)
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
                  (topHmaj A b A₃ top x) (topMu A delta top x) (twoRangeQ a x)
                  (twoRangeT₀ b A₃ x) (twoRangeXmin a x))
          ≤ 2 * ((Real.log x) ^ e
              * relScaledMajorant Ctot (twoRangeWidth b A₃ x) (twoRangeLx b x)
                  (topHmaj A b A₃ top x) (topMu A delta top x) (twoRangeQ a x)
                  (twoRangeT₀ b A₃ x) (twoRangeXmin a x)) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hpe hrel0)
      have hfac2 : (Real.log x) ^ e / ((highBase a x : ℕ) : ℝ)
          ≤ (Real.log x) ^ e / cardLength a x :=
        div_le_div_of_nonneg_left hpe hc0 hRc
      have hexpand : (Real.log x) ^ e * topHighRho A delta Ctot a b c' A₃ top x
          = (4 / Real.log 2)
            * ((1 + highEta c' x)
                * ((Real.log x) ^ e
                  * relScaledMajorant Ctot (twoRangeWidth b A₃ x) (twoRangeLx b x)
                      (topHmaj A b A₃ top x) (topMu A delta top x) (twoRangeQ a x)
                      (twoRangeT₀ b A₃ x) (twoRangeXmin a x))
              + 7 * Real.exp 9 * ((Real.log x) ^ e / ((highBase a x : ℕ) : ℝ))) := by
        rw [topHighRho]
        field_simp
      rw [hexpand]
      have hcoef : (0 : ℝ) ≤ 4 / Real.log 2 := by positivity
      have hstep : (1 + highEta c' x)
              * ((Real.log x) ^ e
                * relScaledMajorant Ctot (twoRangeWidth b A₃ x) (twoRangeLx b x)
                    (topHmaj A b A₃ top x) (topMu A delta top x) (twoRangeQ a x)
                    (twoRangeT₀ b A₃ x) (twoRangeXmin a x))
            + 7 * Real.exp 9 * ((Real.log x) ^ e / ((highBase a x : ℕ) : ℝ))
          ≤ 2 * ((Real.log x) ^ e
              * relScaledMajorant Ctot (twoRangeWidth b A₃ x) (twoRangeLx b x)
                  (topHmaj A b A₃ top x) (topMu A delta top x) (twoRangeQ a x)
                  (twoRangeT₀ b A₃ x) (twoRangeXmin a x))
            + 7 * Real.exp 9 * ((Real.log x) ^ e / cardLength a x) := by
        have h7 : (0 : ℝ) ≤ 7 * Real.exp 9 := by positivity
        nlinarith [hfac1, mul_le_mul_of_nonneg_left hfac2 h7]
      exact mul_le_mul_of_nonneg_left hstep hcoef


/-- The Route-T relative size is nonnegative. -/
theorem topHighRho_nonneg {A₀ δ₀ Ctot a₁ b c' A₃ : ℝ} {top : ℝ → ℝ} (hCtot : 0 ≤ Ctot)
    (hb : 0 < b) (hA₃ : 0 < A₃) (htop1 : ∀ᶠ x : ℝ in atTop, 1 ≤ top x)
    (htopx : ∀ᶠ x : ℝ in atTop, 2 * Real.pi * top x ≤ x) :
    ∀ᶠ x : ℝ in atTop, 0 ≤ topHighRho A₀ δ₀ Ctot a₁ b c' A₃ top x := by
  filter_upwards [topHmaj_bounds (A := A₀) (b := b) (A₃ := A₃) hb hA₃ htop1 htopx,
    Filter.eventually_gt_atTop (1 : ℝ)] with x hHm hx1
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hLx0 : (0 : ℝ) ≤ twoRangeLx b x := by
    rw [twoRangeLx]
    have h1 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h2 : (0 : ℝ) ≤ (Real.log x) ^ b := Real.rpow_nonneg hlogx.le b
    linarith
  have hrel0 : (0 : ℝ) ≤ relScaledMajorant Ctot (twoRangeWidth b A₃ x) (twoRangeLx b x)
      (topHmaj A₀ b A₃ top x) (topMu A₀ δ₀ top x) (twoRangeQ a₁ x)
      (twoRangeT₀ b A₃ x) (twoRangeXmin a₁ x) :=
    relScaledMajorant_nonneg hCtot (twoRangeWidth_pos hx1) hLx0 hHm.1
      (twoRangeT₀_pos hx1) (twoRangeXmin_pos a₁ x)
  have hR0 : (0 : ℝ) < ((highBase a₁ x : ℕ) : ℝ) := by
    have h1 := (highBase_bounds (a := a₁) hx1).1
    have h2 := cardLength_pos a₁ x
    linarith
  have hη : (0 : ℝ) < highEta c' x := highEta_pos hx1
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [topHighRho]
  have h1 : (0 : ℝ) ≤ (1 + highEta c' x)
      * relScaledMajorant Ctot (twoRangeWidth b A₃ x) (twoRangeLx b x)
          (topHmaj A₀ b A₃ top x) (topMu A₀ δ₀ top x) (twoRangeQ a₁ x)
          (twoRangeT₀ b A₃ x) (twoRangeXmin a₁ x) := mul_nonneg (by linarith) hrel0
  have h2 : (0 : ℝ) ≤ 7 * Real.exp 9 / ((highBase a₁ x : ℕ) : ℝ) := by positivity
  have h3 : (0 : ℝ) ≤ 4 / Real.log 2 := by positivity
  exact mul_nonneg h3 (by linarith)

end

end RHTower.Sieve
