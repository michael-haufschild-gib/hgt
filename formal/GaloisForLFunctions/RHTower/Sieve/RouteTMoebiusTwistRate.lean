import GaloisForLFunctions.RHTower.Sieve.RouteTContourRateBounds

/-!
# The twisted Mertens sum with a super-polylogarithmic saving, uniformly in the frequency

Feeding the contour data of `Sieve/RouteTContourRateBounds` into the all-frequency rectangle bound
of `Sieve/RouteTMoebiusTwistAllHeights` with

```text
   H = N e^{−3ε} ,   U = N ,   d = 1 + 1/log N ,   ε = (log N)^{1/20}
```

gives, for every real frequency below the cutoff, a saving over the trivial bound that beats every
power of the logarithm.  The three non-left edges are polylogarithmic because `U = N` divides them
by the full cutoff; the left edge carries `N^{1−shift} ≤ N e^{−10ε}`, which is where the zero-free
region enters.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- A power is an exponential of the scaled logarithm. -/
theorem rpow_le_exp_of_log_mul {x y z : ℝ} (hx : 0 < x) (h : Real.log x * y ≤ z) :
    x ^ y ≤ Real.exp z := by
  rw [Real.rpow_def_of_pos hx]
  exact Real.exp_le_exp.2 h

/-- The elementary growth facts the parameter choice needs. -/
theorem eventually_rate_growth :
    ∀ᶠ N : ℝ in atTop,
      0 < N ∧ 8 ≤ Real.log N ∧ routeTInverseBaseHeight ≤ N
      ∧ (1 + Real.log N) * Real.exp (8 * (Real.log N) ^ ((1 : ℝ) / 20)) ≤ N
      ∧ Real.exp (6 * (Real.log N) ^ ((1 : ℝ) / 20)) ≤ N := by
  have hdom := eventually_const_mul_rpow_polylog_le_rpow
    (C := (16 : ℝ)) (α := (1 : ℝ) / 20) (β := (1 : ℝ)) 0 (by norm_num)
  have hL : ∀ᶠ L : ℝ in atTop, 16 * L ^ ((1 : ℝ) / 20) ≤ L := by
    filter_upwards [hdom] with L h
    rwa [pow_zero, mul_one, Real.rpow_one] at h
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (8 : ℝ),
    eventually_ge_atTop routeTInverseBaseHeight,
    Real.tendsto_log_atTop.eventually hL] with N hN0 hL8 hNbase hLdom
  set L : ℝ := Real.log N with hLdef
  set ε : ℝ := L ^ ((1 : ℝ) / 20) with hεdef
  have hε0 : (0 : ℝ) < ε := Real.rpow_pos_of_pos (by linarith) _
  have hNexp : Real.exp L = N := Real.exp_log hN0
  have h1L : (1 : ℝ) + L ≤ Real.exp (L / 2) := by
    have hq : (1 : ℝ) + L / 4 ≤ Real.exp (L / 4) := by
      have := Real.add_one_le_exp (L / 4)
      linarith
    have hsq : Real.exp (L / 2) = Real.exp (L / 4) * Real.exp (L / 4) := by
      rw [← Real.exp_add]; ring_nf
    have hq0 : (0 : ℝ) ≤ 1 + L / 4 := by linarith
    nlinarith [hq, hsq, hq0]
  refine ⟨hN0, hL8, hNbase, ?_, ?_⟩
  · have hstep : (1 + L) * Real.exp (8 * ε) ≤ Real.exp (L / 2) * Real.exp (L / 2) :=
      mul_le_mul h1L (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le (Real.exp_pos _).le
    have heq : Real.exp (L / 2) * Real.exp (L / 2) = N := by
      rw [← Real.exp_add, show L / 2 + L / 2 = L by ring, hNexp]
    linarith [hstep, heq]
  · have hstep : Real.exp (6 * ε) ≤ Real.exp L := Real.exp_le_exp.2 (by linarith)
    linarith [hstep, hNexp]

end

end RHTower.Sieve

namespace RHTower.Sieve

open Filter Topology

noncomputable section
set_option maxHeartbeats 2000000 in
/-- **The rectangle bound at the rate parameters.**  With `H = N e^{−3ε}`, `U = N`,
`d = 1 + 1/log N` and `ε = (log N)^{1/20}`, the four edges of the all-frequency Route-T rectangle,
together with the smoothing window, are below `K·N·e^{−ε}`. -/
theorem routeTMoebiusAllHeightsSmoothBound_le_rate {A C C' M δ : ℝ}
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (hM : 0 ≤ M) (hδ : 0 < δ) {N τ : ℝ}
    (hN0 : 0 < N) (hL8 : 8 ≤ Real.log N) (hNbase : routeTInverseBaseHeight ≤ N)
    (hF2 : (1 + Real.log N) * Real.exp (8 * (Real.log N) ^ ((1 : ℝ) / 20)) ≤ N)
    (hF3 : Real.exp (6 * (Real.log N) ^ ((1 : ℝ) / 20)) ≤ N)
    (hshift : 10 * (Real.log N) ^ ((1 : ℝ) / 20)
      ≤ routeTContourShift A δ (|τ| + N) * Real.log N)
    (hedge : routeTContourEdgeBound A (|τ| + N)
      ≤ Real.exp ((Real.log N) ^ ((1 : ℝ) / 20))) :
    routeTMoebiusAllHeightsSmoothBound A C C' M δ N
          (N * Real.exp (-(3 * (Real.log N) ^ ((1 : ℝ) / 20)))) τ N (1 + 1 / Real.log N)
        / (2 * Real.pi)
      + (N * Real.exp (-(3 * (Real.log N) ^ ((1 : ℝ) / 20))) + 1)
      ≤ ((162 * Real.exp 7 * C + 108 * Real.exp 1 * C' * (M + 1)
          + (M + 1) * (8 + 54 * C)) / (2 * Real.pi) + 2)
        * N * Real.exp (-((Real.log N) ^ ((1 : ℝ) / 20))) := by
  set L : ℝ := Real.log N with hLdef
  set ε : ℝ := L ^ ((1 : ℝ) / 20) with hεdef
  have hL0 : (0 : ℝ) < L := by linarith
  have hε0 : (0 : ℝ) < ε := Real.rpow_pos_of_pos hL0 _
  have hexpε : (1 : ℝ) ≤ Real.exp ε := Real.one_le_exp hε0.le
  have hNexp : Real.exp L = N := Real.exp_log hN0
  have hbase := routeTInverseBaseHeight_ge
  have hN1 : (1 : ℝ) ≤ N := by linarith
  set H : ℝ := N * Real.exp (-(3 * ε)) with hHdef
  set d : ℝ := 1 + 1 / L with hddef
  set S : ℝ := |τ| + N with hSdef
  have hH0 : (0 : ℝ) < H := by rw [hHdef]; positivity
  have hHN : H ≤ N := by
    rw [hHdef]
    have : Real.exp (-(3 * ε)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    nlinarith [hN0]
  have hd1 : (1 : ℝ) < d := by rw [hddef]; have : (0:ℝ) < 1 / L := by positivity
                               linarith
  have hd2 : d ≤ 2 := by
    rw [hddef]
    have : 1 / L ≤ 1 := by rw [div_le_one hL0]; linarith
    linarith
  have hSbase : routeTInverseBaseHeight ≤ S := by
    rw [hSdef]; linarith [abs_nonneg τ]
  -- abbreviations for the rectangle data
  set c : ℝ := routeTContourLeft A δ S with hcdef
  set Mc : ℝ := max M (routeTContourEdgeBound A S) with hMcdef
  have hc12 : (1 : ℝ) / 2 ≤ c := by rw [hcdef]; exact routeTContourLeft_ge_half A δ S
  have hc1 : c ≤ 1 := by rw [hcdef]; exact routeTContourLeft_le_one hδ
  have hc0 : (0 : ℝ) < c := by linarith
  have hMc0 : (0 : ℝ) ≤ Mc := le_trans hM (le_max_left _ _)
  have hMcle : Mc ≤ (M + 1) * Real.exp ε := by
    rw [hMcdef]
    refine max_le ?_ (le_trans hedge ?_)
    · nlinarith [hM, hexpε]
    · nlinarith [hM, hexpε, Real.exp_pos ε]
  -- the cutoff-scale estimates
  have hNH1 : N + H + 1 ≤ 3 * N := by linarith
  have hNH1pos : (0 : ℝ) < N + H + 1 := by linarith
  have hlog3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlogNH1 : Real.log (N + H + 1) ≤ Real.log 3 + L := by
    have h := Real.log_le_log hNH1pos hNH1
    rwa [Real.log_mul (by norm_num) (ne_of_gt hN0), ← hLdef] at h
  have hlogNH1nn : (0 : ℝ) ≤ Real.log (N + H + 1) := Real.log_nonneg (by linarith)
  have hexp2log3 : Real.exp (2 * Real.log 3) = 9 := by
    rw [show (2 : ℝ) * Real.log 3 = Real.log 9 by
      rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring]
    exact Real.exp_log (by norm_num)
  have hpowd : (N + H + 1) ^ d ≤ 9 * Real.exp 1 * N := by
    refine le_trans (rpow_le_exp_of_log_mul hNH1pos
      (z := L + 2 * Real.log 3 + 1) ?_) ?_
    · have hdle : d ≤ 1 + 1 := by linarith [hd2]
      have hstep : Real.log (N + H + 1) * d ≤ (Real.log 3 + L) * (1 + 1 / L) := by
        refine mul_le_mul hlogNH1 (le_of_eq hddef) (by rw [hddef]; positivity) (by linarith)
      have hexpand : (Real.log 3 + L) * (1 + 1 / L) = Real.log 3 + L + Real.log 3 / L + 1 := by
        field_simp
        ring
      have hdiv : Real.log 3 / L ≤ Real.log 3 := by
        rw [div_le_iff₀ hL0]; nlinarith [hlog3]
      rw [hexpand] at hstep
      linarith
    · rw [Real.exp_add, Real.exp_add, hNexp, hexp2log3]
      exact le_of_eq (by ring)
  have hpowc : (N + H + 1) ^ c ≤ 3 * (N * Real.exp (-(10 * ε))) := by
    refine le_trans (rpow_le_exp_of_log_mul hNH1pos
      (z := Real.log 3 + (L - 10 * ε)) ?_) ?_
    · have hstep : Real.log (N + H + 1) * c ≤ (Real.log 3 + L) * c :=
        mul_le_mul_of_nonneg_right hlogNH1 hc0.le
      have hexpand : (Real.log 3 + L) * c = Real.log 3 * c + L * c := by ring
      have h1 : Real.log 3 * c ≤ Real.log 3 := by nlinarith [hlog3, hc1]
      have h2 : L * c ≤ L - 10 * ε := by
        rw [hcdef, routeTContourLeft]
        nlinarith [hshift]
      rw [hexpand] at hstep
      linarith
    · rw [Real.exp_add, Real.exp_sub, hNexp]
      have h9 : Real.exp (Real.log 3) = 3 := Real.exp_log (by norm_num)
      rw [h9]
      have : Real.exp (10 * ε) = (Real.exp (-(10 * ε)))⁻¹ := by
        rw [Real.exp_neg, inv_inv]
      rw [this]
      field_simp
      norm_num
  have hpowNHc : (N + H) ^ c ≤ 2 * (N * Real.exp (-(10 * ε))) := by
    have hNHpos : (0 : ℝ) < N + H := by linarith
    have hNH2 : N + H ≤ 2 * N := by linarith
    have hlogNH : Real.log (N + H) ≤ Real.log 2 + L := by
      have h := Real.log_le_log hNHpos hNH2
      rwa [Real.log_mul (by norm_num) (ne_of_gt hN0), ← hLdef] at h
    have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    refine le_trans (rpow_le_exp_of_log_mul hNHpos
      (z := Real.log 2 + (L - 10 * ε)) ?_) ?_
    · have hstep : Real.log (N + H) * c ≤ (Real.log 2 + L) * c :=
        mul_le_mul_of_nonneg_right hlogNH hc0.le
      have h1 : Real.log 2 * c ≤ Real.log 2 := by nlinarith [hlog2, hc1]
      have h2 : L * c ≤ L - 10 * ε := by
        rw [hcdef, routeTContourLeft]
        nlinarith [hshift]
      nlinarith [hstep, h1, h2]
    · rw [Real.exp_add, Real.exp_sub, hNexp]
      have h2 : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
      rw [h2]
      have : Real.exp (10 * ε) = (Real.exp (-(10 * ε)))⁻¹ := by
        rw [Real.exp_neg, inv_inv]
      rw [this]
      field_simp
      norm_num
  -- the target scale
  set P : ℝ := N * Real.exp (-(2 * ε)) with hPdef
  have hP0 : (0 : ℝ) < P := by rw [hPdef]; positivity
  have hexpsq : (Real.exp (-(3 * ε))) ^ 2 = Real.exp (-(6 * ε)) := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  have hH2 : H ^ 2 = N ^ 2 * Real.exp (-(6 * ε)) := by
    rw [hHdef, mul_pow, hexpsq]
  have hcancel6 : Real.exp (6 * ε) * Real.exp (-(6 * ε)) = 1 := by
    rw [← Real.exp_add]; norm_num
  have hcancel3 : Real.exp (3 * ε) * Real.exp (-(3 * ε)) = 1 := by
    rw [← Real.exp_add]; norm_num
  have hd1L : 1 / (d - 1) = L := by
    rw [hddef]
    field_simp
    ring
  have hCH : C / H ^ 2 * (N + H + 1) ^ 2 ≤ 9 * C * Real.exp (6 * ε) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < H ^ 2), hH2]
    have hRHS : 9 * C * Real.exp (6 * ε) * (N ^ 2 * Real.exp (-(6 * ε))) = 9 * C * N ^ 2 := by
      calc 9 * C * Real.exp (6 * ε) * (N ^ 2 * Real.exp (-(6 * ε)))
          = 9 * C * N ^ 2 * (Real.exp (6 * ε) * Real.exp (-(6 * ε))) := by ring
        _ = 9 * C * N ^ 2 := by rw [hcancel6]; ring
    rw [hRHS]
    have hsq : (N + H + 1) ^ 2 ≤ 9 * N ^ 2 := by
      have h := mul_self_le_mul_self hNH1pos.le hNH1
      nlinarith [h]
    calc C * (N + H + 1) ^ 2 ≤ C * (9 * N ^ 2) := mul_le_mul_of_nonneg_left hsq hC
      _ = 9 * C * N ^ 2 := by ring
  have hC'H : C' / H ^ 1 * (N + H + 1) ^ 1 ≤ 3 * C' * Real.exp (3 * ε) := by
    rw [pow_one, pow_one, div_mul_eq_mul_div, div_le_iff₀ hH0, hHdef]
    have hRHS : 3 * C' * Real.exp (3 * ε) * (N * Real.exp (-(3 * ε))) = 3 * C' * N := by
      calc 3 * C' * Real.exp (3 * ε) * (N * Real.exp (-(3 * ε)))
          = 3 * C' * N * (Real.exp (3 * ε) * Real.exp (-(3 * ε))) := by ring
        _ = 3 * C' * N := by rw [hcancel3]; ring
    rw [hRHS]
    nlinarith [hNH1, hC']
  have hF2' : (1 + L) * Real.exp (6 * ε) ≤ P := by
    have heq : (1 + L) * Real.exp (6 * ε)
        = (1 + L) * Real.exp (8 * ε) * Real.exp (-(2 * ε)) := by
      rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    rw [heq, hPdef]
    exact mul_le_mul_of_nonneg_right hF2 (Real.exp_pos _).le
  have hF3' : Real.exp (4 * ε) ≤ P := by
    have heq : Real.exp (4 * ε) = Real.exp (6 * ε) * Real.exp (-(2 * ε)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [heq, hPdef]
    exact mul_le_mul_of_nonneg_right hF3 (Real.exp_pos _).le
  have hone : (1 : ℝ) ≤ P := by
    have h1 : (1 : ℝ) ≤ Real.exp (4 * ε) := Real.one_le_exp (by positivity)
    linarith [hF3']
  have hpowd0 : (0 : ℝ) ≤ (N + H + 1) ^ d := Real.rpow_nonneg hNH1pos.le d
  have hpowc0 : (0 : ℝ) ≤ (N + H + 1) ^ c := Real.rpow_nonneg hNH1pos.le c
  have hpowNHc0 : (0 : ℝ) ≤ (N + H) ^ c := Real.rpow_nonneg (by linarith) c
  have hCH0 : (0 : ℝ) ≤ C / H ^ 2 * (N + H + 1) ^ 2 := by positivity
  have hC'H0 : (0 : ℝ) ≤ C' / H ^ 1 * (N + H + 1) ^ 1 := by positivity
  -- the truncation edge
  have hT1 : 2 * ((Real.exp (22 / 4) * (1 + 1 / (d - 1)))
        * (C / H ^ 2 * (N + H + 1) ^ 2 * (N + H + 1) ^ d)) / N
      ≤ 162 * Real.exp 7 * C * P := by
    rw [hd1L, div_le_iff₀ hN0]
    have hstep1 : C / H ^ 2 * (N + H + 1) ^ 2 * (N + H + 1) ^ d
        ≤ 9 * C * Real.exp (6 * ε) * (9 * Real.exp 1 * N) :=
      mul_le_mul hCH hpowd hpowd0 (by positivity)
    have hpref : (0 : ℝ) ≤ 2 * (Real.exp (22 / 4) * (1 + L)) := by
      have : (0 : ℝ) ≤ 1 + L := by linarith
      positivity
    have hmul := mul_le_mul_of_nonneg_left hstep1 hpref
    have hrew : 2 * (Real.exp (22 / 4) * (1 + L))
          * (9 * C * Real.exp (6 * ε) * (9 * Real.exp 1 * N))
        = 162 * (Real.exp (22 / 4) * Real.exp 1) * C * N * ((1 + L) * Real.exp (6 * ε)) := by
      ring
    rw [hrew] at hmul
    have he7 : Real.exp (22 / 4) * Real.exp 1 ≤ Real.exp 7 := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by norm_num)
    have hfac : (0 : ℝ) ≤ 162 * C * N := by positivity
    have hstep2 : 162 * (Real.exp (22 / 4) * Real.exp 1) * C * N * ((1 + L) * Real.exp (6 * ε))
        ≤ 162 * Real.exp 7 * C * P * N := by
      have hpos : (0 : ℝ) ≤ (1 + L) * Real.exp (6 * ε) := by
        have h0 : (0 : ℝ) ≤ 1 + L := by linarith
        positivity
      have hmm : (Real.exp (22 / 4) * Real.exp 1) * ((1 + L) * Real.exp (6 * ε))
          ≤ Real.exp 7 * P := mul_le_mul he7 hF2' hpos (Real.exp_pos 7).le
      have hprod := mul_le_mul_of_nonneg_left hmm hfac
      calc 162 * (Real.exp (22 / 4) * Real.exp 1) * C * N * ((1 + L) * Real.exp (6 * ε))
          = 162 * C * N * ((Real.exp (22 / 4) * Real.exp 1) * ((1 + L) * Real.exp (6 * ε))) := by
            ring
        _ ≤ 162 * C * N * (Real.exp 7 * P) := hprod
        _ = 162 * Real.exp 7 * C * P * N := by ring
    linarith [hmul, hstep2]
  -- the two horizontal edges
  have hT23 : Mc * (C' / H ^ 1 * (N + H + 1) ^ 1 * (N + H + 1) ^ d) / N ^ (0 + 1) * (d - c)
      ≤ 54 * Real.exp 1 * C' * (M + 1) * P := by
    have hNpow : N ^ (0 + 1) = N := by norm_num
    rw [hNpow]
    have hstep1 : C' / H ^ 1 * (N + H + 1) ^ 1 * (N + H + 1) ^ d
        ≤ 3 * C' * Real.exp (3 * ε) * (9 * Real.exp 1 * N) :=
      mul_le_mul hC'H hpowd hpowd0 (by positivity)
    have hstep2 : Mc * (C' / H ^ 1 * (N + H + 1) ^ 1 * (N + H + 1) ^ d)
        ≤ ((M + 1) * Real.exp ε) * (3 * C' * Real.exp (3 * ε) * (9 * Real.exp 1 * N)) :=
      mul_le_mul hMcle hstep1 (by positivity) (by positivity)
    have hdc : d - c ≤ 2 := by linarith
    have hdc0 : (0 : ℝ) ≤ d - c := by linarith
    have hquot : Mc * (C' / H ^ 1 * (N + H + 1) ^ 1 * (N + H + 1) ^ d) / N
        ≤ 27 * Real.exp 1 * C' * (M + 1) * Real.exp (4 * ε) := by
      rw [div_le_iff₀ hN0]
      have heq : ((M + 1) * Real.exp ε) * (3 * C' * Real.exp (3 * ε) * (9 * Real.exp 1 * N))
          = 27 * Real.exp 1 * C' * (M + 1) * (Real.exp ε * Real.exp (3 * ε)) * N := by ring
      have hexp4 : Real.exp ε * Real.exp (3 * ε) = Real.exp (4 * ε) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [heq, hexp4] at hstep2
      linarith [hstep2]
    have hq0 : (0 : ℝ) ≤ Mc * (C' / H ^ 1 * (N + H + 1) ^ 1 * (N + H + 1) ^ d) / N := by
      positivity
    have hfin : Mc * (C' / H ^ 1 * (N + H + 1) ^ 1 * (N + H + 1) ^ d) / N * (d - c)
        ≤ 27 * Real.exp 1 * C' * (M + 1) * Real.exp (4 * ε) * 2 := by
      exact mul_le_mul hquot hdc hdc0 (by positivity)
    have hlast : 27 * Real.exp 1 * C' * (M + 1) * Real.exp (4 * ε) * 2
        ≤ 54 * Real.exp 1 * C' * (M + 1) * P := by
      have hfac : (0 : ℝ) ≤ 54 * Real.exp 1 * C' * (M + 1) := by positivity
      have h := mul_le_mul_of_nonneg_left hF3' hfac
      calc 27 * Real.exp 1 * C' * (M + 1) * Real.exp (4 * ε) * 2
          = 54 * Real.exp 1 * C' * (M + 1) * Real.exp (4 * ε) := by ring
        _ ≤ 54 * Real.exp 1 * C' * (M + 1) * P := h
    linarith [hfin, hlast]
  -- the left edge
  have hT4 : Mc * (2 * ((N + H) ^ c / c)
        + 2 * (C / H ^ 2 * (N + H + 1) ^ 2 * (N + H + 1) ^ c))
      ≤ (M + 1) * (8 + 54 * C) * P := by
    have hdivc : (N + H) ^ c / c ≤ 2 * (N + H) ^ c := by
      rw [div_le_iff₀ hc0]
      nlinarith [hpowNHc0, hc12]
    have hA : 2 * ((N + H) ^ c / c) ≤ 4 * (2 * (N * Real.exp (-(10 * ε)))) := by
      nlinarith [hdivc, hpowNHc]
    have hB : 2 * (C / H ^ 2 * (N + H + 1) ^ 2 * (N + H + 1) ^ c)
        ≤ 54 * C * (Real.exp (6 * ε) * (N * Real.exp (-(10 * ε)))) := by
      have hmm := mul_le_mul hCH hpowc hpowc0 (by positivity)
      calc 2 * (C / H ^ 2 * (N + H + 1) ^ 2 * (N + H + 1) ^ c)
          ≤ 2 * (9 * C * Real.exp (6 * ε) * (3 * (N * Real.exp (-(10 * ε))))) := by
            linarith [hmm]
        _ = 54 * C * (Real.exp (6 * ε) * (N * Real.exp (-(10 * ε)))) := by ring
    have hsum : 2 * ((N + H) ^ c / c)
          + 2 * (C / H ^ 2 * (N + H + 1) ^ 2 * (N + H + 1) ^ c)
        ≤ 8 * (N * Real.exp (-(10 * ε)))
          + 54 * C * (Real.exp (6 * ε) * (N * Real.exp (-(10 * ε)))) := by
      linarith [hA, hB]
    have hsum0 : (0 : ℝ) ≤ 2 * ((N + H) ^ c / c)
          + 2 * (C / H ^ 2 * (N + H + 1) ^ 2 * (N + H + 1) ^ c) := by positivity
    have hstep : Mc * (2 * ((N + H) ^ c / c)
          + 2 * (C / H ^ 2 * (N + H + 1) ^ 2 * (N + H + 1) ^ c))
        ≤ ((M + 1) * Real.exp ε)
            * (8 * (N * Real.exp (-(10 * ε)))
              + 54 * C * (Real.exp (6 * ε) * (N * Real.exp (-(10 * ε))))) :=
      mul_le_mul hMcle hsum hsum0 (by positivity)
    have he9 : Real.exp ε * Real.exp (-(10 * ε)) ≤ Real.exp (-(2 * ε)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    have he3 : Real.exp ε * (Real.exp (6 * ε) * Real.exp (-(10 * ε))) ≤ Real.exp (-(2 * ε)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    have hrew : ((M + 1) * Real.exp ε)
          * (8 * (N * Real.exp (-(10 * ε)))
            + 54 * C * (Real.exp (6 * ε) * (N * Real.exp (-(10 * ε)))))
        = (M + 1) * (8 * N * (Real.exp ε * Real.exp (-(10 * ε)))
            + 54 * C * N * (Real.exp ε * (Real.exp (6 * ε) * Real.exp (-(10 * ε))))) := by
      ring
    rw [hrew] at hstep
    have hbound : (M + 1) * (8 * N * (Real.exp ε * Real.exp (-(10 * ε)))
          + 54 * C * N * (Real.exp ε * (Real.exp (6 * ε) * Real.exp (-(10 * ε)))))
        ≤ (M + 1) * (8 + 54 * C) * P := by
      have hM1 : (0 : ℝ) ≤ M + 1 := by linarith
      have h1 : 8 * N * (Real.exp ε * Real.exp (-(10 * ε)))
          ≤ 8 * N * Real.exp (-(2 * ε)) :=
        mul_le_mul_of_nonneg_left he9 (by positivity)
      have h2 : 54 * C * N * (Real.exp ε * (Real.exp (6 * ε) * Real.exp (-(10 * ε))))
          ≤ 54 * C * N * Real.exp (-(2 * ε)) :=
        mul_le_mul_of_nonneg_left he3 (by positivity)
      have hin : 8 * N * (Real.exp ε * Real.exp (-(10 * ε)))
            + 54 * C * N * (Real.exp ε * (Real.exp (6 * ε) * Real.exp (-(10 * ε))))
          ≤ (8 + 54 * C) * (N * Real.exp (-(2 * ε))) := by linarith
      calc (M + 1) * (8 * N * (Real.exp ε * Real.exp (-(10 * ε)))
              + 54 * C * N * (Real.exp ε * (Real.exp (6 * ε) * Real.exp (-(10 * ε)))))
          ≤ (M + 1) * ((8 + 54 * C) * (N * Real.exp (-(2 * ε)))) :=
            mul_le_mul_of_nonneg_left hin hM1
        _ = (M + 1) * (8 + 54 * C) * P := by rw [hPdef]; ring
    linarith [hstep, hbound]
  -- the smoothing window
  have hHplus : H + 1 ≤ 2 * P := by
    have h1 : H ≤ P := by
      have hmono : Real.exp (-(3 * ε)) ≤ Real.exp (-(2 * ε)) := Real.exp_le_exp.2 (by linarith)
      have hmm := mul_le_mul_of_nonneg_left hmono hN0.le
      rw [hHdef, hPdef]
      exact hmm
    linarith [hone, h1]
  -- assembly
  have hexpmono : Real.exp (-(2 * ε)) ≤ Real.exp (-ε) := Real.exp_le_exp.2 (by linarith)
  have hPle : P ≤ N * Real.exp (-ε) := by
    have hmm := mul_le_mul_of_nonneg_left hexpmono hN0.le
    rw [hPdef]
    exact hmm
  have hKsum : routeTMoebiusAllHeightsSmoothBound A C C' M δ N H τ N d / (2 * Real.pi) + (H + 1)
      ≤ ((162 * Real.exp 7 * C + 108 * Real.exp 1 * C' * (M + 1)
            + (M + 1) * (8 + 54 * C)) / (2 * Real.pi) + 2) * P := by
    have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
    have hnum : routeTMoebiusAllHeightsSmoothBound A C C' M δ N H τ N d
        ≤ (162 * Real.exp 7 * C + 108 * Real.exp 1 * C' * (M + 1)
            + (M + 1) * (8 + 54 * C)) * P := by
      unfold routeTMoebiusAllHeightsSmoothBound
      rw [← hSdef, ← hcdef, ← hMcdef]
      linarith [hT1, hT23, hT4]
    have hdivle : routeTMoebiusAllHeightsSmoothBound A C C' M δ N H τ N d / (2 * Real.pi)
        ≤ (162 * Real.exp 7 * C + 108 * Real.exp 1 * C' * (M + 1)
            + (M + 1) * (8 + 54 * C)) / (2 * Real.pi) * P := by
      rw [div_le_iff₀ hpi]
      have heq : (162 * Real.exp 7 * C + 108 * Real.exp 1 * C' * (M + 1)
            + (M + 1) * (8 + 54 * C)) / (2 * Real.pi) * P * (2 * Real.pi)
          = (162 * Real.exp 7 * C + 108 * Real.exp 1 * C' * (M + 1)
            + (M + 1) * (8 + 54 * C)) * P := by
        field_simp
      rw [heq]
      exact hnum
    linarith [hdivle, hHplus]
  refine le_trans hKsum ?_
  have hKpos : (0 : ℝ) ≤ (162 * Real.exp 7 * C + 108 * Real.exp 1 * C' * (M + 1)
      + (M + 1) * (8 + 54 * C)) / (2 * Real.pi) + 2 := by positivity
  calc ((162 * Real.exp 7 * C + 108 * Real.exp 1 * C' * (M + 1)
          + (M + 1) * (8 + 54 * C)) / (2 * Real.pi) + 2) * P
      ≤ ((162 * Real.exp 7 * C + 108 * Real.exp 1 * C' * (M + 1)
          + (M + 1) * (8 + 54 * C)) / (2 * Real.pi) + 2) * (N * Real.exp (-ε)) :=
        mul_le_mul_of_nonneg_left hPle hKpos
    _ = ((162 * Real.exp 7 * C + 108 * Real.exp 1 * C' * (M + 1)
          + (M + 1) * (8 + 54 * C)) / (2 * Real.pi) + 2) * N * Real.exp (-ε) := by ring


set_option maxHeartbeats 2000000 in
/-- **The twisted Mertens sum, uniformly over every frequency below the cutoff.**  Unconditional,
with a saving that beats every power of the logarithm. -/
theorem exists_norm_sum_moebiusTwist_le_rate :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℝ in atTop, ∀ τ : ℝ, |τ| ≤ N →
      ‖∑ n ∈ Finset.range (⌊N⌋₊ + 1), moebiusTwist τ n‖
        ≤ K * N * Real.exp (-((Real.log N) ^ ((1 : ℝ) / 20))) := by
  obtain ⟨A, C, C', M, δ, hC, hC', hM, hδ, hmain⟩ :=
    exists_norm_sum_moebiusTwist_le_routeTSharp_allHeights
  refine ⟨(162 * Real.exp 7 * C + 108 * Real.exp 1 * C' * (M + 1)
      + (M + 1) * (8 + 54 * C)) / (2 * Real.pi) + 2, by positivity, ?_⟩
  filter_upwards [eventually_rate_growth, eventually_routeT_contour_rate_data A δ hδ]
    with N hgrow hdata
  obtain ⟨hN0, hL8, hNbase, hF2, hF3⟩ := hgrow
  intro τ hτ
  set L : ℝ := Real.log N with hLdef
  set ε : ℝ := L ^ ((1 : ℝ) / 20) with hεdef
  have hL0 : (0 : ℝ) < L := by linarith
  have hε0 : (0 : ℝ) < ε := Real.rpow_pos_of_pos hL0 _
  have hexpε : (1 : ℝ) ≤ Real.exp ε := Real.one_le_exp hε0.le
  have hNexp : Real.exp L = N := Real.exp_log hN0
  have hbase := routeTInverseBaseHeight_ge
  have hN1 : (1 : ℝ) ≤ N := by linarith
  set H : ℝ := N * Real.exp (-(3 * ε)) with hHdef
  set d : ℝ := 1 + 1 / L with hddef
  set S : ℝ := |τ| + N with hSdef
  have hH0 : (0 : ℝ) < H := by rw [hHdef]; positivity
  have hHN : H ≤ N := by
    rw [hHdef]
    have : Real.exp (-(3 * ε)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    nlinarith [hN0]
  have hd1 : (1 : ℝ) < d := by rw [hddef]; have : (0:ℝ) < 1 / L := by positivity
                               linarith
  have hd2 : d ≤ 2 := by
    rw [hddef]
    have : 1 / L ≤ 1 := by rw [div_le_one hL0]; linarith
    linarith
  have hSbase : routeTInverseBaseHeight ≤ S := by
    rw [hSdef]; linarith [abs_nonneg τ]
  have hS2N : S ≤ 2 * N := by rw [hSdef]; linarith
  obtain ⟨hshift, hedge, hinv⟩ := hdata S hSbase hS2N
  have hdright : d ≤ routeTContourRight A S := by
    rw [hddef, routeTContourRight]
    linarith [hinv]
  have hkey := hmain N H τ N d hN0 hH0 (by linarith) hd1 hd2
    (by rw [← hSdef]; exact hSbase) (by rw [← hSdef]; exact hdright)
  refine le_trans hkey ?_
  exact routeTMoebiusAllHeightsSmoothBound_le_rate hC hC' hM hδ hN0 hL8 hNbase hF2 hF3
    hshift hedge

end

end RHTower.Sieve
