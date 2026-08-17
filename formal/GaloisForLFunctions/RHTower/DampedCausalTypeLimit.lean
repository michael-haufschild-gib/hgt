import GaloisForLFunctions.RHTower.DampedPacketComparison

/-!
# The exponential type of the damped causal compression

The upper half of the type law is the radiation envelope.  The lower half is read by the scheduled
Gaussian packet: at frequency `-u^q` and centre `cu` inside the window `(0, κu)`, the compressed
propagator dominates the band-centre scalar up to three defects, each of which is beaten by an
explicit exponential.

This module collects the schedule-level estimates: the window defect of the scheduled packet is a
Gaussian in `u`, so it is invisible against every `e^{-σu^q}`.
-/

open MeasureTheory Filter Topology Complex GaloisForLFunctions.HTGeometry

open scoped FourierTransform

namespace RHTower

open RHTower.MellinL2

noncomputable section

/-- **The window defect of the scheduled packet vanishes.**  With the centre at `cu` inside the
window `(0, κu)`, the defect is a Gaussian in `u`. -/
theorem tendsto_windowDefect_sq {c kappa : ℝ} (hc : 0 < c) (hck : c < kappa) (Rs : ℝ → ℝ) :
    Tendsto (fun u : ℝ => ‖gaussPacket (Rs u) (c * u)
        - windowCutoff (measurableSet_Ioo (a := (0 : ℝ)) (b := kappa * u))
          (gaussPacket (Rs u) (c * u))‖ ^ 2) atTop (𝓝 0) := by
  set m : ℝ := min c (kappa - c) with hm
  have hm0 : 0 < m := lt_min hc (by linarith)
  have hmaj : Tendsto (fun u : ℝ => Real.exp (-(Real.pi * (m * u) ^ 2))) atTop (𝓝 0) := by
    have hgrow : Tendsto (fun u : ℝ => -(Real.pi * (m * u) ^ 2)) atTop atBot := by
      have hpos : Tendsto (fun u : ℝ => Real.pi * (m * u) ^ 2) atTop atTop := by
        have hsq : Tendsto (fun u : ℝ => (m * u) ^ 2) atTop atTop := by
          have hlin : Tendsto (fun u : ℝ => m * u) atTop atTop :=
            Filter.Tendsto.const_mul_atTop hm0 tendsto_id
          have hmul := hlin.atTop_mul_atTop₀ hlin
          refine hmul.congr fun u => ?_
          rw [sq]
        exact Filter.Tendsto.const_mul_atTop Real.pi_pos hsq
      exact tendsto_neg_atTop_atBot.comp hpos
    exact Real.tendsto_exp_atBot.comp hgrow
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards with u
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    have hT : (0 : ℝ) < c * u := by positivity
    have hTH : c * u < kappa * u := by nlinarith
    have hbound := gaussPacket_window_defect_le (R := Rs u) (T := c * u) (H := kappa * u) hT hTH
    have hmin : min (c * u) (kappa * u - c * u) = m * u := by
      rw [hm, min_mul_of_nonneg c (kappa - c) hu.le]
      congr 1
      ring
    rwa [hmin] at hbound

/-! ## The schedule -/

/-- **The band error of the schedule vanishes.**  With band radius `≍ u^{q/2}` at frequency scale
`u^q`, the band error is `≍ u^{1-3q/2}`, which vanishes exactly when `q > 2/3`. -/
theorem tendsto_scheduleBeta {a sigma q Cc : ℝ} (hq : 2 / 3 < q) :
    Tendsto (fun u : ℝ => (sigma + u)
        * (a ^ 2 * (2 * Real.pi * (Cc * u ^ (q / 2))) / (u ^ q) ^ 2
          + 3 * a ^ 4 / (u ^ q) ^ 3)) atTop (𝓝 0) := by
  have hq0 : 0 < q := by linarith
  have h1 : Tendsto (fun u : ℝ => (2 * Real.pi * Cc * a ^ 2) * ((sigma + u) / u ^ (3 * q / 2)))
      atTop (𝓝 0) := by
    simpa using (tendsto_add_div_rpow_atTop (sigma := sigma)
      (by linarith : (1 : ℝ) < 3 * q / 2)).const_mul (2 * Real.pi * Cc * a ^ 2)
  have h2 : Tendsto (fun u : ℝ => (3 * a ^ 4) * ((sigma + u) / u ^ (3 * q)))
      atTop (𝓝 0) := by
    simpa using (tendsto_add_div_rpow_atTop (sigma := sigma)
      (by linarith : (1 : ℝ) < 3 * q)).const_mul (3 * a ^ 4)
  have hsum := h1.add h2
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  have hr : (0 : ℝ) < u ^ q := Real.rpow_pos_of_pos hu _
  have hsq : (u ^ q) ^ 2 = u ^ (2 * q) := by
    rw [← Real.rpow_natCast (u ^ q) 2, ← Real.rpow_mul hu.le]
    congr 1
    ring
  have hcu : (u ^ q) ^ 3 = u ^ (3 * q) := by
    rw [← Real.rpow_natCast (u ^ q) 3, ← Real.rpow_mul hu.le]
    congr 1
    ring
  have h2p : (0 : ℝ) < u ^ (2 * q) := Real.rpow_pos_of_pos hu _
  have h3p : (0 : ℝ) < u ^ (3 * q) := Real.rpow_pos_of_pos hu _
  have hhalf : (0 : ℝ) < u ^ (3 * q / 2) := Real.rpow_pos_of_pos hu _
  have hfac : u ^ (2 * q) = u ^ (q / 2) * u ^ (3 * q / 2) := by
    rw [← Real.rpow_add hu]
    congr 1
    ring
  have hq2 : (0 : ℝ) < u ^ (q / 2) := Real.rpow_pos_of_pos hu _
  rw [hsq, hcu, hfac]
  field_simp

/-- The band radius stays inside the half band of the frequency scale. -/
theorem eventually_bandRadius_le {q Cc : ℝ} (hq0 : 0 < q) :
    ∀ᶠ u : ℝ in atTop, 2 * Real.pi * (Cc * u ^ (q / 2)) ≤ u ^ q / 2 := by
  have hgrow : Tendsto (fun u : ℝ => u ^ (q / 2)) atTop atTop :=
    tendsto_rpow_atTop (by linarith)
  filter_upwards [hgrow.eventually_ge_atTop (4 * Real.pi * |Cc|),
    eventually_gt_atTop (0 : ℝ)] with u hge hu
  have hhalf : (0 : ℝ) < u ^ (q / 2) := Real.rpow_pos_of_pos hu _
  have hsq : u ^ q = u ^ (q / 2) * u ^ (q / 2) := by
    rw [← Real.rpow_add hu]
    congr 1
    ring
  have hC : Cc ≤ |Cc| := le_abs_self Cc
  rw [hsq]
  have hkey : 4 * Real.pi * |Cc| * (u ^ (q / 2) / 2) ≤ u ^ (q / 2) * (u ^ (q / 2) / 2) :=
    mul_le_mul_of_nonneg_right hge (by positivity)
  have hCle : 2 * Real.pi * u ^ (q / 2) * Cc ≤ 2 * Real.pi * u ^ (q / 2) * |Cc| :=
    mul_le_mul_of_nonneg_left hC (by positivity)
  nlinarith [hkey, hCle]


/-- A nonnegative function whose square vanishes vanishes. -/
theorem tendsto_of_tendsto_sq {f : ℝ → ℝ} (hnn : ∀ u, 0 ≤ f u)
    (h : Tendsto (fun u => f u ^ 2) atTop (𝓝 0)) : Tendsto f atTop (𝓝 0) := by
  have hcomp := (Real.continuous_sqrt.tendsto 0).comp h
  rw [Real.sqrt_zero] at hcomp
  refine hcomp.congr fun u => ?_
  rw [Function.comp_apply, Real.sqrt_sq (hnn u)]

/-- **An explicit lower bound for the model scalar.** -/
theorem le_norm_dampedModelConst {a lambda sigma q : ℝ} (hsigma : 0 ≤ sigma) {u : ℝ}
    (hu : 0 < u) :
    Real.exp (lambda * u - u * (lambda - (massGaugeDispersion a lambda (-(u ^ q))).im)
        - sigma * (u ^ q + a ^ 2 / (2 * u ^ q) + a ^ 4 / (4 * (u ^ q) ^ 3))
        + Real.pi * sigma ^ 2)
      ≤ ‖dampedModelConst a lambda sigma u (u ^ q)‖ := by
  have hlog := le_log_norm_dampedSymbol_center (a := a) (lambda := lambda) (sigma := sigma)
    (q := q) hsigma hu
  have hnorm : ‖massGaugeDampedSymbol a lambda sigma u (-(u ^ q))‖
      = Real.exp (-(sigma * (massGaugeDispersion a lambda (-(u ^ q))).re)
        + u * (massGaugeDispersion a lambda (-(u ^ q))).im) := norm_massGaugeDampedSymbol _ _ _ _ _
  have hpos : 0 < ‖massGaugeDampedSymbol a lambda sigma u (-(u ^ q))‖ := by
    rw [hnorm]
    exact Real.exp_pos _
  have hexp : Real.exp (lambda * u - u * (lambda - (massGaugeDispersion a lambda (-(u ^ q))).im)
      - sigma * (u ^ q + a ^ 2 / (2 * u ^ q) + a ^ 4 / (4 * (u ^ q) ^ 3)))
      ≤ ‖massGaugeDampedSymbol a lambda sigma u (-(u ^ q))‖ := by
    rw [hnorm] at hlog ⊢
    rw [Real.log_exp] at hlog
    exact Real.exp_le_exp.2 hlog
  rw [norm_dampedModelConst, Real.exp_add]
  exact mul_le_mul_of_nonneg_right hexp (Real.exp_nonneg _)


/-- **The Gaussian window exponent dominates.**  A quadratic Gaussian exponent beats every
sub-quadratic power together with any vanishing term, so the window defect is invisible on the
damped exponential clock. -/
theorem tendsto_windowExponent_atBot {m sigma a q Kc : ℝ} (hm : 0 < m)
    (hq0 : 0 < q) (hq2 : q < 2) {A : ℝ → ℝ} (hA : Tendsto A atTop (𝓝 0)) :
    Tendsto (fun u : ℝ => -(Real.pi * (m * u) ^ 2)
        + 2 * A u
        + 2 * sigma * (u ^ q + a ^ 2 / (2 * u ^ q) + a ^ 4 / (4 * (u ^ q) ^ 3))
        + Kc) atTop atBot := by
  have hinvsq : Tendsto (fun u : ℝ => 1 / u ^ 2) atTop (𝓝 0) := by
    have h := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    rw [show (-2 : ℝ) = -(2 : ℝ) from rfl, Real.rpow_neg hu.le, one_div,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hAsq : Tendsto (fun u : ℝ => 2 * A u / u ^ 2) atTop (𝓝 0) := by
    have hmul := (hA.const_mul (2 : ℝ)).mul hinvsq
    simp only [mul_zero] at hmul
    refine hmul.congr fun u => ?_
    rw [mul_one_div]
  have hGsq : Tendsto (fun u : ℝ =>
      2 * sigma * (u ^ q + a ^ 2 / (2 * u ^ q) + a ^ 4 / (4 * (u ^ q) ^ 3)) / u ^ 2)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => (2 * sigma) * u ^ (-(2 - q))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < 2 - q)).const_mul (2 * sigma)
    have h2 : Tendsto (fun u : ℝ => (sigma * a ^ 2) * u ^ (-(q + 2))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < q + 2)).const_mul (sigma * a ^ 2)
    have h3 : Tendsto (fun u : ℝ => (sigma * a ^ 4 / 2) * u ^ (-(3 * q + 2))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < 3 * q + 2)).const_mul
        (sigma * a ^ 4 / 2)
    have hsum := (h1.add h2).add h3
    rw [add_zero, add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    have hr : (0 : ℝ) < u ^ q := Real.rpow_pos_of_pos hu _
    have hcu : (u ^ q) ^ 3 = u ^ (3 * q) := by
      rw [← Real.rpow_natCast (u ^ q) 3, ← Real.rpow_mul hu.le]
      congr 1
      ring
    have h3p : (0 : ℝ) < u ^ (3 * q) := Real.rpow_pos_of_pos hu _
    have e1 : u ^ (-(2 - q)) = u ^ q / u ^ 2 := by
      rw [show -(2 - q) = q - 2 by ring, Real.rpow_sub hu,
        show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have e2 : u ^ (-(q + 2)) = 1 / (u ^ q * u ^ 2) := by
      rw [Real.rpow_neg hu.le, Real.rpow_add hu,
        show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      field_simp
    have e3 : u ^ (-(3 * q + 2)) = 1 / (u ^ (3 * q) * u ^ 2) := by
      rw [Real.rpow_neg hu.le, Real.rpow_add hu,
        show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      field_simp
    rw [hcu, e1, e2, e3]
    field_simp
    ring
  have hKsq : Tendsto (fun u : ℝ => Kc / u ^ 2) atTop (𝓝 0) := by
    have hmul := hinvsq.const_mul Kc
    rw [mul_zero] at hmul
    refine hmul.congr fun u => ?_
    rw [mul_one_div]
  have hall := (hAsq.add hGsq).add hKsq
  rw [add_zero, add_zero] at hall
  have hev : ∀ᶠ u : ℝ in atTop,
      2 * A u + 2 * sigma * (u ^ q + a ^ 2 / (2 * u ^ q) + a ^ 4 / (4 * (u ^ q) ^ 3)) + Kc
        ≤ Real.pi * m ^ 2 * u ^ 2 / 2 := by
    have hlt : Tendsto (fun u : ℝ =>
        (2 * A u / u ^ 2 + 2 * sigma * (u ^ q + a ^ 2 / (2 * u ^ q)
          + a ^ 4 / (4 * (u ^ q) ^ 3)) / u ^ 2 + Kc / u ^ 2)) atTop (𝓝 0) := hall
    have hbound := hlt.eventually (eventually_lt_nhds
      (by positivity : (0 : ℝ) < Real.pi * m ^ 2 / 2))
    filter_upwards [hbound, eventually_gt_atTop (0 : ℝ)] with u hb hu
    have husq : (0 : ℝ) < u ^ 2 := by positivity
    have hcomb : 2 * A u / u ^ 2 + 2 * sigma * (u ^ q + a ^ 2 / (2 * u ^ q)
        + a ^ 4 / (4 * (u ^ q) ^ 3)) / u ^ 2 + Kc / u ^ 2
        = (2 * A u + 2 * sigma * (u ^ q + a ^ 2 / (2 * u ^ q)
          + a ^ 4 / (4 * (u ^ q) ^ 3)) + Kc) / u ^ 2 := by
      field_simp
    rw [hcomb, div_lt_iff₀ husq] at hb
    nlinarith [hb]
  have hmaj : Tendsto (fun u : ℝ => -(Real.pi * m ^ 2 * u ^ 2 / 2)) atTop atBot := by
    have hpos : Tendsto (fun u : ℝ => Real.pi * m ^ 2 * u ^ 2 / 2) atTop atTop := by
      have hsq : Tendsto (fun u : ℝ => u ^ 2) atTop atTop := by
        have := (tendsto_id (α := ℝ)).atTop_mul_atTop₀ (tendsto_id (α := ℝ))
        refine this.congr fun u => ?_
        rw [sq]
        rfl
      exact (Filter.Tendsto.const_mul_atTop (by positivity) hsq).atTop_div_const (by norm_num)
    exact tendsto_neg_atTop_atBot.comp hpos
  refine tendsto_atBot_mono' _ ?_ hmaj
  filter_upwards [hev] with u hu
  nlinarith [hu]


/-- **The band exponent dominates.**  With band radius `C u^{q/2}` the off-band gain `πC²u^q` beats
the damping cost `2σu^q` exactly when `2σ < πC²`. -/
theorem tendsto_bandExponent_atBot {sigma a q Cc Kc : ℝ} (hq0 : 0 < q)
    (hCc : 2 * sigma < Real.pi * Cc ^ 2) {A : ℝ → ℝ} (hA : Tendsto A atTop (𝓝 0)) :
    Tendsto (fun u : ℝ => -(Real.pi * (Cc * u ^ (q / 2)) ^ 2)
        + 2 * A u
        + 2 * sigma * (u ^ q + a ^ 2 / (2 * u ^ q) + a ^ 4 / (4 * (u ^ q) ^ 3))
        + Kc) atTop atBot := by
  have htail : Tendsto (fun u : ℝ =>
      2 * A u + 2 * sigma * (a ^ 2 / (2 * u ^ q) + a ^ 4 / (4 * (u ^ q) ^ 3)) + Kc)
      atTop (𝓝 (2 * 0 + 2 * sigma * (0 + 0) + Kc)) := by
    have h1 : Tendsto (fun u : ℝ => a ^ 2 / (2 * u ^ q)) atTop (𝓝 0) := by
      have hbase : Tendsto (fun u : ℝ => (a ^ 2 / 2) * u ^ (-q)) atTop (𝓝 0) := by
        simpa using (tendsto_rpow_neg_atTop hq0).const_mul (a ^ 2 / 2)
      refine hbase.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
      rw [Real.rpow_neg hu.le]
      field_simp
    have h2 : Tendsto (fun u : ℝ => a ^ 4 / (4 * (u ^ q) ^ 3)) atTop (𝓝 0) := by
      have hbase : Tendsto (fun u : ℝ => (a ^ 4 / 4) * u ^ (-(3 * q))) atTop (𝓝 0) := by
        simpa using (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < 3 * q)).const_mul (a ^ 4 / 4)
      refine hbase.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
      have hcu : (u ^ q) ^ 3 = u ^ (3 * q) := by
        rw [← Real.rpow_natCast (u ^ q) 3, ← Real.rpow_mul hu.le]
        congr 1
        ring
      rw [hcu, Real.rpow_neg hu.le]
      field_simp
    exact ((hA.const_mul 2).add ((h1.add h2).const_mul (2 * sigma))).add_const Kc
  rw [mul_zero, add_zero, mul_zero, zero_add] at htail
  have hmain : Tendsto (fun u : ℝ => (2 * sigma - Real.pi * Cc ^ 2) * u ^ q) atTop atBot := by
    have hpow : Tendsto (fun u : ℝ => u ^ q) atTop atTop := tendsto_rpow_atTop hq0
    have hneg : Tendsto (fun u : ℝ => (Real.pi * Cc ^ 2 - 2 * sigma) * u ^ q) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by linarith) hpow
    have := tendsto_neg_atTop_atBot.comp hneg
    refine this.congr fun u => ?_
    rw [Function.comp_apply]
    ring
  have hsum := hmain.atBot_add htail
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  have hsq : (u ^ (q / 2)) ^ 2 = u ^ q := by
    rw [← Real.rpow_natCast (u ^ (q / 2)) 2, ← Real.rpow_mul hu.le]
    congr 1
    ring
  rw [mul_pow, hsq]
  ring


/-! ## The three vanishing defects of the schedule -/

/-- The output window defect of the schedule vanishes. -/
theorem tendsto_outputDefect {sigma c kappa q : ℝ} (hc1 : 1 < c) (hck : c < kappa) :
    Tendsto (fun u : ℝ => ‖gaussPacket (u ^ q / (2 * Real.pi) - sigma) ((c - 1) * u)
        - windowCutoff (measurableSet_Ioo (a := (0 : ℝ)) (b := kappa * u))
          (gaussPacket (u ^ q / (2 * Real.pi) - sigma) ((c - 1) * u))‖) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_sq (fun u => norm_nonneg _) ?_
  exact tendsto_windowDefect_sq (by linarith : (0 : ℝ) < c - 1) (by linarith : c - 1 < kappa)
    (fun u => u ^ q / (2 * Real.pi) - sigma)

/-- The input window defect, amplified by the full radiation envelope, still vanishes against the
model scalar. -/
theorem tendsto_inputDefect_ratio {a lambda sigma c kappa q : ℝ} (hlambda : 0 ≤ lambda)
    (hsigma : 0 ≤ sigma) (hc0 : 0 < c) (hck : c < kappa) (hq : 1 / 2 < q) (hq2 : q < 2) :
    Tendsto (fun u : ℝ => Real.exp (lambda * u)
        * ‖gaussPacket (u ^ q / (2 * Real.pi)) (c * u)
          - windowCutoff (measurableSet_Ioo (a := (0 : ℝ)) (b := kappa * u))
            (gaussPacket (u ^ q / (2 * Real.pi)) (c * u))‖
        / ‖dampedModelConst a lambda sigma u (u ^ q)‖) atTop (𝓝 0) := by
  have hq0 : 0 < q := by linarith
  have hexp2 : ∀ X : ℝ, Real.exp (2 * X) = Real.exp X ^ 2 := by
    intro X
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  set m : ℝ := min c (kappa - c) with hm
  have hm0 : 0 < m := lt_min hc0 (by linarith)
  set A : ℝ → ℝ := fun u => u * (lambda - (massGaugeDispersion a lambda (-(u ^ q))).im) with hA
  have hAlim : Tendsto A atTop (𝓝 0) := by
    have := (tendsto_mul_im_sub_lambda (a := a) (lambda := lambda) (q := q)
      hlambda hq).neg
    rw [neg_zero] at this
    refine this.congr fun u => ?_
    rw [hA]
    ring
  have hexpbot := tendsto_windowExponent_atBot (m := m) (sigma := sigma) (a := a) (q := q)
    (Kc := -(2 * Real.pi * sigma ^ 2)) hm0 hq0 hq2 hAlim
  have hmaj : Tendsto (fun u : ℝ => Real.exp (-(Real.pi * (m * u) ^ 2)
      + 2 * A u + 2 * sigma * (u ^ q + a ^ 2 / (2 * u ^ q) + a ^ 4 / (4 * (u ^ q) ^ 3))
      + -(2 * Real.pi * sigma ^ 2))) atTop (𝓝 0) := Real.tendsto_exp_atBot.comp hexpbot
  refine tendsto_of_tendsto_sq (fun u => by positivity) ?_
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards with u
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    have hT : (0 : ℝ) < c * u := by positivity
    have hTH : c * u < kappa * u := by nlinarith
    have hdef := gaussPacket_window_defect_le (R := u ^ q / (2 * Real.pi)) (T := c * u)
      (H := kappa * u) hT hTH
    have hmin : min (c * u) (kappa * u - c * u) = m * u := by
      rw [hm, min_mul_of_nonneg c (kappa - c) hu.le]
      congr 1
      ring
    rw [hmin] at hdef
    have hK := le_norm_dampedModelConst (a := a) (lambda := lambda) (sigma := sigma) (q := q)
      hsigma hu
    have hKpos : 0 < ‖dampedModelConst a lambda sigma u (u ^ q)‖ :=
      lt_of_lt_of_le (Real.exp_pos _) hK
    set delta : ℝ := ‖gaussPacket (u ^ q / (2 * Real.pi)) (c * u)
      - windowCutoff (measurableSet_Ioo (a := (0 : ℝ)) (b := kappa * u))
        (gaussPacket (u ^ q / (2 * Real.pi)) (c * u))‖ with hdelta
    have hexpsq : Real.exp (lambda * u) ^ 2 = Real.exp (2 * (lambda * u)) :=
      (hexp2 (lambda * u)).symm
    have hnum : (Real.exp (lambda * u) * delta) ^ 2
        ≤ Real.exp (2 * (lambda * u)) * Real.exp (-(Real.pi * (m * u) ^ 2)) := by
      rw [mul_pow, hexpsq]
      exact mul_le_mul_of_nonneg_left hdef (by positivity)
    have hden : Real.exp (2 * (lambda * u - A u
        - sigma * (u ^ q + a ^ 2 / (2 * u ^ q) + a ^ 4 / (4 * (u ^ q) ^ 3)) + Real.pi * sigma ^ 2))
        ≤ ‖dampedModelConst a lambda sigma u (u ^ q)‖ ^ 2 := by
      rw [hexp2]
      exact pow_le_pow_left₀ (Real.exp_nonneg _) hK 2
    have hratio : (Real.exp (lambda * u) * delta
        / ‖dampedModelConst a lambda sigma u (u ^ q)‖) ^ 2
        ≤ Real.exp (2 * (lambda * u)) * Real.exp (-(Real.pi * (m * u) ^ 2))
          / Real.exp (2 * (lambda * u - A u
            - sigma * (u ^ q + a ^ 2 / (2 * u ^ q) + a ^ 4 / (4 * (u ^ q) ^ 3))
            + Real.pi * sigma ^ 2)) := by
      rw [div_pow]
      gcongr
    refine le_trans hratio (le_of_eq ?_)
    rw [← Real.exp_add, ← Real.exp_sub]
    congr 1
    rw [hA]
    ring


/-- **The comparison defect vanishes against the model scalar.** -/
theorem tendsto_packetDefect_ratio {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda)
    {sigma : ℝ} (hsigma : 0 < sigma) {q Cc : ℝ} (hq : 2 / 3 < q) (hq1 : q < 1)
    (hCc : 2 * sigma < Real.pi * Cc ^ 2) (hCc0 : 0 < Cc) (T : ℝ → ℝ) :
    Tendsto (fun u : ℝ => ‖packetDefect ha hlambda hsigma.le u (u ^ q) (T u)‖
        / ‖dampedModelConst a lambda sigma u (u ^ q)‖) atTop (𝓝 0) := by
  have hq0 : 0 < q := by linarith
  have hexp2 : ∀ X : ℝ, Real.exp (2 * X) = Real.exp X ^ 2 := by
    intro X
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  set A : ℝ → ℝ := fun u => u * (lambda - (massGaugeDispersion a lambda (-(u ^ q))).im) with hA
  have hAlim : Tendsto A atTop (𝓝 0) := by
    have hneg := (tendsto_mul_im_sub_lambda (a := a) (lambda := lambda) (q := q)
      hlambda.le (by linarith)).neg
    rw [neg_zero] at hneg
    refine hneg.congr fun u => ?_
    rw [hA]
    ring
  set beta : ℝ → ℝ := fun u => 2 * ((sigma + u)
    * (a ^ 2 * (2 * Real.pi * (Cc * u ^ (q / 2))) / (u ^ q) ^ 2 + 3 * a ^ 4 / (u ^ q) ^ 3))
    with hbeta
  have hbetalim : Tendsto beta atTop (𝓝 0) := by
    have := (tendsto_scheduleBeta (a := a) (sigma := sigma) (q := q) (Cc := Cc) hq).const_mul 2
    rw [mul_zero] at this
    exact this
  set rho : ℝ → ℝ := fun u => Cc * u ^ (q / 2) with hrho
  have hrholim : Tendsto rho atTop atTop :=
    Filter.Tendsto.const_mul_atTop hCc0 (tendsto_rpow_atTop (by linarith))
  -- the three vanishing pieces
  have hterm1 : Tendsto (fun u : ℝ => beta u ^ 2 * Real.sqrt 2⁻¹) atTop (𝓝 0) := by
    have := (hbetalim.pow 2).mul_const (Real.sqrt 2⁻¹)
    simpa using this
  have hterm3 : Tendsto (fun u : ℝ => 2 * Real.exp (-(Real.pi * (rho u - sigma) ^ 2)))
      atTop (𝓝 0) := by
    have hbot : Tendsto (fun u : ℝ => -(Real.pi * (rho u - sigma) ^ 2)) atTop atBot := by
      have hsq : Tendsto (fun u : ℝ => Real.pi * (rho u - sigma) ^ 2) atTop atTop := by
        have hlin : Tendsto (fun u : ℝ => rho u - sigma) atTop atTop := by
          have hadd := Filter.tendsto_atTop_add_const_right atTop (-sigma) hrholim
          refine hadd.congr fun u => ?_
          ring
        have hmul := hlin.atTop_mul_atTop₀ hlin
        have hsq2 : Tendsto (fun u : ℝ => (rho u - sigma) ^ 2) atTop atTop := by
          refine hmul.congr fun u => ?_
          rw [sq]
        exact Filter.Tendsto.const_mul_atTop Real.pi_pos hsq2
      exact tendsto_neg_atTop_atBot.comp hsq
    have := (Real.tendsto_exp_atBot.comp hbot).const_mul 2
    rw [mul_zero] at this
    exact this
  have hterm2 : Tendsto (fun u : ℝ => 2 * Real.exp (-(Real.pi * (rho u) ^ 2)
      + 2 * A u + 2 * sigma * (u ^ q + a ^ 2 / (2 * u ^ q) + a ^ 4 / (4 * (u ^ q) ^ 3))
      + -(2 * Real.pi * sigma ^ 2))) atTop (𝓝 0) := by
    have hbot := tendsto_bandExponent_atBot (sigma := sigma) (a := a) (q := q) (Cc := Cc)
      (Kc := -(2 * Real.pi * sigma ^ 2)) hq0 hCc hAlim
    have := (Real.tendsto_exp_atBot.comp hbot).const_mul 2
    rw [mul_zero] at this
    exact this
  have hsum := (hterm1.add hterm2).add hterm3
  rw [add_zero, add_zero] at hsum
  refine tendsto_of_tendsto_sq (fun u => by positivity) ?_
  refine squeeze_zero' ?_ ?_ hsum
  · filter_upwards with u
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℝ),
      eventually_bandRadius_le (q := q) (Cc := Cc) hq0,
      hbetalim.eventually_le_const (by norm_num : (0 : ℝ) < 2),
      hrholim.eventually_ge_atTop sigma] with u hu hband2 hbeta1 hrhosig
    have hr : (0 : ℝ) < u ^ q := Real.rpow_pos_of_pos hu _
    have hKle := le_norm_dampedModelConst (a := a) (lambda := lambda) (sigma := sigma) (q := q)
      hsigma.le hu
    have hKpos : 0 < ‖dampedModelConst a lambda sigma u (u ^ q)‖ :=
      lt_of_lt_of_le (Real.exp_pos _) hKle
    have hbcomp := band_comparison_of_bounds (a := a) (lambda := lambda) (sigma := sigma)
      (u := u) (r := u ^ q) (rho := rho u) hsigma.le hu.le hr hband2 (by
        have hb2 : beta u ≤ 2 := hbeta1
        rw [hbeta] at hb2
        simp only [hrho] at hb2 ⊢
        linarith [hb2])
    have hdef := norm_packetDefect_sq_le ha hlambda hsigma.le (u := u) (r := u ^ q) (T := T u)
      (rho := rho u) (beta := beta u) hrhosig (ne_of_gt hr) (by
        intro w hw
        have := hbcomp w hw
        rw [hbeta]
        exact this)
    have hNK : ‖dampedModelConst a lambda sigma u (u ^ q)‖ * Real.exp (-(Real.pi * sigma ^ 2))
        = ‖massGaugeDampedSymbol a lambda sigma u (-(u ^ q))‖ := by
      rw [norm_dampedModelConst, mul_assoc, ← Real.exp_add]
      simp
    set K : ℝ := ‖dampedModelConst a lambda sigma u (u ^ q)‖ with hK
    set N : ℝ := ‖massGaugeDampedSymbol a lambda sigma u (-(u ^ q))‖ with hN
    have hKsq : (0 : ℝ) < K ^ 2 := by positivity
    rw [div_pow, div_le_iff₀ hKsq]
    refine le_trans hdef ?_
    have hexpneg2 : Real.exp (-(Real.pi * sigma ^ 2)) ^ 2
        = Real.exp (-(2 * Real.pi * sigma ^ 2)) := by
      rw [← hexp2]
      congr 1
      ring
    have hcancel : Real.exp (-(2 * Real.pi * sigma ^ 2))
        * Real.exp (2 * Real.pi * sigma ^ 2) = 1 := by
      rw [← Real.exp_add]
      norm_num
    have e1 : N ^ 2 * beta u ^ 2 * (Real.exp (2 * Real.pi * sigma ^ 2) * Real.sqrt 2⁻¹)
        = K ^ 2 * (beta u ^ 2 * Real.sqrt 2⁻¹) := by
      have hN2 : N ^ 2 = K ^ 2 * Real.exp (-(2 * Real.pi * sigma ^ 2)) := by
        rw [← hNK, mul_pow, hexpneg2]
      rw [hN2]
      linear_combination (K ^ 2 * beta u ^ 2 * Real.sqrt 2⁻¹) * hcancel
    have habsu : |u| = u := abs_of_pos hu
    have e2 : 2 * Real.exp (|u| * lambda) ^ 2 * Real.exp (-(Real.pi * (rho u) ^ 2))
        ≤ K ^ 2 * (2 * Real.exp (-(Real.pi * (rho u) ^ 2)
          + 2 * A u + 2 * sigma * (u ^ q + a ^ 2 / (2 * u ^ q) + a ^ 4 / (4 * (u ^ q) ^ 3))
          + -(2 * Real.pi * sigma ^ 2))) := by
      have hKlow : Real.exp (2 * (lambda * u - A u
          - sigma * (u ^ q + a ^ 2 / (2 * u ^ q) + a ^ 4 / (4 * (u ^ q) ^ 3))
          + Real.pi * sigma ^ 2)) ≤ K ^ 2 := by
        rw [hexp2]
        exact pow_le_pow_left₀ (Real.exp_nonneg _) hKle 2
      have hval : Real.exp (2 * (lambda * u - A u
          - sigma * (u ^ q + a ^ 2 / (2 * u ^ q) + a ^ 4 / (4 * (u ^ q) ^ 3))
          + Real.pi * sigma ^ 2))
          * (2 * Real.exp (-(Real.pi * (rho u) ^ 2)
            + 2 * A u + 2 * sigma * (u ^ q + a ^ 2 / (2 * u ^ q) + a ^ 4 / (4 * (u ^ q) ^ 3))
            + -(2 * Real.pi * sigma ^ 2)))
          = 2 * Real.exp (|u| * lambda) ^ 2 * Real.exp (-(Real.pi * (rho u) ^ 2)) := by
        have hL : Real.exp (2 * (lambda * u - A u
            - sigma * (u ^ q + a ^ 2 / (2 * u ^ q) + a ^ 4 / (4 * (u ^ q) ^ 3))
            + Real.pi * sigma ^ 2))
            * (2 * Real.exp (-(Real.pi * (rho u) ^ 2)
              + 2 * A u + 2 * sigma * (u ^ q + a ^ 2 / (2 * u ^ q) + a ^ 4 / (4 * (u ^ q) ^ 3))
              + -(2 * Real.pi * sigma ^ 2)))
            = 2 * Real.exp (2 * (lambda * u) + -(Real.pi * (rho u) ^ 2)) := by
          rw [show ∀ X Y : ℝ, Real.exp X * (2 * Real.exp Y) = 2 * (Real.exp X * Real.exp Y) from
            fun X Y => by ring, ← Real.exp_add]
          congr 2
          ring
        have hR : 2 * Real.exp (|u| * lambda) ^ 2 * Real.exp (-(Real.pi * (rho u) ^ 2))
            = 2 * Real.exp (2 * (lambda * u) + -(Real.pi * (rho u) ^ 2)) := by
          rw [habsu, show Real.exp (u * lambda) ^ 2 = Real.exp (2 * (u * lambda)) from
            (hexp2 _).symm,
            show ∀ X Y : ℝ, 2 * Real.exp X * Real.exp Y = 2 * (Real.exp X * Real.exp Y) from
              fun X Y => by ring, ← Real.exp_add]
          congr 2
          ring
        rw [hL, hR]
      rw [← hval]
      refine mul_le_mul_of_nonneg_right hKlow (by positivity)
    have e3 : 2 * K ^ 2 * Real.exp (-(Real.pi * (rho u - sigma) ^ 2))
        = K ^ 2 * (2 * Real.exp (-(Real.pi * (rho u - sigma) ^ 2))) := by ring
    nlinarith [e1, e2, e3]


/-! ## The exact type law -/

/-- **(24.49) The exact type law.**  For every damping `σ > 0` and every superluminal window slope
`κ > 1`, the compressed damped propagator has exponential type exactly `λ`: neither the analytic
real-time damping nor the causal compression lowers the radiation type. -/
theorem tendsto_dampedCompression_type {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda)
    {sigma : ℝ} (hsigma : 0 < sigma) {c kappa q Cc : ℝ}
    (hc1 : 1 < c) (hck : c < kappa) (hq : 2 / 3 < q) (hq1 : q < 1)
    (hCc : 2 * sigma < Real.pi * Cc ^ 2) (hCc0 : 0 < Cc) :
    Tendsto (fun u : ℝ => Real.log ‖dampedCompression ha hlambda hsigma.le u (kappa * u)‖ / u)
      atTop (𝓝 lambda) := by
  have hg0 : 0 < ‖gaussLp‖ := norm_gaussLp_pos
  have hsix : 0 < ‖gaussLp‖ / 6 := by positivity
  have h1 := tendsto_outputDefect (sigma := sigma) (c := c) (kappa := kappa) (q := q) hc1 hck
  have h2 := tendsto_inputDefect_ratio (a := a) (lambda := lambda) (sigma := sigma) (c := c)
    (kappa := kappa) (q := q) hlambda.le hsigma.le (by linarith) hck (by linarith) (by linarith)
  have h3 := tendsto_packetDefect_ratio ha hlambda hsigma hq hq1 hCc hCc0 (fun u => c * u)
  have he1 := h1.eventually (eventually_lt_nhds hsix)
  have he2 := h2.eventually (eventually_lt_nhds hsix)
  have he3 := h3.eventually (eventually_lt_nhds hsix)
  -- the model scalar has type `λ`
  have hKtype : Tendsto (fun u : ℝ =>
      (Real.log ‖dampedModelConst a lambda sigma u (u ^ q)‖ - Real.log 2) / u) atTop
      (𝓝 lambda) := by
    have hN := tendsto_log_norm_dampedSymbol_center (a := a) (lambda := lambda) (sigma := sigma)
      (q := q) ha.le hlambda.le hsigma.le (by linarith) hq1
    have hshift : Tendsto (fun u : ℝ => (Real.pi * sigma ^ 2 - Real.log 2) / u) atTop (𝓝 0) := by
      have hinv : Tendsto (fun u : ℝ => 1 / u) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.congr fun u => (one_div u).symm
      have := hinv.const_mul (Real.pi * sigma ^ 2 - Real.log 2)
      rw [mul_zero] at this
      refine this.congr fun u => ?_
      rw [mul_one_div]
    have hsum := hN.add hshift
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    rw [norm_dampedModelConst, Real.log_mul (by
      have := norm_massGaugeDampedSymbol a lambda sigma u (-(u ^ q))
      rw [this]
      exact ne_of_gt (Real.exp_pos _)) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
    field_simp
    ring
  -- the sandwich
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hKtype tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ), he1, he2, he3] with u hu e1 e2 e3
    have hKpos : 0 < ‖dampedModelConst a lambda sigma u (u ^ q)‖ :=
      lt_of_lt_of_le (Real.exp_pos _) (le_norm_dampedModelConst hsigma.le hu)
    have hmain := le_norm_dampedCompression_mul ha hlambda hsigma.le u (u ^ q) (c * u) (kappa * u)
    have hTu : c * u - u = (c - 1) * u := by ring
    rw [hTu] at hmain
    have habsu : |u| = u := abs_of_pos hu
    rw [habsu] at hmain
    have hA : ‖dampedModelConst a lambda sigma u (u ^ q)‖
        * ‖gaussPacket (u ^ q / (2 * Real.pi) - sigma) ((c - 1) * u)
          - windowCutoff (measurableSet_Ioo (a := (0 : ℝ)) (b := kappa * u))
            (gaussPacket (u ^ q / (2 * Real.pi) - sigma) ((c - 1) * u))‖
        ≤ ‖dampedModelConst a lambda sigma u (u ^ q)‖ * ‖gaussLp‖ / 6 := by
      have := mul_le_mul_of_nonneg_left e1.le hKpos.le
      calc _ ≤ ‖dampedModelConst a lambda sigma u (u ^ q)‖ * (‖gaussLp‖ / 6) := this
        _ = ‖dampedModelConst a lambda sigma u (u ^ q)‖ * ‖gaussLp‖ / 6 := by ring
    have hB : ‖packetDefect ha hlambda hsigma.le u (u ^ q) (c * u)‖
        ≤ ‖dampedModelConst a lambda sigma u (u ^ q)‖ * ‖gaussLp‖ / 6 := by
      have hlt : ‖packetDefect ha hlambda hsigma.le u (u ^ q) (c * u)‖
          / ‖dampedModelConst a lambda sigma u (u ^ q)‖ ≤ ‖gaussLp‖ / 6 := e3.le
      rw [div_le_iff₀ hKpos] at hlt
      calc _ ≤ ‖gaussLp‖ / 6 * ‖dampedModelConst a lambda sigma u (u ^ q)‖ := hlt
        _ = ‖dampedModelConst a lambda sigma u (u ^ q)‖ * ‖gaussLp‖ / 6 := by ring
    have hC : Real.exp (u * lambda)
        * ‖gaussPacket (u ^ q / (2 * Real.pi)) (c * u)
          - windowCutoff (measurableSet_Ioo (a := (0 : ℝ)) (b := kappa * u))
            (gaussPacket (u ^ q / (2 * Real.pi)) (c * u))‖
        ≤ ‖dampedModelConst a lambda sigma u (u ^ q)‖ * ‖gaussLp‖ / 6 := by
      have hlt : Real.exp (lambda * u)
          * ‖gaussPacket (u ^ q / (2 * Real.pi)) (c * u)
            - windowCutoff (measurableSet_Ioo (a := (0 : ℝ)) (b := kappa * u))
              (gaussPacket (u ^ q / (2 * Real.pi)) (c * u))‖
          / ‖dampedModelConst a lambda sigma u (u ^ q)‖ ≤ ‖gaussLp‖ / 6 := e2.le
      rw [div_le_iff₀ hKpos] at hlt
      rw [mul_comm u lambda]
      calc _ ≤ ‖gaussLp‖ / 6 * ‖dampedModelConst a lambda sigma u (u ^ q)‖ := hlt
        _ = ‖dampedModelConst a lambda sigma u (u ^ q)‖ * ‖gaussLp‖ / 6 := by ring
    have hhalf : ‖dampedModelConst a lambda sigma u (u ^ q)‖ / 2
        ≤ ‖dampedCompression ha hlambda hsigma.le u (kappa * u)‖ := by
      have hchain : ‖dampedModelConst a lambda sigma u (u ^ q)‖ * ‖gaussLp‖ / 2
          ≤ ‖dampedCompression ha hlambda hsigma.le u (kappa * u)‖ * ‖gaussLp‖ := by
        linarith [hmain, hA, hB, hC]
      have := (div_le_div_iff_of_pos_right hg0).2 hchain
      calc ‖dampedModelConst a lambda sigma u (u ^ q)‖ / 2
          = ‖dampedModelConst a lambda sigma u (u ^ q)‖ * ‖gaussLp‖ / 2 / ‖gaussLp‖ := by
            field_simp
        _ ≤ ‖dampedCompression ha hlambda hsigma.le u (kappa * u)‖ * ‖gaussLp‖ / ‖gaussLp‖ := by
            gcongr
        _ = ‖dampedCompression ha hlambda hsigma.le u (kappa * u)‖ := by
            field_simp
    have hlogle : Real.log ‖dampedModelConst a lambda sigma u (u ^ q)‖ - Real.log 2
        ≤ Real.log ‖dampedCompression ha hlambda hsigma.le u (kappa * u)‖ := by
      have hposhalf : 0 < ‖dampedModelConst a lambda sigma u (u ^ q)‖ / 2 := by positivity
      have := Real.log_le_log hposhalf hhalf
      rwa [Real.log_div (ne_of_gt hKpos) (by norm_num)] at this
    exact div_le_div_of_nonneg_right hlogle hu.le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    exact log_norm_dampedCompression_div_le ha hlambda hsigma.le hu (kappa * u)


end

end RHTower
