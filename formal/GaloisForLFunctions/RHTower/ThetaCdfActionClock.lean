import GaloisForLFunctions.RHTower.ThetaCdfActionDyadic

/-!
# The sharp theta CDF-action clock

`Φ_n = log log n − log π + O(log log n / log n)`.

With `F` the CDF of the theta density `k`, `M = ∫ k` and `τ = 1 − F`:

* `Φ_n = 2∫₀^∞ (1 − cos 2πnF)` by evenness;
* on `[0, L]`, one integration by parts against the decreasing density gives
  `|∫₀^L cos 2πnF| ≤ M/(πn k(L))`;
* for `x ≥ 1`, the upper envelope gives `τ(x) ≤ C e^{5x/2} e^{−πe^{2x}}`, so
  `∫_L^∞ (1 − cos 2πnF) ≤ 2π²n² C² e^{5L} e^{−2πe^{2L}}`;
* at `L^± = ½ log((1 ± ε_n) log n/π)`, `ε_n = 4 log log n/log n`, every error is `O(ε_n)`.
-/

open MeasureTheory Set Filter Topology intervalIntegral

namespace RHTower

noncomputable section

open HedenmalmThetaSource HedenmalmQuantile GaloisForLFunctions.HTGeometry

/-! ## The half-line form -/

/-- The CDF-action integrand `g_n(x) = 1 − cos 2πnF(x)`. -/
def cdfActionIntegrand (n : ℤ) (x : ℝ) : ℝ := 1 - Real.cos (2 * Real.pi * n * thetaSource.cdfFun x)

theorem cdfActionIntegrand_neg (n : ℤ) (x : ℝ) : cdfActionIntegrand n (-x) = cdfActionIntegrand n x := by
  rw [cdfActionIntegrand, cdfActionIntegrand, cdfFun_thetaSource_neg,
    show 2 * Real.pi * n * (1 - thetaSource.cdfFun x) =
      -(2 * Real.pi * n * thetaSource.cdfFun x - (n : ℝ) * (2 * Real.pi)) by ring,
    Real.cos_neg, Real.cos_sub_int_mul_two_pi]

theorem cdfActionIntegrand_abs (n : ℤ) (x : ℝ) : cdfActionIntegrand n |x| = cdfActionIntegrand n x := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, cdfActionIntegrand_neg]

theorem cdfActionIntegrand_nonneg (n : ℤ) (x : ℝ) : 0 ≤ cdfActionIntegrand n x := by
  unfold cdfActionIntegrand; linarith [Real.cos_le_one (2 * Real.pi * n * thetaSource.cdfFun x)]

theorem cdfActionIntegrand_le_two (n : ℤ) (x : ℝ) : cdfActionIntegrand n x ≤ 2 := by
  unfold cdfActionIntegrand; linarith [Real.neg_one_le_cos (2 * Real.pi * n * thetaSource.cdfFun x)]

/-- `Φ_n = 2 ∫₀^∞ (1 − cos 2πnF)`. -/
theorem cdfAction_eq_two_mul_integral_Ioi (n : ℤ) :
    cdfAction n = 2 * ∫ x in Ioi 0, cdfActionIntegrand n x := by
  rw [← integral_comp_abs (f := cdfActionIntegrand n)]
  simp_rw [cdfActionIntegrand_abs]
  rfl

/-! ## The inner integral: one integration by parts -/

theorem thetaLogHazard_nonpos_of_nonneg {x : ℝ} (hx : 0 ≤ x) : thetaLogHazard x ≤ 0 := by
  have h := thetaLogHazard_nonneg_of_nonpos (x := -x) (by linarith)
  rw [thetaLogHazard_neg] at h
  linarith

theorem deriv_thetaCuspFullSource_nonpos_of_nonneg {x : ℝ} (hx : 0 ≤ x) : deriv thetaCuspFullSource x ≤ 0 := by
  have h := thetaLogHazard_nonpos_of_nonneg hx
  rw [thetaLogHazard] at h
  exact (div_nonpos_iff.1 h).elim (fun h => absurd h.2 (not_le.2 (thetaCuspFullSource_pos x)))
    (fun h => h.1)

theorem hasDerivAt_cdfFun_theta (x : ℝ) :
    HasDerivAt thetaSource.cdfFun (thetaCuspFullSource x / thetaSource.mass) x :=
  thetaSource.hasDerivAt_cdfFun x

/-- `|∫₀^L cos 2πnF| ≤ M/(πn k(L))` for `L ≥ 0`, `n ≥ 1`. -/
theorem abs_integral_cos_cdf_le {n : ℕ} (hn : 1 ≤ n) {L : ℝ} (hL : 0 ≤ L) :
    |∫ x in (0 : ℝ)..L, Real.cos (2 * Real.pi * n * thetaSource.cdfFun x)| ≤
      thetaSource.mass / (Real.pi * n * thetaCuspFullSource L) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hM := thetaSource.mass_pos
  set c : ℝ := 2 * Real.pi * n with hc
  have hc0 : 0 < c := by positivity
  set u : ℝ → ℝ := fun x => thetaSource.mass / (c * thetaCuspFullSource x)
  set u' : ℝ → ℝ := fun x => -(thetaSource.mass * (c * deriv thetaCuspFullSource x)) /
    (c * thetaCuspFullSource x) ^ 2
  set v : ℝ → ℝ := fun x => Real.sin (c * thetaSource.cdfFun x)
  set v' : ℝ → ℝ := fun x => Real.cos (c * thetaSource.cdfFun x) * (c * (thetaCuspFullSource x / thetaSource.mass))
  have hu : ∀ x, HasDerivAt u (u' x) x := fun x => by
    have h := ((hasDerivAt_thetaCuspFullSource x).const_mul c).inv
      (mul_pos hc0 (thetaCuspFullSource_pos x)).ne'
    have h2 := h.const_mul thetaSource.mass
    refine (h2.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    · simp only [u']; ring
    · simp only [u, Pi.inv_apply, div_eq_mul_inv]
  have hv : ∀ x, HasDerivAt v (v' x) x := fun x => by
    have h := ((hasDerivAt_cdfFun_theta x).const_mul c).sin
    exact h.congr_deriv (by simp only [v'])
  have hcontu' : Continuous u' := by
    have hk := contDiff_thetaCuspFullSource
    have hk' : Continuous (deriv thetaCuspFullSource) := hk.continuous_deriv (by norm_num)
    exact (continuous_const.mul (continuous_const.mul hk')).neg.div
      ((continuous_const.mul hk.continuous).pow 2)
      (fun x => pow_ne_zero 2 (mul_pos hc0 (thetaCuspFullSource_pos x)).ne')
  have hcontv' : Continuous v' := by
    have := thetaSource.continuous_cdfFun
    have hk := contDiff_thetaCuspFullSource.continuous
    exact (Real.continuous_cos.comp (continuous_const.mul this)).mul
      (continuous_const.mul (hk.div_const _))
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := L)
    (fun x _ => hu x) (fun x _ => hv x) (hcontu'.intervalIntegrable _ _) (hcontv'.intervalIntegrable _ _)
  have hlhs : ∫ x in (0 : ℝ)..L, u x * v' x = ∫ x in (0 : ℝ)..L, Real.cos (c * thetaSource.cdfFun x) := by
    refine integral_congr fun x _ => ?_
    simp only [u, v']
    have hk := (thetaCuspFullSource_pos x).ne'
    field_simp
  have hu'0 : ∀ x ∈ Icc (0 : ℝ) L, 0 ≤ u' x := fun x hx => by
    simp only [u']
    have := deriv_thetaCuspFullSource_nonpos_of_nonneg hx.1
    have : 0 ≤ -(thetaSource.mass * (c * deriv thetaCuspFullSource x)) := by
      have : thetaSource.mass * (c * deriv thetaCuspFullSource x) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hM.le (mul_nonpos_of_nonneg_of_nonpos hc0.le this)
      linarith
    positivity
  have hftc : ∫ x in (0 : ℝ)..L, u' x = u L - u 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hu x) (hcontu'.intervalIntegrable _ _)
  have hbound : |∫ x in (0 : ℝ)..L, u' x * v x| ≤ ∫ x in (0 : ℝ)..L, u' x := by
    refine (intervalIntegral.abs_integral_le_integral_abs hL).trans
      (intervalIntegral.integral_mono_on hL ?_ (hcontu'.intervalIntegrable _ _) fun x hx => ?_)
    · exact ((hcontu'.mul (Real.continuous_sin.comp (continuous_const.mul
        thetaSource.continuous_cdfFun))).abs).intervalIntegrable _ _
    · rw [abs_mul, abs_of_nonneg (hu'0 x hx)]
      exact mul_le_of_le_one_right (hu'0 x hx) (Real.abs_sin_le_one _)
  have huL : 0 < u L := by simp only [u]; have := thetaCuspFullSource_pos L; positivity
  have hu0 : 0 < u 0 := by simp only [u]; have := thetaCuspFullSource_pos 0; positivity
  have hvL : |v L| ≤ 1 := Real.abs_sin_le_one _
  have hv0 : |v 0| ≤ 1 := Real.abs_sin_le_one _
  rw [← hlhs, hibp]
  calc |u L * v L - u 0 * v 0 - ∫ x in (0 : ℝ)..L, u' x * v x|
      ≤ |u L * v L| + |u 0 * v 0| + |∫ x in (0 : ℝ)..L, u' x * v x| := by
        have := abs_sub (u L * v L - u 0 * v 0) (∫ x in (0 : ℝ)..L, u' x * v x)
        have := abs_sub (u L * v L) (u 0 * v 0)
        linarith
    _ ≤ u L + u 0 + (u L - u 0) := by
        rw [abs_mul, abs_mul, abs_of_pos huL, abs_of_pos hu0, ← hftc]
        gcongr
        · exact mul_le_of_le_one_right huL.le hvL
        · exact mul_le_of_le_one_right hu0.le hv0
    _ = thetaSource.mass / (Real.pi * n * thetaCuspFullSource L) := by
        simp only [u, c]
        have hk := (thetaCuspFullSource_pos L).ne'
        field_simp
        ring

/-- `|∫₀^L g_n − L| ≤ M/(πn k(L))`. -/
theorem abs_integral_cdfActionIntegrand_sub_le {n : ℕ} (hn : 1 ≤ n) {L : ℝ} (hL : 0 ≤ L) :
    |(∫ x in (0 : ℝ)..L, cdfActionIntegrand n x) - L| ≤
      thetaSource.mass / (Real.pi * n * thetaCuspFullSource L) := by
  have hcont : Continuous fun x => Real.cos (2 * Real.pi * n * thetaSource.cdfFun x) :=
    Real.continuous_cos.comp (continuous_const.mul thetaSource.continuous_cdfFun)
  have h : ∫ x in (0 : ℝ)..L, cdfActionIntegrand n x =
      L - ∫ x in (0 : ℝ)..L, Real.cos (2 * Real.pi * n * thetaSource.cdfFun x) := by
    simp only [cdfActionIntegrand, Int.cast_natCast]
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hcont.intervalIntegrable _ _)]
    simp
  rw [h, sub_sub_cancel_left, abs_neg]

  exact abs_integral_cos_cdf_le hn hL

/-! ## The tail -/

/-- `C₁ = U/(πM)`. -/
def thetaTailCoefficient : ℝ := thetaEnvelopeUpper / (Real.pi * thetaSource.mass)

theorem thetaTailCoefficient_pos : 0 < thetaTailCoefficient := by
  unfold thetaTailCoefficient
  have := thetaEnvelopeUpper_pos
  have := thetaSource.mass_pos
  positivity

/-- `1 − F(x) ≤ C₁ e^{5x/2} e^{−πe^{2x}}` for `x ≥ 1`. -/
theorem one_sub_cdfFun_le_tail {x : ℝ} (hx : 1 ≤ x) :
    1 - thetaSource.cdfFun x ≤
      thetaTailCoefficient * (Real.exp (5 / 2 * x) * Real.exp (-Real.pi * Real.exp (2 * x))) := by
  rw [one_sub_cdfFun]
  have h := integral_Ioi_thetaCuspFullSource_le hx
  have hM := thetaSource.mass_pos
  calc (∫ y in Ioi x, thetaSource.k y) / thetaSource.mass ≤
      thetaEnvelopeUpper * thetaEnvelope x / (Real.pi * Real.exp (2 * x)) / thetaSource.mass :=
        div_le_div_of_nonneg_right h hM.le
    _ = thetaTailCoefficient * (Real.exp (5 / 2 * x) * Real.exp (-Real.pi * Real.exp (2 * x))) := by
        rw [thetaTailCoefficient, thetaEnvelope]
        have he : Real.exp (9 * x / 2) = Real.exp (5 / 2 * x) * Real.exp (2 * x) := by
          rw [← Real.exp_add]; ring_nf
        rw [he]
        field_simp

theorem cdfActionIntegrand_le_sq_tail (n : ℤ) (x : ℝ) :
    cdfActionIntegrand n x ≤ 2 * Real.pi ^ 2 * (n : ℝ) ^ 2 * (1 - thetaSource.cdfFun x) ^ 2 := by
  have h : cdfActionIntegrand n x = 1 - Real.cos (2 * Real.pi * n * (1 - thetaSource.cdfFun x)) := by
    rw [cdfActionIntegrand, show 2 * Real.pi * n * (1 - thetaSource.cdfFun x) =
      -(2 * Real.pi * n * thetaSource.cdfFun x - (n : ℝ) * (2 * Real.pi)) by ring,
      Real.cos_neg, Real.cos_sub_int_mul_two_pi]
  rw [h]
  have := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * n * (1 - thetaSource.cdfFun x))
  nlinarith

theorem exp_five_sub_le {L x : ℝ} (hL : 1 ≤ L) (hx : L ≤ x) :
    Real.exp (5 * x) * Real.exp (-Real.pi * Real.exp (2 * x)) ≤
      Real.exp (5 * L) * Real.exp (-Real.pi * Real.exp (2 * L)) := by
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have h1 : Real.exp (2 * L) * (1 + 2 * (x - L)) ≤ Real.exp (2 * x) := by
    have := Real.add_one_le_exp (2 * (x - L))
    have hpos := Real.exp_pos (2 * L)
    calc Real.exp (2 * L) * (1 + 2 * (x - L)) ≤ Real.exp (2 * L) * Real.exp (2 * (x - L)) :=
          mul_le_mul_of_nonneg_left (by linarith) hpos.le
      _ = Real.exp (2 * x) := by rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp 2 ≤ Real.exp (2 * L) := Real.exp_le_exp.2 (by linarith)
  have h3 : (2 : ℝ) < Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ); linarith [Real.add_one_lt_exp (show (2 : ℝ) ≠ 0 by norm_num)]
  have hpi := Real.pi_gt_three
  have hE := Real.exp_pos (2 * L)
  have h4 : Real.pi * (Real.exp (2 * x) - Real.exp (2 * L)) ≥ 2 * Real.pi * Real.exp (2 * L) * (x - L) := by
    nlinarith [Real.pi_pos]
  have h5 : 2 * Real.pi * Real.exp (2 * L) ≥ 5 := by nlinarith
  have h6 := mul_le_mul_of_nonneg_right h5 (sub_nonneg.2 hx)
  nlinarith

theorem exp_neg_pi_exp_le_shift (L x : ℝ) :
    Real.exp (-Real.pi * Real.exp (2 * x)) ≤
      Real.exp (-Real.pi * Real.exp (2 * L)) * Real.exp (-(2 * Real.pi * Real.exp (2 * L)) * (x - L)) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have h1 : Real.exp (2 * L) * (1 + 2 * (x - L)) ≤ Real.exp (2 * x) := by
    have := Real.add_one_le_exp (2 * (x - L))
    have hpos := Real.exp_pos (2 * L)
    calc Real.exp (2 * L) * (1 + 2 * (x - L)) ≤ Real.exp (2 * L) * Real.exp (2 * (x - L)) :=
          mul_le_mul_of_nonneg_left (by linarith) hpos.le
      _ = Real.exp (2 * x) := by rw [← Real.exp_add]; ring_nf
  nlinarith [Real.pi_pos]

/-- `∫_L^∞ g_n ≤ 2π²n² C₁² e^{5L} e^{−2πe^{2L}}` for `L ≥ 1`. -/
theorem integral_Ioi_cdfActionIntegrand_le (n : ℤ) {L : ℝ} (hL : 1 ≤ L) :
    ∫ x in Ioi L, cdfActionIntegrand n x ≤
      2 * Real.pi ^ 2 * (n : ℝ) ^ 2 * thetaTailCoefficient ^ 2 *
        (Real.exp (5 * L) * Real.exp (-Real.pi * Real.exp (2 * L)) * Real.exp (-Real.pi * Real.exp (2 * L))) := by
  set K := 2 * Real.pi ^ 2 * (n : ℝ) ^ 2 * thetaTailCoefficient ^ 2 *
    (Real.exp (5 * L) * Real.exp (-Real.pi * Real.exp (2 * L)) * Real.exp (-Real.pi * Real.exp (2 * L)))
  set a := 2 * Real.pi * Real.exp (2 * L)
  have ha : 0 < a := by positivity
  have hK0 : 0 ≤ K := by positivity
  have hg : IntegrableOn (cdfActionIntegrand n) (Ioi L) volume :=
    (integrable_cdfAction_integrand n).integrableOn
  have hb : IntegrableOn (fun x => K * Real.exp (-a * (x - L))) (Ioi L) volume :=
    (integrableOn_exp_neg_shift ha).const_mul K
  have hpt : ∀ x ∈ Ioi L, cdfActionIntegrand n x ≤ K * Real.exp (-a * (x - L)) := by
    intro x hx
    have hx1 : 1 ≤ x := hL.trans hx.le
    have h1 := cdfActionIntegrand_le_sq_tail n x
    have h2 := one_sub_cdfFun_le_tail hx1
    have hτ0 : 0 ≤ 1 - thetaSource.cdfFun x := by linarith [(thetaSource.cdfFun_mem_Ioo x).2]
    have h3 : (1 - thetaSource.cdfFun x) ^ 2 ≤ thetaTailCoefficient ^ 2 *
        (Real.exp (5 * x) * Real.exp (-Real.pi * Real.exp (2 * x)) * Real.exp (-Real.pi * Real.exp (2 * x))) := by
      have := pow_le_pow_left₀ hτ0 h2 2
      refine this.trans (le_of_eq ?_)
      rw [mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul (-Real.pi * _)]
      rw [show ((2 : ℕ) : ℝ) * (5 / 2 * x) = 5 * x by push_cast; ring]
      rw [show ((2 : ℕ) : ℝ) * (-Real.pi * Real.exp (2 * x)) = -Real.pi * Real.exp (2 * x) + -Real.pi * Real.exp (2 * x) by
        push_cast; ring, Real.exp_add]
      ring
    have h4 := exp_five_sub_le hL hx.le
    have h5 := exp_neg_pi_exp_le_shift L x
    have h6 : Real.exp (5 * x) * Real.exp (-Real.pi * Real.exp (2 * x)) * Real.exp (-Real.pi * Real.exp (2 * x)) ≤
        (Real.exp (5 * L) * Real.exp (-Real.pi * Real.exp (2 * L))) *
          (Real.exp (-Real.pi * Real.exp (2 * L)) * Real.exp (-a * (x - L))) := by
      have := mul_le_mul h4 h5 (Real.exp_pos _).le (by positivity)
      simpa [a, neg_mul, mul_assoc] using this
    calc cdfActionIntegrand n x ≤ 2 * Real.pi ^ 2 * (n : ℝ) ^ 2 * (1 - thetaSource.cdfFun x) ^ 2 := h1
      _ ≤ 2 * Real.pi ^ 2 * (n : ℝ) ^ 2 * (thetaTailCoefficient ^ 2 *
          (Real.exp (5 * x) * Real.exp (-Real.pi * Real.exp (2 * x)) * Real.exp (-Real.pi * Real.exp (2 * x)))) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ 2 * Real.pi ^ 2 * (n : ℝ) ^ 2 * (thetaTailCoefficient ^ 2 *
          ((Real.exp (5 * L) * Real.exp (-Real.pi * Real.exp (2 * L))) *
            (Real.exp (-Real.pi * Real.exp (2 * L)) * Real.exp (-a * (x - L))))) := by gcongr
      _ = K * Real.exp (-a * (x - L)) := by simp only [K]; ring
  calc ∫ x in Ioi L, cdfActionIntegrand n x ≤ ∫ x in Ioi L, K * Real.exp (-a * (x - L)) :=
        setIntegral_mono_on hg hb measurableSet_Ioi hpt
    _ = K * (1 / a) := by rw [MeasureTheory.integral_const_mul, integral_Ioi_exp_neg_shift ha]
    _ ≤ K := by
        have : 1 / a ≤ 1 := by
          rw [div_le_one ha]
          have h2 : (1 : ℝ) ≤ Real.exp (2 * L) := Real.one_le_exp (by linarith)
          nlinarith [Real.pi_gt_three]
        nlinarith

/-! ## The sharp clock -/

theorem integrableOn_cdfActionIntegrand (n : ℤ) (s : Set ℝ) : IntegrableOn (cdfActionIntegrand n) s volume :=
  (integrable_cdfAction_integrand n).integrableOn

theorem log_one_sub_ge {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) : -(2 * ε) ≤ Real.log (1 - ε) := by
  have hpos : 0 < 1 - ε := by linarith
  have h := Real.one_sub_inv_le_log_of_pos hpos
  have : 1 - (1 - ε)⁻¹ ≥ -(2 * ε) := by
    rw [ge_iff_le, ← sub_nonneg]
    have : 1 - (1 - ε)⁻¹ - -(2 * ε) = ε * (1 - 2 * ε) / (1 - ε) := by field_simp; ring
    rw [this]; exact div_nonneg (mul_nonneg h0 (by linarith)) hpos.le
  linarith

theorem log_one_sub_le {ε : ℝ} (h1 : ε < 1) : Real.log (1 - ε) ≤ -ε := by
  have := Real.log_le_sub_one_of_pos (show 0 < 1 - ε by linarith); linarith

theorem log_one_add_le_of_nonneg {ε : ℝ} (h0 : 0 ≤ ε) : Real.log (1 + ε) ≤ ε := by
  have := Real.log_le_sub_one_of_pos (show 0 < 1 + ε by linarith); linarith

/-- The two-sided sandwich for `Φ_n` at cut points `0 ≤ L₁ ≤ L₂`, `1 ≤ L₂`. -/
theorem cdfAction_sandwich {n : ℕ} (hn : 1 ≤ n) {L₁ L₂ : ℝ} (hL₁ : 0 ≤ L₁) (hL₁₂ : L₁ ≤ L₂) (hL₂ : 1 ≤ L₂) :
    2 * (L₁ - thetaSource.mass / (Real.pi * n * thetaCuspFullSource L₁)) ≤ cdfAction n ∧
      cdfAction n ≤ 2 * (L₁ + thetaSource.mass / (Real.pi * n * thetaCuspFullSource L₁)) + 4 * (L₂ - L₁) +
        2 * (2 * Real.pi ^ 2 * (n : ℝ) ^ 2 * thetaTailCoefficient ^ 2 *
          (Real.exp (5 * L₂) * Real.exp (-Real.pi * Real.exp (2 * L₂)) * Real.exp (-Real.pi * Real.exp (2 * L₂)))) := by
  have hinner := abs_integral_cdfActionIntegrand_sub_le hn hL₁
  have hB := integral_Ioi_cdfActionIntegrand_le n hL₂
  have hmid : ∫ x in L₁..L₂, cdfActionIntegrand n x ≤ 2 * (L₂ - L₁) := by
    have := intervalIntegral.integral_mono_on (f := cdfActionIntegrand n) (g := fun _ => (2 : ℝ)) hL₁₂
      ((integrable_cdfAction_integrand n).intervalIntegrable) intervalIntegrable_const
      (fun x _ => cdfActionIntegrand_le_two n x)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  have hmid0 : 0 ≤ ∫ x in L₁..L₂, cdfActionIntegrand n x :=
    intervalIntegral.integral_nonneg hL₁₂ fun x _ => cdfActionIntegrand_nonneg n x
  have hB0 : 0 ≤ ∫ x in Ioi L₂, cdfActionIntegrand n x :=
    setIntegral_nonneg measurableSet_Ioi fun x _ => cdfActionIntegrand_nonneg n x
  have hsplit : ∫ x in Ioi 0, cdfActionIntegrand n x =
      (∫ x in (0 : ℝ)..L₁, cdfActionIntegrand n x) + (∫ x in L₁..L₂, cdfActionIntegrand n x) +
        ∫ x in Ioi L₂, cdfActionIntegrand n x := by
    rw [intervalIntegral.integral_of_le hL₁, intervalIntegral.integral_of_le hL₁₂,
      ← setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
        (integrableOn_cdfActionIntegrand _ _) (integrableOn_cdfActionIntegrand _ _),
      Ioc_union_Ioc_eq_Ioc hL₁ hL₁₂,
      ← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (integrableOn_cdfActionIntegrand _ _) (integrableOn_cdfActionIntegrand _ _),
      Ioc_union_Ioi_eq_Ioi (hL₁.trans hL₁₂)]
  have hΦ := cdfAction_eq_two_mul_integral_Ioi n
  rw [hsplit] at hΦ
  push_cast at hΦ hB
  rw [abs_le] at hinner
  constructor <;> linarith [hinner.1, hinner.2]

/-- The inner error at a cut point with `e^{−πe^{2L}} = ℓ⁴/n`. -/
theorem inner_error_le {n : ℕ} (hn : 1 ≤ n) {L ℓ : ℝ} (hL : 0 < L) (hℓ : 1 ≤ ℓ)
    (hE : Real.exp (-Real.pi * Real.exp (2 * L)) = ℓ ^ 4 / n) :
    thetaSource.mass / (Real.pi * n * thetaCuspFullSource L) ≤
      thetaSource.mass / (Real.pi * thetaEnvelopeLower) * (1 / ℓ ^ 4) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc := thetaEnvelopeLower_pos
  have hM := thetaSource.mass_pos
  have hk : thetaEnvelopeLower * (ℓ ^ 4 / n) ≤ thetaCuspFullSource L := by
    have h := thetaCuspFullSource_ge_envelope hL
    rw [thetaEnvelope] at h
    have : 1 ≤ Real.exp (9 * L / 2) := Real.one_le_exp (by linarith)
    calc thetaEnvelopeLower * (ℓ ^ 4 / n) = thetaEnvelopeLower * (1 * Real.exp (-Real.pi * Real.exp (2 * L))) := by
          rw [hE, one_mul]
      _ ≤ thetaEnvelopeLower * (Real.exp (9 * L / 2) * Real.exp (-Real.pi * Real.exp (2 * L))) := by gcongr
      _ ≤ thetaCuspFullSource L := h
  have hden : Real.pi * thetaEnvelopeLower * ℓ ^ 4 ≤ Real.pi * n * thetaCuspFullSource L := by
    have := mul_le_mul_of_nonneg_left hk (show 0 ≤ Real.pi * n by positivity)
    calc Real.pi * thetaEnvelopeLower * ℓ ^ 4 = Real.pi * n * (thetaEnvelopeLower * (ℓ ^ 4 / n)) := by
          field_simp
      _ ≤ _ := this
  have hpos : 0 < Real.pi * thetaEnvelopeLower * ℓ ^ 4 := by positivity
  calc thetaSource.mass / (Real.pi * n * thetaCuspFullSource L) ≤
      thetaSource.mass / (Real.pi * thetaEnvelopeLower * ℓ ^ 4) :=
        div_le_div_of_nonneg_left hM.le hpos hden
    _ = thetaSource.mass / (Real.pi * thetaEnvelopeLower) * (1 / ℓ ^ 4) := by field_simp

/-- The outer error at a cut point with `e^{2L} ≤ ℓ` and `e^{−πe^{2L}} = 1/(nℓ⁴)`. -/
theorem outer_error_le {n : ℕ} (hn : 1 ≤ n) {L ℓ : ℝ} (hL : 0 ≤ L) (hℓ : 1 ≤ ℓ)
    (h2L : Real.exp (2 * L) ≤ ℓ) (hE : Real.exp (-Real.pi * Real.exp (2 * L)) = 1 / (n * ℓ ^ 4)) :
    2 * Real.pi ^ 2 * (n : ℝ) ^ 2 * thetaTailCoefficient ^ 2 *
        (Real.exp (5 * L) * Real.exp (-Real.pi * Real.exp (2 * L)) * Real.exp (-Real.pi * Real.exp (2 * L))) ≤
      2 * Real.pi ^ 2 * thetaTailCoefficient ^ 2 * (1 / ℓ ^ 5) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hℓ0 : 0 < ℓ := by linarith
  have he5 : Real.exp (5 * L) ≤ ℓ ^ 3 := by
    have h6 : Real.exp (5 * L) ≤ Real.exp (2 * L) ^ 3 := by
      rw [← Real.exp_nat_mul]; exact Real.exp_le_exp.2 (by push_cast; nlinarith)
    exact h6.trans (pow_le_pow_left₀ (Real.exp_pos _).le h2L 3)
  rw [hE]
  calc 2 * Real.pi ^ 2 * (n : ℝ) ^ 2 * thetaTailCoefficient ^ 2 *
        (Real.exp (5 * L) * (1 / (n * ℓ ^ 4)) * (1 / (n * ℓ ^ 4))) =
      2 * Real.pi ^ 2 * thetaTailCoefficient ^ 2 * (Real.exp (5 * L) / ℓ ^ 8) := by
        field_simp
    _ ≤ 2 * Real.pi ^ 2 * thetaTailCoefficient ^ 2 * (ℓ ^ 3 / ℓ ^ 8) := by gcongr
    _ = 2 * Real.pi ^ 2 * thetaTailCoefficient ^ 2 * (1 / ℓ ^ 5) := by field_simp

theorem one_div_pow_le_div {ℓ lam : ℝ} (hℓ : 1 ≤ ℓ) (hlam : 1 ≤ lam) {k : ℕ} (hk : 1 ≤ k) :
    1 / ℓ ^ k ≤ lam / ℓ := by
  have hℓ0 : 0 < ℓ := by linarith
  rw [div_le_div_iff₀ (by positivity) hℓ0]
  have : ℓ ≤ ℓ ^ k := by
    calc ℓ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ k := pow_le_pow_right₀ hℓ hk
  nlinarith

/-- **The sharp CDF-action clock**: `Φ_n = log log n − log π + O(log log n/log n)`. -/
theorem exists_abs_cdfAction_sub_loglog_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      |cdfAction n - (Real.log (Real.log n) - Real.log Real.pi)| ≤
        C * (Real.log (Real.log n) / Real.log n) := by
  have hM := thetaSource.mass_pos
  have hc := thetaEnvelopeLower_pos
  have hC₁ := thetaTailCoefficient_pos
  set KA := thetaSource.mass / (Real.pi * thetaEnvelopeLower)
  set KB := 2 * Real.pi ^ 2 * thetaTailCoefficient ^ 2
  have hKA : 0 ≤ KA := by positivity
  have hKB : 0 ≤ KB := by positivity
  refine ⟨24 + 2 * KA + 2 * KB, by positivity, ?_⟩
  have hℓt : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun n : ℕ => Real.log (Real.log n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hℓt
  have hratio : Tendsto (fun n : ℕ => Real.log (Real.log n) / Real.log n) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hℓt
  have ev1 : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (Real.log n) := hloglog.eventually_ge_atTop 1
  have ev2 : ∀ᶠ n : ℕ in atTop, Real.log (Real.log n) / Real.log n ≤ 1 / 8 :=
    hratio.eventually (ge_mem_nhds (by norm_num))
  have ev3 : ∀ᶠ n : ℕ in atTop, 2 * Real.pi * Real.exp 2 ≤ Real.log n := hℓt.eventually_ge_atTop _
  have ev4 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (((ev1.and ev2).and ev3).and ev4)
  refine ⟨N₀, fun n hn => ?_⟩
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hN₀ n hn
  set ℓ := Real.log n with hℓ_def
  set lam := Real.log ℓ with hlam_def
  set ε := 4 * (lam / ℓ) with hε_def
  have hnR : (0 : ℝ) < n := by exact_mod_cast h4
  have hpi := Real.pi_gt_three
  have he2 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hℓ1 : 1 ≤ ℓ := by nlinarith
  have hℓpos : 0 < ℓ := by linarith
  have hε0 : 0 ≤ ε := by positivity
  have hε2 : ε ≤ 1 / 2 := by simp only [ε]; linarith
  have h1ε : 0 < 1 - ε := by linarith
  set aM : ℝ := (1 - ε) * ℓ / Real.pi
  set aP : ℝ := (1 + ε) * ℓ / Real.pi
  have haM : 0 < aM := div_pos (mul_pos h1ε hℓpos) Real.pi_pos
  have haP : 0 < aP := by positivity
  set Lm := Real.log aM / 2
  set Lp := Real.log aP / 2
  have hexpLm : Real.exp (2 * Lm) = aM := by rw [show 2 * Lm = Real.log aM by ring, Real.exp_log haM]
  have hexpLp : Real.exp (2 * Lp) = aP := by rw [show 2 * Lp = Real.log aP by ring, Real.exp_log haP]
  have hLm1 : 1 ≤ Lm := by
    have hle : Real.exp 2 ≤ aM := by
      simp only [aM]; rw [le_div_iff₀ Real.pi_pos]
      have : (1 / 2 : ℝ) ≤ 1 - ε := by linarith
      nlinarith [Real.exp_pos 2]
    have := Real.log_le_log (Real.exp_pos 2) hle
    rw [Real.log_exp] at this
    simp only [Lm]; linarith
  have hLmLp : Lm ≤ Lp := by
    have hle : aM ≤ aP := by simp only [aM, aP]; gcongr; linarith
    simp only [Lm, Lp]; linarith [Real.log_le_log haM hle]
  have hlogℓ : Real.exp (4 * lam) = ℓ ^ 4 := by
    rw [hlam_def, show 4 * Real.log ℓ = ((4 : ℕ) : ℝ) * Real.log ℓ by norm_num, Real.exp_nat_mul,
      Real.exp_log hℓpos]
  have hlogn : Real.exp ℓ = n := Real.exp_log hnR
  have hEm : Real.exp (-Real.pi * Real.exp (2 * Lm)) = ℓ ^ 4 / n := by
    rw [hexpLm, show -Real.pi * aM = 4 * lam - ℓ by simp only [aM, ε]; field_simp; ring,
      Real.exp_sub, hlogℓ, hlogn]
  have hEp : Real.exp (-Real.pi * Real.exp (2 * Lp)) = 1 / (n * ℓ ^ 4) := by
    rw [hexpLp, show -Real.pi * aP = -(ℓ + 4 * lam) by simp only [aP, ε]; field_simp,
      Real.exp_neg, Real.exp_add, hlogℓ, hlogn]
    field_simp
  have haPℓ : Real.exp (2 * Lp) ≤ ℓ := by
    rw [hexpLp]; simp only [aP]; rw [div_le_iff₀ Real.pi_pos]; nlinarith
  obtain ⟨hlow, hup⟩ := cdfAction_sandwich h4 (by linarith) hLmLp (hLm1.trans hLmLp)
  have hA := inner_error_le h4 (by linarith) hℓ1 hEm
  have hB := outer_error_le h4 (by linarith) hℓ1 haPℓ hEp
  change _ ≤ KA * (1 / ℓ ^ 4) at hA
  change _ ≤ KB * (1 / ℓ ^ 5) at hB
  have hA' : KA * (1 / ℓ ^ 4) ≤ KA * (lam / ℓ) :=
    mul_le_mul_of_nonneg_left (one_div_pow_le_div hℓ1 h1 (by norm_num)) hKA
  have hB' : KB * (1 / ℓ ^ 5) ≤ KB * (lam / ℓ) :=
    mul_le_mul_of_nonneg_left (one_div_pow_le_div hℓ1 h1 (by norm_num)) hKB
  have h2Lm : 2 * Lm = lam - Real.log Real.pi + Real.log (1 - ε) := by
    simp only [Lm, aM]
    rw [show 2 * (Real.log ((1 - ε) * ℓ / Real.pi) / 2) = Real.log ((1 - ε) * ℓ / Real.pi) by ring,
      Real.log_div (mul_pos h1ε hℓpos).ne' Real.pi_pos.ne', Real.log_mul h1ε.ne' hℓpos.ne']
    ring
  have h2Lp : 2 * (Lp - Lm) ≤ 3 * ε := by
    simp only [Lm, Lp, aM, aP]
    rw [show 2 * (Real.log ((1 + ε) * ℓ / Real.pi) / 2 - Real.log ((1 - ε) * ℓ / Real.pi) / 2) =
      Real.log ((1 + ε) * ℓ / Real.pi) - Real.log ((1 - ε) * ℓ / Real.pi) by ring,
      Real.log_div (by positivity) Real.pi_pos.ne', Real.log_div (mul_pos h1ε hℓpos).ne' Real.pi_pos.ne',
      Real.log_mul (by linarith) hℓpos.ne', Real.log_mul h1ε.ne' hℓpos.ne']
    linarith [log_one_add_le_of_nonneg hε0, log_one_sub_ge hε0 hε2]
  have hlog1 := log_one_sub_ge hε0 hε2
  have hlog2 := log_one_sub_le (show ε < 1 by linarith)
  have hq : 0 ≤ lam / ℓ := by positivity
  have hKAq : 0 ≤ KA * (lam / ℓ) := mul_nonneg hKA hq
  have hKBq : 0 ≤ KB * (lam / ℓ) := mul_nonneg hKB hq
  rw [abs_le]
  constructor <;> linarith

/-! ## Consequences: the dyadic increment and the block ratios -/

/-- The paired-block ratio `r_n = (Φ_{2n} − Φ_n)/Φ_n`. -/
def dyadicRatio (n : ℕ) : ℝ := (cdfAction (2 * (n : ℤ)) - cdfAction n) / cdfAction n

theorem log_log_two_mul_sub_le {n : ℕ} (hn : 2 ≤ n) :
    Real.log (Real.log (2 * n)) - Real.log (Real.log n) ≤ Real.log 2 / Real.log n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hℓ : 0 < Real.log n := Real.log_pos (by linarith)
  have h2n : Real.log (2 * n) = Real.log n + Real.log 2 := by
    rw [Real.log_mul (by norm_num) (by linarith), add_comm]
  rw [h2n, ← Real.log_div (by positivity) hℓ.ne']
  have key : (Real.log n + Real.log 2) / Real.log n = 1 + Real.log 2 / Real.log n := by
    field_simp
  rw [key]
  have := Real.log_le_sub_one_of_pos (show 0 < 1 + Real.log 2 / Real.log n by positivity)
  linarith

theorem log_log_le_log_log_two_mul {n : ℕ} (hn : 2 ≤ n) :
    Real.log (Real.log n) ≤ Real.log (Real.log (2 * n)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hℓ : 0 < Real.log n := Real.log_pos (by linarith)
  exact Real.log_le_log hℓ (Real.log_le_log (by linarith) (by linarith))

/-- `Φ_{2n} − Φ_n = O(log log n/log n)`. -/
theorem exists_abs_cdfAction_two_mul_sub_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      |cdfAction (2 * (n : ℤ)) - cdfAction n| ≤ C * (Real.log (Real.log n) / Real.log n) := by
  obtain ⟨C, hC0, N₀, hN₀⟩ := exists_abs_cdfAction_sub_loglog_le
  have hℓt : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun n : ℕ => Real.log (Real.log n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hℓt
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 ((hloglog.eventually_ge_atTop 1).and (eventually_ge_atTop 2))
  refine ⟨3 * C + 1, by positivity, max N₀ N₁, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN₁ n (le_of_max_le_right hn)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast h2
  have hℓ : 0 < Real.log n := Real.log_pos (by linarith)
  have hA := hN₀ n (le_of_max_le_left hn)
  have hB := hN₀ (2 * n) (by have := le_of_max_le_left hn; omega)
  push_cast at hB
  have hℓ2 : Real.log n ≤ Real.log (2 * n) := Real.log_le_log (by linarith) (by linarith)
  have hd := log_log_two_mul_sub_le h2
  have hd0 := log_log_le_log_log_two_mul h2
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hq : Real.log (Real.log (2 * n)) / Real.log (2 * n) ≤ (Real.log (Real.log n) + 1) / Real.log n := by
    have hnum : Real.log (Real.log (2 * n)) ≤ Real.log (Real.log n) + 1 := by
      have : Real.log 2 / Real.log n ≤ 1 := by
        rw [div_le_one hℓ]
        have : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnR
        exact this
      linarith
    have hpos : 0 ≤ Real.log (Real.log (2 * n)) := by linarith
    calc Real.log (Real.log (2 * n)) / Real.log (2 * n) ≤ Real.log (Real.log (2 * n)) / Real.log n :=
          div_le_div_of_nonneg_left hpos hℓ hℓ2
      _ ≤ (Real.log (Real.log n) + 1) / Real.log n := div_le_div_of_nonneg_right hnum hℓ.le
  have hq2 : (Real.log (Real.log n) + 1) / Real.log n ≤ 2 * (Real.log (Real.log n) / Real.log n) := by
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hℓ]; linarith
  have hq3 : Real.log 2 / Real.log n ≤ Real.log (Real.log n) / Real.log n :=
    div_le_div_of_nonneg_right (by linarith) hℓ.le
  have hCq := mul_le_mul_of_nonneg_left (hq.trans hq2) hC0
  rw [abs_le] at hA hB ⊢
  have hr0 : 0 ≤ Real.log (Real.log n) / Real.log n := by positivity
  constructor <;> nlinarith

/-- `Φ_n ≥ ½ log log n` eventually. -/
theorem eventually_cdfAction_ge_half_loglog :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Real.log (Real.log n) / 2 ≤ cdfAction n := by
  obtain ⟨C, hC0, N₀, hN₀⟩ := exists_abs_cdfAction_sub_loglog_le
  have hℓt : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun n : ℕ => Real.log (Real.log n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hℓt
  have ev1 := hloglog.eventually_ge_atTop (4 * Real.log Real.pi + 1)
  have ev2 : ∀ᶠ n : ℕ in atTop, C * (1 / Real.log n) ≤ 1 / 4 := by
    have : Tendsto (fun n : ℕ => C * (1 / Real.log n)) atTop (𝓝 (C * 0)) :=
      (tendsto_const_nhds.div_atTop hℓt).const_mul C
    rw [mul_zero] at this
    exact this.eventually (ge_mem_nhds (by norm_num))
  have ev3 := hℓt.eventually_gt_atTop 0
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 ((ev1.and ev2).and ev3)
  refine ⟨max N₀ N₁, fun n hn => ?_⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := hN₁ n (le_of_max_le_right hn)
  have hA := hN₀ n (le_of_max_le_left hn)
  have hlogpi : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  have hdiv : C * (Real.log (Real.log n) / Real.log n) ≤ Real.log (Real.log n) / 4 := by
    have hll : 0 ≤ Real.log (Real.log n) := by linarith
    calc C * (Real.log (Real.log n) / Real.log n) = C * (1 / Real.log n) * Real.log (Real.log n) := by ring
      _ ≤ 1 / 4 * Real.log (Real.log n) := mul_le_mul_of_nonneg_right h2 hll
      _ = Real.log (Real.log n) / 4 := by ring
  rw [abs_le] at hA
  linarith [hA.1]

/-- `r_n = O(1/log n)`. -/
theorem exists_dyadicRatio_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → dyadicRatio n ≤ C / Real.log n := by
  obtain ⟨C, hC0, N₀, hN₀⟩ := exists_abs_cdfAction_two_mul_sub_le
  obtain ⟨N₁, hN₁⟩ := eventually_cdfAction_ge_half_loglog
  have hℓt : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun n : ℕ => Real.log (Real.log n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hℓt
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (((hloglog.eventually_ge_atTop 1).and
    (hℓt.eventually_gt_atTop 0)).and (eventually_ge_atTop 1))
  refine ⟨2 * C, by positivity, max (max N₀ N₁) N₂, fun n hn => ?_⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := hN₂ n (le_of_max_le_right hn)
  have hA := hN₀ n (le_of_max_le_left (le_of_max_le_left hn))
  have hB := hN₁ n (le_of_max_le_right (le_of_max_le_left hn))
  have hpos : 0 < cdfAction n := cdfAction_pos h3
  have hll : 0 < Real.log (Real.log n) := by linarith
  rw [dyadicRatio, div_le_div_iff₀ hpos h2]
  have hnum := (le_abs_self _).trans hA
  calc (cdfAction (2 * (n : ℤ)) - cdfAction n) * Real.log n ≤
      C * (Real.log (Real.log n) / Real.log n) * Real.log n := mul_le_mul_of_nonneg_right hnum h2.le
    _ = C * Real.log (Real.log n) := by field_simp
    _ ≤ 2 * C * cdfAction n := by nlinarith

theorem tendsto_dyadicRatio : Tendsto dyadicRatio atTop (𝓝 0) := by
  obtain ⟨C, hC0, N₀, hN₀⟩ := exists_dyadicRatio_le
  have hℓt : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hup : Tendsto (fun n : ℕ => C / Real.log n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hℓt
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact (dyadicRatio_mem_Ioo hn).1.le
  · filter_upwards [eventually_ge_atTop N₀] with n hn
    exact hN₀ n hn

/-- **Uniform positivity of the paired-block metric**: a single `c > 0` with
`c ≤ 1 − r_n` and `1 + r_n ≤ 2` for every `n ≥ 1`, i.e. `c I ≤ G₀ ≤ 2 I`. -/
theorem exists_pos_le_one_sub_dyadicRatio :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → c ≤ 1 - dyadicRatio n ∧ 1 + dyadicRatio n ≤ 2 := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (tendsto_dyadicRatio.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)))
  have hfin : ∀ K : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → n < K → c ≤ 1 - dyadicRatio n := by
    intro K
    induction K with
    | zero => exact ⟨1, one_pos, fun n _ h => absurd h (Nat.not_lt_zero n)⟩
    | succ K ih =>
      obtain ⟨c, hc, h⟩ := ih
      by_cases hK : 1 ≤ K
      · have hr : dyadicRatio K < 1 := (dyadicRatio_mem_Ioo hK).2
        refine ⟨min c (1 - dyadicRatio K), lt_min hc (by linarith), fun n hn hnK => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hnK with h1 | h1
        · exact (min_le_left _ _).trans (h n hn h1)
        · rw [h1]; exact min_le_right _ _
      · refine ⟨c, hc, fun n hn hnK => h n hn ?_⟩
        omega
  obtain ⟨c, hc, hcK⟩ := hfin N
  refine ⟨min c (1 / 2), lt_min hc (by norm_num), fun n hn => ⟨?_, ?_⟩⟩
  · rcases lt_or_ge n N with h | h
    · exact (min_le_left _ _).trans (hcK n hn h)
    · have := hN n h
      exact (min_le_right _ _).trans (by linarith)
  · have hr : dyadicRatio n < 1 := (dyadicRatio_mem_Ioo hn).2
    linarith

end

end RHTower
