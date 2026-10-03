import GaloisForLFunctions.RHTower.ThetaRenewalCoshFactorization

/-!
# A logarithmic-integral comparison with an explicit Laplace transform

`L(t) = ∫_0^t (e^u - 1)/u du` (the integrand is the slope of `exp` at `0`, continuous with value `1`
at `0`).  For real `σ > 1`

```text
∫_0^∞ (e^u - 1)/u · e^{-σu} du = log(σ/(σ - 1)),     ∫_0^∞ L(t) e^{-σt} dt = log(σ/(σ - 1))/σ,
```

the first by Frullani's identity (`thetaRenewalFrullani_eq` after the scaling `t = 4(σ - ½)u`), the
second by parts.  And `li(x) = ∫_2^x dt/log t ≤ L(log x) + log log x + 1` for `x ≥ 2`, since
`d/dx [li(x) - L(log x)] = 1/(x log x)`.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- The integrand `(e^u - 1)/u`, continuous with value `1` at `0`. -/
def logIntegralKernel (u : ℝ) : ℝ := dslope Real.exp 0 u

theorem logIntegralKernel_of_ne {u : ℝ} (hu : u ≠ 0) :
    logIntegralKernel u = (Real.exp u - 1) / u := by
  rw [logIntegralKernel, dslope_of_ne _ hu, slope_def_field, Real.exp_zero, sub_zero]

theorem logIntegralKernel_zero : logIntegralKernel 0 = 1 := by
  rw [logIntegralKernel, dslope_same, Real.deriv_exp, Real.exp_zero]

theorem continuous_logIntegralKernel : Continuous logIntegralKernel := by
  rw [continuous_iff_continuousAt]
  intro u
  rcases eq_or_ne u 0 with rfl | hu
  · exact continuousAt_dslope_same.mpr Real.differentiableAt_exp
  · exact (continuousAt_dslope_of_ne hu).mpr Real.continuous_exp.continuousAt

theorem logIntegralKernel_pos (u : ℝ) : 0 < logIntegralKernel u := by
  rcases eq_or_ne u 0 with rfl | hu
  · rw [logIntegralKernel_zero]; norm_num
  · rw [logIntegralKernel_of_ne hu]
    rcases lt_or_gt_of_ne hu with h | h
    · exact div_pos_of_neg_of_neg (by linarith [Real.exp_lt_one_iff.mpr h]) h
    · exact div_pos (by linarith [Real.one_lt_exp_iff.mpr h]) h

theorem logIntegralKernel_le_exp {u : ℝ} (hu : 0 ≤ u) : logIntegralKernel u ≤ Real.exp u := by
  rcases eq_or_lt_of_le hu with rfl | hu
  · rw [logIntegralKernel_zero, Real.exp_zero]
  · rw [logIntegralKernel_of_ne hu.ne', div_le_iff₀ hu]
    have h1 := Real.add_one_le_exp (-u)
    have h2 : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos u]

/-- The comparison function `L(t) = ∫_0^t (e^u - 1)/u du`. -/
def logIntegralCompare (t : ℝ) : ℝ := ∫ u in (0 : ℝ)..t, logIntegralKernel u

theorem hasDerivAt_logIntegralCompare (t : ℝ) :
    HasDerivAt logIntegralCompare (logIntegralKernel t) t :=
  intervalIntegral.integral_hasDerivAt_right
    (continuous_logIntegralKernel.intervalIntegrable _ _)
    (continuous_logIntegralKernel.stronglyMeasurableAtFilter _ _)
    continuous_logIntegralKernel.continuousAt

theorem continuous_logIntegralCompare : Continuous logIntegralCompare :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_logIntegralCompare t).continuousAt

theorem logIntegralCompare_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ logIntegralCompare t :=
  intervalIntegral.integral_nonneg ht fun u _ => (logIntegralKernel_pos u).le

theorem logIntegralCompare_le_exp {t : ℝ} (ht : 0 ≤ t) : logIntegralCompare t ≤ Real.exp t := by
  have h1 : logIntegralCompare t ≤ ∫ u in (0 : ℝ)..t, Real.exp u :=
    intervalIntegral.integral_mono_on ht (continuous_logIntegralKernel.intervalIntegrable _ _)
      (Real.continuous_exp.intervalIntegrable _ _) fun u hu => logIntegralKernel_le_exp hu.1
  rw [integral_exp, Real.exp_zero] at h1
  linarith


/-- **Frullani for the kernel.**  `∫_0^∞ (e^u - 1)/u · e^{-σu} du = log(σ/(σ - 1))`, `σ > 1`. -/
theorem integral_logIntegralKernel_mul_exp {σ : ℝ} (hσ : 1 < σ) :
    ∫ u in Ioi (0 : ℝ), logIntegralKernel u * Real.exp (-σ * u) = Real.log (σ / (σ - 1)) := by
  set c : ℝ := 4 * (σ - 1 / 2) with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  set s : ℝ := 1 / (2 * c) with hs
  have hs0 : 0 < s := by rw [hs]; positivity
  have hs4 : s < 1 / 4 := by
    rw [hs, div_lt_div_iff₀ (by positivity) (by norm_num)]; rw [hc]; linarith
  set f : ℝ → ℝ := fun t => Real.exp (-(t / 4)) * Real.sinh (s * t) / t with hf
  have hpt : ∀ u ∈ Ioi (0 : ℝ), logIntegralKernel u * Real.exp (-σ * u) = 2 * c * f (c * u) := by
    intro u hu
    have hu0 : 0 < u := hu
    rw [logIntegralKernel_of_ne hu0.ne', hf]
    simp only
    rw [Real.sinh_eq]
    have hsc : s * (c * u) = u / 2 := by rw [hs]; field_simp
    rw [hsc]
    have e1 : Real.exp (-(c * u / 4)) * ((Real.exp (u / 2) - Real.exp (-(u / 2))) / 2)
        = (Real.exp u * Real.exp (-σ * u) - Real.exp (-σ * u)) / 2 := by
      have h1 : Real.exp (-(c * u / 4)) * Real.exp (u / 2) = Real.exp u * Real.exp (-σ * u) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; rw [hc]; ring
      have h2 : Real.exp (-(c * u / 4)) * Real.exp (-(u / 2)) = Real.exp (-σ * u) := by
        rw [← Real.exp_add]; congr 1; rw [hc]; ring
      rw [mul_div_assoc', mul_sub, h1, h2]
    rw [e1]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    integral_comp_mul_left_Ioi f 0 hc0, mul_zero, smul_eq_mul]
  -- Frullani from the corpus
  have hF := thetaRenewalFrullani_eq (s := (s : ℂ))
    (by rw [Complex.ofReal_re, abs_of_pos hs0]; exact hs4)
  have hint : thetaRenewalFrullani (s : ℂ) = ((∫ t in Ioi (0 : ℝ), f t : ℝ) : ℂ) := by
    rw [thetaRenewalFrullani, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [hf]
    push_cast
    rfl
  have hphase : thetaRenewalPhase (s : ℂ)
      = (((Real.log (1 / 4 + s) - Real.log (1 / 4 - s)) / 2 : ℝ) : ℂ) := by
    rw [thetaRenewalPhase]
    push_cast
    rw [Complex.ofReal_log (by linarith), Complex.ofReal_log (by linarith)]
    push_cast
    ring
  rw [hint, hphase] at hF
  have hreal := Complex.ofReal_injective hF
  rw [hreal]
  have hratio : (1 / 4 + s) / (1 / 4 - s) = σ / (σ - 1) := by
    have h1 : σ - 1 ≠ 0 := by linarith
    have h2 : (1 : ℝ) / 4 - s ≠ 0 := by linarith
    rw [div_eq_div_iff h2 h1, hs, hc, show (2 : ℝ) * (4 * (σ - 1 / 2)) = 8 * σ - 4 by ring]
    have hk : (8 : ℝ) * σ - 4 ≠ 0 := by linarith
    field_simp
    ring
  rw [← hratio, Real.log_div (by linarith) (by linarith)]
  field_simp

/-- **The Laplace transform of `L`.**  `∫_0^∞ L(t) e^{-σt} dt = log(σ/(σ - 1))/σ`, `σ > 1`. -/
theorem integral_logIntegralCompare_mul_exp {σ : ℝ} (hσ : 1 < σ) :
    ∫ t in Ioi (0 : ℝ), logIntegralCompare t * Real.exp (-σ * t) = Real.log (σ / (σ - 1)) / σ := by
  have hσ0 : 0 < σ := by linarith
  have hdom : IntegrableOn (fun t => Real.exp ((1 - σ) * t)) (Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hexp : ∀ t, Real.exp t * Real.exp (-σ * t) = Real.exp ((1 - σ) * t) := by
    intro t; rw [← Real.exp_add]; ring_nf
  have hL : IntegrableOn (fun t => logIntegralCompare t * Real.exp (-σ * t)) (Ioi (0 : ℝ)) := by
    refine hdom.mono' ((continuous_logIntegralCompare.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).aestronglyMeasurable) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (logIntegralCompare_nonneg (le_of_lt ht))
      (Real.exp_pos _).le), ← hexp]
    exact mul_le_mul_of_nonneg_right (logIntegralCompare_le_exp (le_of_lt ht)) (Real.exp_pos _).le
  have hK : IntegrableOn (fun t => logIntegralKernel t * Real.exp (-σ * t)) (Ioi (0 : ℝ)) := by
    refine hdom.mono' ((continuous_logIntegralKernel.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).aestronglyMeasurable) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (logIntegralKernel_pos t).le
      (Real.exp_pos _).le), ← hexp]
    exact mul_le_mul_of_nonneg_right (logIntegralKernel_le_exp (le_of_lt ht)) (Real.exp_pos _).le
  -- integration by parts
  set G : ℝ → ℝ := fun t => -(logIntegralCompare t * Real.exp (-σ * t) / σ) with hG
  have hGd : ∀ t, HasDerivAt G (logIntegralCompare t * Real.exp (-σ * t)
      - logIntegralKernel t * Real.exp (-σ * t) / σ) t := by
    intro t
    have he : HasDerivAt (fun y => Real.exp (-σ * y)) (Real.exp (-σ * t) * (-σ)) t := by
      have := ((hasDerivAt_id t).const_mul (-σ)).exp
      simpa using this
    have h1 := (hasDerivAt_logIntegralCompare t).mul he
    have h2 := (h1.div_const σ).neg
    have hσne : σ ≠ 0 := hσ0.ne'
    refine h2.congr_deriv ?_
    field_simp
    ring
  have hlim : Tendsto G atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => Real.exp ((1 - σ) * t) / σ) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg
        (by linarith : 1 - σ < 0))).div_const σ
      simpa using this
    refine squeeze_zero_norm' ?_ h1
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [hG, norm_neg, Real.norm_eq_abs, abs_div, abs_of_pos hσ0,
      abs_of_nonneg (mul_nonneg (logIntegralCompare_nonneg ht) (Real.exp_pos _).le), ← hexp]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (logIntegralCompare_le_exp ht)
      (Real.exp_pos _).le) hσ0.le
  have hibp := integral_Ioi_of_hasDerivAt_of_tendsto (f := G) (a := 0)
    (hGd 0).continuousAt.continuousWithinAt (fun t _ => hGd t) (hL.sub (hK.div_const σ)) hlim
  have hG0 : G 0 = 0 := by
    rw [hG]; simp [logIntegralCompare]
  rw [hG0, sub_zero, integral_sub hL (hK.div_const σ), integral_div,
    integral_logIntegralKernel_mul_exp hσ] at hibp
  linarith

/-- **The logarithmic integral through `L`.**
`li(x) = L(log x) - L(log 2) + log(log x/log 2)` for `x ≥ 2`. -/
theorem integral_inv_log_eq_logIntegralCompare {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in (2 : ℝ)..x, 1 / Real.log t
      = logIntegralCompare (Real.log x) - logIntegralCompare (Real.log 2)
        + Real.log (Real.log x / Real.log 2) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  -- change of variables
  have hcv : ∫ t in (2 : ℝ)..x, 1 / Real.log t
      = ∫ w in (Real.log 2)..(Real.log x), Real.exp w / w := by
    have h := intervalIntegral.integral_comp_mul_deriv' (a := Real.log 2) (b := Real.log x)
      (f := Real.exp) (f' := Real.exp) (g := fun t => 1 / Real.log t)
      (fun w _ => Real.hasDerivAt_exp w) Real.continuous_exp.continuousOn ?_
    · rw [Real.exp_log (by norm_num), Real.exp_log (by linarith)] at h
      rw [← h]
      refine intervalIntegral.integral_congr fun w _ => ?_
      simp only [Function.comp, Real.log_exp]
      ring
    · intro t ht
      obtain ⟨w, hw, rfl⟩ := ht
      rw [Set.uIcc_of_le hlx] at hw
      have hw0 : 0 < w := lt_of_lt_of_le hl2 hw.1
      refine ContinuousAt.continuousWithinAt ?_
      refine continuousAt_const.div (Real.continuousAt_log (Real.exp_pos w).ne') ?_
      rw [Real.log_exp]; exact hw0.ne'
  -- the comparison on `[log 2, log x]`
  have hsplit : logIntegralCompare (Real.log x)
      = (∫ u in (0 : ℝ)..(Real.log 2), logIntegralKernel u)
        + ∫ u in (Real.log 2)..(Real.log x), logIntegralKernel u := by
    rw [logIntegralCompare, intervalIntegral.integral_add_adjacent_intervals
      (continuous_logIntegralKernel.intervalIntegrable _ _)
      (continuous_logIntegralKernel.intervalIntegrable _ _)]
  have hcont1 : ContinuousOn (fun w => Real.exp w / w) (Set.uIcc (Real.log 2) (Real.log x)) := by
    refine Real.continuous_exp.continuousOn.div continuousOn_id fun w hw => ?_
    rw [Set.uIcc_of_le hlx] at hw
    exact (lt_of_lt_of_le hl2 hw.1).ne'
  have hcont2 : ContinuousOn (fun w : ℝ => 1 / w) (Set.uIcc (Real.log 2) (Real.log x)) := by
    refine continuousOn_const.div continuousOn_id fun w hw => ?_
    rw [Set.uIcc_of_le hlx] at hw
    exact (lt_of_lt_of_le hl2 hw.1).ne'
  have hker : ∫ u in (Real.log 2)..(Real.log x), logIntegralKernel u
      = (∫ w in (Real.log 2)..(Real.log x), Real.exp w / w)
        - ∫ w in (Real.log 2)..(Real.log x), 1 / w := by
    rw [← intervalIntegral.integral_sub (hcont1.intervalIntegrable) (hcont2.intervalIntegrable)]
    refine intervalIntegral.integral_congr fun w hw => ?_
    rw [Set.uIcc_of_le hlx] at hw
    have hw0 : 0 < w := lt_of_lt_of_le hl2 hw.1
    show logIntegralKernel w = Real.exp w / w - 1 / w
    rw [logIntegralKernel_of_ne hw0.ne', sub_div]
  have hinv : ∫ w in (Real.log 2)..(Real.log x), 1 / w = Real.log (Real.log x / Real.log 2) := by
    rw [← integral_inv_of_pos hl2 (by linarith)]
    exact intervalIntegral.integral_congr fun w _ => by rw [one_div]
  rw [hcv]
  unfold logIntegralCompare at hsplit ⊢
  linarith

/-- `li(x) ≤ L(log x) + log log x + 1` for `x ≥ 2`. -/
theorem integral_inv_log_le_logIntegralCompare {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in (2 : ℝ)..x, 1 / Real.log t
      ≤ logIntegralCompare (Real.log x) + Real.log (Real.log x) + 1 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hhead : 0 ≤ logIntegralCompare (Real.log 2) := logIntegralCompare_nonneg hl2.le
  have hll : Real.log (Real.log x / Real.log 2) ≤ Real.log (Real.log x) + 1 := by
    rw [Real.log_div (by linarith) hl2.ne']
    have : -1 ≤ Real.log (Real.log 2) := by
      rw [show (-1 : ℝ) = Real.log (Real.exp (-1)) from (Real.log_exp _).symm]
      apply Real.log_le_log (Real.exp_pos _)
      have := Real.exp_neg_one_lt_d9
      have := Real.log_two_gt_d9
      linarith
    linarith
  rw [integral_inv_log_eq_logIntegralCompare hx]
  linarith

/-- `L(log x) - L(log 2) ≤ li(x)` for `x ≥ 2`. -/
theorem logIntegralCompare_sub_le_integral_inv_log {x : ℝ} (hx : 2 ≤ x) :
    logIntegralCompare (Real.log x) - logIntegralCompare (Real.log 2)
      ≤ ∫ t in (2 : ℝ)..x, 1 / Real.log t := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have h : 0 ≤ Real.log (Real.log x / Real.log 2) :=
    Real.log_nonneg ((one_le_div hl2).mpr hlx)
  rw [integral_inv_log_eq_logIntegralCompare hx]
  linarith

end

end RHTower
