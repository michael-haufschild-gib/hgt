import Mathlib

/-!
# The Euler–Mascheroni constant as an exponential integral

Mathlib defines `γ` by `harmonic n - log n` and separately proves `Γ'(1) = -γ`.  Differentiating
the Gamma *integral* under the integral sign — which mathlib also owns — identifies that derivative
with `∫₀^∞ e^{-t} log t dt`.  Comparing the two gives the classical representation

`∫₀^∞ e^{-t} log t dt = -γ`,

which is the analytic input behind the exponential-integral asymptotic
`Ein(a) = ∫₀^a (1 - e^{-s}) ds/s = γ + log a + o(1)`.
-/

open MeasureTheory Filter Topology Set

namespace RHTower

/-- **`Γ'(1)` in integral form.** -/
theorem integral_exp_neg_mul_log_complex :
    (∫ t : ℝ in Ioi 0, ((t : ℂ)) ^ ((1 : ℂ) - 1) * ((Real.log t : ℂ) * (Real.exp (-t) : ℂ)))
      = -(Real.eulerMascheroniConstant : ℂ) := by
  have hre : (0 : ℝ) < (1 : ℂ).re := by norm_num
  have hint := Complex.hasDerivAt_GammaIntegral hre
  have hgam := Complex.hasDerivAt_Gamma_one
  have heq : Complex.GammaIntegral =ᶠ[nhds (1 : ℂ)] Complex.Gamma := by
    have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hre] with s hs
    exact (Complex.Gamma_eq_integral hs).symm
  have hgam' : HasDerivAt Complex.GammaIntegral (-(Real.eulerMascheroniConstant : ℂ)) 1 :=
    hgam.congr_of_eventuallyEq heq
  exact hint.unique hgam'

/-- **The Euler–Mascheroni constant as an exponential integral.** -/
theorem integral_exp_neg_mul_log :
    (∫ t : ℝ in Ioi 0, Real.log t * Real.exp (-t)) = -Real.eulerMascheroniConstant := by
  have h := integral_exp_neg_mul_log_complex
  have hsimp : (∫ t : ℝ in Ioi 0, ((t : ℂ)) ^ ((1 : ℂ) - 1)
      * ((Real.log t : ℂ) * (Real.exp (-t) : ℂ)))
      = ∫ t : ℝ in Ioi 0, ((Real.log t * Real.exp (-t) : ℝ) : ℂ) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with t
    rw [sub_self, Complex.cpow_zero, one_mul]
    push_cast
    ring
  rw [hsimp, integral_complex_ofReal] at h
  exact_mod_cast h

/-! ## The two Frullani constants -/

/-- The regularized head `∫₀¹ (1 - e^{-t}) dt/t`, with the integrand extended by zero at the
origin. -/
noncomputable def einProfile (t : ℝ) : ℝ := if t = 0 then 0 else (1 - Real.exp (-t)) / t

theorem einProfile_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ einProfile t := by
  rw [einProfile]
  split_ifs with h
  · exact le_rfl
  · have ht0 : 0 < t := lt_of_le_of_ne ht (Ne.symm h)
    have : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    positivity

theorem einProfile_le_one {t : ℝ} (ht : 0 ≤ t) : einProfile t ≤ 1 := by
  rw [einProfile]
  split_ifs with h
  · norm_num
  · have ht0 : 0 < t := lt_of_le_of_ne ht (Ne.symm h)
    rw [div_le_one ht0]
    have := Real.add_one_le_exp (-t)
    linarith

theorem continuousOn_einProfile_Ioc {a : ℝ} :
    ContinuousOn einProfile (Set.Ioc (0 : ℝ) a) := by
  have hquot : ContinuousOn (fun t : ℝ => (1 - Real.exp (-t)) / t) (Set.Ioc (0 : ℝ) a) :=
    ((continuousOn_const.sub
      (Real.continuous_exp.comp continuous_neg).continuousOn).div continuousOn_id
      (fun t ht => ne_of_gt ht.1))
  refine hquot.congr fun t ht => ?_
  rw [einProfile, if_neg (ne_of_gt ht.1)]

theorem intervalIntegrable_einProfile {a : ℝ} (ha : 0 ≤ a) :
    IntervalIntegrable einProfile volume 0 a := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha]
  exact ⟨(continuousOn_einProfile_Ioc).aestronglyMeasurable measurableSet_Ioc,
    MeasureTheory.HasFiniteIntegral.restrict_of_bounded (C := 1) measure_Ioc_lt_top
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => by
        rw [Real.norm_eq_abs, abs_of_nonneg (einProfile_nonneg ht.1.le)]
        exact einProfile_le_one ht.1.le)⟩

/-- `C₁ = ∫₀¹ (1 - e^{-t}) dt/t`. -/
noncomputable def frullaniHead : ℝ := ∫ t in (0 : ℝ)..1, einProfile t

/-- `C₂ = ∫₁^∞ e^{-t} dt/t`. -/
noncomputable def frullaniTail : ℝ := ∫ t in Set.Ioi (1 : ℝ), Real.exp (-t) / t

/-! ## The head: `∫₀¹ e^{-t} log t dt = -C₁` -/

theorem intervalIntegrable_log_mul_exp {a b : ℝ} :
    IntervalIntegrable (fun t : ℝ => Real.log t * Real.exp (-t)) volume a b :=
  (intervalIntegral.intervalIntegrable_log' ).mul_continuousOn
    ((Real.continuous_exp.comp continuous_neg).continuousOn)

theorem integral_exp_neg_mul_log_head :
    (∫ t in (0 : ℝ)..1, Real.log t * Real.exp (-t)) = -frullaniHead := by
  set F : ℝ → ℝ := fun t => (Real.exp (-t) - 1) * Real.log t with hFdef
  set F' : ℝ → ℝ := fun t => -(Real.log t * Real.exp (-t)) - einProfile t with hF'def
  have hcont : ContinuousOn F (Set.Icc 0 1) := by
    intro t ht
    rcases eq_or_ne t 0 with rfl | htne
    · have hval : F 0 = 0 := by rw [hFdef]; simp
      rw [ContinuousWithinAt, hval]
      refine squeeze_zero_norm' (a := fun x : ℝ => |x * Real.log x|) ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with x hx
        rcases eq_or_lt_of_le hx.1 with h0 | h0
        · rw [hFdef]
          simp [← h0]
        · have hx1 : |Real.exp (-x) - 1| ≤ x := by
            have h1 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
            have h2 : 1 - x ≤ Real.exp (-x) := by
              have := Real.add_one_le_exp (-x); linarith
            rw [abs_of_nonpos (by linarith)]
            linarith
          rw [hFdef]
          simp only [Real.norm_eq_abs, abs_mul]
          rw [abs_of_pos h0]
          exact mul_le_mul_of_nonneg_right hx1 (abs_nonneg _)
      · have h := (Real.continuous_mul_log.tendsto 0).comp
          (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id (s := Set.Icc (0:ℝ) 1))
        have habs := (continuous_abs.tendsto ((0:ℝ) * Real.log 0)).comp h
        simpa [Function.comp_def] using habs
    · have hc : ContinuousWithinAt (fun t : ℝ => (Real.exp (-t) - 1) * Real.log t)
          (Set.Icc 0 1) t :=
        (((Real.continuous_exp.comp continuous_neg).continuousWithinAt).sub
          continuousWithinAt_const).mul (Real.continuousAt_log htne).continuousWithinAt
      exact hc
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivWithinAt F (F' x) (Set.Ioi x) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t) - 1) (-Real.exp (-x)) x := by
      have := ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).sub_const 1
      simpa [Function.comp_def] using this
    have h2 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0
    have h3 := h1.mul h2
    refine (h3.congr_deriv ?_).hasDerivWithinAt
    simp only [hF'def, einProfile, if_neg hx0]
    field_simp
    ring
  have hint : IntervalIntegrable F' volume 0 1 := by
    rw [hF'def]
    exact (intervalIntegrable_log_mul_exp.neg).sub (intervalIntegrable_einProfile (by norm_num))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    (by norm_num : (0:ℝ) ≤ 1) hcont hderiv hint
  have hF1 : F 1 = 0 := by rw [hFdef]; simp
  have hF0 : F 0 = 0 := by rw [hFdef]; simp
  rw [hF1, hF0, sub_zero] at hftc
  have hneg : IntervalIntegrable (fun y : ℝ => -(Real.log y * Real.exp (-y))) volume 0 1 := by
    have h := (intervalIntegrable_log_mul_exp (a := (0:ℝ)) (b := 1)).neg
    exact h.congr (fun y _ => rfl)
  have hbeta : (∫ y in (0 : ℝ)..1, F' y)
      = ∫ y in (0 : ℝ)..1, (-(Real.log y * Real.exp (-y)) - einProfile y) := rfl
  rw [hbeta, intervalIntegral.integral_sub hneg (intervalIntegrable_einProfile (by norm_num)),
    intervalIntegral.integral_neg] at hftc
  rw [frullaniHead]
  linarith

/-! ## The tail: `∫₁^∞ e^{-t} log t dt = C₂` -/

theorem integrableOn_exp_neg_Ioi_one :
    IntegrableOn (fun t : ℝ => Real.exp (-t)) (Set.Ioi (1 : ℝ)) volume := by
  have h := Real.GammaIntegral_convergent (s := 1) (by norm_num)
  have h' : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ ((1 : ℝ) - 1)) (Set.Ioi 0) volume := h
  refine (h'.mono_set (Set.Ioi_subset_Ioi (by norm_num))).congr_fun ?_ measurableSet_Ioi
  intro x hx
  simp

theorem integrableOn_lin_exp_neg_Ioi_one :
    IntegrableOn (fun t : ℝ => t * Real.exp (-t)) (Set.Ioi (1 : ℝ)) volume := by
  have h := Real.GammaIntegral_convergent (s := 2) (by norm_num)
  have h' : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ ((2 : ℝ) - 1)) (Set.Ioi 0) volume := h
  refine (h'.mono_set (Set.Ioi_subset_Ioi (by norm_num))).congr_fun ?_ measurableSet_Ioi
  intro x hx
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  simp only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
  ring

theorem integrableOn_exp_neg_div_Ioi_one :
    IntegrableOn (fun t : ℝ => Real.exp (-t) / t) (Set.Ioi (1 : ℝ)) volume := by
  refine MeasureTheory.Integrable.mono' integrableOn_exp_neg_Ioi_one ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact ((Real.continuous_exp.comp continuous_neg).continuousOn).div continuousOn_id
      (fun t ht => ne_of_gt (lt_trans zero_lt_one ht))
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ ht0]
    nlinarith [Real.exp_pos (-t)]

theorem integrableOn_log_mul_exp_Ioi_one :
    IntegrableOn (fun t : ℝ => Real.log t * Real.exp (-t)) (Set.Ioi (1 : ℝ)) volume := by
  refine MeasureTheory.Integrable.mono' integrableOn_lin_exp_neg_Ioi_one ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact (ContinuousOn.mul (Real.continuousOn_log.mono (fun t ht => ne_of_gt
      (lt_trans zero_lt_one ht))) ((Real.continuous_exp.comp continuous_neg).continuousOn))
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
    have hlog : 0 ≤ Real.log t := Real.log_nonneg ht1
    have hlt : Real.log t ≤ t := le_trans (Real.log_le_sub_one_of_pos ht0) (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right hlt (Real.exp_nonneg _)

theorem integral_exp_neg_mul_log_tail :
    (∫ t in Set.Ioi (1 : ℝ), Real.log t * Real.exp (-t)) = frullaniTail := by
  set G : ℝ → ℝ := fun t => -(Real.exp (-t) * Real.log t) with hGdef
  set G' : ℝ → ℝ := fun t => Real.log t * Real.exp (-t) - Real.exp (-t) / t with hG'def
  have hcont : ContinuousWithinAt G (Set.Ici 1) 1 := by
    refine ContinuousWithinAt.neg ?_
    exact ((Real.continuous_exp.comp continuous_neg).continuousWithinAt).mul
      (Real.continuousAt_log (by norm_num)).continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioi (1 : ℝ), HasDerivAt G (G' x) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-x)) x := by
      have := (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
      simpa [Function.comp_def] using this
    have h2 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0
    have h3 := (h1.mul h2).neg
    refine h3.congr_deriv ?_
    rw [hG'def]
    field_simp
    ring
  have hint : IntegrableOn G' (Set.Ioi (1 : ℝ)) volume := by
    rw [hG'def]
    exact integrableOn_log_mul_exp_Ioi_one.sub integrableOn_exp_neg_div_Ioi_one
  have hlim : Tendsto G atTop (nhds 0) := by
    refine squeeze_zero_norm' (a := fun t : ℝ => t * Real.exp (-t)) ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
      have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
      have hlt : Real.log t ≤ t := le_trans (Real.log_le_sub_one_of_pos ht0) (by linarith)
      rw [hGdef]
      simp only [Real.norm_eq_abs, abs_neg, abs_mul,
        abs_of_nonneg (Real.exp_nonneg (-t)), abs_of_nonneg hlog]
      nlinarith [Real.exp_nonneg (-t)]
    · have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
      simpa using this
  have hftc := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  have hG1 : G 1 = 0 := by rw [hGdef]; simp
  rw [hG1, sub_zero] at hftc
  rw [hG'def] at hftc
  rw [MeasureTheory.integral_sub integrableOn_log_mul_exp_Ioi_one
    integrableOn_exp_neg_div_Ioi_one] at hftc
  rw [frullaniTail]
  linarith

/-! ## The Frullani identity for the Euler–Mascheroni constant -/

theorem integrableOn_log_mul_exp_Ioc :
    IntegrableOn (fun t : ℝ => Real.log t * Real.exp (-t)) (Set.Ioc (0 : ℝ) 1) volume := by
  have h := intervalIntegrable_log_mul_exp (a := (0 : ℝ)) (b := 1)
  rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at h

/-- **The Frullani representation of `γ`.**  `γ = ∫₀¹ (1 - e^{-t}) dt/t - ∫₁^∞ e^{-t} dt/t`. -/
theorem frullani_eq_eulerMascheroni :
    frullaniHead - frullaniTail = Real.eulerMascheroniConstant := by
  have hsplit : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) = Set.Ioi (0 : ℝ) :=
    Set.Ioc_union_Ioi_eq_Ioi (by norm_num)
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi (1 : ℝ)) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx' (not_lt.mpr hx.2)
  have hunion := MeasureTheory.setIntegral_union (μ := volume)
    (f := fun t : ℝ => Real.log t * Real.exp (-t)) hdisj measurableSet_Ioi
    integrableOn_log_mul_exp_Ioc integrableOn_log_mul_exp_Ioi_one
  rw [hsplit] at hunion
  have hIoc : (∫ t in Set.Ioc (0 : ℝ) 1, Real.log t * Real.exp (-t))
      = ∫ t in (0 : ℝ)..1, Real.log t * Real.exp (-t) :=
    (intervalIntegral.integral_of_le (by norm_num)).symm
  rw [hIoc, integral_exp_neg_mul_log_head, integral_exp_neg_mul_log_tail,
    integral_exp_neg_mul_log] at hunion
  linarith

end RHTower
