import GaloisForLFunctions.RHTower.ThetaQuantileProfileCalculus

/-!
# Dyadic inequalities for the theta CDF action

For `n ≥ 1`:

* `Φ_{2n} = ∫₀¹ q(u/2)(1 − cos 2πnu) du` (reflection `q(1−t) = q(t)` and `t = u/2`);
* strict concavity of `h = 1/q` with `h > 0` gives `q(u/2) < 2 q(u)`, hence `Φ_{2n} < 2Φ_n`;
* with `W_n = (1 − cos 2πnt)²/(2(2πn)²)`, `W_n'' = cos 2πnt − cos 4πnt`, two integrations by parts
  give `Φ_{2n} − Φ_n = ∫₀¹ q'' W_n > 0` (the endpoint terms vanish by `t³q → 0`, `t⁴q' → 0`);
* so `r_n = (Φ_{2n} − Φ_n)/Φ_n ∈ (0, 1)`.
-/

open MeasureTheory Set Filter Topology intervalIntegral

namespace RHTower

noncomputable section

open HedenmalmThetaSource HedenmalmQuantile GaloisForLFunctions.HTGeometry

/-! ## Interval-integral form of the action -/

theorem integrableOn_Icc_of_Ioo {f : ℝ → ℝ} (hf : IntegrableOn f (Ioo (0 : ℝ) 1)) :
    IntegrableOn f (Icc (0 : ℝ) 1) :=
  (integrableOn_Icc_iff_integrableOn_Ioo (f := f) (a := 0) (b := 1)).2 hf

theorem intervalIntegrable_of_integrableOn_unitIoo {f : ℝ → ℝ} (hf : IntegrableOn f (Ioo (0 : ℝ) 1))
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) : IntervalIntegrable f volume a b := by
  refine (IntegrableOn.intervalIntegrable ?_)
  exact (integrableOn_Icc_of_Ioo hf).mono_set (uIcc_subset_Icc ha hb)

/-- The action integrand `g_k(t) = q(t)(1 − cos 2πkt)`. -/
def actionIntegrand (k : ℤ) (t : ℝ) : ℝ := thetaQuantileSpeed t * (1 - Real.cos (2 * Real.pi * k * t))

theorem cdfAction_eq_intervalIntegral (k : ℤ) : cdfAction k = ∫ t in (0 : ℝ)..1, actionIntegrand k t := by
  rw [cdfAction_eq_quantileSpeed, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  rfl

theorem actionIntegrand_nonneg (k : ℤ) (t : ℝ) : 0 ≤ actionIntegrand k t :=
  mul_nonneg (thetaQuantileSpeed_pos t).le (by linarith [Real.cos_le_one (2 * Real.pi * k * t)])

theorem one_sub_cos_pos {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) (1 / n)) :
    0 < 1 - Real.cos (2 * Real.pi * n * u) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : 0 < 2 * Real.pi * n * u := by have := hu.1; positivity
  have h2 : 2 * Real.pi * n * u < 2 * Real.pi := by
    have := hu.2
    rw [lt_div_iff₀ hnR] at this
    nlinarith [Real.pi_pos]
  have hne : Real.cos (2 * Real.pi * n * u) ≠ 1 := fun h =>
    h1.ne' ((Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos]) h2).1 h)
  have := Real.cos_le_one (2 * Real.pi * n * u)
  exact sub_pos.2 (lt_of_le_of_ne this hne)

theorem cdfAction_pos {n : ℕ} (hn : 1 ≤ n) : 0 < cdfAction n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h1n : (1 : ℝ) / n ≤ 1 := by rw [div_le_one hnR]; exact_mod_cast hn
  rw [cdfAction_eq_intervalIntegral]
  have hint : IntervalIntegrable (actionIntegrand n) volume 0 1 :=
    intervalIntegrable_of_integrableOn_unitIoo (integrableOn_thetaQuantileSpeed_mul_one_sub_cos n)
      ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
  calc (0 : ℝ) < ∫ t in (0 : ℝ)..(1 / n), actionIntegrand n t := by
        refine intervalIntegral_pos_of_pos_on (hint.mono_set ?_) (fun u hu => ?_) (by positivity)
        · rw [uIcc_of_le (by positivity), uIcc_of_le zero_le_one]
          exact Icc_subset_Icc le_rfl h1n
        · exact mul_pos (thetaQuantileSpeed_pos u) (by exact_mod_cast one_sub_cos_pos hn hu)
    _ ≤ ∫ t in (0 : ℝ)..1, actionIntegrand n t :=
        integral_mono_interval le_rfl (by positivity) h1n
          (Eventually.of_forall fun t => actionIntegrand_nonneg n t) hint

/-! ## The dilation identity -/

theorem actionIntegrand_one_sub (k : ℤ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    actionIntegrand k (1 - t) = actionIntegrand k t := by
  simp only [actionIntegrand, thetaQuantileSpeed]
  rw [quantileSpeed_one_sub ht,
    show 2 * Real.pi * k * (1 - t) = -(2 * Real.pi * k * t - (k : ℝ) * (2 * Real.pi)) by ring,
    Real.cos_neg, Real.cos_sub_int_mul_two_pi]

/-- `Φ_{2n} = ∫₀¹ q(u/2)(1 − cos 2πnu) du`. -/
theorem cdfAction_two_mul_eq (n : ℕ) :
    cdfAction (2 * (n : ℤ)) = ∫ u in (0 : ℝ)..1, thetaQuantileSpeed (u / 2) * (1 - Real.cos (2 * Real.pi * n * u)) := by
  set g := actionIntegrand (2 * (n : ℤ))
  have hint := integrableOn_thetaQuantileSpeed_mul_one_sub_cos (2 * (n : ℤ))
  have hg01 : IntervalIntegrable g volume 0 (1 / 2) :=
    intervalIntegrable_of_integrableOn_unitIoo hint ⟨le_rfl, zero_le_one⟩ ⟨by norm_num, by norm_num⟩
  have hg12 : IntervalIntegrable g volume (1 / 2) 1 :=
    intervalIntegrable_of_integrableOn_unitIoo hint ⟨by norm_num, by norm_num⟩ ⟨zero_le_one, le_rfl⟩
  have hsplit := integral_add_adjacent_intervals hg01 hg12
  have hrefl : ∫ t in (1 / 2 : ℝ)..1, g t = ∫ t in (0 : ℝ)..(1 / 2), g t := by
    have h := intervalIntegral.integral_comp_sub_left g (1 : ℝ) (a := 0) (b := 1 / 2)
    rw [sub_zero, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at h
    rw [← h]
    refine intervalIntegral.integral_congr_ae ?_
    have hnull : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 1 / 2 := by simp [ae_iff, measure_singleton]
    filter_upwards [hnull] with t ht1 ht
    rw [uIoc_of_le (by norm_num)] at ht
    exact actionIntegrand_one_sub _ ⟨ht.1, by linarith [ht.2]⟩
  have hhalf : ∫ u in (0 : ℝ)..1, g (u / 2) = 2 * ∫ t in (0 : ℝ)..(1 / 2), g t := by
    rw [intervalIntegral.integral_comp_div g (two_ne_zero), smul_eq_mul]; norm_num
  rw [cdfAction_eq_intervalIntegral, ← hsplit, hrefl, ← two_mul, ← hhalf]
  refine integral_congr fun u _ => ?_
  show actionIntegrand (2 * (n : ℤ)) (u / 2) = _
  unfold actionIntegrand
  push_cast
  ring_nf

/-! ## `Φ_{2n} < 2Φ_n` -/

/-- `q(u/2) < 2 q(u)` on `(0,1)`: strict concavity of `h = 1/q > 0`. -/
theorem thetaQuantileSpeed_half_lt {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    thetaQuantileSpeed (u / 2) < 2 * thetaQuantileSpeed u := by
  set h := thetaQuantileProfile
  have hc := strictConcaveOn_thetaQuantileProfile
  have hu4 : u / 4 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hu2 : u / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  set S := (h (u / 2) - h (u / 4)) / (u / 2 - u / 4)
  have hS1 : (h u - h (u / 2)) / (u - u / 2) < S :=
    hc.slope_anti_adjacent hu4 hu (by linarith [hu.1]) (by linarith [hu.1])
  have hS2 : ∀ ε ∈ Ioo (0 : ℝ) (u / 4), S < h (u / 4) / (u / 4 - ε) := by
    intro ε hε
    have hεI : ε ∈ Ioo (0 : ℝ) 1 := ⟨hε.1, by linarith [hε.2, hu.2]⟩
    have h1 := hc.slope_anti_adjacent hεI hu2 hε.2 (by linarith [hu.1])
    have hpos := thetaQuantileProfile_pos ε
    have hden : 0 < u / 4 - ε := by linarith [hε.2]
    calc S < (h (u / 4) - h ε) / (u / 4 - ε) := h1
      _ ≤ h (u / 4) / (u / 4 - ε) := div_le_div_of_nonneg_right (by linarith) hden.le
  have hlim : Tendsto (fun ε : ℝ => h (u / 4) / (u / 4 - ε)) (𝓝[>] 0) (𝓝 (h (u / 4) / (u / 4 - 0))) :=
    ((continuousAt_const.div (continuousAt_const.sub continuousAt_id)
      (show u / 4 - (0 : ℝ) ≠ 0 by rw [sub_zero]; exact (div_pos hu.1 (by norm_num)).ne')).tendsto).mono_left
      nhdsWithin_le_nhds
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), S ≤ h (u / 4) / (u / 4 - ε) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < u / 4 by linarith [hu.1])] with ε hε
    exact (hS2 ε hε).le
  have hS3 : S ≤ h (u / 4) / (u / 4) := by simpa using ge_of_tendsto hlim hev
  have hu0 : 0 < u := hu.1
  have hprof : 2 * h (u / 2) > h u := by
    have e1 : S * (u / 4) = h (u / 2) - h (u / 4) := by
      simp only [S]; field_simp; ring
    have e2 : (h u - h (u / 2)) / (u - u / 2) * (u / 2) = h u - h (u / 2) := by
      field_simp; ring
    have e3 : S * (u / 4) ≤ h (u / 4) := by
      have := mul_le_mul_of_nonneg_right hS3 (show 0 ≤ u / 4 by linarith)
      rwa [div_mul_cancel₀ _ (by linarith : u / 4 ≠ 0)] at this
    have e4 : (h u - h (u / 2)) / (u - u / 2) * (u / 2) < S * (u / 2) :=
      mul_lt_mul_of_pos_right hS1 (by linarith)
    nlinarith
  have key : (thetaQuantileSpeed u)⁻¹ < 2 * (thetaQuantileSpeed (u / 2))⁻¹ := hprof
  have hqa := thetaQuantileSpeed_pos (u / 2)
  have hqb := thetaQuantileSpeed_pos u
  calc thetaQuantileSpeed (u / 2) = thetaQuantileSpeed (u / 2) * thetaQuantileSpeed u *
        (thetaQuantileSpeed u)⁻¹ := by field_simp
    _ < thetaQuantileSpeed (u / 2) * thetaQuantileSpeed u * (2 * (thetaQuantileSpeed (u / 2))⁻¹) :=
        mul_lt_mul_of_pos_left key (by positivity)
    _ = 2 * thetaQuantileSpeed u := by field_simp

/-- **Dyadic upper bound** `Φ_{2n} < 2Φ_n` for `n ≥ 1`. -/
theorem cdfAction_two_mul_lt {n : ℕ} (hn : 1 ≤ n) : cdfAction (2 * (n : ℤ)) < 2 * cdfAction n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h1n : (1 : ℝ) / n ≤ 1 := by rw [div_le_one hnR]; exact_mod_cast hn
  set f : ℝ → ℝ := fun u => (2 * thetaQuantileSpeed u - thetaQuantileSpeed (u / 2)) *
    (1 - Real.cos (2 * Real.pi * n * u))
  have hA : IntervalIntegrable (actionIntegrand n) volume 0 1 :=
    intervalIntegrable_of_integrableOn_unitIoo (integrableOn_thetaQuantileSpeed_mul_one_sub_cos n)
      ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
  have hcos1 : Real.cos (2 * Real.pi * n * 1) = 1 := by
    rw [mul_one, show 2 * Real.pi * (n : ℝ) = (n : ℤ) * (2 * Real.pi) by push_cast; ring]
    exact Real.cos_int_mul_two_pi n
  have hBm : AEStronglyMeasurable (fun u => thetaQuantileSpeed (u / 2) * (1 - Real.cos (2 * Real.pi * n * u)))
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    refine (((measurable_const.div ((thetaSource.continuous_k.measurable).comp
      (thetaSource.measurable_quantileFun.comp (measurable_id.div_const 2))))).mul
      (by fun_prop : Measurable fun u : ℝ => 1 - Real.cos (2 * Real.pi * n * u))).aestronglyMeasurable
  have hB : IntervalIntegrable (fun u => thetaQuantileSpeed (u / 2) * (1 - Real.cos (2 * Real.pi * n * u)))
      volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    refine ((hA.1.const_mul 2)).mono' hBm ((ae_restrict_iff' measurableSet_Ioc).2
      (Eventually.of_forall fun u hu => ?_))
    have hc : 0 ≤ 1 - Real.cos (2 * Real.pi * n * u) := by
      linarith [Real.cos_le_one (2 * Real.pi * n * u)]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (thetaQuantileSpeed_pos _).le hc)]
    rcases (eq_or_lt_of_le hu.2) with h1 | h1
    · subst h1
      rw [hcos1, sub_self, mul_zero]
      exact mul_nonneg zero_le_two (actionIntegrand_nonneg _ _)
    · have := thetaQuantileSpeed_half_lt ⟨hu.1, h1⟩
      simp only [actionIntegrand]
      push_cast
      nlinarith
  have hf : IntervalIntegrable f volume 0 1 := by
    refine ((hA.const_mul 2).sub hB).congr (fun u _ => ?_)
    simp only [f, actionIntegrand]
    push_cast; ring
  have hpos : 0 < ∫ u in (0 : ℝ)..1, f u := by
    calc (0 : ℝ) < ∫ u in (0 : ℝ)..(1 / n), f u := by
          refine intervalIntegral_pos_of_pos_on (hf.mono_set ?_) (fun u hu => ?_) (by positivity)
          · rw [uIcc_of_le (by positivity), uIcc_of_le zero_le_one]
            exact Icc_subset_Icc le_rfl h1n
          · have hu1 : u ∈ Ioo (0 : ℝ) 1 := ⟨hu.1, hu.2.trans_le h1n⟩
            exact mul_pos (by linarith [thetaQuantileSpeed_half_lt hu1]) (one_sub_cos_pos hn hu)
      _ ≤ ∫ u in (0 : ℝ)..1, f u := by
          refine integral_mono_interval le_rfl (by positivity) h1n ?_ hf
          refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
          rcases (eq_or_lt_of_le hu.2) with h1 | h1
          · subst h1
            simp only [f, Pi.zero_apply]
            rw [hcos1, sub_self, mul_zero]
          · exact mul_nonneg (by linarith [thetaQuantileSpeed_half_lt ⟨hu.1, h1⟩])
              (by linarith [Real.cos_le_one (2 * Real.pi * n * u)])
  have heq : ∫ u in (0 : ℝ)..1, f u = 2 * cdfAction n - cdfAction (2 * (n : ℤ)) := by
    rw [cdfAction_two_mul_eq, cdfAction_eq_intervalIntegral, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hA.const_mul 2) hB]
    refine integral_congr fun u _ => ?_
    simp only [f, actionIntegrand]
    push_cast; ring
  linarith

/-! ## `Φ_{2n} > Φ_n`: two integrations by parts -/

/-- `q' = −H(Q) q²`. -/
def thetaQuantileSpeedDeriv (t : ℝ) : ℝ := -(thetaLogHazard (thetaQuantile t) * thetaQuantileSpeed t ^ 2)

/-- `q'' = q³ (2H(Q)² − H'(Q))`. -/
def thetaQuantileSpeedDeriv2 (t : ℝ) : ℝ :=
  thetaQuantileSpeed t ^ 3 * (2 * thetaLogHazard (thetaQuantile t) ^ 2 -
    thetaCuspLogConcavityNumerator (thetaQuantile t) / thetaCuspFullSource (thetaQuantile t) ^ 2)

theorem continuousOn_thetaQuantile : ContinuousOn thetaQuantile (Ioo (0 : ℝ) 1) :=
  fun _ ht => (hasDerivAt_thetaQuantile ht).continuousAt.continuousWithinAt

theorem continuousOn_thetaQuantileSpeed : ContinuousOn thetaQuantileSpeed (Ioo (0 : ℝ) 1) :=
  fun _ ht => (hasDerivAt_thetaQuantileSpeed ht).continuousAt.continuousWithinAt

theorem continuousOn_thetaQuantileSpeedDeriv : ContinuousOn thetaQuantileSpeedDeriv (Ioo (0 : ℝ) 1) :=
  fun _ ht => (hasDerivAt_thetaQuantileSpeedDeriv ht).continuousAt.continuousWithinAt

theorem continuousOn_thetaQuantileSpeedDeriv2 : ContinuousOn thetaQuantileSpeedDeriv2 (Ioo (0 : ℝ) 1) := by
  have hk : Continuous thetaCuspFullSource := contDiff_thetaCuspFullSource.continuous
  have hH : Continuous thetaLogHazard := continuous_thetaLogHazard
  have hN : Continuous thetaCuspLogConcavityNumerator := continuous_thetaCuspLogConcavityNumerator
  refine (continuousOn_thetaQuantileSpeed.pow 3).mul ?_
  refine ((hH.comp_continuousOn continuousOn_thetaQuantile).pow 2 |>.const_smul (2 : ℝ)).sub ?_
  exact (hN.comp_continuousOn continuousOn_thetaQuantile).div
    ((hk.comp_continuousOn continuousOn_thetaQuantile).pow 2)
    (fun t _ => pow_ne_zero 2 (thetaCuspFullSource_pos _).ne')

theorem thetaQuantileSpeedDeriv_one_sub {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    thetaQuantileSpeedDeriv (1 - t) = -thetaQuantileSpeedDeriv t := by
  simp only [thetaQuantileSpeedDeriv, thetaQuantileSpeed, thetaQuantile]
  rw [quantileSpeed_one_sub ht, quantileFun_one_sub ht, thetaLogHazard_neg]
  ring

/-- `W_n(t) = (1 − cos 2πnt)²/(2(2πn)²)`. -/
def cdfDyadicWeight (n : ℕ) (t : ℝ) : ℝ :=
  (1 - Real.cos (2 * Real.pi * n * t)) ^ 2 / (2 * (2 * Real.pi * n) ^ 2)

def cdfDyadicWeightDeriv (n : ℕ) (t : ℝ) : ℝ :=
  (1 - Real.cos (2 * Real.pi * n * t)) * Real.sin (2 * Real.pi * n * t) / (2 * Real.pi * n)

def cdfDyadicWeightDeriv2 (n : ℕ) (t : ℝ) : ℝ :=
  Real.cos (2 * Real.pi * n * t) - Real.cos (2 * Real.pi * (2 * n) * t)

theorem hasDerivAt_dyadicWeight {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    HasDerivAt (cdfDyadicWeight n) (cdfDyadicWeightDeriv n t) t := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (2 * Real.pi * n : ℝ) ≠ 0 := by positivity
  have h := ((((hasDerivAt_id t).const_mul (2 * Real.pi * n)).cos.const_sub 1).pow 2).div_const
    (2 * (2 * Real.pi * n) ^ 2)
  refine h.congr_deriv ?_
  simp only [cdfDyadicWeightDeriv, id]
  field_simp
  ring

theorem hasDerivAt_dyadicWeightDeriv {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    HasDerivAt (cdfDyadicWeightDeriv n) (cdfDyadicWeightDeriv2 n t) t := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (2 * Real.pi * n : ℝ) ≠ 0 := by positivity
  have hθ := (hasDerivAt_id t).const_mul (2 * Real.pi * n)
  have h := ((hθ.cos.const_sub 1).mul hθ.sin).div_const (2 * Real.pi * n)
  refine h.congr_deriv ?_
  simp only [cdfDyadicWeightDeriv2, id, mul_one]
  have hcos2 : Real.cos (2 * Real.pi * (2 * n) * t) =
      Real.cos (2 * Real.pi * n * t) ^ 2 - Real.sin (2 * Real.pi * n * t) ^ 2 := by
    rw [show 2 * Real.pi * (2 * n) * t = 2 * (2 * Real.pi * n * t) by ring, Real.cos_two_mul,
      ← Real.cos_sq_add_sin_sq (2 * Real.pi * n * t)]
    ring
  rw [hcos2]
  field_simp
  ring

theorem cdfDyadicWeight_nonneg (n : ℕ) (t : ℝ) : 0 ≤ cdfDyadicWeight n t := by
  unfold cdfDyadicWeight; positivity

theorem cdfDyadicWeight_pos {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (1 / n)) :
    0 < cdfDyadicWeight n t := by
  have := one_sub_cos_pos hn ht
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold cdfDyadicWeight; positivity

theorem cdfDyadicWeight_one_sub (n : ℕ) (t : ℝ) : cdfDyadicWeight n (1 - t) = cdfDyadicWeight n t := by
  unfold cdfDyadicWeight
  rw [show 2 * Real.pi * n * (1 - t) = -(2 * Real.pi * n * t - ((n : ℤ) : ℝ) * (2 * Real.pi)) by
    push_cast; ring, Real.cos_neg, Real.cos_sub_int_mul_two_pi]

theorem cdfDyadicWeightDeriv_one_sub (n : ℕ) (t : ℝ) : cdfDyadicWeightDeriv n (1 - t) = -cdfDyadicWeightDeriv n t := by
  unfold cdfDyadicWeightDeriv
  rw [show 2 * Real.pi * n * (1 - t) = -(2 * Real.pi * n * t - ((n : ℤ) : ℝ) * (2 * Real.pi)) by
    push_cast; ring, Real.cos_neg, Real.sin_neg, Real.cos_sub_int_mul_two_pi, Real.sin_sub_int_mul_two_pi]
  ring

theorem abs_one_sub_cos_le_sq (x : ℝ) : |1 - Real.cos x| ≤ x ^ 2 / 2 := by
  rw [abs_of_nonneg (by linarith [Real.cos_le_one x])]
  linarith [Real.one_sub_sq_div_two_le_cos (x := x)]

theorem abs_dyadicWeightDeriv_le {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    |cdfDyadicWeightDeriv n t| ≤ (2 * Real.pi * n) ^ 2 / 2 * t ^ 3 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < 2 * Real.pi * n := by positivity
  set θ := 2 * Real.pi * n * t
  have hθ : 0 ≤ θ := by positivity
  have h1 := abs_one_sub_cos_le_sq θ
  have h2 : |Real.sin θ| ≤ θ := Real.abs_sin_le_abs.trans (abs_of_nonneg hθ).le
  rw [cdfDyadicWeightDeriv, abs_div, abs_mul, abs_of_pos hn0, div_le_iff₀ hn0]
  calc |1 - Real.cos θ| * |Real.sin θ| ≤ θ ^ 2 / 2 * θ :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = (2 * Real.pi * n) ^ 2 / 2 * t ^ 3 * (2 * Real.pi * n) := by simp only [θ]; ring

theorem abs_dyadicWeight_le {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    |cdfDyadicWeight n t| ≤ (2 * Real.pi * n) ^ 2 / 8 * t ^ 4 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < 2 * Real.pi * n := by positivity
  set θ := 2 * Real.pi * n * t
  have h1 := abs_one_sub_cos_le_sq θ
  rw [abs_of_nonneg (cdfDyadicWeight_nonneg n t), cdfDyadicWeight, div_le_iff₀ (by positivity)]
  have h2 : (1 - Real.cos θ) ^ 2 ≤ (θ ^ 2 / 2) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  calc (1 - Real.cos θ) ^ 2 ≤ (θ ^ 2 / 2) ^ 2 := h2
    _ = (2 * Real.pi * n) ^ 2 / 8 * t ^ 4 * (2 * (2 * Real.pi * n) ^ 2) := by simp only [θ]; ring

theorem tendsto_boundary_dyadic {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun ε => -2 * (thetaQuantileSpeed ε * cdfDyadicWeightDeriv n ε) +
      2 * (thetaQuantileSpeedDeriv ε * cdfDyadicWeight n ε)) (𝓝[>] 0) (𝓝 0) := by
  set C1 := (2 * Real.pi * n) ^ 2 / 2
  set C2 := (2 * Real.pi * n) ^ 2 / 8
  have h1 : Tendsto (fun ε => thetaQuantileSpeed ε * cdfDyadicWeightDeriv n ε) (𝓝[>] 0) (𝓝 0) := by
    have hb : Tendsto (fun ε => C1 * (ε ^ 3 * thetaQuantileSpeed ε)) (𝓝[>] 0) (𝓝 0) := by
      simpa using tendsto_cube_mul_thetaQuantileSpeed.const_mul C1
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (thetaQuantileSpeed_pos ε)]
    calc thetaQuantileSpeed ε * |cdfDyadicWeightDeriv n ε| ≤ thetaQuantileSpeed ε * (C1 * ε ^ 3) :=
          mul_le_mul_of_nonneg_left (abs_dyadicWeightDeriv_le hn (le_of_lt hε)) (thetaQuantileSpeed_pos ε).le
      _ = C1 * (ε ^ 3 * thetaQuantileSpeed ε) := by ring
  have h2 : Tendsto (fun ε => thetaQuantileSpeedDeriv ε * cdfDyadicWeight n ε) (𝓝[>] 0) (𝓝 0) := by
    have hb : Tendsto (fun ε => C2 * |ε ^ 4 * thetaQuantileSpeedDeriv ε|) (𝓝[>] 0) (𝓝 (C2 * |0|)) :=
      (tendsto_pow_four_mul_thetaQuantileSpeedDeriv.abs).const_mul C2
    rw [abs_zero, mul_zero] at hb
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : (0 : ℝ) ≤ ε := le_of_lt hε
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 4)]
    calc |thetaQuantileSpeedDeriv ε| * |cdfDyadicWeight n ε| ≤ |thetaQuantileSpeedDeriv ε| * (C2 * ε ^ 4) :=
          mul_le_mul_of_nonneg_left (abs_dyadicWeight_le hn ε) (abs_nonneg _)
      _ = C2 * (ε ^ 4 * |thetaQuantileSpeedDeriv ε|) := by ring
  simpa using (h1.const_mul (-2)).add (h2.const_mul 2)

/-- Convergence of truncated integrals `∫_ε^{1−ε} g → ∫₀¹ g` for `g` integrable on `[0,1]`. -/
theorem tendsto_integral_symm_truncation {g : ℝ → ℝ} (hg : IntegrableOn g (Icc (0 : ℝ) 1)) :
    Tendsto (fun ε => ∫ t in ε..(1 - ε), g t) (𝓝[>] 0) (𝓝 (∫ t in (0 : ℝ)..1, g t)) := by
  set G : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, g t
  have hGc : ContinuousOn G (Icc 0 1) := by
    have := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := 1) (μ := volume)
      (by rwa [uIcc_of_le zero_le_one])
    rwa [uIcc_of_le zero_le_one] at this
  have hlim1 : Tendsto (fun ε : ℝ => G (1 - ε)) (𝓝[>] 0) (𝓝 (G 1)) := by
    have hc : Tendsto (fun ε : ℝ => 1 - ε) (𝓝[>] 0) (𝓝[Icc 0 1] 1) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have h : Tendsto (fun ε : ℝ => 1 - ε) (𝓝 0) (𝓝 (1 - 0)) := tendsto_const_nhds.sub tendsto_id
        rw [sub_zero] at h
        exact h.mono_left nhdsWithin_le_nhds
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
        exact ⟨by linarith [hε.2], by linarith [hε.1]⟩
    exact (hGc 1 ⟨zero_le_one, le_rfl⟩).tendsto.comp hc
  have hlim0 : Tendsto G (𝓝[>] 0) (𝓝 (G 0)) := by
    have hc : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝[Icc 0 1] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨nhdsWithin_le_nhds, ?_⟩
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
      exact ⟨hε.1.le, hε.2.le⟩
    exact (hGc 0 ⟨le_rfl, zero_le_one⟩).tendsto.comp hc
  have hG0 : G 0 = 0 := by simp [G]
  have heq : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∫ t in ε..(1 - ε), g t = G (1 - ε) - G ε := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
    have hi : ∀ a b : ℝ, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 → IntervalIntegrable g volume a b :=
      fun a b ha hb => (hg.mono_set (uIcc_subset_Icc ha hb)).intervalIntegrable
    exact (intervalIntegral.integral_interval_sub_left
      (hi 0 (1 - ε) ⟨le_rfl, zero_le_one⟩ ⟨by linarith [hε.2], by linarith [hε.1]⟩)
      (hi 0 ε ⟨le_rfl, zero_le_one⟩ ⟨hε.1.le, by linarith [hε.2]⟩)).symm
  have := (hlim1.sub hlim0).congr' (EventuallyEq.symm heq)
  rwa [hG0, sub_zero] at this

/-- **Dyadic lower bound** `Φ_n < Φ_{2n}` for `n ≥ 1`. -/
theorem cdfAction_lt_two_mul {n : ℕ} (hn : 1 ≤ n) : cdfAction n < cdfAction (2 * (n : ℤ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set c : ℝ := 1 / (4 * n)
  set d : ℝ := 3 / (4 * n)
  have hc0 : 0 < c := by positivity
  have hcd : c < d := by simp only [c, d]; rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num
  have hd1 : d ≤ 3 / 4 := by
    simp only [d]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hdn : d < 1 / n := by
    simp only [d]; rw [div_lt_div_iff₀ (by positivity) hnR]; nlinarith
  -- the positive interior mass
  set J := ∫ t in c..d, thetaQuantileSpeedDeriv2 t * cdfDyadicWeight n t
  have hcont : ContinuousOn (fun t => thetaQuantileSpeedDeriv2 t * cdfDyadicWeight n t) (Ioo (0 : ℝ) 1) :=
    continuousOn_thetaQuantileSpeedDeriv2.mul (fun t _ => (hasDerivAt_dyadicWeight hn t).continuousAt.continuousWithinAt)
  have hJ : 0 < J := by
    refine intervalIntegral_pos_of_pos_on ?_ (fun t ht => ?_) hcd
    · refine (hcont.mono ?_).intervalIntegrable
      rw [uIcc_of_le hcd.le]
      exact Icc_subset_Ioo hc0 (by linarith)
    · have htn : t ∈ Ioo (0 : ℝ) (1 / n) := ⟨hc0.trans ht.1, ht.2.trans hdn⟩
      exact mul_pos (thetaQuantileSpeedDeriv2_pos t) (cdfDyadicWeight_pos hn htn)
  -- the integration by parts on `[ε, 1 − ε]`
  have hibp : ∀ ε ∈ Ioo (0 : ℝ) c,
      ∫ t in ε..(1 - ε), (actionIntegrand (2 * (n : ℤ)) t - actionIntegrand n t) ≥
        (-2 * (thetaQuantileSpeed ε * cdfDyadicWeightDeriv n ε) +
          2 * (thetaQuantileSpeedDeriv ε * cdfDyadicWeight n ε)) + J := by
    intro ε hε
    have hε1 : ε < 1 / 4 := by
      have : c ≤ 1 / 4 := by
        simp only [c]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith
      linarith [hε.2]
    have hsub : uIcc ε (1 - ε) ⊆ Ioo (0 : ℝ) 1 := by
      rw [uIcc_of_le (by linarith [hε.1])]
      exact Icc_subset_Ioo hε.1 (by linarith [hε.1])
    have hq : ∀ x ∈ uIcc ε (1 - ε), HasDerivAt thetaQuantileSpeed (thetaQuantileSpeedDeriv x) x :=
      fun x hx => hasDerivAt_thetaQuantileSpeed (hsub hx)
    have hq' : ∀ x ∈ uIcc ε (1 - ε), HasDerivAt thetaQuantileSpeedDeriv (thetaQuantileSpeedDeriv2 x) x :=
      fun x hx => hasDerivAt_thetaQuantileSpeedDeriv (hsub hx)
    have hW : ∀ x ∈ uIcc ε (1 - ε), HasDerivAt (cdfDyadicWeight n) (cdfDyadicWeightDeriv n x) x :=
      fun x _ => hasDerivAt_dyadicWeight hn x
    have hW' : ∀ x ∈ uIcc ε (1 - ε), HasDerivAt (cdfDyadicWeightDeriv n) (cdfDyadicWeightDeriv2 n x) x :=
      fun x _ => hasDerivAt_dyadicWeightDeriv hn x
    have iq' : IntervalIntegrable thetaQuantileSpeedDeriv volume ε (1 - ε) :=
      (continuousOn_thetaQuantileSpeedDeriv.mono hsub).intervalIntegrable
    have iq'' : IntervalIntegrable thetaQuantileSpeedDeriv2 volume ε (1 - ε) :=
      (continuousOn_thetaQuantileSpeedDeriv2.mono hsub).intervalIntegrable
    have iW' : IntervalIntegrable (cdfDyadicWeightDeriv n) volume ε (1 - ε) :=
      (continuous_iff_continuousAt.2 fun x =>
        (hasDerivAt_dyadicWeightDeriv hn x).continuousAt).continuousOn.intervalIntegrable
    have iW'' : IntervalIntegrable (cdfDyadicWeightDeriv2 n) volume ε (1 - ε) :=
      (by unfold cdfDyadicWeightDeriv2; fun_prop : Continuous (cdfDyadicWeightDeriv2 n)).continuousOn.intervalIntegrable
    have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul hq hW' iq' iW''
    have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul hq' hW iq'' iW'
    have hint : ∫ t in ε..(1 - ε), (actionIntegrand (2 * (n : ℤ)) t - actionIntegrand n t) =
        ∫ t in ε..(1 - ε), thetaQuantileSpeed t * cdfDyadicWeightDeriv2 n t := by
      refine integral_congr fun t _ => ?_
      simp only [actionIntegrand, cdfDyadicWeightDeriv2]
      push_cast; ring
    have hmono : J ≤ ∫ t in ε..(1 - ε), thetaQuantileSpeedDeriv2 t * cdfDyadicWeight n t := by
      refine integral_mono_interval hε.2.le hcd.le (by linarith) ?_ ?_
      · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => ?_)
        exact mul_nonneg (thetaQuantileSpeedDeriv2_pos t).le (cdfDyadicWeight_nonneg n t)
      · exact (hcont.mono hsub).intervalIntegrable
    have hε' : ε ∈ Ioo (0 : ℝ) 1 := ⟨hε.1, by linarith⟩
    have hsym1 : thetaQuantileSpeed (1 - ε) * cdfDyadicWeightDeriv n (1 - ε) =
        -(thetaQuantileSpeed ε * cdfDyadicWeightDeriv n ε) := by
      rw [show thetaQuantileSpeed (1 - ε) = thetaQuantileSpeed ε from quantileSpeed_one_sub hε',
        cdfDyadicWeightDeriv_one_sub]; ring
    have hsym2 : thetaQuantileSpeedDeriv (1 - ε) * cdfDyadicWeight n (1 - ε) =
        -(thetaQuantileSpeedDeriv ε * cdfDyadicWeight n ε) := by
      rw [thetaQuantileSpeedDeriv_one_sub hε', cdfDyadicWeight_one_sub]; ring
    rw [hint, h1, h2, hsym1, hsym2]
    linarith
  -- pass to the limit
  have hlimL := tendsto_integral_symm_truncation (g := fun t => actionIntegrand (2 * (n : ℤ)) t - actionIntegrand n t)
    ((integrableOn_Icc_of_Ioo (integrableOn_thetaQuantileSpeed_mul_one_sub_cos (2 * (n : ℤ)))).sub
      (integrableOn_Icc_of_Ioo (integrableOn_thetaQuantileSpeed_mul_one_sub_cos n)))
  have hlimR := (tendsto_boundary_dyadic hn).add_const J
  rw [zero_add] at hlimR
  have hle := le_of_tendsto_of_tendsto hlimR hlimL (by
    filter_upwards [Ioo_mem_nhdsGT hc0] with ε hε
    exact (hibp ε hε).le)
  have hA2 : IntervalIntegrable (actionIntegrand (2 * (n : ℤ))) volume 0 1 :=
    intervalIntegrable_of_integrableOn_unitIoo (integrableOn_thetaQuantileSpeed_mul_one_sub_cos _)
      ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
  have hA1 : IntervalIntegrable (actionIntegrand n) volume 0 1 :=
    intervalIntegrable_of_integrableOn_unitIoo (integrableOn_thetaQuantileSpeed_mul_one_sub_cos _)
      ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
  have hval : ∫ t in (0 : ℝ)..1, (actionIntegrand (2 * (n : ℤ)) t - actionIntegrand n t) =
      cdfAction (2 * (n : ℤ)) - cdfAction n := by
    have := intervalIntegral.integral_sub hA2 hA1
    rw [this, ← cdfAction_eq_intervalIntegral, ← cdfAction_eq_intervalIntegral]
  linarith

/-- `r_n = (Φ_{2n} − Φ_n)/Φ_n ∈ (0, 1)`. -/
theorem dyadicRatio_mem_Ioo {n : ℕ} (hn : 1 ≤ n) :
    (cdfAction (2 * (n : ℤ)) - cdfAction n) / cdfAction n ∈ Ioo (0 : ℝ) 1 := by
  have hpos := cdfAction_pos hn
  constructor
  · exact div_pos (by linarith [cdfAction_lt_two_mul hn]) hpos
  · rw [div_lt_one hpos]; linarith [cdfAction_two_mul_lt hn]

end

end RHTower
