import GaloisForLFunctions.RHTower.PMAnalyticPowerVariance

/-!
# Sharp variance boundary of the analytic PM inputs

The literal model variance has a finite limit below exponent `1/2`, logarithmic
growth at `1/2`, and a positive power asymptotic above it. Dividing by `log² R`
gives convergence to zero exactly at or below `1/2`. Every scalar centering retains
supercritical divergence. An unconditional existence theorem packages the analytic
input obstruction without asserting any prime-support or divisor-convolution law.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower

theorem tendsto_pmPowerVariance_remainder {σ : ℝ} (hσ : σ < 1) :
    Tendsto (fun R : ℝ => 1 - 1 / (2 * σ - 1) +
      2 * (1 / σ) * (1 + 1 / σ) * R ^ (σ - 1) - (1 + 1 / σ) ^ 2 / R)
      atTop (𝓝 (1 - 1 / (2 * σ - 1))) := by
  have hp : Tendsto (fun R : ℝ => R ^ (σ - 1)) atTop (𝓝 0) := by
    simpa only [neg_sub] using tendsto_rpow_neg_atTop (sub_pos.mpr hσ)
  have hi : Tendsto (fun R : ℝ => (1 + 1 / σ) ^ 2 / R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  simpa using (tendsto_const_nhds.add (hp.const_mul (2 * (1 / σ) * (1 + 1 / σ)))).sub hi

theorem tendsto_pmPowerVariance_subcritical {σ : ℝ} (hσ0 : 0 < σ) (hσ : σ < 1 / 2) :
    Tendsto (pmPowerVariance σ) atTop (𝓝 (1 + 1 / (1 - 2 * σ))) := by
  have hd : 2 * σ - 1 < 0 := by linarith
  have hp : Tendsto (fun R : ℝ => R ^ (2 * σ - 1)) atTop (𝓝 0) := by
    simpa only [neg_sub] using tendsto_rpow_neg_atTop (by linarith : 0 < 1 - 2 * σ)
  have hc : 1 - 1 / (2 * σ - 1) = 1 + 1 / (1 - 2 * σ) := by
    rw [show 2 * σ - 1 = -(1 - 2 * σ) by ring, div_neg]
    ring
  have ht := (hp.const_mul ((1 - σ) ^ 2 / (σ ^ 2 * (2 * σ - 1)))).add
    (tendsto_pmPowerVariance_remainder (by linarith : σ < 1))
  simp only [mul_zero, zero_add] at ht
  rw [← hc]
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with R hR
  rw [pmPowerVariance_formula hσ0 (by linarith) hd.ne hR]
  ring

theorem tendsto_pmPowerVariance_half_sub_log :
    Tendsto (fun R : ℝ => pmPowerVariance (1 / 2) R - Real.log R) atTop (𝓝 (-3)) := by
  have hp : Tendsto (fun R : ℝ => R ^ (-1 / 2 : ℝ)) atTop (𝓝 0) := by
    simpa only [neg_div] using tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)
  have hi : Tendsto (fun R : ℝ => 9 / R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have ht : Tendsto (fun R : ℝ => -3 + 12 * R ^ (-1 / 2 : ℝ) - 9 / R) atTop (𝓝 (-3)) := by
    simpa using (tendsto_const_nhds.add (hp.const_mul 12)).sub hi
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with R hR
  rw [pmPowerVariance_half_formula hR]
  ring

theorem pmPowerVariance_leadingCoeff_pos {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1) :
    0 < (1 - σ) ^ 2 / (σ ^ 2 * (2 * σ - 1)) := by
  exact div_pos (sq_pos_of_pos (sub_pos.mpr hσ1))
    (mul_pos (sq_pos_of_pos (by linarith)) (by linarith))

theorem tendsto_pmPowerVariance_supercritical {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1) :
    Tendsto (fun R : ℝ => pmPowerVariance σ R / R ^ (2 * σ - 1)) atTop
      (𝓝 ((1 - σ) ^ 2 / (σ ^ 2 * (2 * σ - 1)))) := by
  have hd : 0 < 2 * σ - 1 := by linarith
  have hq := (tendsto_pmPowerVariance_remainder hσ1).div_atTop (tendsto_rpow_atTop hd)
  have hc : Tendsto (fun _ : ℝ => (1 - σ) ^ 2 / (σ ^ 2 * (2 * σ - 1))) atTop
      (𝓝 ((1 - σ) ^ 2 / (σ ^ 2 * (2 * σ - 1)))) := tendsto_const_nhds
  have ht := hc.add hq
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with R hR
  have hp : R ^ (2 * σ - 1) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
  rw [pmPowerVariance_formula (by linarith) hσ1.le hd.ne' hR]
  field_simp
  ring

theorem tendsto_pmPowerVariance_div_log_sq_subcritical {σ : ℝ}
    (hσ0 : 0 < σ) (hσ : σ < 1 / 2) :
    Tendsto (fun R : ℝ => pmPowerVariance σ R / Real.log R ^ 2) atTop (𝓝 0) :=
  (tendsto_pmPowerVariance_subcritical hσ0 hσ).div_atTop
    ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp Real.tendsto_log_atTop)

theorem tendsto_pmPowerVariance_div_log_sq_half :
    Tendsto (fun R : ℝ => pmPowerVariance (1 / 2) R / Real.log R ^ 2) atTop (𝓝 0) := by
  have hs := tendsto_pmPowerVariance_half_sub_log.div_atTop
    ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp Real.tendsto_log_atTop)
  have hi : Tendsto (fun R : ℝ => 1 / Real.log R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have ht := hs.add hi
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 1] with R hR
  have hlog : Real.log R ≠ 0 := (Real.log_pos hR).ne'
  simp only [Function.comp_apply]
  field_simp
  ring

theorem tendsto_pmPowerVariance_div_log_sq_supercritical {σ : ℝ}
    (hσ : 1 / 2 < σ) (hσ1 : σ < 1) :
    Tendsto (fun R : ℝ => pmPowerVariance σ R / Real.log R ^ 2) atTop atTop := by
  have hd : 0 < 2 * σ - 1 := by linarith
  have hs : Tendsto (fun R : ℝ => Real.log R ^ 2 / R ^ (2 * σ - 1)) atTop (𝓝 0) := by
    simpa only [Real.rpow_two] using
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hd).tendsto_div_nhds_zero
  have hpos : ∀ᶠ R : ℝ in atTop, Real.log R ^ 2 / R ^ (2 * σ - 1) ∈ Ioi (0 : ℝ) := by
    filter_upwards [eventually_gt_atTop 1] with R hR
    exact div_pos (sq_pos_of_pos (Real.log_pos hR)) (Real.rpow_pos_of_pos (by linarith) _)
  have hw := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hs hpos
  have hinv : Tendsto (fun R : ℝ => R ^ (2 * σ - 1) / Real.log R ^ 2) atTop atTop := by
    apply hw.inv_tendsto_nhdsGT_zero.congr
    intro R
    change (Real.log R ^ 2 / R ^ (2 * σ - 1))⁻¹ = _
    rw [inv_div]
  have ht := (tendsto_pmPowerVariance_supercritical hσ hσ1).pos_mul_atTop
    (pmPowerVariance_leadingCoeff_pos hσ hσ1) hinv
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 1] with R hR
  have hp : R ^ (2 * σ - 1) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
  field_simp

theorem tendsto_pmPowerVariance_div_log_sq_iff {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Tendsto (fun R : ℝ => pmPowerVariance σ R / Real.log R ^ 2) atTop (𝓝 0) ↔ σ ≤ 1 / 2 := by
  constructor
  · intro h
    by_contra hn
    have ht := tendsto_pmPowerVariance_div_log_sq_supercritical (lt_of_not_ge hn) hσ1
    have hu := h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    have hl := ht.eventually_gt_atTop 1
    obtain ⟨R, hR, hR'⟩ := (hu.and hl).exists
    exact (not_lt_of_ge hR.le) hR'
  · intro h
    rcases lt_or_eq_of_le h with h | h
    · exact tendsto_pmPowerVariance_div_log_sq_subcritical hσ0 h
    · subst σ
      exact tendsto_pmPowerVariance_div_log_sq_half

/-- Every choice of centering scalar retains supercritical divergence. -/
theorem tendsto_pmPowerProfile_scalar_error_div_log_sq {σ : ℝ}
    (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (B : ℝ → ℝ) :
    Tendsto (fun R : ℝ => (∫ x in Ioo (0 : ℝ) R, (B R - pmPowerProfile σ x) ^ 2) /
      Real.log R ^ 2) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ (tendsto_pmPowerVariance_div_log_sq_supercritical hσ hσ1)
  filter_upwards [eventually_gt_atTop 1] with R hR
  exact div_le_div_of_nonneg_right
    (pmPowerVariance_minimizes (by linarith) hσ1.le (by linarith) (B R)) (sq_nonneg _)


theorem integrableOn_pmPowerModel_errors_from_half {σ : ℝ} (hσ : σ < 1) :
    IntegrableOn (fun x : ℝ => |pmPowerModel σ x - x| / x ^ 2) (Ioi (1 / 2)) ∧
      IntegrableOn (fun x : ℝ => (pmPowerModel σ x - x) ^ 2 / x ^ 3) (Ioi (1 / 2)) := by
  have hc : ContinuousOn (fun x : ℝ => 1 / x) (Icc (1 / 2) 1) :=
    continuousOn_const.div continuousOn_id (fun x hx => by linarith [hx.1])
  have hi : IntegrableOn (fun x : ℝ => 1 / x) (Ioc (1 / 2) 1) :=
    hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have ha : IntegrableOn (fun x : ℝ => |pmPowerModel σ x - x| / x ^ 2) (Ioc (1 / 2) 1) := by
    apply hi.congr_fun _ measurableSet_Ioc
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    dsimp only
    rw [pmPowerModel, if_pos hx.2, zero_sub, abs_neg, abs_of_pos hx0]
    field_simp
  have hs : IntegrableOn (fun x : ℝ => (pmPowerModel σ x - x) ^ 2 / x ^ 3) (Ioc (1 / 2) 1) := by
    apply hi.congr_fun _ measurableSet_Ioc
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    dsimp only
    rw [pmPowerModel, if_pos hx.2, zero_sub, neg_sq]
    field_simp
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (1 / 2 : ℝ) ≤ 1)]
  exact ⟨ha.union (integrableOn_pmPowerModel_absError_div_sq hσ),
    hs.union (integrableOn_pmPowerModel_sqError_div_cube hσ)⟩

/-- The analytic source inputs alone admit a profile whose every scalar-centered
canonical error diverges. No prime-support or divisor-convolution identity is asserted. -/
theorem exists_pm_analytic_inputs_with_divergent_variance :
    ∃ P : ℝ → ℝ, Measurable P ∧ Monotone P ∧
      (∀ x, 0 ≤ P x) ∧ (∀ x, x ≤ 1 → P x = 0) ∧
      (∀ x, 0 ≤ x → P x ≤ 2 * x) ∧
      Tendsto (fun x => P x / x) atTop (𝓝 1) ∧
      IntegrableOn (fun x : ℝ => |P x - x| / x ^ 2) (Ioi (1 / 2)) ∧
      IntegrableOn (fun x : ℝ => (P x - x) ^ 2 / x ^ 3) (Ioi (1 / 2)) ∧
      (∀ α : ℝ, α < 1 → ∀ᶠ x : ℝ in atTop, |P x - x| ≤ x * Real.exp (-(Real.log x) ^ α)) ∧
      (∀ B : ℝ → ℝ, Tendsto (fun R : ℝ =>
        (∫ x in Ioo (0 : ℝ) R, (B R - P x / x) ^ 2) / Real.log R ^ 2) atTop atTop) := by
  refine ⟨pmPowerModel (3 / 4), measurable_pmPowerModel (by norm_num),
    pmPowerModel_monotone (by norm_num), pmPowerModel_nonneg _, ?_, ?_,
    tendsto_pmPowerProfile_one (by norm_num),
    (integrableOn_pmPowerModel_errors_from_half (by norm_num : (3 / 4 : ℝ) < 1)).1,
    (integrableOn_pmPowerModel_errors_from_half (by norm_num : (3 / 4 : ℝ) < 1)).2,
    ?_, ?_⟩
  · intro x hx
    simp [pmPowerModel, hx]
  · intro x hx
    exact pmPowerModel_le_two_mul (by norm_num) hx
  · intro α hα
    exact pmPowerModel_stretchedLog_bound (by norm_num) hα
  · intro B
    exact tendsto_pmPowerProfile_scalar_error_div_log_sq (by norm_num) (by norm_num) B

end RHTower
