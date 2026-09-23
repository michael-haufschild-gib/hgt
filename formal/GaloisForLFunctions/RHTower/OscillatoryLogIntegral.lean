import Mathlib

/-!
# The oscillatory logarithmic integral
-/

namespace RHTower

open Filter Complex MeasureTheory
open scoped Topology

/-- The unimodular logarithmic phase `t ↦ t^{-iλ}`. -/
noncomputable def logPhase (lam : ℝ) (t : ℝ) : ℂ :=
  Complex.exp (-(lam : ℂ) * Complex.I * ((Real.log t : ℝ) : ℂ))

theorem norm_logPhase (lam t : ℝ) : ‖logPhase lam t‖ = 1 := by
  rw [logPhase, Complex.norm_exp]
  have hre : (-(lam : ℂ) * Complex.I * ((Real.log t : ℝ) : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_zero]

theorem hasDerivAt_logPhase {lam t : ℝ} (ht : 0 < t) :
    HasDerivAt (logPhase lam) (logPhase lam t * (-(lam : ℂ) * Complex.I * ((t⁻¹ : ℝ) : ℂ))) t := by
  have hlog : HasDerivAt (fun x : ℝ => ((Real.log x : ℝ) : ℂ)) (((t⁻¹ : ℝ) : ℂ)) t :=
    (Real.hasDerivAt_log ht.ne').ofReal_comp
  have h2 : HasDerivAt (fun x : ℝ => -(lam : ℂ) * Complex.I * ((Real.log x : ℝ) : ℂ))
      (-(lam : ℂ) * Complex.I * ((t⁻¹ : ℝ) : ℂ)) t := hlog.const_mul _
  exact h2.cexp

/-- The antiderivative of the phase-over-`t` kernel. -/
noncomputable def logPhaseAntideriv (lam : ℝ) (t : ℝ) : ℂ :=
  logPhase lam t / (-(lam : ℂ) * Complex.I)

theorem norm_logPhaseAntideriv (lam : ℝ) (t : ℝ) :
    ‖logPhaseAntideriv lam t‖ = |lam|⁻¹ := by
  rw [logPhaseAntideriv, norm_div, norm_logPhase, norm_mul, norm_neg, Complex.norm_real,
    Complex.norm_I, mul_one, Real.norm_eq_abs, one_div]

theorem hasDerivAt_logPhaseAntideriv {lam : ℝ} (hlam : lam ≠ 0) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (logPhaseAntideriv lam) (logPhase lam t * ((t⁻¹ : ℝ) : ℂ)) t := by
  have hc : (-(lam : ℂ) * Complex.I) ≠ 0 := by
    refine mul_ne_zero ?_ Complex.I_ne_zero
    simpa using hlam
  have hlamC : ((lam : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlam
  have h := (hasDerivAt_logPhase (lam := lam) ht).div_const (-(lam : ℂ) * Complex.I)
  refine h.congr_deriv ?_
  field_simp

/-- The reciprocal-logarithm factor. -/
noncomputable def invLogC (t : ℝ) : ℂ := ((Real.log t : ℝ) : ℂ)⁻¹

theorem hasDerivAt_invLogC {t : ℝ} (ht : 1 < t) :
    HasDerivAt invLogC (-((((t * (Real.log t) ^ (2 : ℕ))⁻¹ : ℝ)) : ℂ)) t := by
  have ht0 : t ≠ 0 := by linarith
  have hlog : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hbase : HasDerivAt (fun x : ℝ => ((Real.log x : ℝ) : ℂ)) (((t⁻¹ : ℝ) : ℂ)) t :=
    (Real.hasDerivAt_log ht0).ofReal_comp
  have hne : ((Real.log t : ℝ) : ℂ) ≠ 0 := by
    simpa using hlog
  have h := hbase.inv hne
  refine h.congr_deriv ?_
  push_cast
  field_simp

/-! ## Integrability of the logarithmic tail weight -/

theorem hasDerivAt_negInvLog_oscillatoryLogIntegral {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun x : ℝ => -(Real.log x)⁻¹) ((t * (Real.log t) ^ (2 : ℕ))⁻¹) t := by
  have ht0 : t ≠ 0 := by linarith
  have hlog : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have h := ((Real.hasDerivAt_log ht0).inv hlog).neg
  refine h.congr_deriv ?_
  field_simp

theorem integrableOn_logTailWeight :
    MeasureTheory.IntegrableOn (fun t : ℝ => (t * (Real.log t) ^ (2 : ℕ))⁻¹) (Set.Ioi 2) := by
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg (g := fun x : ℝ => -(Real.log x)⁻¹)
    (l := 0) ?_ ?_ ?_ ?_
  · refine ContinuousAt.continuousWithinAt ?_
    have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    exact ((Real.continuousAt_log (by norm_num)).inv₀ hlog).neg
  · intro x hx
    have hx2 : (2 : ℝ) < x := hx
    exact hasDerivAt_negInvLog_oscillatoryLogIntegral (by linarith)
  · intro x hx
    have hx2 : (2 : ℝ) < x := hx
    have hlog : 0 < Real.log x := Real.log_pos (by linarith)
    positivity
  · have hlogTop : Filter.Tendsto Real.log Filter.atTop Filter.atTop := Real.tendsto_log_atTop
    have hinv := hlogTop.inv_tendsto_atTop
    simpa using hinv.neg

/-! ## The oscillatory logarithmic integral converges -/

theorem continuousAt_logPhase (lam : ℝ) {t : ℝ} (ht : t ≠ 0) :
    ContinuousAt (logPhase lam) t := by
  have h1 : ContinuousAt (fun x : ℝ => ((Real.log x : ℝ) : ℂ)) t :=
    Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log ht)
  exact Complex.continuous_exp.continuousAt.comp (h1.const_mul _)

/-- The oscillatory logarithmic kernel `t^{-1-iλ}/log t`. -/
noncomputable def oscLogKernel (lam : ℝ) (t : ℝ) : ℂ :=
  invLogC t * (logPhase lam t * ((t⁻¹ : ℝ) : ℂ))

/-- The integrand of the integrated-by-parts remainder. -/
noncomputable def oscLogRemainder (lam : ℝ) (t : ℝ) : ℂ :=
  (-((((t * (Real.log t) ^ (2 : ℕ))⁻¹ : ℝ)) : ℂ)) * logPhaseAntideriv lam t

theorem norm_oscLogRemainder (lam : ℝ) {t : ℝ} (ht : 1 < t) :
    ‖oscLogRemainder lam t‖ = |lam|⁻¹ * (t * (Real.log t) ^ (2 : ℕ))⁻¹ := by
  have hlog : 0 < Real.log t := Real.log_pos ht
  have hpos : (0 : ℝ) < t * (Real.log t) ^ (2 : ℕ) := by positivity
  rw [oscLogRemainder, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < (t * (Real.log t) ^ (2 : ℕ))⁻¹), norm_logPhaseAntideriv]
  ring

theorem integral_oscLogKernel_eq {lam : ℝ} (hlam : lam ≠ 0) {U : ℝ} (hU : 2 ≤ U) :
    ∫ t in (2 : ℝ)..U, oscLogKernel lam t
      = invLogC U * logPhaseAntideriv lam U - invLogC 2 * logPhaseAntideriv lam 2
        - ∫ t in (2 : ℝ)..U, oscLogRemainder lam t := by
  have hcontRem : ContinuousOn (fun t : ℝ => -((((t * (Real.log t) ^ (2 : ℕ))⁻¹ : ℝ)) : ℂ))
      (Set.uIcc (2 : ℝ) U) := by
    rw [Set.uIcc_of_le hU]
    intro x hx
    have hx2 : (2 : ℝ) ≤ x := hx.1
    have hlog : 0 < Real.log x := Real.log_pos (by linarith)
    have hne : x * (Real.log x) ^ (2 : ℕ) ≠ 0 := by positivity
    refine ContinuousAt.continuousWithinAt ?_
    refine (Complex.continuous_ofReal.continuousAt.comp ?_).neg
    exact (continuousAt_id.mul ((Real.continuousAt_log (by linarith)).pow 2)).inv₀ hne
  have hcontPhase : ContinuousOn (fun t : ℝ => logPhase lam t * ((t⁻¹ : ℝ) : ℂ))
      (Set.uIcc (2 : ℝ) U) := by
    rw [Set.uIcc_of_le hU]
    intro x hx
    have hx2 : (2 : ℝ) ≤ x := hx.1
    refine ContinuousAt.continuousWithinAt ?_
    refine (continuousAt_logPhase lam (by linarith)).mul ?_
    exact Complex.continuous_ofReal.continuousAt.comp (continuousAt_inv₀ (by linarith))
  refine intervalIntegral.integral_mul_deriv_eq_deriv_mul ?_ ?_ ?_ ?_
  · intro x hx
    rw [Set.uIcc_of_le hU] at hx
    exact hasDerivAt_invLogC (by linarith [hx.1])
  · intro x hx
    rw [Set.uIcc_of_le hU] at hx
    exact hasDerivAt_logPhaseAntideriv hlam (by linarith [hx.1])
  · exact hcontRem.intervalIntegrable
  · exact hcontPhase.intervalIntegrable

theorem integrableOn_oscLogRemainder {lam : ℝ} (hlam : lam ≠ 0) :
    MeasureTheory.IntegrableOn (oscLogRemainder lam) (Set.Ioi 2) := by
  have hmeas : MeasureTheory.AEStronglyMeasurable (oscLogRemainder lam)
      (MeasureTheory.volume.restrict (Set.Ioi 2)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro x hx
    have hx2 : (2 : ℝ) < x := hx
    have hlog : 0 < Real.log x := Real.log_pos (by linarith)
    have hne : x * (Real.log x) ^ (2 : ℕ) ≠ 0 := by positivity
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.mul ?_ ?_
    · refine (Complex.continuous_ofReal.continuousAt.comp ?_).neg
      exact (continuousAt_id.mul ((Real.continuousAt_log (by linarith)).pow 2)).inv₀ hne
    · exact (continuousAt_logPhase lam (by linarith)).div_const _
  refine MeasureTheory.Integrable.mono
    (integrableOn_logTailWeight.const_mul |lam|⁻¹) hmeas ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
  have hx2 : (2 : ℝ) < x := hx
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hnn : (0 : ℝ) ≤ |lam|⁻¹ * (x * Real.log x ^ (2 : ℕ))⁻¹ := by positivity
  rw [norm_oscLogRemainder lam (by linarith), Real.norm_eq_abs, abs_of_nonneg hnn]

/-- **The oscillatory logarithmic integral converges.**  Integration by parts against the phase
leaves a boundary term of size `1/log U` and an absolutely convergent remainder. -/
theorem exists_tendsto_integral_oscLogKernel {lam : ℝ} (hlam : lam ≠ 0) :
    ∃ L : ℂ, Filter.Tendsto (fun U : ℝ => ∫ t in (2 : ℝ)..U, oscLogKernel lam t)
      Filter.atTop (nhds L) := by
  have hbdry : Filter.Tendsto (fun U : ℝ => invLogC U * logPhaseAntideriv lam U)
      Filter.atTop (nhds 0) := by
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    have hlogTop : Filter.Tendsto Real.log Filter.atTop Filter.atTop := Real.tendsto_log_atTop
    have hsmall : Filter.Tendsto (fun U : ℝ => |lam|⁻¹ * (Real.log U)⁻¹)
        Filter.atTop (nhds 0) := by
      have := hlogTop.inv_tendsto_atTop
      simpa using this.const_mul |lam|⁻¹
    filter_upwards [hsmall.eventually (eventually_lt_nhds hε), Filter.eventually_gt_atTop 1]
      with U hU hU1
    have hlog : 0 < Real.log U := Real.log_pos hU1
    rw [norm_mul, norm_logPhaseAntideriv, invLogC, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hlog]
    calc (Real.log U)⁻¹ * |lam|⁻¹ = |lam|⁻¹ * (Real.log U)⁻¹ := by ring
      _ < ε := hU
  have hrem : Filter.Tendsto (fun U : ℝ => ∫ t in (2 : ℝ)..U, oscLogRemainder lam t)
      Filter.atTop (nhds (∫ t in Set.Ioi (2 : ℝ), oscLogRemainder lam t)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi (2 : ℝ)
      (integrableOn_oscLogRemainder hlam) Filter.tendsto_id
  refine ⟨0 - invLogC 2 * logPhaseAntideriv lam 2 -
    ∫ t in Set.Ioi (2 : ℝ), oscLogRemainder lam t, ?_⟩
  have hcomb := ((hbdry.sub
    (tendsto_const_nhds (x := invLogC 2 * logPhaseAntideriv lam 2))).sub hrem)
  refine hcomb.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with U hU
  exact (integral_oscLogKernel_eq hlam hU).symm

/-! ## The de la Vallée Poussin error weight -/

theorem exp_neg_sqrt_le {c : ℝ} (hc : 0 < c) {u : ℝ} (hu : 0 < u) :
    Real.exp (-c * Real.sqrt u) ≤ 24 / (c ^ (4 : ℕ) * u ^ (2 : ℕ)) := by
  have hs : 0 ≤ Real.sqrt u := Real.sqrt_nonneg u
  have hcs : 0 ≤ c * Real.sqrt u := by positivity
  have hbound := Real.sum_le_exp_of_nonneg hcs 5
  have hterm : (c * Real.sqrt u) ^ (4 : ℕ) / 24 ≤ Real.exp (c * Real.sqrt u) := by
    refine le_trans ?_ hbound
    have hsum : ∑ i ∈ Finset.range 5, (c * Real.sqrt u) ^ i / (i.factorial : ℝ)
        = 1 + (c * Real.sqrt u) + (c * Real.sqrt u) ^ (2 : ℕ) / 2 + (c * Real.sqrt u) ^ (3 : ℕ) / 6 +
          (c * Real.sqrt u) ^ (4 : ℕ) / 24 := by
      simp [Finset.sum_range_succ]
      ring
    rw [hsum]
    nlinarith [pow_nonneg hcs 2, pow_nonneg hcs 3, pow_nonneg hcs 4]
  have hsq : (Real.sqrt u) ^ (4 : ℕ) = u ^ (2 : ℕ) := by
    have h2 : (Real.sqrt u) ^ (2 : ℕ) = u := Real.sq_sqrt hu.le
    calc (Real.sqrt u) ^ (4 : ℕ) = ((Real.sqrt u) ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      _ = u ^ (2 : ℕ) := by rw [h2]
  have hpow : (c * Real.sqrt u) ^ (4 : ℕ) = c ^ (4 : ℕ) * u ^ (2 : ℕ) := by
    rw [mul_pow, hsq]
  rw [hpow] at hterm
  have hexp : Real.exp (-c * Real.sqrt u) = (Real.exp (c * Real.sqrt u))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [hexp]
  rw [inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
  have hden : (0 : ℝ) < c ^ (4 : ℕ) * u ^ (2 : ℕ) := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hden]
  nlinarith [hterm, hden]

theorem integrableOn_pntErrorWeight {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => Real.exp (-c * Real.sqrt (Real.log t)) / t) (Set.Ioi 2) := by
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => Real.exp (-c * Real.sqrt (Real.log t)) / t)
      (volume.restrict (Set.Ioi 2)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro x hx
    have hx2 : (2 : ℝ) < x := hx
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.div ?_ continuousAt_id (by linarith)
    exact Real.continuous_exp.continuousAt.comp
      ((Real.continuous_sqrt.continuousAt.comp
        (Real.continuousAt_log (by linarith))).const_mul _)
  refine Integrable.mono (integrableOn_logTailWeight.const_mul (24 / c ^ (4 : ℕ))) hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx2 : (2 : ℝ) < x := hx
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hle := exp_neg_sqrt_le hc hlog
  have hxpos : (0 : ℝ) < x := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.exp (-c * Real.sqrt (Real.log x)) / x),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ 24 / c ^ (4 : ℕ) * (x * Real.log x ^ (2 : ℕ))⁻¹)]
  have hgoal : Real.exp (-c * Real.sqrt (Real.log x)) / x
      ≤ 24 / c ^ (4 : ℕ) * (x * Real.log x ^ (2 : ℕ))⁻¹ := by
    rw [div_le_iff₀ hxpos]
    have hkey : Real.exp (-c * Real.sqrt (Real.log x)) ≤ 24 / (c ^ (4 : ℕ) * Real.log x ^ (2 : ℕ)) := hle
    have hrw : 24 / c ^ (4 : ℕ) * (x * Real.log x ^ (2 : ℕ))⁻¹ * x = 24 / (c ^ (4 : ℕ) * Real.log x ^ (2 : ℕ)) := by
      field_simp
    rw [hrw]
    exact hkey
  exact hgoal


end RHTower
