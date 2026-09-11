import GaloisForLFunctions.HTGeometry.FirstEndpointMellinLimit

/-! Exact two-term endpoint restoration for analytic frequency-dependent Mellin families. -/
namespace GaloisForLFunctions.HTGeometry.QuadraticEndpointMellin
open Complex Set Filter Topology MeasureTheory Metric
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

def remainder (F : ℂ → ℝ → ℂ) (a₀ a₁ : ℂ → ℂ) (b : ℝ) (w : ℂ) : ℂ :=
  ∫ t in Ioc (0:ℝ) b, (t:ℂ)^(w-1)*(F w t-a₀ w-a₁ w*(t:ℂ))

def finitePart (F : ℂ → ℝ → ℂ) (a₀ a₁ : ℂ → ℂ) (b : ℝ) (w : ℂ) : ℂ :=
  a₀ w*(b:ℂ)^w/w+a₁ w*(b:ℂ)^(w+1)/(w+1)+remainder F a₀ a₁ b w

private theorem density_bound {w E : ℂ} {t C : ℝ} (ht : 0 < t)
    (hE : ‖E‖ ≤ C*t^2) :
    ‖(t:ℂ)^(w-1)*E‖ ≤ C*t^(w.re+1) := by
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ht,Complex.sub_re,Complex.one_re]
  calc
    _ ≤ t^(w.re-1)*(C*t^2) := mul_le_mul_of_nonneg_left hE (Real.rpow_nonneg ht.le _)
    _ = C*t^(w.re+1) := by
      rw [show w.re+1=(w.re-1)+2 by ring,Real.rpow_add ht,Real.rpow_two]
      ring

private theorem density_continuousOn {F : ℂ → ℝ → ℂ} {a₀ a₁ : ℂ → ℂ} {w : ℂ} {b : ℝ}
    (hc : ContinuousOn (F w) (Ioc (0:ℝ) b)) :
    ContinuousOn (fun t : ℝ => (t:ℂ)^(w-1)*(F w t-a₀ w-a₁ w*(t:ℂ))) (Ioc 0 b) := by
  intro t ht
  have hp := (Complex.hasStrictDerivAt_cpow_const (c := w-1)
    (show (t:ℂ) ∈ Complex.slitPlane by simp [Complex.mem_slitPlane_iff,ht.1])).hasDerivAt.comp_ofReal
  exact hp.continuousAt.continuousWithinAt.mul ((hc t ht).sub continuousWithinAt_const |>.sub
    (continuousWithinAt_const.mul Complex.continuous_ofReal.continuousAt.continuousWithinAt))

/-- Quadratic subtraction gives an integrable original density precisely on Re(w)>-2. -/
theorem remainder_integrable {F : ℂ → ℝ → ℂ} {a₀ a₁ : ℂ → ℂ} {w : ℂ} {b C : ℝ}
    (hb : 0 ≤ b) (hw : -2 < w.re) (hc : ContinuousOn (F w) (Ioc (0:ℝ) b))
    (hC : ∀ t ∈ Ioc (0:ℝ) b, ‖F w t-a₀ w-a₁ w*(t:ℂ)‖ ≤ C*t^2) :
    IntegrableOn (fun t : ℝ => (t:ℂ)^(w-1)*(F w t-a₀ w-a₁ w*(t:ℂ))) (Ioc 0 b) := by
  have hp : IntegrableOn (fun t : ℝ => t^(w.re+1)) (Ioc 0 b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  refine (hp.const_mul C).mono' ((density_continuousOn hc).aestronglyMeasurable measurableSet_Ioc) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact density_bound ht.1 (hC t ht)

/-- The restored small-end remainder has a quantitative bound tending to zero. -/
theorem remainder_norm_le {F : ℂ → ℝ → ℂ} {a₀ a₁ : ℂ → ℂ} {w : ℂ} {b C : ℝ}
    (hb : 0 ≤ b) (hw : -2 < w.re)
    (hC : ∀ t ∈ Ioc (0:ℝ) b, ‖F w t-a₀ w-a₁ w*(t:ℂ)‖ ≤ C*t^2) :
    ‖remainder F a₀ a₁ b w‖ ≤ C*b^(w.re+2)/(w.re+2) := by
  rw [remainder,← intervalIntegral.integral_of_le hb]
  calc
    _ ≤ ∫ t in (0:ℝ)..b, C*t^(w.re+1) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hb
      · filter_upwards with t ht
        exact density_bound ht.1 (hC t ht)
      · exact (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < w.re+1)).const_mul C
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,integral_rpow (Or.inl (by linarith : -1 < w.re+1))]
      rw [show w.re+1+1=w.re+2 by ring,Real.zero_rpow (by linarith : w.re+2 ≠ 0),sub_zero]
      ring

theorem remainder_tendsto_zero {F : ℂ → ℝ → ℂ} {a₀ a₁ : ℂ → ℂ} {w : ℂ} {b C : ℝ}
    (hb : 0 < b) (hw : -2 < w.re)
    (hC : ∀ t ∈ Ioc (0:ℝ) b, ‖F w t-a₀ w-a₁ w*(t:ℂ)‖ ≤ C*t^2) :
    Tendsto (fun e => remainder F a₀ a₁ e w) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hp : 0 < w.re+2 := by linarith
  have hlim : Tendsto (fun e : ℝ => C*e^(w.re+2)/(w.re+2)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h := ((Real.continuousAt_rpow_const 0 (w.re+2) (Or.inr hp.le)).const_mul C).div_const (w.re+2)
    simpa only [Real.zero_rpow hp.ne',mul_zero,zero_div] using h.tendsto.mono_left nhdsWithin_le_nhds
  apply squeeze_zero_norm' _ hlim
  have he : ∀ᶠ e : ℝ in 𝓝[>] (0:ℝ), e < b :=
    (show ∀ᶠ e : ℝ in 𝓝 (0:ℝ), e < b from Iio_mem_nhds hb).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,he] with e he0 heb
  exact remainder_norm_le he0.le hw (fun t ht => hC t ⟨ht.1,ht.2.trans heb.le⟩)

/-- Common quadratic subtraction proves holomorphy even when the entire kernel varies with frequency. -/
theorem remainder_analyticAt {F : ℂ → ℝ → ℂ} {a₀ a₁ : ℂ → ℂ} {w : ℂ} {b R C β : ℝ}
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (hR : 0 < R) (hC0 : 0 ≤ C) (hβ : -2 < β)
    (hreal : ∀ u ∈ ball w R, β ≤ u.re)
    (hc : ∀ u ∈ ball w R, ContinuousOn (F u) (Ioc (0:ℝ) b))
    (ha : ∀ u ∈ ball w R, AnalyticAt ℂ a₀ u ∧ AnalyticAt ℂ a₁ u)
    (hd : ∀ t ∈ Ioc (0:ℝ) b, ∀ u ∈ ball w R, AnalyticAt ℂ (fun v => F v t) u)
    (hC : ∀ u ∈ ball w R, ∀ t ∈ Ioc (0:ℝ) b, ‖F u t-a₀ u-a₁ u*(t:ℂ)‖ ≤ C*t^2) :
    AnalyticAt ℂ (remainder F a₀ a₁ b) w := by
  let G (u : ℂ) : ℝ → ℂ := (Ioc (0:ℝ) b).indicator (fun t => (t:ℂ)^(u-1)*(F u t-a₀ u-a₁ u*(t:ℂ)))
  let B : ℝ → ℝ := (Ioc (0:ℝ) b).indicator (fun t => C*t^(β+1))
  have hmeas (u : ℂ) (hu : u ∈ ball w R) : AEStronglyMeasurable (G u) volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Ioc).mpr
      ((density_continuousOn (hc u hu)).aestronglyMeasurable measurableSet_Ioc)
  have hdiff (t : ℝ) : DifferentiableOn ℂ (fun u => G u t) (ball w R) := by
    intro u hu
    by_cases ht : t ∈ Ioc (0:ℝ) b
    · simp only [G,indicator_of_mem ht]
      exact (((differentiableAt_id.sub_const 1).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt ht.1)))).mul
        (((hd t ht u hu).sub (ha u hu).1).sub ((ha u hu).2.mul analyticAt_const)).differentiableAt).differentiableWithinAt
    · simp only [G,indicator_of_notMem ht]
      fun_prop
  have hbound (t : ℝ) (u : ℂ) (hu : u ∈ ball w R) : ‖G u t‖ ≤ B t := by
    by_cases ht : t ∈ Ioc (0:ℝ) b
    · simp only [G,B,indicator_of_mem ht]
      exact (density_bound ht.1 (hC u hu t ht)).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge ht.1 (ht.2.trans hb1) (by linarith [hreal u hu])) hC0)
    · simp only [G,B,indicator_of_notMem ht,norm_zero,le_refl]
  have hBI : Integrable B volume := by
    apply (integrable_indicator_iff measurableSet_Ioc).mpr
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < β+1))).const_mul C
  have hDI : DifferentiableOn ℂ (fun u => ∫ t, G u t) (ball w R) := by
    intro v hv
    obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (isOpen_ball.mem_nhds hv)
    exact (differentiableAt_integral_of_cauchy_dominated hr
      (fun u hu => hmeas u (hsub hu)) (fun t => (hdiff t).mono hsub)
      (fun t u hu => hbound t u (hsub hu)) hBI).differentiableWithinAt
  have hA := hDI.analyticOnNhd isOpen_ball w (mem_ball_self hR)
  change AnalyticAt ℂ (fun u => ∫ t in Ioc (0:ℝ) b, (t:ℂ)^(u-1)*(F u t-a₀ u-a₁ u*(t:ℂ))) w
  simpa only [G,integral_indicator measurableSet_Ioc] using hA


/-- The exact primitive restoration equals each original positive-cutoff integral. -/
theorem cutoff_eq {F : ℂ → ℝ → ℂ} {a₀ a₁ : ℂ → ℂ} {w : ℂ} {b e C : ℝ}
    (he : 0 < e) (heb : e ≤ b) (hw : -2 < w.re) (hw0 : w ≠ 0) (hw1 : w+1 ≠ 0)
    (hc : ContinuousOn (F w) (Ioc (0:ℝ) b))
    (hC : ∀ t ∈ Ioc (0:ℝ) b, ‖F w t-a₀ w-a₁ w*(t:ℂ)‖ ≤ C*t^2) :
    (∫ t in e..b, (t:ℂ)^(w-1)*F w t)+a₀ w*(e:ℂ)^w/w+a₁ w*(e:ℂ)^(w+1)/(w+1)=
      finitePart F a₀ a₁ b w-remainder F a₀ a₁ e w := by
  have hb : 0 < b := he.trans_le heb
  let q := fun t : ℝ => (t:ℂ)^(w-1)*(F w t-a₀ w-a₁ w*(t:ℂ))
  have hi : IntervalIntegrable q volume 0 b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mpr (remainder_integrable hb.le hw hc hC)
  have hie : IntervalIntegrable q volume 0 e :=
    hi.mono_set (by rw [uIcc_of_le hb.le,uIcc_of_le he.le]; exact Icc_subset_Icc le_rfl heb)
  have hieb : IntervalIntegrable q volume e b :=
    hi.mono_set (by rw [uIcc_of_le hb.le,uIcc_of_le heb]; exact Icc_subset_Icc he.le le_rfl)
  have hpos (t : ℝ) (ht : t ∈ uIcc e b) : 0 < t := by
    rw [uIcc_of_le heb] at ht
    exact he.trans_le ht.1
  have hp (v : ℂ) : IntervalIntegrable (fun t : ℝ => (t:ℂ)^v) volume e b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    exact ((Complex.hasStrictDerivAt_cpow_const (c := v)
      (show (t:ℂ) ∈ Complex.slitPlane by simp [Complex.mem_slitPlane_iff,hpos t ht])).hasDerivAt.comp_ofReal).continuousAt.continuousWithinAt
  have hsplit : (∫ t in e..b, (t:ℂ)^(w-1)*F w t)=
      a₀ w*(∫ t in e..b, (t:ℂ)^(w-1))+a₁ w*(∫ t in e..b, (t:ℂ)^w)+(∫ t in e..b, q t) := by
    rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add ((hp (w-1)).const_mul _) ((hp w).const_mul _),
      ← intervalIntegral.integral_add (((hp (w-1)).const_mul _).add ((hp w).const_mul _)) hieb]
    rw [intervalIntegral.integral_of_le heb,intervalIntegral.integral_of_le heb]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    have ht0 : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (he.trans ht.1))
    have heq : (t:ℂ)^w=(t:ℂ)^(w-1)*(t:ℂ) := by
      symm
      calc
        _ = (t:ℂ)^(w-1)*(t:ℂ)^(1:ℂ) := by rw [Complex.cpow_one]
        _ = _ := by rw [← Complex.cpow_add _ _ ht0,sub_add_cancel]
    dsimp [q]
    rw [heq]
    ring
  have hq : (∫ t in e..b, q t)=remainder F a₀ a₁ b w-remainder F a₀ a₁ e w := by
    rw [remainder,remainder,← intervalIntegral.integral_of_le hb.le,← intervalIntegral.integral_of_le he.le]
    have hh := intervalIntegral.integral_add_adjacent_intervals hie hieb
    dsimp [q] at hh ⊢
    linear_combination hh
  have he0 : (0:ℝ) ∉ uIcc e b := by intro ht; exact (lt_irrefl 0 (hpos 0 ht))
  have hwsub : w-1 ≠ -1 := by intro h; apply hw0; linear_combination h
  have hwn : w ≠ -1 := by intro h; apply hw1; rw [h]; ring
  rw [hsplit,hq,integral_cpow (Or.inr ⟨hwsub,he0⟩),integral_cpow (Or.inr ⟨hwn,he0⟩),sub_add_cancel,finitePart]
  ring

/-- The finite part is the limit of the actual density with exactly its two derived counterterms. -/
theorem cutoff_tendsto {F : ℂ → ℝ → ℂ} {a₀ a₁ : ℂ → ℂ} {w : ℂ} {b C : ℝ}
    (hb : 0 < b) (hw : -2 < w.re) (hw0 : w ≠ 0) (hw1 : w+1 ≠ 0)
    (hc : ContinuousOn (F w) (Ioc (0:ℝ) b))
    (hC : ∀ t ∈ Ioc (0:ℝ) b, ‖F w t-a₀ w-a₁ w*(t:ℂ)‖ ≤ C*t^2) :
    Tendsto (fun e : ℝ => (∫ t in e..b, (t:ℂ)^(w-1)*F w t)+
      a₀ w*(e:ℂ)^w/w+a₁ w*(e:ℂ)^(w+1)/(w+1))
      (𝓝[>] (0:ℝ)) (𝓝 (finitePart F a₀ a₁ b w)) := by
  have h := (tendsto_const_nhds (x := finitePart F a₀ a₁ b w)).sub (remainder_tendsto_zero hb hw hC)
  simp only [sub_zero] at h
  apply h.congr'
  have he : ∀ᶠ e : ℝ in 𝓝[>] (0:ℝ), e < b :=
    (show ∀ᶠ e : ℝ in 𝓝 (0:ℝ), e < b from Iio_mem_nhds hb).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,he] with e he0 heb
  exact (cutoff_eq he0 heb.le hw hw0 hw1 hc hC).symm

/-- Analytic endpoint coefficients and a common quadratic remainder give an analytic restored finite part. -/
theorem finitePart_analyticAt {F : ℂ → ℝ → ℂ} {a₀ a₁ : ℂ → ℂ} {w : ℂ} {b R C β : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1) (hR : 0 < R) (hC0 : 0 ≤ C) (hβ : -2 < β)
    (hw0 : w ≠ 0) (hw1 : w+1 ≠ 0)
    (hreal : ∀ u ∈ ball w R, β ≤ u.re)
    (hc : ∀ u ∈ ball w R, ContinuousOn (F u) (Ioc (0:ℝ) b))
    (ha : ∀ u ∈ ball w R, AnalyticAt ℂ a₀ u ∧ AnalyticAt ℂ a₁ u)
    (hd : ∀ t ∈ Ioc (0:ℝ) b, ∀ u ∈ ball w R, AnalyticAt ℂ (fun v => F v t) u)
    (hC : ∀ u ∈ ball w R, ∀ t ∈ Ioc (0:ℝ) b, ‖F u t-a₀ u-a₁ u*(t:ℂ)‖ ≤ C*t^2) :
    AnalyticAt ℂ (finitePart F a₀ a₁ b) w := by
  have hb0 : (b:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hb)
  have hp : AnalyticAt ℂ (fun u => (b:ℂ)^u) w := by
    simp_rw [Complex.cpow_def_of_ne_zero hb0]
    fun_prop
  have hp1 : AnalyticAt ℂ (fun u => (b:ℂ)^(u+1)) w := by
    simp_rw [Complex.cpow_def_of_ne_zero hb0]
    fun_prop
  unfold finitePart
  exact ((((ha w (mem_ball_self hR)).1.mul hp).div analyticAt_id hw0).add
    (((ha w (mem_ball_self hR)).2.mul hp1).div (analyticAt_id.add analyticAt_const) hw1)).add
      (remainder_analyticAt hb.le hb1 hR hC0 hβ hreal hc ha hd hC)

end
end GaloisForLFunctions.HTGeometry.QuadraticEndpointMellin
