import GaloisForLFunctions.HTGeometry.FirstEndpointMellin

/-! Exact logarithmic endpoint restoration for analytic parameter-dependent kernels. -/
namespace GaloisForLFunctions.HTGeometry.LogarithmicEndpoint
open Complex Set Filter Topology MeasureTheory Metric
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

def remainder (F : ℂ → ℝ → ℂ) (a₀ : ℂ → ℂ) (b : ℝ) (w : ℂ) : ℂ :=
  ∫ t in Ioc (0:ℝ) b, (F w t-a₀ w)/(t:ℂ)

def finitePart (F : ℂ → ℝ → ℂ) (a₀ : ℂ → ℂ) (b : ℝ) (w : ℂ) : ℂ :=
  a₀ w*(Real.log b:ℂ)+remainder F a₀ b w

private theorem density_bound {E : ℂ} {t C : ℝ} (ht : 0 < t) (hE : ‖E‖ ≤ C*t) :
    ‖E/(t:ℂ)‖ ≤ C := by
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht]
  exact (div_le_iff₀ ht).mpr hE

private theorem density_continuousOn {F : ℂ → ℝ → ℂ} {a₀ : ℂ → ℂ} {w : ℂ} {b : ℝ}
    (hc : ContinuousOn (F w) (Ioc (0:ℝ) b)) :
    ContinuousOn (fun t : ℝ => (F w t-a₀ w)/(t:ℂ)) (Ioc 0 b) := by
  intro t ht
  exact ((hc t ht).sub continuousWithinAt_const).div
    Complex.continuous_ofReal.continuousAt.continuousWithinAt
    (Complex.ofReal_ne_zero.mpr (ne_of_gt ht.1))

theorem remainder_integrable {F : ℂ → ℝ → ℂ} {a₀ : ℂ → ℂ} {w : ℂ} {b C : ℝ}
    (hc : ContinuousOn (F w) (Ioc (0:ℝ) b))
    (hC : ∀ t ∈ Ioc (0:ℝ) b, ‖F w t-a₀ w‖ ≤ C*t) :
    IntegrableOn (fun t : ℝ => (F w t-a₀ w)/(t:ℂ)) (Ioc 0 b) := by
  have hi : IntegrableOn (fun _ : ℝ => C) (Ioc (0:ℝ) b) := integrableOn_const (by simp)
  refine hi.mono' ((density_continuousOn hc).aestronglyMeasurable measurableSet_Ioc) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact density_bound ht.1 (hC t ht)

theorem remainder_norm_le {F : ℂ → ℝ → ℂ} {a₀ : ℂ → ℂ} {w : ℂ} {b C : ℝ}
    (hb : 0 ≤ b) (hC : ∀ t ∈ Ioc (0:ℝ) b, ‖F w t-a₀ w‖ ≤ C*t) :
    ‖remainder F a₀ b w‖ ≤ C*b := by
  rw [remainder,← intervalIntegral.integral_of_le hb]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := b)
    (f := fun t => (F w t-a₀ w)/(t:ℂ)) (C := C) (fun t ht => by
      rw [uIoc_of_le hb] at ht
      exact density_bound ht.1 (hC t ht))
  simpa only [sub_zero,abs_of_nonneg hb] using h

theorem remainder_tendsto_zero {F : ℂ → ℝ → ℂ} {a₀ : ℂ → ℂ} {w : ℂ} {b C : ℝ}
    (hb : 0 < b) (hC : ∀ t ∈ Ioc (0:ℝ) b, ‖F w t-a₀ w‖ ≤ C*t) :
    Tendsto (fun e => remainder F a₀ e w) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hlim : Tendsto (fun e : ℝ => C*e) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hc : ContinuousAt (fun e : ℝ => C*e) (0:ℝ) := by fun_prop
    simpa only [mul_zero] using hc.tendsto.mono_left
      (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  apply squeeze_zero_norm' _ hlim
  have he : ∀ᶠ e : ℝ in 𝓝[>] (0:ℝ), e < b :=
    (show ∀ᶠ e : ℝ in 𝓝 (0:ℝ), e < b from Iio_mem_nhds hb).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,he] with e he0 heb
  exact remainder_norm_le he0.le (fun t ht => hC t ⟨ht.1,ht.2.trans heb.le⟩)

/-- Subtracting the actual endpoint coefficient gives a holomorphic parameter family. -/
theorem remainder_analyticAt {F : ℂ → ℝ → ℂ} {a₀ : ℂ → ℂ} {w : ℂ} {b R C : ℝ}
    (hR : 0 < R)
    (hc : ∀ u ∈ ball w R, ContinuousOn (F u) (Ioc (0:ℝ) b))
    (ha : ∀ u ∈ ball w R, AnalyticAt ℂ a₀ u)
    (hd : ∀ t ∈ Ioc (0:ℝ) b, ∀ u ∈ ball w R, AnalyticAt ℂ (fun v => F v t) u)
    (hC : ∀ u ∈ ball w R, ∀ t ∈ Ioc (0:ℝ) b, ‖F u t-a₀ u‖ ≤ C*t) :
    AnalyticAt ℂ (remainder F a₀ b) w := by
  let G (u : ℂ) : ℝ → ℂ := (Ioc (0:ℝ) b).indicator (fun t => (F u t-a₀ u)/(t:ℂ))
  let B : ℝ → ℝ := (Ioc (0:ℝ) b).indicator (fun _ => C)
  have hm (u : ℂ) (hu : u ∈ ball w R) : AEStronglyMeasurable (G u) volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Ioc).mpr
      ((density_continuousOn (hc u hu)).aestronglyMeasurable measurableSet_Ioc)
  have hdif (t : ℝ) : DifferentiableOn ℂ (fun u => G u t) (ball w R) := by
    intro u hu
    by_cases ht : t ∈ Ioc (0:ℝ) b
    · simp only [G,indicator_of_mem ht]
      exact (((hd t ht u hu).sub (ha u hu)).div analyticAt_const
        (Complex.ofReal_ne_zero.mpr (ne_of_gt ht.1))).differentiableAt.differentiableWithinAt
    · simp only [G,indicator_of_notMem ht]
      fun_prop
  have hbound (t : ℝ) (u : ℂ) (hu : u ∈ ball w R) : ‖G u t‖ ≤ B t := by
    by_cases ht : t ∈ Ioc (0:ℝ) b
    · simp only [G,B,indicator_of_mem ht]
      exact density_bound ht.1 (hC u hu t ht)
    · simp only [G,B,indicator_of_notMem ht,norm_zero,le_refl]
  have hi : Integrable B volume := (integrable_indicator_iff measurableSet_Ioc).mpr
    (integrableOn_const (by simp))
  have hDI : DifferentiableOn ℂ (fun u => ∫ t, G u t) (ball w R) := by
    intro v hv
    obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (isOpen_ball.mem_nhds hv)
    exact (differentiableAt_integral_of_cauchy_dominated hr
      (fun u hu => hm u (hsub hu)) (fun t => (hdif t).mono hsub)
      (fun t u hu => hbound t u (hsub hu)) hi).differentiableWithinAt
  have hA := hDI.analyticOnNhd isOpen_ball w (mem_ball_self hR)
  change AnalyticAt ℂ (fun u => ∫ t in Ioc (0:ℝ) b, (F u t-a₀ u)/(t:ℂ)) w
  simpa only [G,integral_indicator measurableSet_Ioc] using hA

/-- The restored logarithm retains the original cutoff integral exactly. -/
theorem cutoff_eq {F : ℂ → ℝ → ℂ} {a₀ : ℂ → ℂ} {w : ℂ} {b e C : ℝ}
    (he : 0 < e) (heb : e ≤ b) (hc : ContinuousOn (F w) (Ioc (0:ℝ) b))
    (hC : ∀ t ∈ Ioc (0:ℝ) b, ‖F w t-a₀ w‖ ≤ C*t) :
    (∫ t in e..b, F w t/(t:ℂ))+a₀ w*(Real.log e:ℂ)=
      finitePart F a₀ b w-remainder F a₀ e w := by
  have hb : 0 < b := he.trans_le heb
  let q := fun t : ℝ => (F w t-a₀ w)/(t:ℂ)
  have hi : IntervalIntegrable q volume 0 b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mpr (remainder_integrable hc hC)
  have hie : IntervalIntegrable q volume 0 e :=
    hi.mono_set (by rw [uIcc_of_le hb.le,uIcc_of_le he.le]; exact Icc_subset_Icc le_rfl heb)
  have hieb : IntervalIntegrable q volume e b :=
    hi.mono_set (by rw [uIcc_of_le hb.le,uIcc_of_le heb]; exact Icc_subset_Icc he.le le_rfl)
  have hip : IntervalIntegrable (fun t : ℝ => (t:ℂ)⁻¹) volume e b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le heb] at ht
    exact (Complex.continuous_ofReal.continuousAt.inv₀
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (he.trans_le ht.1)))).continuousWithinAt
  have hsplit : (∫ t in e..b, F w t/(t:ℂ))=
      a₀ w*(∫ t in e..b, (t:ℂ)⁻¹)+(∫ t in e..b, q t) := by
    rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_add (hip.const_mul _) hieb,
      intervalIntegral.integral_of_le heb,intervalIntegral.integral_of_le heb]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only [q]
    rw [sub_div]
    ring
  have hq : (∫ t in e..b, q t)=remainder F a₀ b w-remainder F a₀ e w := by
    rw [remainder,remainder,← intervalIntegral.integral_of_le hb.le,← intervalIntegral.integral_of_le he.le]
    have hh := intervalIntegral.integral_add_adjacent_intervals hie hieb
    dsimp only [q] at hh ⊢
    linear_combination hh
  have hlog : (∫ t in e..b, (t:ℂ)⁻¹)=(Real.log b:ℂ)-(Real.log e:ℂ) := by
    simp_rw [← Complex.ofReal_inv]
    rw [intervalIntegral.integral_ofReal,integral_inv_of_pos he hb,
      Real.log_div (ne_of_gt hb) (ne_of_gt he),Complex.ofReal_sub]
  rw [hsplit,hq,hlog,finitePart]
  ring

theorem cutoff_tendsto {F : ℂ → ℝ → ℂ} {a₀ : ℂ → ℂ} {w : ℂ} {b C : ℝ}
    (hb : 0 < b) (hc : ContinuousOn (F w) (Ioc (0:ℝ) b))
    (hC : ∀ t ∈ Ioc (0:ℝ) b, ‖F w t-a₀ w‖ ≤ C*t) :
    Tendsto (fun e : ℝ => (∫ t in e..b, F w t/(t:ℂ))+a₀ w*(Real.log e:ℂ))
      (𝓝[>] (0:ℝ)) (𝓝 (finitePart F a₀ b w)) := by
  have h := (tendsto_const_nhds (x := finitePart F a₀ b w)).sub (remainder_tendsto_zero hb hC)
  simp only [sub_zero] at h
  apply h.congr'
  have he : ∀ᶠ e : ℝ in 𝓝[>] (0:ℝ), e < b :=
    (show ∀ᶠ e : ℝ in 𝓝 (0:ℝ), e < b from Iio_mem_nhds hb).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,he] with e he0 heb
  exact (cutoff_eq he0 heb.le hc hC).symm

theorem finitePart_analyticAt {F : ℂ → ℝ → ℂ} {a₀ : ℂ → ℂ} {w : ℂ} {b R C : ℝ}
    (hR : 0 < R)
    (hc : ∀ u ∈ ball w R, ContinuousOn (F u) (Ioc (0:ℝ) b))
    (ha : ∀ u ∈ ball w R, AnalyticAt ℂ a₀ u)
    (hd : ∀ t ∈ Ioc (0:ℝ) b, ∀ u ∈ ball w R, AnalyticAt ℂ (fun v => F v t) u)
    (hC : ∀ u ∈ ball w R, ∀ t ∈ Ioc (0:ℝ) b, ‖F u t-a₀ u‖ ≤ C*t) :
    AnalyticAt ℂ (finitePart F a₀ b) w := by
  unfold finitePart
  exact ((ha w (mem_ball_self hR)).mul analyticAt_const).add (remainder_analyticAt hR hc ha hd hC)

end
end GaloisForLFunctions.HTGeometry.LogarithmicEndpoint
