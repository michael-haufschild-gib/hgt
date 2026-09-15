import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFundamentalCanonicalContour

/-! Integral attachment of the actual fixed-source logarithmic Jacobi derivative. -/
open Complex Set Filter Topology MeasureTheory Metric
namespace RHTower.D4BMJointSource
open GaloisForLFunctions.HTGeometry D4BMLaplaceRadial
noncomputable section
set_option autoImplicit false

/-- Cauchy domination supplies both admission of the derivative and its exact integral formula. -/
private theorem source_hasDerivAt_integral_of_cauchy_dominated
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℂ → α → ℂ} {z₀ : ℂ} {R : ℝ} {bound : α → ℝ}
    (hR : 0 < R)
    (hmeas : ∀ z ∈ ball z₀ R, AEStronglyMeasurable (F z) μ)
    (hdiff : ∀ a : α, DifferentiableOn ℂ (fun z : ℂ => F z a) (ball z₀ R))
    (hbound : ∀ a : α, ∀ z ∈ ball z₀ R, ‖F z a‖ ≤ bound a)
    (hboundInt : Integrable bound μ) :
    Integrable (fun a => deriv (fun z : ℂ => F z a) z₀) μ ∧
    HasDerivAt (fun z : ℂ => ∫ a : α, F z a ∂μ)
      (∫ a : α, deriv (fun z : ℂ => F z a) z₀ ∂μ) z₀ := by
  have hzmem : z₀ ∈ ball z₀ R := mem_ball_self hR
  have hFint : Integrable (F z₀) μ :=
    Integrable.mono' hboundInt (hmeas z₀ hzmem)
      (Filter.Eventually.of_forall fun a => hbound a z₀ hzmem)
  have hderivMeas : AEStronglyMeasurable
      (fun a : α => deriv (fun z : ℂ => F z a) z₀) μ :=
    aestronglyMeasurable_deriv_param_complex hR hmeas
      (fun a => (hdiff a).differentiableAt (isOpen_ball.mem_nhds hzmem))
  have hderivBound : ∀ a : α, ∀ z ∈ ball z₀ (R/2),
      ‖deriv (fun w : ℂ => F w a) z‖ ≤ (2/R)*bound a := by
    intro a z hz
    have hc := Bottcher.norm_deriv_le_of_bounded_on_ball hR (hdiff a) (hbound a) z hz
    calc
      _ ≤ 2*bound a/R := hc
      _ = _ := by ring
  have hboundInt' : Integrable (fun a => (2/R)*bound a) μ := hboundInt.const_mul (2/R)
  have hdiff' : ∀ᵐ a : α ∂μ, ∀ z ∈ ball z₀ (R/2),
      HasDerivAt (fun w : ℂ => F w a) (deriv (fun w : ℂ => F w a) z) z := by
    filter_upwards with a
    intro z hz
    exact ((hdiff a).differentiableAt
      (isOpen_ball.mem_nhds (ball_subset_ball (by linarith) hz))).hasDerivAt
  have hFmeas : ∀ᶠ z : ℂ in nhds z₀, AEStronglyMeasurable (F z) μ := by
    filter_upwards [ball_mem_nhds z₀ (by positivity : 0<R/2)] with z hz
    exact hmeas z (ball_subset_ball (by linarith) hz)
  refine ⟨hboundInt'.mono' hderivMeas
    (Filter.Eventually.of_forall fun a => hderivBound a z₀ (mem_ball_self (by positivity))),?_⟩
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := fun z a => deriv (fun w : ℂ => F w a) z)
    (bound := fun a => (2/R)*bound a)
    (ball_mem_nhds z₀ (by positivity : 0<R/2)) hFmeas hFint hderivMeas
    (Filter.Eventually.of_forall fun a z hz => hderivBound a z hz) hboundInt' hdiff').2

private theorem jacobiComplexCore_real (n : ℕ) (s : ℂ) (x : ℝ) :
    fundamentalJacobiComplexCore n s (x:ℂ)=fundamentalJacobiCore n s x := by
  simp only [fundamentalJacobiComplexCore,fundamentalJacobiCore,Complex.ofReal_sub,
    Complex.ofReal_ofNat]
  ring

/-- Uniform first subtraction for the actual source-frequency family, derived from its spatial derivative. -/
theorem fundamentalJacobiCore_source_uniform_first_bound (n : ℕ) (s w : ℂ) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v ∈ closedBall w R, ∀ x ∈ Ioc (0:ℝ) 1,
      ‖fundamentalJacobiCore n (s+(w-v)/2) x-
        fundamentalJacobiCore n (s+(w-v)/2) 0‖ ≤ C*x := by
  have hr {z : ℂ} (hz : z ∈ closedBall (0:ℂ) 1) : z.re < 2 := by
    have hn : ‖z‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hz
    have h := (Complex.re_le_norm z).trans hn
    linarith
  have hc : ContinuousOn (fun p : ℂ × ℂ =>
      fundamentalJacobiComplexCoreFirst n (s+(w-p.1)/2) p.2)
      (closedBall w R ×ˢ closedBall (0:ℂ) 1) := by
    intro p hp
    have hslit : 2-p.2 ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      left
      change 0<2-p.2.re
      linarith [hr hp.2]
    have hb : ContinuousAt (fun p : ℂ × ℂ => 2-p.2) p := by fun_prop
    have hs : ContinuousAt (fun p : ℂ × ℂ => s+(w-p.1)/2) p := by fun_prop
    have hp0 := hb.cpow (hs.const_mul 2) hslit
    have hp1 := hb.cpow ((hs.const_mul 2).sub_const 1) hslit
    have hn : ContinuousAt (fun p : ℂ × ℂ => 1-p.2) p := by fun_prop
    exact (((((hs.const_mul 2).neg.mul hp1).mul (hn.pow n))).sub
      ((hp0.const_mul (n:ℂ)).mul (hn.pow (n-1)))).continuousWithinAt
  obtain ⟨C,hC⟩ := ((isCompact_closedBall w R).prod (isCompact_closedBall (0:ℂ) 1)).exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro v hv x hx
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fundamentalJacobiComplexCore n (s+(w-v)/2))
    (f' := fundamentalJacobiComplexCoreFirst n (s+(w-v)/2))
    (fun y hy => (fundamentalJacobiComplexCore_hasDerivAt n (s+(w-v)/2) (hr hy)).hasDerivWithinAt)
    (fun y hy => (hC (v,y) ⟨hv,hy⟩).trans (le_max_left C 0))
    (convex_closedBall (0:ℂ) 1) (by simp : (0:ℂ) ∈ closedBall (0:ℂ) 1)
    (show (x:ℂ) ∈ closedBall (0:ℂ) 1 from by
      simpa only [mem_closedBall,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg hx.1.le] using hx.2)
  have hzero := jacobiComplexCore_real n (s+(w-v)/2) 0
  simp only [Complex.ofReal_zero] at hzero
  rw [hzero] at h
  simpa only [jacobiComplexCore_real,sub_zero,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hx.1.le] using h

/-- The fixed-source Jacobi family differentiates only its exponent, leaving the polynomial weight fixed. -/
theorem fundamentalJacobiCore_source_hasDerivAt (n : ℕ) (s w v : ℂ) {x : ℝ} (hx : x < 2) :
    HasDerivAt (fun u : ℂ => fundamentalJacobiCore n (s+(w-u)/2) x)
      (-fundamentalJacobiCore n (s+(w-v)/2) x*(Real.log (2-x):ℂ)) v := by
  have hbase : ((2-x:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have harg := (((((hasDerivAt_id v).const_sub w).div_const (2:ℂ)).const_add s).const_mul (2:ℂ))
  have hp := harg.const_cpow (c := ((2-x:ℝ):ℂ)) (Or.inl hbase)
  rw [← Complex.ofReal_log (by linarith : (0:ℝ)≤2-x)] at hp
  apply (hp.const_mul ((1-(x:ℂ))^n)).congr_deriv
  dsimp only [fundamentalJacobiCore,id_eq]
  ring

/-- The admitted logarithmic remainder preserves the original source's constant at the horizon. -/
def fundamentalJacobiTortoiseRemainder (n : ℕ) (w s : ℂ) (x : ℝ) : ℂ :=
  (x:ℂ)^w*(fundamentalJacobiCore n s x*((Real.log x:ℂ)-(Real.log (2-x):ℂ))/2-
    fundamentalJacobiCore n s 0*((Real.log x:ℂ)-(Real.log 2:ℂ))/2)

/-- The derivative of the first-subtracted source density is twice the actual tortoise remainder. -/
theorem fundamentalJacobiDensity_source_hasDerivAt (n : ℕ) (w s : ℂ)
    {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    HasDerivAt (fun v : ℂ => (x:ℂ)^v*(fundamentalJacobiCore n (s+(w-v)/2) x-
      fundamentalJacobiCore n (s+(w-v)/2) 0))
      (2*fundamentalJacobiTortoiseRemainder n w s x) w := by
  have hp := (hasDerivAt_id w).const_cpow (c := (x:ℂ))
    (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  rw [← Complex.ofReal_log hx.le] at hp
  have hg := fundamentalJacobiCore_source_hasDerivAt n s w w (by linarith : x < 2)
  have hz := fundamentalJacobiCore_source_hasDerivAt n s w w (by norm_num : (0:ℝ)<2)
  apply (hp.mul (hg.sub hz)).congr_deriv
  simp only [Pi.sub_apply,sub_self,zero_div,add_zero,sub_zero,id_eq]
  dsimp only [fundamentalJacobiTortoiseRemainder]
  ring

/-- Differentiating the actual first subtraction admits its logarithmic remainder and
identifies the derivative of its integral. No logarithmic bound or interchange premise is supplied. -/
theorem fundamentalJacobiTortoiseRemainder_integrable_hasDerivAt (n : ℕ) (w s : ℂ)
    (hw : -2 < w.re) :
    IntegrableOn (fundamentalJacobiTortoiseRemainder n w s) (Ioc (0:ℝ) 1) ∧
    HasDerivAt (fun v : ℂ => ∫ x in Ioc (0:ℝ) 1,
      (x:ℂ)^v*(fundamentalJacobiCore n (s+(w-v)/2) x-
        fundamentalJacobiCore n (s+(w-v)/2) 0))
      (2*∫ x in Ioc (0:ℝ) 1, fundamentalJacobiTortoiseRemainder n w s x) w := by
  let R : ℝ := (w.re+2)/2
  let beta : ℝ := w.re-R
  have hR : 0<R := by dsimp only [R];linarith
  have hbeta : -2<beta := by dsimp only [beta,R];linarith
  obtain ⟨C,hC0,hC⟩ := fundamentalJacobiCore_source_uniform_first_bound n s w R
  have hreal (v : ℂ) (hv : v ∈ ball w R) : beta ≤ v.re := by
    have hn : ‖v-w‖<R := by simpa only [mem_ball,dist_eq_norm] using hv
    have hr := Complex.re_le_norm (w-v)
    rw [Complex.sub_re,norm_sub_rev] at hr
    dsimp only [beta]
    linarith
  let F (v : ℂ) : ℝ → ℂ := (Ioc (0:ℝ) 1).indicator (fun x =>
    (x:ℂ)^v*(fundamentalJacobiCore n (s+(w-v)/2) x-
      fundamentalJacobiCore n (s+(w-v)/2) 0))
  let bound : ℝ → ℝ := (Ioc (0:ℝ) 1).indicator (fun x => C*x^(beta+1))
  have hm (v : ℂ) (_ : v ∈ ball w R) : AEStronglyMeasurable (F v) volume := by
    have hm0 : Measurable (fundamentalJacobiCore n (s+(w-v)/2)) := by
      unfold fundamentalJacobiCore
      fun_prop
    exact ((show Measurable (fun x : ℝ => (x:ℂ)^v*
      (fundamentalJacobiCore n (s+(w-v)/2) x-fundamentalJacobiCore n (s+(w-v)/2) 0))
        by fun_prop).indicator measurableSet_Ioc).aestronglyMeasurable
  have hd (x : ℝ) : DifferentiableOn ℂ (fun v => F v x) (ball w R) := by
    intro v hv
    by_cases hx : x ∈ Ioc (0:ℝ) 1
    · simp only [F,indicator_of_mem hx]
      exact ((differentiableAt_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.1.ne'))).mul
        ((fundamentalJacobiCore_source_hasDerivAt n s w v (by linarith [hx.2] : x<2)).differentiableAt.sub
          (fundamentalJacobiCore_source_hasDerivAt n s w v (by norm_num : (0:ℝ)<2)).differentiableAt)).differentiableWithinAt
    · simp only [F,indicator_of_notMem hx]
      fun_prop
  have hb (x : ℝ) (v : ℂ) (hv : v ∈ ball w R) : ‖F v x‖ ≤ bound x := by
    by_cases hx : x ∈ Ioc (0:ℝ) 1
    · simp only [F,bound,indicator_of_mem hx,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
      calc
        _ ≤ x^v.re*(C*x) := mul_le_mul_of_nonneg_left
          (hC v (ball_subset_closedBall hv) x hx) (Real.rpow_nonneg hx.1.le _)
        _ ≤ x^beta*(C*x) := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 (hreal v hv)) (mul_nonneg hC0 hx.1.le)
        _ = _ := by rw [Real.rpow_add hx.1,Real.rpow_one];ring
    · simp only [F,bound,indicator_of_notMem hx,norm_zero,le_refl]
  have hi : Integrable bound volume := by
    apply (integrable_indicator_iff measurableSet_Ioc).mpr
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1<beta+1))).const_mul C
  have h := source_hasDerivAt_integral_of_cauchy_dominated hR hm hd hb hi
  have hder (x : ℝ) : deriv (fun v : ℂ => F v x) w =
      (Ioc (0:ℝ) 1).indicator (fun x => 2*fundamentalJacobiTortoiseRemainder n w s x) x := by
    by_cases hx : x ∈ Ioc (0:ℝ) 1
    · simp only [F,indicator_of_mem hx]
      exact (fundamentalJacobiDensity_source_hasDerivAt n w s hx.1 hx.2).deriv
    · simp only [F,indicator_of_notMem hx,deriv_const]
  simp_rw [hder] at h
  have hri : IntegrableOn (fun x => 2*fundamentalJacobiTortoiseRemainder n w s x) (Ioc (0:ℝ) 1) :=
    (integrable_indicator_iff measurableSet_Ioc).mp h.1
  have hr : IntegrableOn (fundamentalJacobiTortoiseRemainder n w s) (Ioc (0:ℝ) 1) := by
    change Integrable (fundamentalJacobiTortoiseRemainder n w s) (volume.restrict (Ioc (0:ℝ) 1))
    convert hri.const_mul (1/2:ℂ) using 1
    funext x
    ring
  refine ⟨hr,?_⟩
  have he := h.2
  simp only [F,integral_indicator measurableSet_Ioc,integral_const_mul] at he
  exact he

/-- The fixed-source logarithmic finite part equals its original first-subtracted integral,
including the finite log-two constant. -/
theorem fundamentalJacobiTortoiseMoment_eq_integral (n : ℕ) (w s : ℂ)
    (hw : -2 < w.re) (hw1 : w+1 ≠ 0) :
    fundamentalJacobiTortoiseMoment n w s=
      -fundamentalJacobiCore n s 0*((Real.log 2:ℂ)/(2*(w+1))+1/(2*(w+1)^2))+
        ∫ x in Ioc (0:ℝ) 1, fundamentalJacobiTortoiseRemainder n w s x := by
  have hR := (fundamentalJacobiTortoiseRemainder_integrable_hasDerivAt n w s hw).2
  have hg := fundamentalJacobiCore_source_hasDerivAt n s w w (by norm_num : (0:ℝ)<2)
  simp only [sub_self,zero_div,add_zero,sub_zero] at hg
  have hP := hg.div ((hasDerivAt_id w).add_const 1) hw1
  have hj := hP.add hR
  have he : (fun v : ℂ => fundamentalJacobiMoment n v (s+(w-v)/2)) =ᶠ[𝓝 w]
      (fun v => fundamentalJacobiCore n (s+(w-v)/2) 0/(v+1)+
        ∫ x in Ioc (0:ℝ) 1, (x:ℂ)^v*(fundamentalJacobiCore n (s+(w-v)/2) x-
          fundamentalJacobiCore n (s+(w-v)/2) 0)) := by
    filter_upwards with v
    simp only [fundamentalJacobiMoment,firstEndpointMellin,firstEndpointMellinRemainder,
      Complex.ofReal_one,Complex.one_cpow,mul_one]
  have hj' := hj.congr_of_eventuallyEq he
  have hp := hj'.comp_of_eq (0:ℂ) (((hasDerivAt_id (0:ℂ)).div_const 2).const_add w) (by simp)
  simp only [Function.comp_def,id_eq,sub_self,zero_div,add_zero,mul_one] at hp
  have hepath : (fun u : ℂ => fundamentalJacobiMoment n (w+u/2) (s+(w-(w+u/2))/2)) =
      (fun u : ℂ => fundamentalJacobiMoment n (w+u/2) (s-u/4)) := by
    funext u
    congr 1
    ring
  rw [hepath] at hp
  rw [fundamentalJacobiTortoiseMoment,hp.deriv]
  field_simp [hw1]
  ring

/-- The source's logarithmic leading primitive with its finite constant fixed. -/
def fundamentalJacobiTortoisePrimitive (n : ℕ) (w s : ℂ) (x : ℝ) : ℂ :=
  fundamentalJacobiCore n s 0*(x:ℂ)^(w+1)*
    (((Real.log x:ℂ)-(Real.log 2:ℂ))/(2*(w+1))-1/(2*(w+1)^2))

theorem fundamentalJacobiTortoisePrimitive_hasDerivAt (n : ℕ) (w s : ℂ)
    (hw1 : w+1 ≠ 0) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fundamentalJacobiTortoisePrimitive n w s)
      (fundamentalJacobiCore n s 0*(x:ℂ)^w*((Real.log x:ℂ)-(Real.log 2:ℂ))/2) x := by
  have hp := (power_derivatives (w+1) hx).1
  have hl := (Real.hasDerivAt_log hx.ne').ofReal_comp
  have hd := (((hl.sub_const (Real.log 2:ℂ)).div_const (2*(w+1))).sub_const (1/(2*(w+1)^2)))
  apply (((hp.const_mul (fundamentalJacobiCore n s 0))).mul hd).congr_deriv
  dsimp only [powerFirst,power]
  rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne'),Complex.cpow_one]
  simp only [Complex.ofReal_inv]
  field_simp [hw1,Complex.ofReal_ne_zero.mpr hx.ne']
  ring

/-- The primitive at the upper endpoint is exactly the finite logarithmic constant. -/
theorem fundamentalJacobiTortoisePrimitive_one (n : ℕ) (w s : ℂ) :
    fundamentalJacobiTortoisePrimitive n w s 1=
      -fundamentalJacobiCore n s 0*((Real.log 2:ℂ)/(2*(w+1))+1/(2*(w+1)^2)) := by
  simp only [fundamentalJacobiTortoisePrimitive,Complex.ofReal_one,Complex.one_cpow,
    mul_one,Real.log_one,Complex.ofReal_zero,zero_sub]
  ring

/-- The original logarithmic Jacobi cutoff, with its unchanged lower primitive restored. -/
theorem fundamentalJacobiTortoiseMoment_cutoff (n : ℕ) (w s : ℂ)
    (hw : -2 < w.re) (hw1 : w+1 ≠ 0) :
    Tendsto (fun e : ℝ =>
      (∫ x in e..1, (x:ℂ)^w*fundamentalJacobiCore n s x*
        (((Real.log x:ℂ)-(Real.log (2-x):ℂ))/2))+
      fundamentalJacobiTortoisePrimitive n w s e)
      (𝓝[>] (0:ℝ)) (𝓝 (fundamentalJacobiTortoiseMoment n w s)) := by
  let R := fundamentalJacobiTortoiseRemainder n w s
  let L : ℝ → ℂ := fun x => fundamentalJacobiCore n s 0*(x:ℂ)^w*
    ((Real.log x:ℂ)-(Real.log 2:ℂ))/2
  have hR : IntervalIntegrable R volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)).mpr
      (fundamentalJacobiTortoiseRemainder_integrable_hasDerivAt n w s hw).1
  have hevent : ∀ᶠ e : ℝ in 𝓝[>] (0:ℝ), e ∈ Ioc (0:ℝ) 1 := by
    have he1 : ∀ᶠ e : ℝ in 𝓝 (0:ℝ), e < 1 := Iio_mem_nhds (by norm_num)
    filter_upwards [self_mem_nhdsWithin,he1.filter_mono nhdsWithin_le_nhds] with e he he1
    exact ⟨he,he1.le⟩
  have hid : Tendsto (fun e : ℝ => e) (𝓝[>] (0:ℝ)) (𝓝[uIcc (0:ℝ) 1] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_id.mono_left nhdsWithin_le_nhds,?_⟩
    filter_upwards [hevent] with e he
    rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)]
    exact ⟨he.1.le,he.2⟩
  have hc := intervalIntegral.continuousOn_primitive_interval' hR
    (right_mem_uIcc : (1:ℝ) ∈ uIcc (0:ℝ) 1)
  have hlim := ((hc 0 left_mem_uIcc).tendsto.comp hid).neg
  simp only [Function.comp_apply,← intervalIntegral.integral_symm] at hlim
  have ht := hlim.const_add (fundamentalJacobiTortoisePrimitive n w s 1)
  have hv : fundamentalJacobiTortoisePrimitive n w s 1+(∫ x in (0:ℝ)..1, R x)=
      fundamentalJacobiTortoiseMoment n w s := by
    rw [fundamentalJacobiTortoiseMoment_eq_integral n w s hw hw1,
      fundamentalJacobiTortoisePrimitive_one,
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  rw [hv] at ht
  apply ht.congr'
  filter_upwards [hevent] with e he
  have hRc : IntervalIntegrable R volume e 1 := hR.mono_set (by
    rw [uIcc_of_le he.2,uIcc_of_le (by norm_num : (0:ℝ)≤1)]
    exact fun x hx => ⟨he.1.le.trans hx.1,hx.2⟩)
  have hL : IntervalIntegrable L volume e 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc he.2
    intro x hx
    have hx0 := he.1.trans_le hx.1
    exact (((power_derivatives w hx0).1.continuousAt.const_mul (fundamentalJacobiCore n s 0)).mul
      (((Real.hasDerivAt_log hx0.ne').ofReal_comp.continuousAt).sub continuousAt_const)).div_const 2
      |>.continuousWithinAt
  have hP : (∫ x in e..1, L x)=fundamentalJacobiTortoisePrimitive n w s 1-
      fundamentalJacobiTortoisePrimitive n w s e := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      rw [uIcc_of_le he.2] at hx
      exact fundamentalJacobiTortoisePrimitive_hasDerivAt n w s hw1 (he.1.trans_le hx.1)
    · exact hL
  have hsplit : (∫ x in e..1, (x:ℂ)^w*fundamentalJacobiCore n s x*
      (((Real.log x:ℂ)-(Real.log (2-x):ℂ))/2))=(∫ x in e..1,R x)+(∫ x in e..1,L x) := by
    rw [← intervalIntegral.integral_add hRc hL]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only [R,L,fundamentalJacobiTortoiseRemainder]
    ring
  rw [hsplit,hP]
  ring

end
end RHTower.D4BMJointSource
