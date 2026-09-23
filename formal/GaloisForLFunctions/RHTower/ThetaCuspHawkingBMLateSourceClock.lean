import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSpinTwoDelayCharacteristic

/-! Exact late evaluation of the literal finite two-source clock, its moving-cap
flux, and the retained native spin-two delay bulk. The original onset and clock
rates are unchanged. These identities do not assert cancellation of the complete
nonlinear physical action. -/

open Set Filter Topology MeasureTheory
namespace RHTower.D4BMLateSourceClock
open GaloisForLFunctions.HTGeometry D4BMSpinTwoDelay D4BMReducedOpticalTail
  D4BMJointSource D4BMModularCore D4BMHorizon D4BMNativeSpinTwoPrimitive
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

private def alpha (s : ℂ) : ℂ := (2*s+1)*(2*s+2)
private def onsetCoefficient (s : ℂ) (w : ℝ) : ℂ :=
  s*(s-1)/2*(w:ℂ)*(3+(2*s+3)*(w:ℂ))/(1+(w:ℂ))

/-- Coefficient of the original onset history in the two-source late clock. -/
def memoryCoefficient (q : XiZeroCopy) (branch : Bool) (w : ℝ) : ℂ :=
  let s := physicalRate q branch
  alpha s*(alpha (-s-3)-6*onsetCoefficient (-s-3) w)*(tailClock:ℂ)

/-- Coefficient contributed by the original moving terminal cap. -/
def terminalCoefficient (q : XiZeroCopy) (branch : Bool) (V : ℝ) : ℂ :=
  let s := physicalRate q branch
  alpha s*alpha (-s-3)*Complex.exp (-6*(V:ℂ))/6

private theorem finite_tail (c : ℝ) (hc : 1 ≤ c) :
    (∫ v in (0:ℝ)..c, Real.exp (-6*v)*Real.smoothTransition v) =
      tailClock-Real.exp (-6*c)/6 := by
  have he : Continuous (fun v : ℝ => Real.exp (-6*v)) := by fun_prop
  have hf : Continuous (fun v : ℝ => Real.exp (-6*v)*Real.smoothTransition v) :=
    he.mul (Real.smoothTransition.contDiff (n := 0)).continuous
  have ht : (∫ v in (1:ℝ)..c, Real.exp (-6*v)*Real.smoothTransition v) =
      (Real.exp (-6)-Real.exp (-6*c))/6 := by
    have hfun : (∫ v in (1:ℝ)..c, Real.exp (-6*v)*Real.smoothTransition v) =
        ∫ v in (1:ℝ)..c, Real.exp (-6*v) := by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [uIcc_of_le hc] at hv
      dsimp only
      rw [Real.smoothTransition.one_of_one_le hv.1,mul_one]
    rw [hfun]
    have hd (v : ℝ) : HasDerivAt (fun x : ℝ => -Real.exp (-6*x)/6)
        (Real.exp (-6*v)) v := by
      apply (((((hasDerivAt_id v).const_mul (-6)).exp).neg).div_const 6).congr_deriv
      simp only [id_eq,mul_one]
      ring
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v _ => hd v) (he.intervalIntegrable (μ:=volume) 1 c)
    rw [hint]
    simp only [mul_one]
    ring
  have hs := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ:=volume) 0 1) (hf.intervalIntegrable (μ:=volume) 1 c)
  rw [ht] at hs
  dsimp [tailClock]
  linarith only [hs]

private theorem profile_pair (s : ℂ) (u w h v : ℝ) (hh : 1 < h) (hv : 0 ≤ v) :
    clockProfile s u (v+h)*clockProfile (-s-3) w v =
      alpha s*Complex.exp (2*s*(h:ℂ))*
        ((alpha (-s-3))*((Real.exp (-6*v)*Real.smoothTransition v:ℝ):ℂ)-
          onsetCoefficient (-s-3) w*((Real.exp (-6*v)*deriv Real.smoothTransition v:ℝ):ℂ)) := by
  have hvh : 1 < v+h := by linarith
  have hd : deriv Real.smoothTransition (v+h)=0 :=
    deriv_smoothTransition_eq_zero_of_notMem
      (fun ht => not_le_of_gt hvh ht.2)
  have he : Complex.exp (2*s*((v+h:ℝ):ℂ))*Complex.exp (2*(-s-3)*(v:ℂ)) =
      Complex.exp (2*s*(h:ℂ))*(Real.exp (-6*v):ℂ) := by
    rw [Complex.ofReal_exp,← Complex.exp_add,← Complex.exp_add]
    congr 1
    push_cast
    ring
  dsimp [clockProfile,alpha,onsetCoefficient]
  rw [Real.smoothTransition.one_of_one_le hvh.le,hd]
  push_cast at he ⊢
  simp only [mul_one,mul_zero,sub_zero]
  linear_combination ((2*s+1)*(2*s+2)*
    (((2*(-s-3)+1)*(2*(-s-3)+2))*(Real.smoothTransition v:ℂ)-
      ((-s-3)*(-s-3-1)/2*(w:ℂ)*(3+(2*(-s-3)+3)*(w:ℂ))/(1+(w:ℂ)))*
        ((deriv Real.smoothTransition v:ℝ):ℂ)))*he

/-- Exact original finite two-source clock, including the terminal exponential. -/
theorem clockDensity_late (q : XiZeroCopy) (branch : Bool) (u w V : ℝ)
    (h : Ioo (1:ℝ) (V-1)) :
    clockDensity q branch u w V h =
      memoryCoefficient q branch w*Complex.exp (2*physicalRate q branch*(h.val:ℂ))-
        terminalCoefficient q branch V*Complex.exp ((2*physicalRate q branch+6)*(h.val:ℂ)) := by
  let s := physicalRate q branch
  have hc : 1 ≤ V-h.val := by have := h.property.2; linarith
  have h0c : 0 ≤ V-h.val := by linarith
  have he : Continuous (fun v : ℝ => Real.exp (-6*v)) := by fun_prop
  have hf : Continuous (fun v : ℝ => ((Real.exp (-6*v)*Real.smoothTransition v:ℝ):ℂ)) :=
    Complex.continuous_ofReal.comp (he.mul (Real.smoothTransition.contDiff (n := 0)).continuous)
  have hd : Continuous (fun v : ℝ => ((Real.exp (-6*v)*deriv Real.smoothTransition v:ℝ):ℂ)) :=
    Complex.continuous_ofReal.comp (he.mul continuous_deriv_smoothTransition)
  rw [clockDensity_original]
  have hp : (∫ v in (0:ℝ)..(V-h.val), clockProfile s u (v+h.val)*clockProfile (-s-3) w v) =
      alpha s*Complex.exp (2*s*(h.val:ℂ))*
        (alpha (-s-3)*((∫ v in (0:ℝ)..(V-h.val), Real.exp (-6*v)*Real.smoothTransition v : ℝ):ℂ)-
          onsetCoefficient (-s-3) w*((∫ v in (0:ℝ)..(V-h.val), Real.exp (-6*v)*deriv Real.smoothTransition v : ℝ):ℂ)) := by
    calc
      _ = ∫ v in (0:ℝ)..(V-h.val), alpha s*Complex.exp (2*s*(h.val:ℂ))*
          (alpha (-s-3)*((Real.exp (-6*v)*Real.smoothTransition v:ℝ):ℂ)-
            onsetCoefficient (-s-3) w*((Real.exp (-6*v)*deriv Real.smoothTransition v:ℝ):ℂ)) := by
        apply intervalIntegral.integral_congr
        intro v hv
        rw [uIcc_of_le h0c] at hv
        exact profile_pair s u w h.val v h.property.1 hv.1
      _ = _ := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_sub ((hf.intervalIntegrable _ _).const_mul _) ((hd.intervalIntegrable _ _).const_mul _),
          intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
          intervalIntegral.integral_ofReal,intervalIntegral.integral_ofReal]
  change (∫ v in (0:ℝ)..(V-h.val), clockProfile s u (v+h.val)*clockProfile (-s-3) w v)=_
  rw [hp,finite_clock_contact,Real.smoothTransition.one_of_one_le hc,mul_one,finite_tail _ hc]
  have hexp : Complex.exp (2*s*(h.val:ℂ))*(Real.exp (-6*(V-h.val)):ℂ) =
      Complex.exp (-6*(V:ℂ))*Complex.exp ((2*s+6)*(h.val:ℂ)) := by
    rw [Complex.ofReal_exp,← Complex.exp_add,← Complex.exp_add]
    congr 1
    push_cast
    ring
  dsimp [memoryCoefficient,terminalCoefficient]
  change _=alpha s*(alpha (-s-3)-6*onsetCoefficient (-s-3) w)*(tailClock:ℂ)*Complex.exp (2*s*(h.val:ℂ))-
    (alpha s*alpha (-s-3)*Complex.exp (-6*(V:ℂ))/6)*Complex.exp ((2*s+6)*(h.val:ℂ))
  push_cast at hexp ⊢
  linear_combination -(alpha s*alpha (-s-3)/6)*hexp

private theorem profile_continuous (s : ℂ) (u : ℝ) : Continuous (clockProfile s u) := by
  have hc : Continuous (fun v : ℝ => (Real.smoothTransition v:ℂ)) :=
    Complex.continuous_ofReal.comp (Real.smoothTransition.contDiff (n := 0)).continuous
  have hd : Continuous (fun v : ℝ => ((deriv Real.smoothTransition v:ℝ):ℂ)) :=
    Complex.continuous_ofReal.comp continuous_deriv_smoothTransition
  unfold clockProfile
  exact (show Continuous (fun v : ℝ => Complex.exp (2*s*(v:ℂ))) by fun_prop).mul
    ((continuous_const.mul hc).sub (continuous_const.mul hd))

/-- Complete observation-cap balance for the literal two-source clock, including both onsets. -/
theorem clockDensity_cap_balance (q : XiZeroCopy) (branch : Bool) (u w V h : ℝ) :
    HasDerivAt (fun T : ℝ => clockDensity q branch u w T h)
      (clockProfile (physicalRate q branch) u V*
        clockProfile (-physicalRate q branch-3) w (V-h)) V := by
  let f : ℝ → ℂ := fun v => clockProfile (physicalRate q branch) u (v+h)*
    clockProfile (-physicalRate q branch-3) w v
  have hf : Continuous f :=
    ((profile_continuous _ _).comp (continuous_id.add_const h)).mul (profile_continuous _ _)
  have ht : HasDerivAt (fun T : ℝ => T-h) 1 V := by
    simpa only [id_eq] using (hasDerivAt_id V).sub_const h
  have hd := (intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable (μ:=volume) 0 (V-h))
    hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt).scomp V ht
  have he : (fun T : ℝ => clockDensity q branch u w T h) =
      (fun T : ℝ => ∫ v in (0:ℝ)..(T-h), f v) := by
    funext T
    exact clockDensity_original q branch u w T h
  rw [he]
  simpa only [Function.comp_def,f,id_eq,sub_add_cancel,one_smul] using hd


private theorem exp_derivative (r : ℂ) (h : ℝ) :
    HasDerivAt (fun v : ℝ => Complex.exp (r*(v:ℂ)))
      (r*Complex.exp (r*(h:ℂ))) h := by
  have hc : HasDerivAt (fun v : ℝ => (v:ℂ)) 1 h := by
    simpa only [id_eq,Complex.ofReal_one] using (hasDerivAt_id h).ofReal_comp
  apply ((hc.const_mul r).cexp).congr_deriv
  simp only [mul_one]
  ring

private theorem late_jets (q : XiZeroCopy) (branch : Bool) (u w V : ℝ)
    (h : Ioo (1:ℝ) (V-1)) :
    HasDerivAt (clockDensity q branch u w V)
      (memoryCoefficient q branch w*(2*physicalRate q branch)*Complex.exp (2*physicalRate q branch*(h.val:ℂ))-
        terminalCoefficient q branch V*(2*physicalRate q branch+6)*Complex.exp ((2*physicalRate q branch+6)*(h.val:ℂ))) h.val ∧
    HasDerivAt (deriv (clockDensity q branch u w V))
      (memoryCoefficient q branch w*(2*physicalRate q branch)^(2 : ℕ)*Complex.exp (2*physicalRate q branch*(h.val:ℂ))-
        terminalCoefficient q branch V*(2*physicalRate q branch+6)^(2 : ℕ)*Complex.exp ((2*physicalRate q branch+6)*(h.val:ℂ))) h.val := by
  let s := 2*physicalRate q branch
  let a := memoryCoefficient q branch w
  let b := terminalCoefficient q branch V
  let f : ℝ → ℂ := fun v => a*Complex.exp (s*(v:ℂ))-b*Complex.exp ((s+6)*(v:ℂ))
  let g : ℝ → ℂ := fun v => a*s*Complex.exp (s*(v:ℂ))-b*(s+6)*Complex.exp ((s+6)*(v:ℂ))
  have hf (v : ℝ) : HasDerivAt f (g v) v := by
    apply (((exp_derivative s v).const_mul a).sub ((exp_derivative (s+6) v).const_mul b)).congr_deriv
    dsimp [g]
    ring
  have hg : HasDerivAt g
      (a*s^(2 : ℕ)*Complex.exp (s*(h.val:ℂ))-b*(s+6)^(2 : ℕ)*Complex.exp ((s+6)*(h.val:ℂ))) h.val := by
    apply (((exp_derivative s h.val).const_mul (a*s)).sub
      ((exp_derivative (s+6) h.val).const_mul (b*(s+6)))).congr_deriv
    ring
  have he : clockDensity q branch u w V =ᶠ[𝓝 h.val] f := by
    filter_upwards [Ioo_mem_nhds h.property.1 h.property.2] with v hv
    exact clockDensity_late q branch u w V ⟨v,hv⟩
  refine ⟨(hf h.val).congr_of_eventuallyEq he,?_⟩
  apply hg.congr_of_eventuallyEq
  filter_upwards [he.deriv] with v hv
  exact hv.trans (hf v).deriv

/-- Actual first and second derivatives of the original clock on its late interval. -/
theorem clockDensity_late_derivatives (q : XiZeroCopy) (branch : Bool) (u w V : ℝ)
    (h : Ioo (1:ℝ) (V-1)) :
    deriv (clockDensity q branch u w V) h.val =
      memoryCoefficient q branch w*(2*physicalRate q branch)*Complex.exp (2*physicalRate q branch*(h.val:ℂ))-
        terminalCoefficient q branch V*(2*physicalRate q branch+6)*Complex.exp ((2*physicalRate q branch+6)*(h.val:ℂ)) ∧
    deriv (deriv (clockDensity q branch u w V)) h.val =
      memoryCoefficient q branch w*(2*physicalRate q branch)^(2 : ℕ)*Complex.exp (2*physicalRate q branch*(h.val:ℂ))-
        terminalCoefficient q branch V*(2*physicalRate q branch+6)^(2 : ℕ)*Complex.exp ((2*physicalRate q branch+6)*(h.val:ℂ)) :=
  ⟨(late_jets q branch u w V h).1.deriv,(late_jets q branch u w V h).2.deriv⟩

/-- The original source terminal cap has a nonzero coefficient at every Xi occurrence. -/
theorem terminalCoefficient_ne_zero (q : XiZeroCopy) (branch : Bool) (V : ℝ) :
    terminalCoefficient q branch V ≠ 0 := by
  have hi : (physicalRate q branch).im ≠ 0 := by
    have hq := xi_divisor_support_im_ne_zero q.1
    cases branch <;> simpa [physicalRate] using hq
  have ha (s : ℂ) (hs : s.im ≠ 0) : alpha s ≠ 0 := by
    apply mul_ne_zero
    · intro hzero
      have hh := congrArg Complex.im hzero
      norm_num [Complex.mul_im] at hh
      exact hs (by linarith)
    · intro hzero
      have hh := congrArg Complex.im hzero
      norm_num [Complex.mul_im] at hh
      exact hs (by linarith)
  have ht : (-physicalRate q branch-3).im ≠ 0 := by
    simpa using hi
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (ha _ hi) (ha _ ht)) (Complex.exp_ne_zero _)) (by norm_num)

/-- The finite cap forces an exact inhomogeneous delay equation in the unchanged clock. -/
theorem clockDensity_late_terminal_law (q : XiZeroCopy) (branch : Bool) (u w V : ℝ)
    (h : Ioo (1:ℝ) (V-1)) :
    deriv (clockDensity q branch u w V) h.val-
      2*physicalRate q branch*clockDensity q branch u w V h.val =
      -6*terminalCoefficient q branch V*Complex.exp ((2*physicalRate q branch+6)*(h.val:ℂ)) := by
  rw [(clockDensity_late_derivatives q branch u w V h).1,clockDensity_late q branch u w V h]
  ring

/-- Exact coefficient with which an exponential clock enters the physical delay transpose. -/
def delayRateCoefficient (r : ℂ) (image : Bool) (x y h : ℝ) : ℂ :=
  let A : ℂ := delaySlope image x y h
  let B : ℂ := D4BMCausalKernel.invariantTimeSecond (h-x+y) x (if image then -y else y)
  r^(2 : ℕ)/A^(2 : ℕ)-3*B*r/A^(3 : ℕ)+(3*B^(2 : ℕ)-A^(2 : ℕ))/A^(4 : ℕ)

/-- The already constructed native spin-two bulk, with both original clock terms evaluated.
The full angular primitive and both choices of causal image are unchanged. -/
theorem delayBulk_late (q : XiZeroCopy) (branch image : Bool) (x y : Iic (0:ℝ)) (V X k : ℝ)
    (h : Ioo (max (1:ℝ) (causalDelayStart image x y)) (V-1)) :
    delayBulk image q branch x y V X k h.val =
      primitive q X k (delayArgument image x y h.val)*
        (memoryCoefficient q branch (radialUnit y)*Complex.exp (2*physicalRate q branch*(h.val:ℂ))*
            delayRateCoefficient (2*physicalRate q branch) image x y h.val-
          terminalCoefficient q branch V*Complex.exp ((2*physicalRate q branch+6)*(h.val:ℂ))*
            delayRateCoefficient (2*physicalRate q branch+6) image x y h.val) := by
  let hlate : Ioo (1:ℝ) (V-1) :=
    ⟨h.val,lt_of_le_of_lt (le_max_left _ _) h.property.1,h.property.2⟩
  obtain ⟨h1,h2⟩ := clockDensity_late_derivatives q branch (radialUnit x) (radialUnit y) V hlate
  unfold delayBulk
  change primitive q X k (delayArgument image x y h.val)*
    (deriv (deriv (clockDensity q branch (radialUnit x) (radialUnit y) V)) h.val/(delaySlope image x y h.val:ℂ)^(2 : ℕ)-
      3*(D4BMCausalKernel.invariantTimeSecond (h.val-x+y) x (if image then -y else y):ℂ)*
        deriv (clockDensity q branch (radialUnit x) (radialUnit y) V) h.val/(delaySlope image x y h.val:ℂ)^(3 : ℕ)+
      (3*(D4BMCausalKernel.invariantTimeSecond (h.val-x+y) x (if image then -y else y):ℂ)^(2 : ℕ)-
        (delaySlope image x y h.val:ℂ)^(2 : ℕ))*clockDensity q branch (radialUnit x) (radialUnit y) V h.val/
          (delaySlope image x y h.val:ℂ)^(4 : ℕ))=_
  rw [h1,h2,clockDensity_late q branch (radialUnit x) (radialUnit y) V hlate]
  dsimp only [delayRateCoefficient]
  ring


/-- Differentiating the original observation cap gives its exact late source flux. -/
theorem clockDensity_terminal_flux (q : XiZeroCopy) (branch : Bool) (u w : ℝ)
    (h : Ioi (1:ℝ)) (V : Ioi (h.val+1)) :
    HasDerivAt (fun T : ℝ => clockDensity q branch u w T h.val)
      (6*terminalCoefficient q branch V.val*
        Complex.exp ((2*physicalRate q branch+6)*(h.val:ℂ))) V.val := by
  let s := physicalRate q branch
  let a := memoryCoefficient q branch w*Complex.exp (2*s*(h.val:ℂ))
  let b := alpha s*alpha (-s-3)/6
  let e := Complex.exp ((2*s+6)*(h.val:ℂ))
  have hd : HasDerivAt (fun T : ℝ => a-b*Complex.exp (-6*(T:ℂ))*e)
      (6*terminalCoefficient q branch V.val*e) V.val := by
    apply ((hasDerivAt_const V.val a).sub
      (((exp_derivative (-6) V.val).const_mul b).mul_const e)).congr_deriv
    dsimp [b,s,terminalCoefficient]
    ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds V.property] with T hT
  have hh : h.val ∈ Ioo (1:ℝ) (T-1) := ⟨h.property,by have ht : h.val+1<T := hT; linarith⟩
  have heq := clockDensity_late q branch u w T ⟨h.val,hh⟩
  dsimp only at heq
  rw [heq]
  dsimp [a,b,e,s,terminalCoefficient]
  ring

/-- The finite observation cap is not stationary, even after the later source onset ends. -/
theorem clockDensity_terminal_flux_ne_zero (q : XiZeroCopy) (branch : Bool) (u w : ℝ)
    (h : Ioi (1:ℝ)) (V : Ioi (h.val+1)) :
    deriv (fun T : ℝ => clockDensity q branch u w T h.val) V.val ≠ 0 := by
  rw [(clockDensity_terminal_flux q branch u w h V).deriv]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (terminalCoefficient_ne_zero q branch V.val))
    (Complex.exp_ne_zero _)


/-- Exact finite translation of the original late observation clock; its cap survives. -/
theorem clockDensity_finite_cap_translation (q : XiZeroCopy) (branch : Bool) (u w : ℝ)
    (h : Ioi (1:ℝ)) (V : Ioi (h.val+1)) (H : Ioi (0:ℝ)) :
    clockDensity q branch u w (V.val+H.val) h.val-clockDensity q branch u w V.val h.val =
      terminalCoefficient q branch V.val*(1-Complex.exp (-6*(H.val:ℂ)))*
        Complex.exp ((2*physicalRate q branch+6)*(h.val:ℂ)) := by
  have hv : h.val ∈ Ioo (1:ℝ) (V.val-1) :=
    ⟨h.property,by have hv0 : h.val+1<V.val := V.property; linarith⟩
  have hvH : h.val ∈ Ioo (1:ℝ) (V.val+H.val-1) :=
    ⟨h.property,by have := hv.2; have hH : 0<H.val := H.property; linarith⟩
  rw [clockDensity_late q branch u w (V.val+H.val) ⟨h.val,hvH⟩,
    clockDensity_late q branch u w V.val ⟨h.val,hv⟩]
  dsimp only [terminalCoefficient]
  have he : Complex.exp (-6*((V.val+H.val:ℝ):ℂ)) =
      Complex.exp (-6*(V.val:ℂ))*Complex.exp (-6*(H.val:ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring

/-- No positive finite cap translation leaves this original source clock unchanged. -/
theorem clockDensity_finite_cap_translation_ne_zero (q : XiZeroCopy) (branch : Bool) (u w : ℝ)
    (h : Ioi (1:ℝ)) (V : Ioi (h.val+1)) (H : Ioi (0:ℝ)) :
    clockDensity q branch u w (V.val+H.val) h.val-clockDensity q branch u w V.val h.val ≠ 0 := by
  rw [clockDensity_finite_cap_translation q branch u w h V H]
  apply mul_ne_zero (mul_ne_zero (terminalCoefficient_ne_zero q branch V.val) ?_) (Complex.exp_ne_zero _)
  have hH : 0 < H.val := H.property
  have hr : Real.exp (-6*H.val) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have he : Complex.exp (-6*(H.val:ℂ)) = (Real.exp (-6*H.val):ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [he]
  exact_mod_cast (sub_pos.mpr hr).ne'


end
end RHTower.D4BMLateSourceClock
