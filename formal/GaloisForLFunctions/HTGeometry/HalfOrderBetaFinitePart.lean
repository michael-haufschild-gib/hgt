import GaloisForLFunctions.HTGeometry.FirstEndpointMellinLimit
import GaloisForLFunctions.HTGeometry.GammaAnalyticOffPoles
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Analytic.Uniqueness

/-! The original square-root horizon norm, with its two fixed endpoint subtractions. -/
namespace GaloisForLFunctions.HTGeometry.HalfOrderBeta
open Complex Set Filter Topology MeasureTheory Metric
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The exact first quotient of the square-root endpoint remainder. -/
def core (z : ℝ) : ℂ := ((-1/(1+Real.sqrt (1-z)) : ℝ) : ℂ)

theorem core_zero : core 0 = -1/2 := by norm_num [core]

theorem core_continuous : Continuous core := by
  unfold core
  exact Complex.continuous_ofReal.comp (continuous_const.div
    (continuous_const.add (Real.continuous_sqrt.comp (continuous_const.sub continuous_id)))
      (fun z => ne_of_gt (by positivity : 0 < 1+Real.sqrt (1-z))))

theorem sqrt_eq_core (z : ℝ) (hz : z ∈ Icc (0:ℝ) 1) :
    (Real.sqrt (1-z):ℂ)=1+(z:ℂ)*core z := by
  have hs := Real.sq_sqrt (sub_nonneg.mpr hz.2)
  have hd : 1+Real.sqrt (1-z) ≠ 0 := by positivity
  have he : Real.sqrt (1-z)=1+z*(-1/(1+Real.sqrt (1-z))) := by
    field_simp [hd]
    nlinarith
  unfold core
  exact_mod_cast he

/-- An exact rational second remainder, including both endpoints. -/
theorem core_sub_zero (z : ℝ) (hz : z ∈ Icc (0:ℝ) 1) :
    core z-core 0=((-z/(2*(1+Real.sqrt (1-z))^(2 : ℕ)):ℝ):ℂ) := by
  have hs := Real.sq_sqrt (sub_nonneg.mpr hz.2)
  have hd : 1+Real.sqrt (1-z) ≠ 0 := by positivity
  have he : -1/(1+Real.sqrt (1-z))-(-1/2) = -z/(2*(1+Real.sqrt (1-z))^(2 : ℕ)) := by
    field_simp [hd]
    nlinarith
  rw [core_zero]
  unfold core
  exact_mod_cast he

/-- The second remainder gains exactly the power needed for Re(w)>-2. -/
theorem core_remainder_bound (z : ℝ) (hz : z ∈ Icc (0:ℝ) 1) :
    ‖core z-core 0‖ ≤ (1/2)*z := by
  rw [core_sub_zero z hz,Complex.norm_real,Real.norm_eq_abs,
    abs_div,abs_neg,abs_of_nonneg hz.1,abs_of_pos (by positivity : 0 < 2*(1+Real.sqrt (1-z))^(2 : ℕ))]
  calc
    _ ≤ z/2 := div_le_div_of_nonneg_left hz.1 (by norm_num)
      (by nlinarith [Real.sqrt_nonneg (1-z),sq_nonneg (Real.sqrt (1-z))])
    _ = _ := by ring

/-- Source-determined finite part of the square-root beta density. -/
def finitePart (w : ℂ) : ℂ := 1/w+firstEndpointMellin (fun _ => core) 1 w

/-- Its analytic numerator is defined also at the removable points w=0,-1. -/
def cleared (w : ℂ) : ℂ :=
  (w+1)+w*core 0+w*(w+1)*firstEndpointMellinRemainder (fun _ => core) 1 w

theorem finitePart_cleared (w : ℂ) (hw : w ≠ 0) (hw1 : w+1 ≠ 0) :
    w*(w+1)*finitePart w=cleared w := by
  simp only [finitePart,cleared,firstEndpointMellin,Complex.ofReal_one,Complex.one_cpow,mul_one]
  field_simp [hw,hw1]
  ring

private theorem remainder_differentiable (w : ℂ) (hw : -2 < w.re) :
    DifferentiableAt ℂ (firstEndpointMellinRemainder (fun _ => core) 1) w := by
  apply firstEndpointMellinRemainder_differentiableAt (by norm_num) le_rfl
    (show 0 < (w.re+2)/2 by linarith) (by norm_num : (0:ℝ) ≤ 1/2)
    (show -2 < (w.re-2)/2 by linarith)
  · intro u hu
    have hn : ‖u-w‖ < (w.re+2)/2 := by simpa only [dist_eq_norm] using mem_ball.mp hu
    have hh := neg_le_of_abs_le (Complex.abs_re_le_norm (u-w))
    simp only [Complex.sub_re] at hh
    linarith
  · intro u hu
    exact core_continuous.measurable
  · intro t ht u hu
    exact differentiableAt_const _
  · intro u hu t ht
    exact core_remainder_bound t ⟨ht.1.le,ht.2⟩

theorem cleared_analytic (w : ℂ) (hw : -2 < w.re) : AnalyticAt ℂ cleared w := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have he : ∀ᶠ v : ℂ in 𝓝 w, -2 < v.re :=
    continuousAt_const.eventually_lt Complex.continuous_re.continuousAt hw
  filter_upwards [he] with v hv
  exact ((differentiableAt_id.add_const 1).add (differentiableAt_id.mul_const (core 0))).add
    ((differentiableAt_id.mul (differentiableAt_id.add_const 1)).mul (remainder_differentiable v hv))

private theorem square_root_cpow (z : ℝ) (hz : z ≤ 1) :
    (1-(z:ℂ))^(3/2-1:ℂ)=(Real.sqrt (1-z):ℂ) := by
  have he : (3/2-1:ℂ)=((1/2:ℝ):ℂ) := by norm_num
  rw [he,← Complex.ofReal_one,← Complex.ofReal_sub,
    ← Complex.ofReal_cpow (sub_nonneg.mpr hz),← Real.sqrt_eq_rpow]

/-- In the ordinary convergence chamber the restored expression is the actual beta integral. -/
theorem finitePart_eq_beta (w : ℂ) (hw : 0 < w.re) : finitePart w=Complex.betaIntegral w (3/2) := by
  have hw0 : w ≠ 0 := by intro he; rw [he] at hw; exact (lt_irrefl 0 hw)
  have hpow : IntervalIntegrable (fun z : ℝ => (z:ℂ)^(w-1)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_cpow' (by simp only [Complex.sub_re,Complex.one_re]; linarith)
  have hcore : IntervalIntegrable (fun z : ℝ => (z:ℂ)^w*core z) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_cpow' (by linarith : -1 < w.re)).mul_continuousOn
      core_continuous.continuousOn
  have hbase : (∫ z in (0:ℝ)..1, (z:ℂ)^(w-1))=1/w := by
    rw [integral_cpow (Or.inl (by simp only [Complex.sub_re,Complex.one_re]; linarith : -1 < (w-1).re)),
      sub_add_cancel,Complex.ofReal_one,Complex.ofReal_zero,Complex.one_cpow,
      Complex.zero_cpow hw0,sub_zero]
  have hbeta : Complex.betaIntegral w (3/2)=
      (∫ z in (0:ℝ)..1, (z:ℂ)^(w-1))+(∫ z in (0:ℝ)..1, (z:ℂ)^w*core z) := by
    rw [← intervalIntegral.integral_add hpow hcore,Complex.betaIntegral,
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro z hz
    change (z:ℂ)^(w-1)*(1-(z:ℂ))^(3/2-1:ℂ)=(z:ℂ)^(w-1)+(z:ℂ)^w*core z
    rw [square_root_cpow z hz.2,sqrt_eq_core z ⟨hz.1.le,hz.2⟩]
    have hp : (z:ℂ)^(w-1)*(z:ℂ)=(z:ℂ)^w := by
      calc
        _ = (z:ℂ)^(w-1)*(z:ℂ)^(1:ℂ) := by rw [Complex.cpow_one]
        _ = _ := by rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hz.1)),sub_add_cancel]
    rw [mul_add,mul_one,← mul_assoc,hp]
  rw [hbeta,hbase,finitePart,
    firstEndpointMellin_eq_integral (by norm_num : (0:ℝ) ≤ 1) (by linarith : -1 < w.re)
      core_continuous.measurable (fun z hz => core_remainder_bound z ⟨hz.1.le,hz.2⟩),
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]

/-- Clearing the two actual endpoint poles gives the Gamma numerator on the initial half-plane. -/
theorem cleared_eq_gamma_pos (w : ℂ) (hw : 0 < w.re) :
    cleared w=Complex.Gamma (w+2)*Complex.Gamma (3/2)/Complex.Gamma (w+3/2) := by
  have hw0 : w ≠ 0 := by intro he; rw [he] at hw; exact (lt_irrefl 0 hw)
  have hw1 : w+1 ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    simp only [Complex.add_re,Complex.one_re,Complex.zero_re] at hh
    linarith
  rw [← finitePart_cleared w hw0 hw1,finitePart_eq_beta w hw,
    Complex.betaIntegral_eq_Gamma_mul_div w (3/2) hw (by norm_num),
    show w+2=w+1+1 by ring,Complex.Gamma_add_one (w+1) hw1,Complex.Gamma_add_one w hw0]
  ring

/-- The gamma evaluation is forced by analytic continuation of the actual restored integral. -/
theorem cleared_eq_gamma (w : ℂ) (hw : -2 < w.re) :
    cleared w=Complex.Gamma (w+2)*Complex.Gamma (3/2)/Complex.Gamma (w+3/2) := by
  let U : Set ℂ := {v : ℂ | -2 < v.re}
  have hf : AnalyticOnNhd ℂ cleared U := fun v hv => cleared_analytic v hv
  have hg : AnalyticOnNhd ℂ
      (fun v => Complex.Gamma (v+2)*Complex.Gamma (3/2)/Complex.Gamma (v+3/2)) U := by
    intro v hv
    have hG0 : AnalyticAt ℂ Complex.Gamma (v+2) :=
      _root_.HTGeometry.analyticAt_Gamma_of_re_pos (by change 0 < v.re+2; change -2 < v.re at hv; linarith)
    have hG : AnalyticAt ℂ (fun u : ℂ => Complex.Gamma (u+2)) v :=
      hG0.comp (f := fun u : ℂ => u+2) (by fun_prop)
    have hI : AnalyticAt ℂ (fun u : ℂ => (Complex.Gamma (u+3/2))⁻¹) v :=
      (Complex.differentiable_one_div_Gamma.analyticAt (v+3/2)).comp
        (f := fun u : ℂ => u+3/2) (by fun_prop)
    simpa only [div_eq_mul_inv] using! (hG.mul (show AnalyticAt ℂ (fun _ : ℂ => Complex.Gamma (3/2)) v from analyticAt_const)).mul hI
  have hU : IsPreconnected U := (convex_halfSpace_re_gt (-2:ℝ)).isPreconnected
  have h1 : (1:ℂ) ∈ U := by norm_num [U]
  have he : cleared =ᶠ[𝓝 (1:ℂ)]
      (fun v => Complex.Gamma (v+2)*Complex.Gamma (3/2)/Complex.Gamma (v+3/2)) := by
    have hopen : IsOpen {v : ℂ | 0 < v.re} := Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
    filter_upwards [hopen.mem_nhds (by simp)] with v hv
    exact cleared_eq_gamma_pos v hv
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hU h1 he hw

private theorem density_split (w : ℂ) (z : ℝ) (hz : z ∈ Ioc (0:ℝ) 1) :
    (z:ℂ)^(w-1)*(Real.sqrt (1-z):ℂ)=(z:ℂ)^(w-1)+(z:ℂ)^w*core z := by
  rw [sqrt_eq_core z ⟨hz.1.le,hz.2⟩]
  have hp : (z:ℂ)^(w-1)*(z:ℂ)=(z:ℂ)^w := by
    calc
      _ = (z:ℂ)^(w-1)*(z:ℂ)^(1:ℂ) := by rw [Complex.cpow_one]
      _ = _ := by rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hz.1)),sub_add_cancel]
  rw [mul_add,mul_one,← mul_assoc,hp]

private theorem cutoff_split (w : ℂ) (hw : w ≠ 0) (e : ℝ) (he : 0 < e) (he1 : e ≤ 1) :
    (∫ z in e..1, (z:ℂ)^(w-1)*(Real.sqrt (1-z):ℂ))+(e:ℂ)^w/w-
      (e:ℂ)^(w+1)/(2*(w+1)) =
      1/w+((∫ z in e..1, (z:ℂ)^w*core z)+core 0*(e:ℂ)^(w+1)/(w+1)) := by
  have hpos (z : ℝ) (hz : z ∈ uIcc e 1) : 0 < z := by
    rw [uIcc_of_le he1] at hz
    exact he.trans_le hz.1
  have hp (v : ℂ) : IntervalIntegrable (fun z : ℝ => (z:ℂ)^v) volume e 1 := by
    apply ContinuousOn.intervalIntegrable
    intro z hz
    have h := (Complex.hasStrictDerivAt_cpow_const (c := v)
      (show (z:ℂ) ∈ Complex.slitPlane by simp [Complex.mem_slitPlane_iff,hpos z hz])).hasDerivAt.comp_ofReal
    exact h.continuousAt.continuousWithinAt
  have hcore := (hp w).mul_continuousOn core_continuous.continuousOn
  have hsplit : (∫ z in e..1, (z:ℂ)^(w-1)*(Real.sqrt (1-z):ℂ))=
      (∫ z in e..1, (z:ℂ)^(w-1))+(∫ z in e..1, (z:ℂ)^w*core z) := by
    rw [← intervalIntegral.integral_add (hp (w-1)) hcore,
      intervalIntegral.integral_of_le he1,intervalIntegral.integral_of_le he1]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro z hz
    exact density_split w z ⟨he.trans hz.1,hz.2⟩
  have hwsub : w-1 ≠ -1 := by intro hh; apply hw; linear_combination hh
  have he0 : (0:ℝ) ∉ uIcc e 1 := by intro hh; exact (lt_irrefl 0 (hpos 0 hh))
  rw [hsplit,integral_cpow (Or.inr ⟨hwsub,he0⟩),sub_add_cancel,
    Complex.ofReal_one,Complex.one_cpow,core_zero]
  simp only [div_mul_eq_div_div]
  ring

/-- The actual cutoff density converges after precisely its two horizon counterterms. -/
theorem finitePart_cutoff_tendsto (w : ℂ) (hw : -2 < w.re) (hw0 : w ≠ 0) (hw1 : w+1 ≠ 0) :
    Tendsto (fun e : ℝ => (∫ z in e..1, (z:ℂ)^(w-1)*(Real.sqrt (1-z):ℂ))+
      (e:ℂ)^w/w-(e:ℂ)^(w+1)/(2*(w+1)))
      (𝓝[>] (0:ℝ)) (𝓝 (finitePart w)) := by
  have h := (firstEndpointMellin_cutoff_tendsto (F := fun _ => core)
    (by norm_num : (0:ℝ) < 1) hw hw1 core_continuous.measurable
    (fun z hz => core_continuous.continuousAt)
    (fun z hz => core_remainder_bound z ⟨hz.1.le,hz.2⟩)).const_add (1/w)
  apply h.congr'
  have he : ∀ᶠ e : ℝ in 𝓝[>] (0:ℝ), e < 1 :=
    (show ∀ᶠ e : ℝ in 𝓝 (0:ℝ), e < 1 from Iio_mem_nhds (by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,he] with e he0 he1
  exact (cutoff_split w hw0 e he0 he1.le).symm

/-- The original two-subtraction finite part has its exact beta/Gamma value at every nonreal frequency in the admitted strip. -/
theorem finitePart_eq_gamma (w : ℂ) (hw : -2 < w.re) (hi : w.im ≠ 0) :
    finitePart w=Complex.Gamma w*Complex.Gamma (3/2)/Complex.Gamma (w+3/2) := by
  have hw0 : w ≠ 0 := by intro he; apply hi; rw [he]; rfl
  have hw1 : w+1 ≠ 0 := by
    intro he
    apply hi
    have hh := congrArg Complex.im he
    simpa using hh
  apply mul_left_cancel₀ (mul_ne_zero hw0 hw1)
  rw [finitePart_cleared w hw0 hw1,cleared_eq_gamma w hw,
    show w+2=w+1+1 by ring,Complex.Gamma_add_one (w+1) hw1,Complex.Gamma_add_one w hw0]
  ring

/-- The admitted original radial norm never vanishes at a nonreal frequency in the fundamental strip. -/
theorem finitePart_ne_zero (w : ℂ) (hw : -2 < w.re) (hi : w.im ≠ 0) : finitePart w ≠ 0 := by
  have hG : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero (fun n hn => by
    apply hi
    have hh := congrArg Complex.im hn
    simpa using hh)
  have hD : Complex.Gamma (w+3/2) ≠ 0 := Complex.Gamma_ne_zero (fun n hn => by
    apply hi
    have hh := congrArg Complex.im hn
    simpa using hh)
  rw [finitePart_eq_gamma w hw hi]
  exact div_ne_zero (mul_ne_zero hG (Complex.Gamma_ne_zero_of_re_pos (by norm_num))) hD

end
end GaloisForLFunctions.HTGeometry.HalfOrderBeta
