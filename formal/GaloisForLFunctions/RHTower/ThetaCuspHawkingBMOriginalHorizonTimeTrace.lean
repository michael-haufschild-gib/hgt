import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCausalAdmission
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Original causal horizon trace and temporal moments

The actual scalar period, including the arithmetic coefficient and fixed source lift,
has a differentiable horizon trace. Its original exponential bounds justify passage
to the horizon under every damped time moment. The first moment differentiates the
actual horizon Laplace transform and its prescribed factor `2^(-w)`.

This closes temporal admission of the horizon amplitude on its convergence half-plane.
It does not identify the full metric action or continue that amplitude to a QNM.
-/

open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalHorizonTimeTrace
open D4BMOriginalCausalAdmission D4BMJointSource D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

/-- Horizon value of the unchanged reduced causal solution. -/
def reducedTrace (q : XiZeroCopy) (br : Bool) (amp m : ℂ) (p : ℝ) : ℂ :=
  limUnder atTop (nullValue (-m) (physicalRate q br) amp p)

/-- Limit of the genuine first null derivative. -/
def reducedSlope (q : XiZeroCopy) (br : Bool) (amp m : ℂ) (p : ℝ) : ℂ :=
  limUnder atTop (fun r => deriv (fun a => nullValue (-m) (physicalRate q br) amp a r) p)

private theorem trace_data (q : XiZeroCopy) (br : Bool) (amp m : ℂ) (hm : 0 ≤ m.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℝ, 0 < p  → 
      Tendsto (nullValue (-m) (physicalRate q br) amp p) atTop (𝓝 (reducedTrace q br amp m p)) ∧
      Tendsto (fun r => deriv (fun a => nullValue (-m) (physicalRate q br) amp a r) p)
        atTop (𝓝 (reducedSlope q br amp m p)) ∧
      ∀ r : ℝ, p ≤ r  → 
        ‖reducedTrace q br amp m p-nullValue (-m) (physicalRate q br) amp p r‖  ≤ 
          C*Real.exp (p-r)*Real.exp (m.re*p) ∧
        ‖reducedSlope q br amp m p-deriv (fun a => nullValue (-m) (physicalRate q br) amp a r) p‖  ≤ 
          C*Real.exp (p-r)*Real.exp (m.re*p) := by
  obtain ⟨C,hC,h⟩ := physical_null_horizon_traces q br amp m hm
  refine ⟨C,hC,?_⟩
  intro p hp
  obtain ⟨H,Hp,hH,hHp,hb⟩ := h p hp
  simpa only [reducedTrace,reducedSlope,hH.limUnder_eq,hHp.limUnder_eq] using And.intro hH (And.intro hHp hb)

/-- Uniform convergence of the actual derivative on each bounded positive time interval. -/
theorem reduced_slope_uniform (q : XiZeroCopy) (br : Bool) (amp m : ℂ) (hm : 0 ≤ m.re) (M : ℝ) :
    TendstoUniformlyOn
      (fun r p => deriv (fun a => nullValue (-m) (physicalRate q br) amp a r) p)
      (reducedSlope q br amp m) atTop (Ioo 0 M) := by
  obtain ⟨C,hC,h⟩ := trace_data q br amp m hm
  have ht : Tendsto (fun r : ℝ => C*Real.exp (M-r)*Real.exp (m.re*M)) atTop (𝓝 (0:ℝ)) := by
    have hh := (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (C*Real.exp M)).mul_const (Real.exp (m.re*M))
    simpa only [sub_eq_add_neg,Real.exp_add,mul_assoc,mul_zero,zero_mul] using hh
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [eventually_ge_atTop M,ht.eventually (gt_mem_nhds heps)] with r hr her
  intro p hp
  rw [dist_eq_norm]
  apply ((h p hp.1).2.2 r (hp.2.le.trans hr)).2.trans_lt
  apply lt_of_le_of_lt _ her
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (sub_le_sub_right hp.2.le r)) hC
  · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hp.2.le hm)
  · positivity
  · positivity

/-- The horizon derivative is the derivative of the original horizon trace. -/
theorem reduced_trace_hasDerivAt (q : XiZeroCopy) (br : Bool) (amp m : ℂ)
    (hm : 0 ≤ m.re) {p : ℝ} (hp : 0 < p) :
    HasDerivAt (reducedTrace q br amp m) (reducedSlope q br amp m p) p := by
  obtain ⟨C,hC,h⟩ := trace_data q br amp m hm
  apply hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo
    (reduced_slope_uniform q br amp m hm (p+1))
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with r hr
    intro a ha
    exact (original_null_first (-m) (physicalRate q br) amp ha.1 hr).differentiableAt.hasDerivAt
  · intro a ha
    exact (h a ha.1).1
  · exact ⟨hp,by linarith⟩

/-- Horizon value and slope retain the original exponential growth exponent. -/
theorem reduced_trace_growth (q : XiZeroCopy) (br : Bool) (amp m : ℂ) (hm : 0 ≤ m.re) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p : ℝ, 0 < p  → 
      ‖reducedTrace q br amp m p‖+‖reducedSlope q br amp m p‖  ≤  B*Real.exp (m.re*p) := by
  obtain ⟨C,hC,h⟩ := trace_data q br amp m hm
  obtain ⟨B,hB,hV⟩ := physical_radialResponse_ingoing_growth q br amp m hm
  obtain ⟨D,hD,hDbd⟩ := physical_null_derivatives_bound q br amp m hm
  refine ⟨B+D,add_nonneg hB hD,?_⟩
  intro p hp
  have hv : ‖reducedTrace q br amp m p‖  ≤  B*Real.exp (m.re*p) :=
    le_of_tendsto (h p hp).1.norm (by
      filter_upwards [eventually_ge_atTop (0:ℝ)] with r hr
      exact hV p r hp.le hr)
  have hd : ‖reducedSlope q br amp m p‖  ≤  D*Real.exp (m.re*p) :=
    le_of_tendsto (h p hp).2.1.norm (by
      filter_upwards [eventually_ge_atTop p] with r hr
      exact (hDbd p r hp hr).1)
  nlinarith

/-- Original source coefficient and fixed onset lift remain in the horizon value. -/
def horizonTrace (q : XiZeroCopy) (br : Bool) (amp : ℂ) (p : ℝ) : ℂ :=
  physicalSelfSourceCoefficient q*(reducedTrace q br amp (D4BMOriginalCirclePeriod.readerExponent q) p+
    liftHorizon (physicalRate q br) amp*timeOnset (2*physicalRate q br) p)

def horizonSlope (q : XiZeroCopy) (br : Bool) (amp : ℂ) (p : ℝ) : ℂ :=
  physicalSelfSourceCoefficient q*(reducedSlope q br amp (D4BMOriginalCirclePeriod.readerExponent q) p+
    liftHorizon (physicalRate q br) amp*timeOnsetFirst (2*physicalRate q br) p)

private theorem reader_re_nonneg (q : XiZeroCopy) :
    0 ≤ (D4BMOriginalCirclePeriod.readerExponent q).re := by
  have hr := (xi_divisor_support_re_mem_open_unit q.1).2
  norm_num [D4BMOriginalCirclePeriod.readerExponent]
  linarith

/-- Actual differentiable time trace required by the moving-corner first moment. -/
theorem horizon_trace_hasDerivAt (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    {p : ℝ} (hp : 0 < p) : HasDerivAt (horizonTrace q br amp) (horizonSlope q br amp p) p := by
  exact ((reduced_trace_hasDerivAt q br amp _ (reader_re_nonneg q) hp).add
    ((timeOnset_hasDerivAt (2*physicalRate q br) p).const_mul (liftHorizon (physicalRate q br) amp))).const_mul
      (physicalSelfSourceCoefficient q)


/-- The original lift on a collar is independent of the ingoing time except for its fixed onset. -/
def liftCoefficient (s amp : ℂ) (L : ℝ) : ℂ := radialLift s 0 amp 1 (-L/2)

private theorem lift_coefficient_limit (s amp : ℂ) :
    Tendsto (liftCoefficient s amp) atTop (𝓝 (liftHorizon s amp)) := by
  have hu : Tendsto (fun L : ℝ => radialUnit (-L/2)) atTop (𝓝 (1:ℝ)) := by
    have he := Real.tendsto_exp_neg_atTop_nhds_zero
    have hform (L : ℝ) : radialUnit (-L/2)=(1-Real.exp (-L))/(1+Real.exp (-L)) := by
      apply (eq_div_iff (ne_of_gt (by positivity : 0 < 1+Real.exp (-L)))).mpr
      have hh := radialUnit_one_sub (-L/2)
      rw [show 2*(-L/2) = -L by ring] at hh
      nlinarith
    simp_rw [hform]
    convert! (tendsto_const_nhds.sub he).div (tendsto_const_nhds.add he)
      (by norm_num : (1:ℝ)+0 ≠ 0) using 1; norm_num
  have hP : Tendsto (fun L => D4BMLaplaceRadial.power (2*s) (1+radialUnit (-L/2))) atTop
      (𝓝 (D4BMLaplaceRadial.power (2*s) 2)) := by
    have ht : Tendsto (fun L : ℝ => 1+radialUnit (-L/2)) atTop (𝓝 (2:ℝ)) := by
      convert! hu.const_add 1 using 1; norm_num
    exact ((D4BMLaplaceRadial.power_derivatives (2*s) (by norm_num : (0:ℝ) < 2)).1.continuousAt.tendsto).comp ht
  have hA : Tendsto (fun L => sourceAmplitude s 0 amp 1 (-L/2)) atTop
      (𝓝 (D4BMLaplaceRadial.power (2*s) 2*amp^2)) := by
    simpa only [sourceAmplitude,zero_mul,Complex.exp_zero,one_mul,mul_one] using hP.mul_const (amp^2)
  change Tendsto (fun L : ℝ => radialLift s 0 amp 1 (-L/2)) atTop (𝓝 (liftHorizon s amp))
  simpa only [radialLift,liftHorizon,Complex.ofReal_one,one_pow,mul_one] using
    (hA.mul (hu.ofReal.pow 3)).const_mul (-s*(s-1)/4)

private theorem scalar_on_collar (q : XiZeroCopy) (br : Bool) (amp : ℂ) (p L : ℝ) :
    originalScalar q br amp p (p+L) = physicalSelfSourceCoefficient q*
      (nullValue (-D4BMOriginalCirclePeriod.readerExponent q) (physicalRate q br) amp p (p+L)+
        liftCoefficient (physicalRate q br) amp L*timeOnset (2*physicalRate q br) p) := by
  simp only [originalScalar,D4BMOriginalCausalPotential.nullLift,liftCoefficient,
    show (p-(p+L))/2 = -L/2 by ring]

private theorem collar_continuous (q : XiZeroCopy) (br : Bool) (amp : ℂ) (L : ℝ) :
    Continuous (fun p => originalScalar q br amp p (p+L)) := by
  have hV : Continuous (fun p => nullValue (-D4BMOriginalCirclePeriod.readerExponent q)
      (physicalRate q br) amp p (p+L)) := by
    have hc := (D4BMNativeResponse.radialResponse_continuous
      (-D4BMOriginalCirclePeriod.readerExponent q) (physicalRate q br) amp).comp
      (show Continuous (fun p : ℝ => ((p+(p+L))/2,(p-(p+L))/2)) by fun_prop)
    simpa only [Function.comp_def,nullValue] using hc
  simp_rw [scalar_on_collar]
  exact (hV.add ((continuous_const.mul
    (continuous_iff_continuousAt.mpr (fun p => (timeOnset_hasDerivAt _ p).continuousAt))))).const_mul _

/-- The named time trace is the limit of the complete original scalar, including its source lift. -/
theorem original_horizon_trace (q : XiZeroCopy) (br : Bool) (amp : ℂ) {p : ℝ} (hp : 0 < p) :
    Tendsto (fun L => originalScalar q br amp p (p+L)) atTop (𝓝 (horizonTrace q br amp p)) := by
  obtain ⟨C,hC,h⟩ := trace_data q br amp _ (reader_re_nonneg q)
  have ht : Tendsto (fun L : ℝ => p+L) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (b-p)] with L hL
    linarith
  have hV := (h p hp).1.comp ht
  simpa only [horizonTrace,scalar_on_collar,Function.comp_def] using
    (hV.add ((lift_coefficient_limit (physicalRate q br) amp).mul_const
      (timeOnset (2*physicalRate q br) p))).const_mul (physicalSelfSourceCoefficient q)

private theorem onset_bounded (q : XiZeroCopy) (br : Bool) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p : ℝ, ‖timeOnset (2*physicalRate q br) p‖ ≤ B := by
  have hr := currentRate_re_lt q br
  change (2*physicalRate q br).re < -2 at hr
  obtain ⟨B,hB,h⟩ := timeOnset_pair_bound (2*physicalRate q br) 0 (by linarith)
  refine ⟨B,hB,fun p => ?_⟩
  have hb := h p
  simp only [neg_zero,zero_mul,Real.exp_zero,mul_one] at hb
  exact (le_add_of_nonneg_right (norm_nonneg _)).trans hb

/-- One original-source bound controls every sufficiently distant collar and every positive time. -/
theorem original_collar_growth (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ L : ℝ in atTop, ∀ p : ℝ, 0 < p →
      ‖originalScalar q br amp p (p+L)‖ ≤ B*Real.exp ((D4BMOriginalCirclePeriod.readerExponent q).re*p) := by
  obtain ⟨D,hD,hV⟩ := physical_radialResponse_ingoing_growth q br amp _ (reader_re_nonneg q)
  obtain ⟨A,hA,hAub⟩ := onset_bounded q br
  let K := ‖liftHorizon (physicalRate q br) amp‖+1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hL : ∀ᶠ L in atTop, ‖liftCoefficient (physicalRate q br) amp L‖ ≤ K :=
    ((lift_coefficient_limit (physicalRate q br) amp).norm.eventually
      (gt_mem_nhds (by dsimp [K]; linarith))).mono (fun L h => h.le)
  refine ⟨‖physicalSelfSourceCoefficient q‖*(D+K*A),by positivity,?_⟩
  filter_upwards [hL,eventually_ge_atTop (0:ℝ)] with L hL hL0
  intro p hp
  have he : 1 ≤ Real.exp ((D4BMOriginalCirclePeriod.readerExponent q).re*p) :=
    Real.one_le_exp (mul_nonneg (reader_re_nonneg q) hp.le)
  have hv := hV p (p+L) hp.le (by linarith)
  have hl : ‖liftCoefficient (physicalRate q br) amp L*timeOnset (2*physicalRate q br) p‖ ≤ K*A := by
    rw [norm_mul]
    exact mul_le_mul hL (hAub p) (norm_nonneg _) hK
  rw [scalar_on_collar,norm_mul]
  calc
    _ ≤ ‖physicalSelfSourceCoefficient q‖*
        (D*Real.exp ((D4BMOriginalCirclePeriod.readerExponent q).re*p)+K*A) :=
      mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hv hl)) (norm_nonneg _)
    _ ≤ _ := by
      have hKA : K*A ≤ K*A*Real.exp ((D4BMOriginalCirclePeriod.readerExponent q).re*p) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left he (mul_nonneg hK hA)
      calc
        _ ≤ ‖physicalSelfSourceCoefficient q‖*
            (D*Real.exp ((D4BMOriginalCirclePeriod.readerExponent q).re*p)+
              K*A*Real.exp ((D4BMOriginalCirclePeriod.readerExponent q).re*p)) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl hKA) (norm_nonneg _)
        _ = _ := by ring

private theorem moment_majorant_integrable (n : ℕ) {c : ℝ} (hc : 0 < c) (B : ℝ) :
    IntegrableOn (fun p : ℝ => B*(p^n*Real.exp (-c*p))) (Ioi 0) := by
  have hn : (-1:ℝ) < (n:ℝ) := lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n)
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p:=1) hn (by norm_num) hc
  simpa only [IntegrableOn,Real.rpow_one,Real.rpow_natCast] using h.const_mul B

private theorem moment_bound (n : ℕ) (w : ℂ) (G B p : ℝ) (v : ℂ)
    (hp : 0 ≤ p) (hv : ‖v‖ ≤ B*Real.exp (G*p)) :
    ‖(p:ℂ)^n*Complex.exp (-w*(p:ℂ))*v‖ ≤ B*(p^n*Real.exp (-(w.re-G)*p)) := by
  have he : ‖Complex.exp (-w*(p:ℂ))‖ = Real.exp (-w.re*p) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp,he]
  calc
    _ ≤ (p^n*Real.exp (-w.re*p))*(B*Real.exp (G*p)) :=
      mul_le_mul_of_nonneg_left hv (by positivity)
    _ = _ := by
      rw [show -(w.re-G)*p = -w.re*p+G*p by ring,Real.exp_add]
      ring

/-- All exponentially damped time moments of the actual horizon trace are integrable. -/
theorem horizon_moment_integrable (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (n : ℕ)
    (hw : (D4BMOriginalCirclePeriod.readerExponent q).re < w.re) :
    IntegrableOn (fun p : ℝ => (p:ℂ)^n*Complex.exp (-w*(p:ℂ))*horizonTrace q br amp p) (Ioi 0) := by
  obtain ⟨B,hB,hbound⟩ := original_collar_growth q br amp
  have hb (p : ℝ) (hp : 0 < p) : ‖horizonTrace q br amp p‖ ≤
      B*Real.exp ((D4BMOriginalCirclePeriod.readerExponent q).re*p) :=
    le_of_tendsto (original_horizon_trace q br amp hp).norm (hbound.mono (fun L h => h p hp))
  have hcont : ContinuousOn (horizonTrace q br amp) (Ioi 0) :=
    fun p hp => (horizon_trace_hasDerivAt q br amp hp).continuousAt.continuousWithinAt
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ => (p:ℂ)^n*Complex.exp (-w*(p:ℂ))*horizonTrace q br amp p)
      (volume.restrict (Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    exact (show Continuous (fun p : ℝ => (p:ℂ)^n*Complex.exp (-w*(p:ℂ))) by fun_prop).continuousOn.mul hcont
  apply (moment_majorant_integrable n (sub_pos.mpr hw) B).mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
  exact moment_bound n w _ B p _ hp.le (hb p hp)

/-- Horizon passage commutes with every time moment of the full original causal scalar.
The case `n=1` retains the time moment needed by the frequency derivative in the moving corner. -/
theorem original_horizon_moment_limit (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (n : ℕ)
    (hw : (D4BMOriginalCirclePeriod.readerExponent q).re < w.re) :
    Tendsto (fun L : ℝ => ∫ p in Ioi (0:ℝ),
      (p:ℂ)^n*Complex.exp (-w*(p:ℂ))*originalScalar q br amp p (p+L)) atTop
      (𝓝 (∫ p in Ioi (0:ℝ), (p:ℂ)^n*Complex.exp (-w*(p:ℂ))*horizonTrace q br amp p)) := by
  obtain ⟨B,hB,hbound⟩ := original_collar_growth q br amp
  apply tendsto_integral_filter_of_dominated_convergence
    (fun p : ℝ => B*(p^n*Real.exp (-(w.re-(D4BMOriginalCirclePeriod.readerExponent q).re)*p)))
  · exact Filter.Eventually.of_forall (fun L =>
      ((show Continuous (fun p : ℝ => (p:ℂ)^n*Complex.exp (-w*(p:ℂ))) by fun_prop).mul
        (collar_continuous q br amp L)).aestronglyMeasurable)
  · filter_upwards [hbound] with L hL
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    exact moment_bound n w _ B p _ hp.le (hL p hp)
  · exact moment_majorant_integrable n (sub_pos.mpr hw) B
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    exact (original_horizon_trace q br amp hp).const_mul _

/-- The actual horizon trace's Laplace transform on its convergence half-plane. -/
def horizonTransform (q : XiZeroCopy) (br : Bool) (amp w : ℂ) : ℂ :=
  ∫ p in Ioi (0:ℝ), Complex.exp (-w*(p:ℂ))*horizonTrace q br amp p

/-- Frequency differentiation is the original first time moment, with its sign retained. -/
theorem horizon_transform_hasDerivAt (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : (D4BMOriginalCirclePeriod.readerExponent q).re < w.re) :
    HasDerivAt (horizonTransform q br amp)
      (-(∫ p in Ioi (0:ℝ), (p:ℂ)*Complex.exp (-w*(p:ℂ))*horizonTrace q br amp p)) w := by
  let G := (D4BMOriginalCirclePeriod.readerExponent q).re
  let c := (G+w.re)/2
  have hGc : G < c := by dsimp [c,G]; linarith
  have hcw : c < w.re := by dsimp [c,G]; linarith
  obtain ⟨B,hB,hbound⟩ := original_collar_growth q br amp
  have hb (p : ℝ) (hp : 0 < p) : ‖horizonTrace q br amp p‖ ≤ B*Real.exp (G*p) :=
    le_of_tendsto (original_horizon_trace q br amp hp).norm (hbound.mono (fun L h => h p hp))
  have hcont : ContinuousOn (horizonTrace q br amp) (Ioi 0) :=
    fun p hp => (horizon_trace_hasDerivAt q br amp hp).continuousAt.continuousWithinAt
  let F := fun z : ℂ => fun p : ℝ => Complex.exp (-z*(p:ℂ))*horizonTrace q br amp p
  let D := fun z : ℂ => fun p : ℝ => -(p:ℂ)*Complex.exp (-z*(p:ℂ))*horizonTrace q br amp p
  have hF (z : ℂ) : AEStronglyMeasurable (F z) (volume.restrict (Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    exact (show Continuous (fun p : ℝ => Complex.exp (-z*(p:ℂ))) by fun_prop).continuousOn.mul hcont
  have hD : AEStronglyMeasurable (D w) (volume.restrict (Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    exact (show Continuous (fun p : ℝ => -(p:ℂ)*Complex.exp (-w*(p:ℂ))) by fun_prop).continuousOn.mul hcont
  have hi : Integrable (F w) (volume.restrict (Ioi 0)) := by
    simpa only [IntegrableOn,F,pow_zero,one_mul] using horizon_moment_integrable q br amp w 0 hw
  have hs : {z : ℂ | c < z.re} ∈ 𝓝 w :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hcw
  have hdiff (p : ℝ) (z : ℂ) : HasDerivAt (fun a => F a p) (D z p) z := by
    apply (((Complex.hasDerivAt_exp (-z*(p:ℂ))).comp z
      ((hasDerivAt_id z).neg.mul_const (p:ℂ))).mul_const (horizonTrace q br amp p)).congr_deriv
    dsimp [D]
    ring
  have hder := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F:=F) (F':=D) (μ:=volume.restrict (Ioi 0))
    (bound:=fun p : ℝ => B*(p*Real.exp (-(c-G)*p))) hs
    (Filter.Eventually.of_forall hF) hi hD
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
      intro z hz
      have h1 := moment_bound 1 z G B p (horizonTrace q br amp p) hp.le (hb p hp)
      have hnorm : ‖D z p‖ = ‖(p:ℂ)^1*Complex.exp (-z*(p:ℂ))*horizonTrace q br amp p‖ := by
        simp only [D,pow_one,neg_mul,norm_neg]
      rw [hnorm]
      apply h1.trans
      simp only [pow_one]
      apply mul_le_mul_of_nonneg_left _ hB
      apply mul_le_mul_of_nonneg_left _ hp.le
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (neg_le_neg (sub_le_sub_right hz.le G)) hp.le)
    (by simpa only [IntegrableOn,pow_one] using moment_majorant_integrable 1 (sub_pos.mpr hGc) B)
    (Filter.Eventually.of_forall (fun p z _ => hdiff p z))
  change HasDerivAt (fun z => ∫ p in Ioi (0:ℝ),
    Complex.exp (-z*(p:ℂ))*horizonTrace q br amp p) _ w
  simpa only [F,D,neg_mul,integral_neg] using hder.2

/-- The corner coefficient retains the horizon normalization and its logarithmic derivative. -/
def cornerAmplitude (q : XiZeroCopy) (br : Bool) (amp w : ℂ) : ℂ :=
  Complex.exp (-w*(Real.log 2:ℂ))*horizonTransform q br amp w

/-- The frequency derivative required by the moving corner comes from the original causal trace. -/
theorem corner_amplitude_hasDerivAt (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : (D4BMOriginalCirclePeriod.readerExponent q).re < w.re) :
    HasDerivAt (cornerAmplitude q br amp)
      (Complex.exp (-w*(Real.log 2:ℂ))*(-(Real.log 2:ℂ)*horizonTransform q br amp w-
        ∫ p in Ioi (0:ℝ), (p:ℂ)*Complex.exp (-w*(p:ℂ))*horizonTrace q br amp p)) w := by
  apply (((Complex.hasDerivAt_exp (-w*(Real.log 2:ℂ))).comp w
    ((hasDerivAt_id w).neg.mul_const (Real.log 2:ℂ))).mul
      (horizon_transform_hasDerivAt q br amp w hw)).congr_deriv
  dsimp only [Function.comp_def,Pi.neg_apply,id_eq]
  ring

end
end RHTower.D4BMOriginalHorizonTimeTrace
