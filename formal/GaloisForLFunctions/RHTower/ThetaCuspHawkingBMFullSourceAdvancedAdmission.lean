import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullSourceCircleGrowth
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeGreenBand
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeGoursat
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod

/-!
The actual full theta-square Dirichlet kernel admits the future integral of the
original reduced forcing. The source estimate retains its horizon factor and
the derivative of the fixed onset. No advanced wave equation, tensor response,
Peierls identification, or extinction is asserted here.
-/
open Set MeasureTheory Filter Topology
namespace RHTower.D4BMFullSourceAdvanced
open D4BMNativeCircle D4BMCausalKernel D4BMJointSource D4BMModularCore
noncomputable section
set_option autoImplicit false

/-- A majorant exponent; the physical source and its Hawking clock are unchanged. -/
def decayExponent (q : XiZeroCopy) : ℝ := (sourceGrowthExponent q+2)/2

theorem decayExponent_bounds (q : XiZeroCopy) :
    sourceGrowthExponent q < decayExponent q ∧ decayExponent q < 2 := by
  have h := (sourceGrowthExponent_bounds q).2
  dsimp only [decayExponent]
  constructor <;> linarith

private theorem causal_radius_le_time (h x y : ℝ) (hc : |x-y| ≤ h) :
    Real.arcosh (invariant h x y) ≤ h := by
  have hz := invariant_causal ⟨h,x,y,hc⟩
  have hd := Real.arcosh_nonneg hz
  have hh := (abs_nonneg (x-y)).trans hc
  have hb := invariant_le_cosh_time h x y
  rw [← Real.cosh_arcosh hz] at hb
  simpa only [abs_of_nonneg hd,abs_of_nonneg hh] using Real.cosh_le_cosh.mp hb

/-- Both original causal supports and the image subtraction retain the full source growth bound. -/
theorem kernel_growth (q : XiZeroCopy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h x y X k : ℝ, 0 ≤ h →
      ‖nativeDirichletCausalKernel q h x y X k‖ ≤
        C*Real.exp (sourceGrowthExponent q*(h+|k|)) := by
  obtain ⟨C,hC,hb⟩ := mean_global_growth q
  have ha : 0 ≤ sourceGrowthExponent q := le_trans (by norm_num) (sourceGrowthExponent_bounds q).1
  refine ⟨C,hC,fun h x y X k hh => ?_⟩
  have cone_bound (y : ℝ) :
      ‖if |x-y| ≤ h then nativeRiemannKernel q h x y X k else 0‖ ≤
        C*Real.exp (sourceGrowthExponent q*(h+|k|)) := by
    split_ifs with hc
    · have hz := invariant_causal ⟨h,x,y,hc⟩
      exact (hb _ X k (Real.arcosh_nonneg hz)).trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (by linarith [causal_radius_le_time h x y hc]) ha)) hC)
    · simp only [norm_zero]
      positivity
  have h1 := cone_bound y
  have h2 := cone_bound (-y)
  simp only [sub_neg_eq_add] at h2
  dsimp only [nativeDirichletCausalKernel]
  rw [norm_div,Complex.norm_ofNat]
  exact (div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num)).trans (by linarith)

private theorem kernel_measurable (q : XiZeroCopy) (x X k : ℝ) :
    Measurable (fun p : ℝ × ℝ => nativeDirichletCausalKernel q p.1 x p.2 X k) := by
  classical
  have one_cone (b : Bool) : Measurable (fun p : ℝ × ℝ =>
      if |x-(if b then -p.2 else p.2)| ≤ p.1 then
        nativeRiemannKernel q p.1 x (if b then -p.2 else p.2) X k else 0) := by
    let y : ℝ × ℝ → ℝ := fun p => if b then -p.2 else p.2
    have hy : Continuous y := by
      cases b <;> simp only [y,Bool.false_eq_true,↓reduceIte] <;> fun_prop
    have hi : Continuous (fun p : ℝ × ℝ => invariant p.1 x (y p)) := by
      unfold invariant
      exact (Real.continuous_cosh.comp continuous_fst |>.add
        ((Real.continuous_sinh.comp hy).const_mul (Real.sinh x))).div
        ((Real.continuous_cosh.comp hy).const_mul (Real.cosh x))
        (fun p => mul_ne_zero (Real.cosh_pos x).ne' (Real.cosh_pos (y p)).ne')
    have hr : Continuous (fun p : ℝ × ℝ => Real.arcosh (max 1 (invariant p.1 x (y p)))) :=
      Real.continuousOn_arcosh.comp_continuous (continuous_const.max hi)
        (fun p => show 1 ≤ max 1 (invariant p.1 x (y p)) from le_max_left _ _)
    have hm := ((mean_radial_smooth q X k).continuous.comp hr).measurable
    have hs : MeasurableSet {p : ℝ × ℝ | |x-y p| ≤ p.1} :=
      (isClosed_le (continuous_const.sub hy |>.abs) continuous_fst).measurableSet
    have he : Measurable (fun p : ℝ × ℝ =>
        if |x-y p| ≤ p.1 then mean q (Real.arcosh (max 1 (invariant p.1 x (y p)))) X k else 0) :=
      Measurable.ite hs hm measurable_const
    convert! he using 1
    funext p
    change (if |x-y p| ≤ p.1 then nativeRiemannKernel q p.1 x (y p) X k else 0) =
      (if |x-y p| ≤ p.1 then mean q (Real.arcosh (max 1 (invariant p.1 x (y p)))) X k else 0)
    by_cases hc : |x-y p| ≤ p.1
    · simp only [if_pos hc,nativeRiemannKernel,angularKernel,
        max_eq_right (invariant_causal ⟨p.1,x,y p,hc⟩)]
    · rw [if_neg hc,if_neg hc]
  have h1 := one_cone false
  have h2 := one_cone true
  simpa only [Bool.false_eq_true,if_false,if_true,sub_neg_eq_add,
    nativeDirichletCausalKernel,Pi.sub_apply] using (h1.sub h2).div_const (2:ℂ)

/-- The original full reduced forcing evaluated in the future, with no angular truncation. -/
def density (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ)
    (τ x X k : ℝ) (p : ℝ × ℝ) : ℂ :=
  nativeDirichletCausalKernel q p.1 x p.2 X k*
    timeReducedCoefficient (physicalRate q branch) amplitude (τ+p.1) p.2

private theorem density_measurable (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ)
    (τ x X k : ℝ) : Measurable (density q branch amplitude τ x X k) := by
  have hs := (timeReducedCoefficient_joint_continuous (physicalRate q branch) amplitude).comp
    (show Continuous (fun p : ℝ × ℝ => (τ+p.1,p.2)) by fun_prop)
  exact (kernel_measurable q x X k).mul hs.measurable

/-- Decay in future delay and towards the original horizon holds simultaneously. -/
theorem density_bound (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ x X k h y : ℝ, 0 < h → y < 0 →
      ‖density q branch amplitude τ x X k (h,y)‖ ≤
        (C*Real.exp (-decayExponent q*τ+sourceGrowthExponent q*|k|))*
          (Real.exp ((sourceGrowthExponent q-decayExponent q)*h)*
            Real.exp ((2-decayExponent q)*y)) := by
  obtain ⟨C,hC,hkernel⟩ := kernel_growth q
  obtain ⟨B,hB,hsource⟩ := timeReducedCoefficient_physical_bound q branch amplitude
    (decayExponent q) (decayExponent_bounds q).2
  refine ⟨C*B,mul_nonneg hC hB,fun τ x X k h y hh hy => ?_⟩
  rw [density,norm_mul]
  have hb := mul_le_mul (hkernel h x y X k hh.le) (hsource (τ+h) y hy)
    (norm_nonneg _) (mul_nonneg hC (Real.exp_pos _).le)
  refine hb.trans_eq ?_
  calc
    _ = (C*B)*(Real.exp (sourceGrowthExponent q*(h+|k|))*
        (Real.exp (-decayExponent q*(τ+h))*Real.exp ((2-decayExponent q)*y))) := by ring
    _ = _ := by
      simp only [mul_assoc,← Real.exp_add]
      congr 3
      ring

/-- The source itself admits the full native future integral, independently of RH. -/
private theorem majorant_integrable (q : XiZeroCopy) (D : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => D*
      (Real.exp ((sourceGrowthExponent q-decayExponent q)*p.1)*
        Real.exp ((2-decayExponent q)*p.2))) (Ioi 0 ×ˢ Iio 0) := by
  have hc := decayExponent_bounds q
  have hh := integrableOn_exp_mul_Ioi (show sourceGrowthExponent q-decayExponent q < 0 by linarith) 0
  have hy := (integrableOn_exp_mul_Iic (show 0 < 2-decayExponent q by linarith) 0).mono_set Iio_subset_Iic_self
  rw [IntegrableOn,Measure.volume_eq_prod,← Measure.prod_restrict]
  exact (hh.mul_prod hy).const_mul D

/-- The source itself admits the full native future integral, independently of RH. -/
theorem density_integrable (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ)
    (τ x X k : ℝ) :
    IntegrableOn (density q branch amplitude τ x X k) (Ioi 0 ×ˢ Iio 0) := by
  obtain ⟨C,hC,hb⟩ := density_bound q branch amplitude
  have hm := majorant_integrable q (C*Real.exp (-decayExponent q*τ+sourceGrowthExponent q*|k|))
  apply hm.mono' (density_measurable q branch amplitude τ x X k).aestronglyMeasurable.restrict
  exact (ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Iio)).mpr
    (Eventually.of_forall (fun p hp => hb τ x X k p.1 p.2 hp.1 hp.2))

/-- Absolutely convergent future convolution of the original reduced source. -/
def response (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ) (τ x X k : ℝ) : ℂ :=
  ∫ p in Ioi 0 ×ˢ Iio 0, density q branch amplitude τ x X k p

theorem response_fubini (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ) (τ x X k : ℝ) :
    response q branch amplitude τ x X k =
      ∫ h in Ioi 0, ∫ y in Iio 0, nativeDirichletCausalKernel q h x y X k*
        timeReducedCoefficient (physicalRate q branch) amplitude (τ+h) y := by
  have hi := density_integrable q branch amplitude τ x X k
  rw [response,Measure.volume_eq_prod]
  exact setIntegral_prod _ (by simpa only [Measure.volume_eq_prod] using hi)

private theorem majorant_integral (q : XiZeroCopy) (D : ℝ) :
    (∫ p in Ioi 0 ×ˢ Iio 0, D*
      (Real.exp ((sourceGrowthExponent q-decayExponent q)*p.1)*
        Real.exp ((2-decayExponent q)*p.2))) =
      D/((decayExponent q-sourceGrowthExponent q)*(2-decayExponent q)) := by
  have hc := decayExponent_bounds q
  rw [integral_const_mul,Measure.volume_eq_prod,
    setIntegral_prod_mul (fun h : ℝ => Real.exp ((sourceGrowthExponent q-decayExponent q)*h))
      (fun y : ℝ => Real.exp ((2-decayExponent q)*y)) (Ioi 0) (Iio 0),
    integral_exp_mul_Ioi (by linarith : sourceGrowthExponent q-decayExponent q < 0),
    ← integral_Iic_eq_integral_Iio,
    integral_exp_mul_Iic (by linarith : 0 < 2-decayExponent q)]
  simp only [mul_zero,Real.exp_zero]
  rw [show sourceGrowthExponent q-decayExponent q=-(decayExponent q-sourceGrowthExponent q) by ring]
  field_simp

/-- Uniform decay in physical time, retaining the full source's angular growth. -/
theorem response_bound (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ x X k : ℝ,
      ‖response q branch amplitude τ x X k‖ ≤
        C*Real.exp (-decayExponent q*τ+sourceGrowthExponent q*|k|) := by
  obtain ⟨C,hC,hb⟩ := density_bound q branch amplitude
  have hc := decayExponent_bounds q
  have hden : 0 < (decayExponent q-sourceGrowthExponent q)*(2-decayExponent q) :=
    mul_pos (sub_pos.mpr hc.1) (sub_pos.mpr hc.2)
  refine ⟨C/((decayExponent q-sourceGrowthExponent q)*(2-decayExponent q)),
    div_nonneg hC hden.le,fun τ x X k => ?_⟩
  let D := C*Real.exp (-decayExponent q*τ+sourceGrowthExponent q*|k|)
  have hm := majorant_integrable q D
  have hi := density_integrable q branch amplitude τ x X k
  calc
    _ ≤ ∫ p in Ioi 0 ×ˢ Iio 0, ‖density q branch amplitude τ x X k p‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ p in Ioi 0 ×ˢ Iio 0, D*
        (Real.exp ((sourceGrowthExponent q-decayExponent q)*p.1)*
          Real.exp ((2-decayExponent q)*p.2)) :=
      setIntegral_mono_on hi.norm hm (measurableSet_Ioi.prod measurableSet_Iio)
        (fun p hp => hb τ x X k p.1 p.2 hp.1 hp.2)
    _ = _ := by rw [majorant_integral]; dsimp only [D]; ring

/-- The reduced future convolution has zero trace at fixed original ingoing time. -/
theorem response_ingoing_horizon (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ)
    (v X k : ℝ) :
    Tendsto (fun x : ℝ => response q branch amplitude (v-x) x X k) atBot (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := response_bound q branch amplitude
  have hc : 0 < decayExponent q := by
    have ha := (sourceGrowthExponent_bounds q).1
    have h := (decayExponent_bounds q).1
    linarith
  have ht : Tendsto (fun x : ℝ => decayExponent q*x) atBot atBot :=
    (tendsto_const_mul_atBot_of_pos hc).mpr tendsto_id
  have he := (Real.tendsto_exp_atBot.comp ht).const_mul
    (C*Real.exp (-decayExponent q*v+sourceGrowthExponent q*|k|))
  apply squeeze_zero_norm (fun x => ?_) (by simpa only [mul_zero] using he)
  have h := hb (v-x) x X k
  convert h using 1
  simp only [Function.comp_apply]
  rw [mul_assoc,← Real.exp_add]
  congr 2
  ring

/-- The full future integral preserves the original Dirichlet boundary. -/
theorem response_dirichlet (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ)
    (τ X k : ℝ) : response q branch amplitude τ 0 X k=0 := by
  have hz (h y : ℝ) : nativeDirichletCausalKernel q h 0 y X k=0 := by
    simp only [nativeDirichletCausalKernel,nativeRiemannKernel,invariant,
      Real.sinh_zero,Real.cosh_zero,Real.sinh_neg,Real.cosh_neg,zero_mul,
      one_mul,add_zero,zero_sub,zero_add,abs_neg,sub_self,zero_div]
  simp only [response,density,hz,zero_mul,integral_zero]

private theorem unit_horizon : Tendsto radialUnit atBot (𝓝 (1:ℝ)) := by
  have ht : Tendsto (fun x : ℝ => 2*x) atBot atBot :=
    (tendsto_const_mul_atBot_of_pos (by norm_num : (0:ℝ)<2)).mpr tendsto_id
  have he := Real.tendsto_exp_atBot.comp ht
  have hform : radialUnit=fun x => (1-Real.exp (2*x))/(1+Real.exp (2*x)) := by
    funext x
    apply (eq_div_iff (ne_of_gt (by positivity : 0 < 1+Real.exp (2*x)))).mpr
    have hh := radialUnit_one_sub x
    nlinarith
  rw [hform]
  simpa only [Function.comp_def,Pi.div_apply,sub_zero,add_zero,div_one] using!
    (tendsto_const_nhds.sub he).div (tendsto_const_nhds.add he) (by norm_num : (1:ℝ)+0 ≠ 0)

/-- The lift keeps its original horizon trace even after the reduced future integral is added. -/
theorem lift_plus_response_ingoing_horizon (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ)
    (v X k : ℝ) :
    Tendsto (fun x : ℝ =>
      timeLiftField q branch amplitude (v-x) x ![X,Real.exp k]+
        response q branch amplitude (v-x) x X k) atBot
      (𝓝 ((-physicalRate q branch*(physicalRate q branch-1)/4)*
        D4BMLaplaceRadial.power (2*physicalRate q branch) 2*amplitude^2*
        timeOnset (2*physicalRate q branch) v*fullSquarePotential q ![X,Real.exp k])) := by
  let s := physicalRate q branch
  have hp : ContinuousAt (fun u : ℝ => D4BMLaplaceRadial.power (2*s) (1+u)) 1 :=
    (D4BMLaplaceRadial.power_derivatives (2*s) (by norm_num : 0 < (1+(1:ℝ)))).1.continuousAt.comp
      (f := fun u : ℝ => 1+u) (by fun_prop)
  have hc : ContinuousAt (fun u : ℝ =>
      (-s*(s-1)/4)*(D4BMLaplaceRadial.power (2*s) (1+u)*amplitude^2)*(u:ℂ)^3) 1 := by
    fun_prop
  have hl := (hc.tendsto.comp unit_horizon).mul_const
    (timeOnset (2*s) v*fullSquarePotential q ![X,Real.exp k])
  have he : Tendsto (fun x : ℝ => timeLiftField q branch amplitude (v-x) x ![X,Real.exp k]) atBot
      (𝓝 ((-s*(s-1)/4)*D4BMLaplaceRadial.power (2*s) 2*amplitude^2*
        timeOnset (2*s) v*fullSquarePotential q ![X,Real.exp k])) := by
    simpa only [s,timeLiftField,timeRadialLift,radialLift,sourceAmplitude,zero_mul,
      Complex.exp_zero,one_mul,mul_one,sub_add_cancel,Function.comp_apply,
      Complex.ofReal_one,one_pow,mul_assoc,show (1:ℝ)+1=2 by norm_num] using hl
  simpa only [add_zero] using he.add (response_ingoing_horizon q branch amplitude v X k)

end
end RHTower.D4BMFullSourceAdvanced
