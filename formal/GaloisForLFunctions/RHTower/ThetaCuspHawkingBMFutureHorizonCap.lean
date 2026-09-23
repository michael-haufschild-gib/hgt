import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullSourceAdvancedAdmission
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Original future-horizon kernel and its source-derived boundary integral.
The clock, the complete theta half-square, and both characteristic supports are retained.
The actual onset derivative is integrated with an admitted global majorant. The resulting
cap field has zero Dirichlet value and exactly the original lift's ingoing horizon trace.
Subtracting it cancels the lift-plus-reduced-future-response value at that boundary.

The finite Green cap identity is documented separately on paper. No advanced wave equation,
differentiated Einstein flux, complete-channel action identification, or RH extinction is
asserted by this leaf.
-/
open Set MeasureTheory Filter Topology
namespace RHTower.D4BMFutureHorizon
open D4BMNativeCircle D4BMCausalKernel D4BMJointSource D4BMModularCore
open D4BMFullSourceAdvanced
noncomputable section
set_option autoImplicit false

private theorem unit_limit : Tendsto radialUnit atBot (𝓝 (1:ℝ)) := by
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

private def closedMean (q : XiZeroCopy) (X k z : ℝ) : ℂ :=
  mean q (Real.arcosh (max 1 z)) X k

private theorem closedMean_continuous (q : XiZeroCopy) (X k : ℝ) :
    Continuous (closedMean q X k) := by
  apply (mean_radial_smooth q X k).continuous.comp
  exact Real.continuousOn_arcosh.comp_continuous (continuous_const.max continuous_id)
    (fun z => le_max_left 1 z)

private theorem closedMean_one (q : XiZeroCopy) (X k : ℝ) :
    closedMean q X k 1=fullSquarePotential q ![X,Real.exp k] := by
  simp only [closedMean,max_self,Real.arcosh_zero,mean_zero]

/-- Original invariant at a source horizon point with fixed source ingoing time. -/
def horizonArgument (τ x v : ℝ) : ℝ :=
  (Real.exp (v-τ)-Real.sinh x)/Real.cosh x

private theorem invariant_formula (τ x v y : ℝ) :
    invariant (v-τ-y) x y =
      (Real.cosh (v-τ)+(Real.sinh (v-τ)-Real.sinh x)*radialUnit y)/Real.cosh x := by
  rw [invariant,Real.cosh_sub,radialUnit]
  field_simp [(Real.cosh_pos x).ne',(Real.cosh_pos y).ne']
  ring

theorem invariant_source_horizon (τ x v : ℝ) :
    Tendsto (fun y => invariant (v-τ-y) x y) atBot (𝓝 (horizonArgument τ x v)) := by
  simp_rw [invariant_formula]
  have h := ((tendsto_const_nhds (x := Real.cosh (v-τ))).add
    (unit_limit.const_mul (Real.sinh (v-τ)-Real.sinh x))).div_const (Real.cosh x)
  have he : (Real.cosh (v-τ)+(Real.sinh (v-τ)-Real.sinh x)*1)/Real.cosh x=
      horizonArgument τ x v := by
    rw [mul_one,← add_sub_assoc,Real.cosh_add_sinh]
    rfl
  rw [he] at h
  exact h

/-- The one-sided causal support is retained, including its characteristic value. -/
def halfKernel (q : XiZeroCopy) (τ x v X k : ℝ) : ℂ :=
  if τ+x ≤ v then closedMean q X k (horizonArgument τ x v) else 0

private theorem cone_horizon (q : XiZeroCopy) (τ x v X k : ℝ) :
    Tendsto (fun y => if |x-y| ≤ v-τ-y then
      nativeRiemannKernel q (v-τ-y) x y X k else 0) atBot
      (𝓝 (halfKernel q τ x v X k)) := by
  have he : (fun y => if |x-y| ≤ v-τ-y then
      nativeRiemannKernel q (v-τ-y) x y X k else 0) =ᶠ[atBot]
      (fun y => if τ+x ≤ v then closedMean q X k (invariant (v-τ-y) x y) else 0) := by
    filter_upwards [eventually_le_atBot x] with y hy
    rw [abs_of_nonneg (sub_nonneg.mpr hy)]
    have hc : x-y ≤ v-τ-y ↔ τ+x ≤ v := by constructor <;> intro h <;> linarith
    simp only [hc]
    split_ifs with h
    · have hz := invariant_causal (⟨v-τ-y,x,y,by rw [abs_of_nonneg (sub_nonneg.mpr hy)]; linarith⟩ : CausalPoint)
      simp only [nativeRiemannKernel,angularKernel,closedMean,max_eq_right hz]
    · rfl
  apply Filter.Tendsto.congr' he.symm
  unfold halfKernel
  split_ifs
  · exact (closedMean_continuous q X k).continuousAt.tendsto.comp (invariant_source_horizon τ x v)
  · exact tendsto_const_nhds

/-- Full theta Dirichlet kernel at the original source horizon, with both causal faces. -/
theorem native_kernel_source_horizon (q : XiZeroCopy) (τ x v X k : ℝ) :
    Tendsto (fun y => nativeDirichletCausalKernel q (v-τ-y) x y X k) atBot
      (𝓝 ((halfKernel q τ x v X k-halfKernel q τ (-x) v X k)/2)) := by
  have h := ((cone_horizon q τ x v X k).sub (cone_horizon q τ (-x) v X k)).div_const (2:ℂ)
  convert h using 1
  funext y
  have he : invariant (v-τ-y) (-x) y=invariant (v-τ-y) x (-y) := by
    simp [invariant,Real.sinh_neg,Real.cosh_neg]
  have ha : |(-x)-y|=|x+y| := by rw [show -x-y=-(x+y) by ring,abs_neg]
  simp only [nativeDirichletCausalKernel,ha,nativeRiemannKernel,he]

private def coefficient (x : ℝ) : ℝ := Real.exp x/Real.cosh x

private theorem coefficient_eq (x : ℝ) : coefficient x=1-radialUnit x := by
  rw [coefficient,radialUnit,← Real.cosh_add_sinh x]
  field_simp [(Real.cosh_pos x).ne']
  ring

private theorem coefficient_bounds (x : ℝ) : 0 ≤ coefficient x ∧ coefficient x ≤ 2 := by
  have hc := Real.cosh_pos x
  constructor
  · exact (div_pos (Real.exp_pos x) hc).le
  · rw [coefficient,div_le_iff₀ hc,← Real.cosh_add_sinh x]
    have hp := Real.exp_pos (-x)
    rw [← Real.cosh_sub_sinh x] at hp
    linarith

/-- Direct horizon circle mean at delay r from its original characteristic. -/
def horizonMean (q : XiZeroCopy) (x r X k : ℝ) : ℂ :=
  closedMean q X k (1+coefficient x*(Real.exp r-1))

theorem halfKernel_at_delay (q : XiZeroCopy) (τ x r X k : ℝ) (hr : 0 ≤ r) :
    halfKernel q τ x (τ+x+r) X k = horizonMean q x r X k := by
  rw [halfKernel,if_pos (by linarith)]
  unfold horizonMean
  congr 1
  unfold horizonArgument coefficient
  rw [show τ+x+r-τ=x+r by ring,Real.exp_add,← Real.cosh_add_sinh x]
  field_simp [(Real.cosh_pos x).ne']
  ring

theorem horizonMean_ingoing (q : XiZeroCopy) (r X k : ℝ) :
    Tendsto (fun x => horizonMean q x r X k) atBot
      (𝓝 (fullSquarePotential q ![X,Real.exp k])) := by
  have hc : Tendsto coefficient atBot (𝓝 (0:ℝ)) := by
    have he : coefficient=fun x => 1-radialUnit x := funext coefficient_eq
    rw [he]
    simpa only [sub_self] using ((tendsto_const_nhds (x := (1:ℝ))).sub unit_limit)
  have hz : Tendsto (fun x => 1+coefficient x*(Real.exp r-1)) atBot (𝓝 (1:ℝ)) := by
    simpa only [zero_mul,add_zero] using tendsto_const_nhds.add (hc.mul_const (Real.exp r-1))
  simpa only [Function.comp_def,horizonMean,closedMean_one] using
    (closedMean_continuous q X k).continuousAt.tendsto.comp hz

private theorem horizonMean_continuous (q : XiZeroCopy) (x X k : ℝ) :
    Continuous (fun r => horizonMean q x r X k) :=
  (closedMean_continuous q X k).comp
    (continuous_const.add ((Real.continuous_exp.sub continuous_const).const_mul _))

private theorem horizon_radius_bound (x r : ℝ) (hr : 0 ≤ r) :
    Real.arcosh (max 1 (1+coefficient x*(Real.exp r-1))) ≤ r+Real.log 4 := by
  have he : 1 ≤ Real.exp r := Real.one_le_exp_iff.mpr hr
  have hx := coefficient_bounds x
  have hz : 1 ≤ 1+coefficient x*(Real.exp r-1) := by nlinarith
  rw [max_eq_right hz]
  have hZ : 1+coefficient x*(Real.exp r-1) ≤ 2*Real.exp r := by nlinarith
  have hp : 0 ≤ r+Real.log 4 := add_nonneg hr (Real.log_nonneg (by norm_num))
  have hb : 2*Real.exp r ≤ Real.cosh (r+Real.log 4) := by
    rw [Real.cosh_eq,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<4)]
    linarith [Real.exp_pos (-(r+Real.log 4))]
  have h := Real.cosh_le_cosh.mp ((Real.cosh_arcosh hz).trans_le (hZ.trans hb))
  simpa only [abs_of_nonneg (Real.arcosh_nonneg hz),abs_of_nonneg hp] using h

/-- A common bound for the full source horizon means, uniform in the radial target. -/
theorem horizonMean_growth (q : XiZeroCopy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x r X k : ℝ, 0 ≤ r →
      ‖horizonMean q x r X k‖ ≤ C*Real.exp (sourceGrowthExponent q*(r+|k|)) := by
  obtain ⟨C,hC,hb⟩ := mean_global_growth q
  have ha : 0 ≤ sourceGrowthExponent q := (by norm_num : (0:ℝ)≤1).trans (sourceGrowthExponent_bounds q).1
  refine ⟨C*Real.exp (sourceGrowthExponent q*Real.log 4),by positivity,fun x r X k hr => ?_⟩
  have hd : 1 ≤ max 1 (1+coefficient x*(Real.exp r-1)) := le_max_left _ _
  have h := hb (Real.arcosh (max 1 (1+coefficient x*(Real.exp r-1)))) X k (Real.arcosh_nonneg hd)
  calc
    _ ≤ C*Real.exp (sourceGrowthExponent q*
        (Real.arcosh (max 1 (1+coefficient x*(Real.exp r-1)))+|k|)) := h
    _ ≤ C*Real.exp (sourceGrowthExponent q*((r+Real.log 4)+|k|)) := by
      have hradius : Real.arcosh (max 1 (1+coefficient x*(Real.exp r-1)))+|k| ≤
          (r+Real.log 4)+|k| := by linarith [horizon_radius_bound x r hr]
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hradius ha)) hC
    _ = _ := by rw [show sourceGrowthExponent q*((r+Real.log 4)+|k|)=
        sourceGrowthExponent q*Real.log 4+sourceGrowthExponent q*(r+|k|) by ring,Real.exp_add]; ring

private theorem onset_bound (q : XiZeroCopy) (branch : Bool) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ v : ℝ,
      ‖timeOnset (2*physicalRate q branch) v‖+‖timeOnsetFirst (2*physicalRate q branch) v‖ ≤
        B*Real.exp (-decayExponent q*v) := by
  apply timeOnset_pair_bound
  have hs := currentRate_re_lt q branch
  change (2*physicalRate q branch).re < -2 at hs
  linarith [(decayExponent_bounds q).2]

/-- The actual ingoing derivative in the limiting cap, with full angular source. -/
def boundaryDensity (q : XiZeroCopy) (branch : Bool) (v x X k r : ℝ) : ℂ :=
  timeOnsetFirst (2*physicalRate q branch) (v+r)*horizonMean q x r X k

private theorem boundaryDensity_continuous (q : XiZeroCopy) (branch : Bool) (v x X k : ℝ) :
    Continuous (boundaryDensity q branch v x X k) := by
  have h : Continuous (timeOnsetFirst (2*physicalRate q branch)) :=
    continuous_iff_continuousAt.mpr (fun r => (timeOnsetFirst_hasDerivAt _ r).continuousAt)
  exact (h.comp (continuous_const.add continuous_id)).mul (horizonMean_continuous q x X k)

theorem boundaryDensity_bound (q : XiZeroCopy) (branch : Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v x X k r : ℝ, 0 ≤ r →
      ‖boundaryDensity q branch v x X k r‖ ≤
        (C*Real.exp (-decayExponent q*v+sourceGrowthExponent q*|k|))*
          Real.exp ((sourceGrowthExponent q-decayExponent q)*r) := by
  obtain ⟨B,hB,hb⟩ := onset_bound q branch
  obtain ⟨C,hC,hc⟩ := horizonMean_growth q
  refine ⟨B*C,mul_nonneg hB hC,fun v x X k r hr => ?_⟩
  have hfirst : ‖timeOnsetFirst (2*physicalRate q branch) (v+r)‖ ≤
      B*Real.exp (-decayExponent q*(v+r)) := by
    linarith [hb (v+r),norm_nonneg (timeOnset (2*physicalRate q branch) (v+r))]
  rw [boundaryDensity,norm_mul]
  calc
    _ ≤ (B*Real.exp (-decayExponent q*(v+r)))*
        (C*Real.exp (sourceGrowthExponent q*(r+|k|))) :=
      mul_le_mul hfirst (hc x r X k hr) (norm_nonneg _) (by positivity)
    _ = _ := by
      have he : Real.exp (-decayExponent q*(v+r))*Real.exp (sourceGrowthExponent q*(r+|k|)) =
          Real.exp (-decayExponent q*v+sourceGrowthExponent q*|k|)*
            Real.exp ((sourceGrowthExponent q-decayExponent q)*r) := by
        rw [← Real.exp_add,← Real.exp_add]
        congr 1
        ring
      calc
        _ = (B*C)*(Real.exp (-decayExponent q*(v+r))*Real.exp (sourceGrowthExponent q*(r+|k|))) := by ring
        _ = _ := by rw [he]; ring

private theorem majorant_integrable (q : XiZeroCopy) (C : ℝ) :
    IntegrableOn (fun r => C*Real.exp ((sourceGrowthExponent q-decayExponent q)*r)) (Ioi 0) :=
  (integrableOn_exp_mul_Ioi (sub_neg.mpr (decayExponent_bounds q).1) 0).const_mul C

theorem boundaryDensity_integrable (q : XiZeroCopy) (branch : Bool) (v x X k : ℝ) :
    IntegrableOn (boundaryDensity q branch v x X k) (Ioi 0) := by
  obtain ⟨C,hC,hb⟩ := boundaryDensity_bound q branch
  apply (majorant_integrable q (C*Real.exp (-decayExponent q*v+sourceGrowthExponent q*|k|))).mono'
    (boundaryDensity_continuous q branch v x X k).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  exact hb v x X k r hr.le

/-- Full source cap integral on one original characteristic arm. -/
def boundaryArm (q : XiZeroCopy) (branch : Bool) (v x X k : ℝ) : ℂ :=
  ∫ r in Ioi (0:ℝ), boundaryDensity q branch v x X k r

theorem boundaryArm_bound (q : XiZeroCopy) (branch : Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v x X k : ℝ,
      ‖boundaryArm q branch v x X k‖ ≤
        C*Real.exp (-decayExponent q*v+sourceGrowthExponent q*|k|) := by
  obtain ⟨C,hC,hb⟩ := boundaryDensity_bound q branch
  have hp : 0 < decayExponent q-sourceGrowthExponent q := sub_pos.mpr (decayExponent_bounds q).1
  refine ⟨C/(decayExponent q-sourceGrowthExponent q),div_nonneg hC hp.le,fun v x X k => ?_⟩
  let D := C*Real.exp (-decayExponent q*v+sourceGrowthExponent q*|k|)
  have hi := boundaryDensity_integrable q branch v x X k
  calc
    _ ≤ ∫ r in Ioi (0:ℝ), ‖boundaryDensity q branch v x X k r‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ r in Ioi (0:ℝ), D*Real.exp ((sourceGrowthExponent q-decayExponent q)*r) :=
      setIntegral_mono_on hi.norm (majorant_integrable q D) measurableSet_Ioi (fun r hr => hb v x X k r hr.le)
    _ = _ := by
      rw [integral_const_mul,integral_exp_mul_Ioi (by linarith : sourceGrowthExponent q-decayExponent q<0)]
      simp only [mul_zero,Real.exp_zero]
      dsimp only [D]
      rw [show sourceGrowthExponent q-decayExponent q=-(decayExponent q-sourceGrowthExponent q) by ring]
      simp only [neg_div_neg_eq]
      ring

/-- The direct arm has its exact complete-source horizon integral; no flux is discarded. -/
theorem boundaryArm_ingoing_integral (q : XiZeroCopy) (branch : Bool) (v X k : ℝ) :
    Tendsto (fun x => boundaryArm q branch v x X k) atBot
      (𝓝 ((∫ r in Ioi (0:ℝ), timeOnsetFirst (2*physicalRate q branch) (v+r))*
        fullSquarePotential q ![X,Real.exp k])) := by
  obtain ⟨C,hC,hb⟩ := boundaryDensity_bound q branch
  let D := C*Real.exp (-decayExponent q*v+sourceGrowthExponent q*|k|)
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (0:ℝ))) (fun r => D*Real.exp ((sourceGrowthExponent q-decayExponent q)*r))
    (Filter.Eventually.of_forall (fun x => (boundaryDensity_continuous q branch v x X k).aestronglyMeasurable))
    (Filter.Eventually.of_forall (fun x => (ae_restrict_mem measurableSet_Ioi).mono
      (fun r hr => hb v x X k r hr.le)))
    (majorant_integrable q D)
    (Filter.Eventually.of_forall (fun r => (horizonMean_ingoing q r X k).const_mul
      (timeOnsetFirst (2*physicalRate q branch) (v+r))))
  simpa only [boundaryArm,boundaryDensity,integral_mul_const] using h

private theorem decay_pos (q : XiZeroCopy) : 0 < decayExponent q := by
  have h := (sourceGrowthExponent_bounds q).1
  have hc := (decayExponent_bounds q).1
  linarith

private theorem onsetFirst_shift_integrable (q : XiZeroCopy) (branch : Bool) (v : ℝ) :
    IntegrableOn (fun r => timeOnsetFirst (2*physicalRate q branch) (v+r)) (Ioi 0) := by
  obtain ⟨B,hB,hb⟩ := onset_bound q branch
  have hm := (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (decay_pos q)) 0).const_mul
    (B*Real.exp (-decayExponent q*v))
  have hc : Continuous (timeOnsetFirst (2*physicalRate q branch)) :=
    continuous_iff_continuousAt.mpr (fun r => (timeOnsetFirst_hasDerivAt _ r).continuousAt)
  apply hm.mono' (hc.comp (continuous_const.add continuous_id)).aestronglyMeasurable
  filter_upwards with r
  have he : (B*Real.exp (-decayExponent q*v))*Real.exp (-decayExponent q*r) =
      B*Real.exp (-decayExponent q*(v+r)) := by
    rw [mul_assoc,← Real.exp_add]
    congr 2
    ring
  rw [he]
  simp only [Function.comp_apply,Pi.add_apply,id_eq]
  linarith [hb (v+r),norm_nonneg (timeOnset (2*physicalRate q branch) (v+r))]

private theorem onset_shift_limit (q : XiZeroCopy) (branch : Bool) (v : ℝ) :
    Tendsto (fun r => timeOnset (2*physicalRate q branch) (v+r)) atTop (𝓝 0) := by
  obtain ⟨B,hB,hb⟩ := onset_bound q branch
  have he := Real.tendsto_exp_atBot.comp
    ((tendsto_const_mul_atBot_of_neg (neg_lt_zero.mpr (decay_pos q))).mpr tendsto_id)
  have hbnd (r : ℝ) : ‖timeOnset (2*physicalRate q branch) (v+r)‖ ≤
      (B*Real.exp (-decayExponent q*v))*Real.exp (-decayExponent q*r) := by
    rw [mul_assoc,← Real.exp_add,show -decayExponent q*v+-decayExponent q*r=
        -decayExponent q*(v+r) by ring]
    linarith [hb (v+r),norm_nonneg (timeOnsetFirst (2*physicalRate q branch) (v+r))]
  apply squeeze_zero_norm hbnd
  simpa only [Function.comp_def,id_eq,mul_zero] using he.const_mul (B*Real.exp (-decayExponent q*v))

/-- The fixed onset derivative integrates to its actual source contact at the lower endpoint. -/
theorem onsetFirst_future_integral (q : XiZeroCopy) (branch : Bool) (v : ℝ) :
    (∫ r in Ioi (0:ℝ), timeOnsetFirst (2*physicalRate q branch) (v+r)) =
      -timeOnset (2*physicalRate q branch) v := by
  have hd (r : ℝ) : HasDerivAt (fun a => timeOnset (2*physicalRate q branch) (v+a))
      (timeOnsetFirst (2*physicalRate q branch) (v+r)) r := by
    exact HasDerivAt.comp_const_add v r (timeOnset_hasDerivAt (2*physicalRate q branch) (v+r))
  simpa only [zero_sub,add_zero] using integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun r _ => hd r) (onsetFirst_shift_integrable q branch v) (onset_shift_limit q branch v)

theorem boundaryArm_ingoing (q : XiZeroCopy) (branch : Bool) (v X k : ℝ) :
    Tendsto (fun x => boundaryArm q branch v x X k) atBot
      (𝓝 (-timeOnset (2*physicalRate q branch) v*fullSquarePotential q ![X,Real.exp k])) := by
  simpa only [onsetFirst_future_integral] using boundaryArm_ingoing_integral q branch v X k

theorem imageArm_ingoing_zero (q : XiZeroCopy) (branch : Bool) (v X k : ℝ) :
    Tendsto (fun x => boundaryArm q branch (v-2*x) (-x) X k) atBot (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := boundaryArm_bound q branch
  have ht : Tendsto (fun x : ℝ => (2*decayExponent q)*x) atBot atBot :=
    (tendsto_const_mul_atBot_of_pos (mul_pos (by norm_num : (0:ℝ)<2) (decay_pos q))).mpr tendsto_id
  have he := Real.tendsto_exp_atBot.comp ht
  have hbnd (x : ℝ) : ‖boundaryArm q branch (v-2*x) (-x) X k‖ ≤
      (C*Real.exp (-decayExponent q*v+sourceGrowthExponent q*|k|))*Real.exp ((2*decayExponent q)*x) := by
    have h := hb (v-2*x) (-x) X k
    rw [show -decayExponent q*(v-2*x)+sourceGrowthExponent q*|k|=
      (-decayExponent q*v+sourceGrowthExponent q*|k|)+(2*decayExponent q)*x by ring,Real.exp_add] at h
    simpa only [mul_assoc] using h
  apply squeeze_zero_norm hbnd
  simpa only [Function.comp_def,id_eq,mul_zero] using
    he.const_mul (C*Real.exp (-decayExponent q*v+sourceGrowthExponent q*|k|))

def liftTraceCoefficient (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ) : ℂ :=
  (-physicalRate q branch*(physicalRate q branch-1)/4)*
    D4BMLaplaceRadial.power (2*physicalRate q branch) 2*amplitude^(2 : ℕ)

/-- Source-derived direct/image null-cap field, with the original lift normalization. -/
def capBoundaryField (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ) (τ x X k : ℝ) : ℂ :=
  -liftTraceCoefficient q branch amplitude*
    (boundaryArm q branch (τ+x) x X k-boundaryArm q branch (τ-x) (-x) X k)

theorem capBoundaryField_dirichlet (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ) (τ X k : ℝ) :
    capBoundaryField q branch amplitude τ 0 X k=0 := by
  simp only [capBoundaryField,add_zero,sub_zero,neg_zero,sub_self,mul_zero]

/-- The cap field has exactly the original source lift trace at fixed ingoing Hawking time. -/
theorem capBoundaryField_ingoing (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ) (v X k : ℝ) :
    Tendsto (fun x => capBoundaryField q branch amplitude (v-x) x X k) atBot
      (𝓝 (liftTraceCoefficient q branch amplitude*timeOnset (2*physicalRate q branch) v*
        fullSquarePotential q ![X,Real.exp k])) := by
  have h := ((boundaryArm_ingoing q branch v X k).sub (imageArm_ingoing_zero q branch v X k)).const_mul
    (-liftTraceCoefficient q branch amplitude)
  convert h using 1
  · funext x
    simp only [capBoundaryField,sub_add_cancel,show v-x-x=v-2*x by ring]
  · simp only [sub_zero,neg_mul,mul_neg,neg_neg,mul_assoc]

/-- The source-derived cap field cancels the retained lift trace after the actual reduced
future integral is added. This is a field-value boundary identity, not Einstein-current extinction. -/
theorem lift_response_sub_cap_ingoing_zero (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ)
    (v X k : ℝ) :
    Tendsto (fun x => timeLiftField q branch amplitude (v-x) x ![X,Real.exp k]+
      D4BMFullSourceAdvanced.response q branch amplitude (v-x) x X k-
        capBoundaryField q branch amplitude (v-x) x X k) atBot (𝓝 0) := by
  have h := (lift_plus_response_ingoing_horizon q branch amplitude v X k).sub
    (capBoundaryField_ingoing q branch amplitude v X k)
  simpa only [liftTraceCoefficient,sub_self] using h

end
end RHTower.D4BMFutureHorizon
