import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFutureSeedFiniteGreen
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularMeanGrowth
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFutureHorizonCap

/-!
The actual seed's outgoing-null terminal face converges to its independently
specified full angular horizon cap. Original seed coefficients, onset derivatives,
characteristic supports, direct/image subtraction and normalization are retained.
Absolute cap admission and the infinite null-exhaustion limit of the original
pulse-minus-source balance follow from the verified angular growth estimate.
-/
namespace RHTower.D4BMFutureSeedHorizon
open Set Filter Topology MeasureTheory
open D4BMHorizon D4BMModularCore D4BMJointSource D4BMLaplaceRadial
open D4BMGlobalAngularResponse D4BMFullAngularCircle D4BMCausalKernel
open D4BMFutureSeedGreen D4BMFullSourceAdvanced D4BMFullAngularGrowth
open scoped ContDiff
noncomputable section
set_option autoImplicit false

/-- The actual limiting radial coefficient of the original seed. -/
def seedTraceCoefficient (q : XiZeroCopy) (branch : Bool) (amp : ℂ) : ℂ :=
  -parameter q branch*power (2*physicalRate q branch) 2*amp^2

private def seedProfile (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (u : ℝ) : ℂ :=
  -parameter q branch*power (2*physicalRate q branch) (1+u)*amp^2*(u:ℂ)

private def seedFirstProfile (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (u : ℝ) : ℂ :=
  -parameter q branch*power (2*physicalRate q branch) (1+u)*amp^2*
    (2*physicalRate q branch*((u:ℂ)-1)*(u:ℂ)+((u:ℂ)^2-1))

private theorem seed_profiles (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (y : ℝ) :
    sourceSeedField (physicalRate q branch) 0 amp 1 (parameter q branch) y=
      seedProfile q branch amp (radialUnit y) ∧
    sourceSeedFieldFirst (physicalRate q branch) 0 amp 1 (parameter q branch) y=
      seedFirstProfile q branch amp (radialUnit y) := by
  constructor <;>
    simp only [sourceSeedField,sourceSeedFieldFirst,sourceAmplitude,sourceSeedPolynomial,
      sourceSeedFirst,amplitudeRate,seedProfile,seedFirstProfile,parameter_physicalRate,
      D4BMQuadraticMixedSource.resolventParameter,zero_mul,Complex.exp_zero,one_mul,mul_one,
      sub_self,mul_zero,sub_zero,zero_add] <;> ring

private theorem profiles_continuousAt (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (u : ℝ) (hu : 0 < 1+u) :
    ContinuousAt (seedProfile q branch amp) u ∧ ContinuousAt (seedFirstProfile q branch amp) u := by
  have hp : ContinuousAt (fun u : ℝ => power (2*physicalRate q branch) (1+u)) u :=
    (power_derivatives (2*physicalRate q branch) hu).1.continuousAt.comp
      (continuous_const.add continuous_id).continuousAt
  constructor
  · change ContinuousAt (fun v : ℝ => -parameter q branch*
      power (2*physicalRate q branch) (1+v)*amp^2*(v:ℂ)) u
    fun_prop
  · change ContinuousAt (fun v : ℝ => -parameter q branch*
      power (2*physicalRate q branch) (1+v)*amp^2*
        (2*physicalRate q branch*((v:ℂ)-1)*(v:ℂ)+((v:ℂ)^2-1))) u
    fun_prop

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

theorem seed_radial_limits (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    Tendsto (sourceSeedField (physicalRate q branch) 0 amp 1 (parameter q branch)) atBot
      (𝓝 (seedTraceCoefficient q branch amp)) ∧
    Tendsto (sourceSeedFieldFirst (physicalRate q branch) 0 amp 1 (parameter q branch)) atBot
      (𝓝 0) := by
  obtain ⟨hc,hc1⟩ := profiles_continuousAt q branch amp 1 (by norm_num)
  have h := hc.tendsto.comp unit_limit
  have h1 := hc1.tendsto.comp unit_limit
  have hf := funext (fun y => (seed_profiles q branch amp y).1)
  have hf1 := funext (fun y => (seed_profiles q branch amp y).2)
  rw [hf,hf1]
  constructor
  · simpa only [Function.comp_def,seedProfile,seedTraceCoefficient,show (1:ℝ)+1=2 by ring,
      Complex.ofReal_one,mul_one] using h
  · simpa only [Function.comp_def,seedFirstProfile,show (1:ℝ)+1=2 by ring,Complex.ofReal_one,
      sub_self,mul_zero,zero_mul,one_pow,zero_add,add_zero] using h1

theorem seed_radial_bound (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, y ≤ 0 →
      ‖sourceSeedField (physicalRate q branch) 0 amp 1 (parameter q branch) y‖+
        ‖sourceSeedFieldFirst (physicalRate q branch) 0 amp 1 (parameter q branch) y‖ ≤ C := by
  have hc : ContinuousOn (fun u => ‖seedProfile q branch amp u‖+‖seedFirstProfile q branch amp u‖)
      (Icc (0:ℝ) 1) := by
    intro u hu
    have h := profiles_continuousAt q branch amp u (by linarith [hu.1])
    exact (h.1.norm.add h.2.norm).continuousWithinAt
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,fun y hy => ?_⟩
  have hu : radialUnit y ∈ Icc (0:ℝ) 1 := by
    rcases lt_or_eq_of_le hy with hy | rfl
    · exact ⟨(radialUnit_bounds y hy).1.le,(radialUnit_bounds y hy).2.le⟩
    · simp [radialUnit]
  rw [(seed_profiles q branch amp y).1,(seed_profiles q branch amp y).2]
  have hb := hC (radialUnit y) hu
  rw [Real.norm_eq_abs,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))] at hb
  exact hb.trans (le_max_left _ _)

private theorem onset_bound (q : XiZeroCopy) (branch : Bool) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ v : ℝ,
      ‖timeOnset (2*physicalRate q branch) v‖+‖timeOnsetFirst (2*physicalRate q branch) v‖ ≤
        B*Real.exp (2*(physicalRate q branch).re*v) := by
  obtain ⟨B,hB,hb⟩ := timeOnset_pair_bound (2*physicalRate q branch)
    (-(2*physicalRate q branch).re) (by simp)
  have hr : (2*physicalRate q branch).re=2*(physicalRate q branch).re := by simp
  exact ⟨B,hB,by simpa only [neg_neg,hr] using hb⟩

theorem seedNullFirst_bound (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v w : ℝ, v ≤ w →
      ‖seedNullFirst q branch amp v w‖ ≤ C*Real.exp (2*(physicalRate q branch).re*v) := by
  obtain ⟨C,hC,hc⟩ := seed_radial_bound q branch amp
  obtain ⟨B,hB,hb⟩ := onset_bound q branch
  refine ⟨C*B,mul_nonneg hC hB,fun v w hvw => ?_⟩
  let f := sourceSeedField (physicalRate q branch) 0 amp 1 (parameter q branch) ((v-w)/2)
  let df := sourceSeedFieldFirst (physicalRate q branch) 0 amp 1 (parameter q branch) ((v-w)/2)
  let o := timeOnset (2*physicalRate q branch) v
  let do' := timeOnsetFirst (2*physicalRate q branch) v
  have hs : ‖f‖+‖df‖ ≤ C := hc _ (by linarith)
  have ho : ‖o‖+‖do'‖ ≤ B*Real.exp (2*(physicalRate q branch).re*v) := hb v
  have hn : ‖seedNullFirst q branch amp v w‖ ≤ (‖df‖/2)*‖o‖+‖f‖*‖do'‖ := by
    change ‖df/2*o+f*do'‖ ≤ _
    calc
      _ ≤ ‖df/2*o‖+‖f*do'‖ := norm_add_le _ _
      _ = _ := by rw [norm_mul,norm_mul,norm_div,Complex.norm_ofNat]
  have hp : (‖df‖/2)*‖o‖+‖f‖*‖do'‖ ≤ (‖f‖+‖df‖)*(‖o‖+‖do'‖) := by
    nlinarith [mul_nonneg (norm_nonneg f) (norm_nonneg o),
      mul_nonneg (norm_nonneg df) (norm_nonneg do'),mul_nonneg (norm_nonneg df) (norm_nonneg o)]
  have ht := mul_le_mul hs ho (add_nonneg (norm_nonneg _) (norm_nonneg _)) hC
  exact hn.trans (hp.trans (by nlinarith only [ht]))

private def closedMean (q : XiZeroCopy) (branch : Bool) (X k z : ℝ) : ℂ :=
  angularMean q branch (Real.arcosh (max 1 z)) X k

private theorem closedMean_continuous (q : XiZeroCopy) (branch : Bool) (X k : ℝ) :
    Continuous (closedMean q branch X k) := by
  apply (angularMean_smooth q branch X k).continuous.comp
  exact Real.continuousOn_arcosh.comp_continuous (continuous_const.max continuous_id)
    (fun z => le_max_left 1 z)

/-- Actual full angular horizon kernel on one original characteristic arm. -/
def halfKernel (q : XiZeroCopy) (branch : Bool) (tau x v X k : ℝ) : ℂ :=
  if tau+x ≤ v then closedMean q branch X k (D4BMFutureHorizon.horizonArgument tau x v) else 0

private theorem source_depth_limit (v : ℝ) :
    Tendsto (fun w : ℝ => (v-w)/2) atTop atBot := by
  apply tendsto_atBot.mpr
  intro b
  filter_upwards [eventually_ge_atTop (v-2*b)] with w hw
  linarith

theorem seedNullFirst_limit (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v : ℝ) :
    Tendsto (seedNullFirst q branch amp v) atTop
      (𝓝 (seedTraceCoefficient q branch amp*timeOnsetFirst (2*physicalRate q branch) v)) := by
  obtain ⟨hf,hdf⟩ := seed_radial_limits q branch amp
  have h := (((hdf.comp (source_depth_limit v)).div_const (2:ℂ)).mul_const
      (timeOnset (2*physicalRate q branch) v)).add
    ((hf.comp (source_depth_limit v)).mul_const (timeOnsetFirst (2*physicalRate q branch) v))
  change Tendsto (fun w => sourceSeedFieldFirst (physicalRate q branch) 0 amp 1
      (parameter q branch) ((v-w)/2)/2*timeOnset (2*physicalRate q branch) v+
      sourceSeedField (physicalRate q branch) 0 amp 1 (parameter q branch) ((v-w)/2)*
        timeOnsetFirst (2*physicalRate q branch) v) atTop _
  simpa only [Function.comp_def,zero_div,zero_mul,zero_add] using h

private theorem seedNullFirst_continuous (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (w : ℝ) :
    Continuous (fun v => seedNullFirst q branch amp v w) := by
  have hf : Continuous (sourceSeedField (physicalRate q branch) 0 amp 1 (parameter q branch)) :=
    continuous_iff_continuousAt.mpr (fun y => (sourceSeedField_hasDerivAt _ _ _ _ _ y).continuousAt)
  have hdf : Continuous (sourceSeedFieldFirst (physicalRate q branch) 0 amp 1 (parameter q branch)) :=
    continuous_iff_continuousAt.mpr (fun y => (sourceSeedFieldFirst_hasDerivAt _ _ _ _ _ y).continuousAt)
  have ho : Continuous (timeOnset (2*physicalRate q branch)) :=
    continuous_iff_continuousAt.mpr (fun v => (timeOnset_hasDerivAt _ v).continuousAt)
  have hdo : Continuous (timeOnsetFirst (2*physicalRate q branch)) :=
    continuous_iff_continuousAt.mpr (fun v => (timeOnsetFirst_hasDerivAt _ v).continuousAt)
  have hd : Continuous (fun v : ℝ => (v-w)/2) := by fun_prop
  exact (((hdf.comp hd).div_const 2).mul ho).add ((hf.comp hd).mul hdo)

private theorem onsetFirst_zero_nonpos (s : ℂ) (v : ℝ) (hv : v ≤ 0) :
    timeOnsetFirst s v=0 := by
  have hm : IsLocalMin Real.smoothTransition v := by
    apply Filter.Eventually.of_forall
    intro t
    simpa only [Real.smoothTransition.zero_of_nonpos hv] using Real.smoothTransition.nonneg t
  simp only [timeOnsetFirst,hm.deriv_eq_zero,Real.smoothTransition.zero_of_nonpos hv,
    Complex.ofReal_zero,mul_zero,zero_add,zero_mul]

private theorem seedNullFirst_zero_nonpos (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (v w : ℝ) (hv : v ≤ 0) : seedNullFirst q branch amp v w=0 := by
  simp only [seedNullFirst,timeOnset_zero_of_nonpos _ hv,onsetFirst_zero_nonpos _ _ hv,mul_zero,add_zero]

private def movingMean (q : XiZeroCopy) (branch : Bool) (tau x X k v w : ℝ) : ℂ :=
  closedMean q branch X k (invariant (v-(v-w)/2-tau) x ((v-w)/2))

private theorem movingMean_continuous (q : XiZeroCopy) (branch : Bool) (tau x X k w : ℝ) :
    Continuous (fun v => movingMean q branch tau x X k v w) := by
  apply (closedMean_continuous q branch X k).comp
  unfold invariant
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro v
  exact (mul_pos (Real.cosh_pos x) (Real.cosh_pos ((v-w)/2))).ne'

private theorem movingMean_limit (q : XiZeroCopy) (branch : Bool) (tau x v X k : ℝ) :
    Tendsto (movingMean q branch tau x X k v) atTop
      (𝓝 (closedMean q branch X k (D4BMFutureHorizon.horizonArgument tau x v))) := by
  have h := (closedMean_continuous q branch X k).continuousAt.tendsto.comp
    ((D4BMFutureHorizon.invariant_source_horizon tau x v).comp (source_depth_limit v))
  convert h using 1
  funext w
  change closedMean q branch X k (invariant (v-(v-w)/2-tau) x ((v-w)/2))=
    closedMean q branch X k (invariant (v-tau-(v-w)/2) x ((v-w)/2))
  congr 2
  ring

private theorem movingMean_bound (q : XiZeroCopy) (branch : Bool) (tau X k : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ v x w : ℝ, 0 ≤ v → v ≤ w →
      Real.exp (2*(physicalRate q branch).re*v)*‖movingMean q branch tau x X k v w‖ ≤
        B*Real.exp ((2*(physicalRate q branch).re+decayExponent q)*v) := by
  obtain ⟨B,hB,_,hb⟩ := angularMean_source_horizon_majorant q branch tau X k
  refine ⟨B,hB,fun v x w hv hw => ?_⟩
  have h := hb v x ((v-w)/2) hv (by linarith)
  change Real.exp (2*(physicalRate q branch).re*v)*
    (‖movingMean q branch tau x X k v w‖+_) ≤ _ at h
  have hh := mul_nonneg (Real.exp_pos (2*(physicalRate q branch).re*v)).le
    (norm_nonneg (deriv (fun r => angularMean q branch r X k)
      (Real.arcosh (max 1 (invariant (v-(v-w)/2-tau) x ((v-w)/2))))))
  nlinarith only [h,hh]

/-- Direct minus reflected full angular horizon kernel, with the original half factor. -/
def horizonKernel (q : XiZeroCopy) (branch : Bool) (tau x v X k : ℝ) : ℂ :=
  (halfKernel q branch tau x v X k-halfKernel q branch tau (-x) v X k)/2

/-- The seed cap is specified by the original horizon kernel and onset derivative. -/
def seedCapField (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (tau x X k : ℝ) : ℂ :=
  -2*seedTraceCoefficient q branch amp*
    ∫ v in Ioi (0:ℝ), timeOnsetFirst (2*physicalRate q branch) v*horizonKernel q branch tau x v X k

private def horizonDensity (q : XiZeroCopy) (branch : Bool) (tau x X k v : ℝ) : ℂ :=
  timeOnsetFirst (2*physicalRate q branch) v*halfKernel q branch tau x v X k

private theorem horizonDensity_measurable (q : XiZeroCopy) (branch : Bool) (tau x X k : ℝ) :
    AEStronglyMeasurable (horizonDensity q branch tau x X k) (volume.restrict (Ioi 0)) := by
  have ho : Continuous (timeOnsetFirst (2*physicalRate q branch)) :=
    continuous_iff_continuousAt.mpr (fun v => (timeOnsetFirst_hasDerivAt _ v).continuousAt)
  have hz : Continuous (fun v => D4BMFutureHorizon.horizonArgument tau x v) := by
    unfold D4BMFutureHorizon.horizonArgument
    fun_prop
  have hc := ho.mul ((closedMean_continuous q branch X k).comp hz)
  have he : horizonDensity q branch tau x X k=(Ici (tau+x)).indicator
      (fun v => timeOnsetFirst (2*physicalRate q branch) v*
        closedMean q branch X k (D4BMFutureHorizon.horizonArgument tau x v)) := by
    funext v
    by_cases h : tau+x ≤ v <;> simp [horizonDensity,halfKernel,Set.indicator,h]
  rw [he]
  exact hc.aestronglyMeasurable.indicator measurableSet_Ici

private theorem halfKernel_bound (q : XiZeroCopy) (branch : Bool) (tau X k : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ v x : ℝ, 0 ≤ v →
      Real.exp (2*(physicalRate q branch).re*v)*‖halfKernel q branch tau x v X k‖ ≤
        B*Real.exp ((2*(physicalRate q branch).re+decayExponent q)*v) := by
  obtain ⟨B,hB,hb⟩ := movingMean_bound q branch tau X k
  refine ⟨B,hB,fun v x hv => ?_⟩
  by_cases h : tau+x ≤ v
  · rw [halfKernel,if_pos h]
    apply le_of_tendsto ((movingMean_limit q branch tau x v X k).norm.const_mul
      (Real.exp (2*(physicalRate q branch).re*v)))
    filter_upwards [eventually_ge_atTop v] with w hw
    exact hb v x w hv hw
  · simp only [halfKernel,if_neg h,norm_zero,mul_zero]
    positivity

private theorem horizonDensity_bound (q : XiZeroCopy) (branch : Bool) (tau X k : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v x : ℝ, 0 ≤ v →
      ‖horizonDensity q branch tau x X k v‖ ≤
        C*Real.exp ((2*(physicalRate q branch).re+decayExponent q)*v) := by
  obtain ⟨B,hB,hb⟩ := onset_bound q branch
  obtain ⟨K,hK,hk⟩ := halfKernel_bound q branch tau X k
  refine ⟨B*K,mul_nonneg hB hK,fun v x hv => ?_⟩
  have ho : ‖timeOnsetFirst (2*physicalRate q branch) v‖ ≤ B*Real.exp (2*(physicalRate q branch).re*v) := by
    linarith [hb v,norm_nonneg (timeOnset (2*physicalRate q branch) v)]
  rw [horizonDensity,norm_mul]
  calc
    _ ≤ (B*Real.exp (2*(physicalRate q branch).re*v))*‖halfKernel q branch tau x v X k‖ :=
      mul_le_mul_of_nonneg_right ho (norm_nonneg _)
    _ = B*(Real.exp (2*(physicalRate q branch).re*v)*‖halfKernel q branch tau x v X k‖) := by ring
    _ ≤ B*(K*Real.exp ((2*(physicalRate q branch).re+decayExponent q)*v)) :=
      mul_le_mul_of_nonneg_left (hk v x hv) hB
    _ = _ := by ring

private theorem horizonDensity_integrable (q : XiZeroCopy) (branch : Bool) (tau x X k : ℝ) :
    IntegrableOn (horizonDensity q branch tau x X k) (Ioi 0) := by
  obtain ⟨C,hC,hb⟩ := horizonDensity_bound q branch tau X k
  apply ((integrableOn_exp_mul_Ioi (terminal_exponent_neg q branch) 0).const_mul C).mono'
    (horizonDensity_measurable q branch tau x X k)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact hb v x hv.le

/-- Absolute admission of the independently specified full seed-cap integrand. -/
theorem seedCap_integrable (q : XiZeroCopy) (branch : Bool) (tau x X k : ℝ) :
    IntegrableOn (fun v => timeOnsetFirst (2*physicalRate q branch) v*
      horizonKernel q branch tau x v X k) (Ioi 0) := by
  have he : (fun v => timeOnsetFirst (2*physicalRate q branch) v*horizonKernel q branch tau x v X k)=
      fun v => (horizonDensity q branch tau x X k v-horizonDensity q branch tau (-x) X k v)/2 := by
    funext v
    dsimp only [horizonKernel,horizonDensity]
    ring
  rw [he]
  exact ((horizonDensity_integrable q branch tau x X k).sub
    (horizonDensity_integrable q branch tau (-x) X k)).div_const (2:ℂ)

private def terminalArm (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (tau x X k w v : ℝ) : ℂ :=
  (Icc (tau+x) w).indicator (fun v => movingMean q branch tau x X k v w*seedNullFirst q branch amp v w) v

private theorem terminalArm_measurable (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (tau x X k w : ℝ) :
    AEStronglyMeasurable (terminalArm q branch amp tau x X k w) (volume.restrict (Ioi 0)) :=
  ((movingMean_continuous q branch tau x X k w).mul
    (seedNullFirst_continuous q branch amp w)).aestronglyMeasurable.indicator measurableSet_Icc

private theorem terminalArm_pointwise (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (tau x X k v : ℝ) :
    Tendsto (fun w => terminalArm q branch amp tau x X k w v) atTop
      (𝓝 (seedTraceCoefficient q branch amp*horizonDensity q branch tau x X k v)) := by
  by_cases hv : tau+x ≤ v
  · have h := (movingMean_limit q branch tau x v X k).mul (seedNullFirst_limit q branch amp v)
    have he : (fun w => movingMean q branch tau x X k v w*seedNullFirst q branch amp v w)=ᶠ[atTop]
        (fun w => terminalArm q branch amp tau x X k w v) := by
      filter_upwards [eventually_ge_atTop v] with w hw
      simp only [terminalArm,indicator_of_mem (show v ∈ Icc (tau+x) w from ⟨hv,hw⟩)]
    have hh := h.congr' he
    simpa only [horizonDensity,halfKernel,if_pos hv,mul_assoc,mul_comm,mul_left_comm] using hh
  · have he : (fun w => terminalArm q branch amp tau x X k w v)=fun _ => (0:ℂ) := by
      funext w
      simp [terminalArm,Set.indicator,hv]
    rw [he]
    simp only [horizonDensity,halfKernel,if_neg hv,mul_zero]
    exact tendsto_const_nhds

private theorem terminalArm_bound (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (tau X k : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v x w : ℝ, 0 ≤ v →
      ‖terminalArm q branch amp tau x X k w v‖ ≤
        C*Real.exp ((2*(physicalRate q branch).re+decayExponent q)*v) := by
  obtain ⟨B,hB,hb⟩ := seedNullFirst_bound q branch amp
  obtain ⟨K,hK,hk⟩ := movingMean_bound q branch tau X k
  refine ⟨B*K,mul_nonneg hB hK,fun v x w hv => ?_⟩
  by_cases h : v ∈ Icc (tau+x) w
  · rw [terminalArm,indicator_of_mem h,norm_mul]
    calc
      _ ≤ ‖movingMean q branch tau x X k v w‖*(B*Real.exp (2*(physicalRate q branch).re*v)) :=
        mul_le_mul_of_nonneg_left (hb v w h.2) (norm_nonneg _)
      _ = B*(Real.exp (2*(physicalRate q branch).re*v)*‖movingMean q branch tau x X k v w‖) := by ring
      _ ≤ B*(K*Real.exp ((2*(physicalRate q branch).re+decayExponent q)*v)) :=
        mul_le_mul_of_nonneg_left (hk v x w hv h.2) hB
      _ = _ := by ring
  · rw [terminalArm,indicator_of_notMem h,norm_zero]
    positivity

private theorem terminalArm_limit (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (tau x X k : ℝ) :
    Tendsto (fun w => ∫ v in Ioi (0:ℝ), terminalArm q branch amp tau x X k w v) atTop
      (𝓝 (seedTraceCoefficient q branch amp*∫ v in Ioi (0:ℝ), horizonDensity q branch tau x X k v)) := by
  obtain ⟨C,hC,hb⟩ := terminalArm_bound q branch amp tau X k
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (0:ℝ)))
    (fun v => C*Real.exp ((2*(physicalRate q branch).re+decayExponent q)*v))
    (Filter.Eventually.of_forall (fun w => terminalArm_measurable q branch amp tau x X k w))
    (Filter.Eventually.of_forall (fun w => (ae_restrict_mem measurableSet_Ioi).mono
      (fun v hv => hb v x w hv.le)))
    ((integrableOn_exp_mul_Ioi (terminal_exponent_neg q branch) 0).const_mul C)
    (Filter.Eventually.of_forall (fun v => terminalArm_pointwise q branch amp tau x X k v))
  simpa only [integral_const_mul] using h

private theorem movingMean_on_cone (q : XiZeroCopy) (branch : Bool) (tau x X k v w : ℝ)
    (hv : tau+x ≤ v) (hw : tau-x ≤ w) :
    movingMean q branch tau x X k v w=
      angularMean q branch (Real.arcosh (invariant ((v+w)/2-tau) x ((v-w)/2))) X k := by
  have hh : v-(v-w)/2-tau=(v+w)/2-tau := by ring
  have hc : |x-(v-w)/2| ≤ (v+w)/2-tau := abs_le.mpr ⟨by linarith,by linarith⟩
  have hz := invariant_causal (⟨(v+w)/2-tau,x,(v-w)/2,hc⟩ : CausalPoint)
  simp only [movingMean,closedMean,hh,max_eq_right hz]

private theorem sourceKernel_moving (q : XiZeroCopy) (branch image : Bool)
    (p r X k v w : ℝ) (hv : (if image then r else p) ≤ v) (hw : (if image then p else r) ≤ w) :
    sourceKernel q branch image p r X k v w=
      movingMean q branch ((p+r)/2) (if image then -((p-r)/2) else (p-r)/2) X k v w := by
  rw [sourceKernel_circleMean]
  have hh : (v+w-p-r)/2=(v+w)/2-(p+r)/2 := by ring
  cases image
  · simp only [Bool.false_eq_true,↓reduceIte] at hv hw ⊢
    rw [movingMean_on_cone q branch ((p+r)/2) ((p-r)/2) X k v w
      (by linarith) (by linarith),hh]
  · simp only [↓reduceIte] at hv hw ⊢
    rw [movingMean_on_cone q branch ((p+r)/2) (-((p-r)/2)) X k v w
      (by linarith) (by linarith)]
    have hi : invariant ((v+w-p-r)/2) ((p-r)/2) (-((v-w)/2))=
        invariant ((v+w-p-r)/2) (-((p-r)/2)) ((v-w)/2) := by
      simp only [invariant,Real.sinh_neg,Real.cosh_neg]
      ring
    rw [hi,hh]

private theorem terminalArm_integral (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (tau x X k L : ℝ) (hL : tau+x ≤ L) :
    (∫ v in Ioi (0:ℝ), terminalArm q branch amp tau x X k L v)=
      ∫ v in (tau+x)..L, movingMean q branch tau x X k v L*seedNullFirst q branch amp v L := by
  have he (v : ℝ) : (Ioi (0:ℝ)).indicator (terminalArm q branch amp tau x X k L) v=
      terminalArm q branch amp tau x X k L v := by
    by_cases hv : 0 < v
    · exact indicator_of_mem hv _
    · have hz := seedNullFirst_zero_nonpos q branch amp v L (le_of_not_gt hv)
      simp [Set.indicator,terminalArm,hv,hz]
  calc
    _ = ∫ v, (Ioi (0:ℝ)).indicator (terminalArm q branch amp tau x X k L) v :=
      (integral_indicator measurableSet_Ioi).symm
    _ = ∫ v, terminalArm q branch amp tau x X k L v :=
      integral_congr_ae (Filter.Eventually.of_forall he)
    _ = ∫ v in Icc (tau+x) L, movingMean q branch tau x X k v L*seedNullFirst q branch amp v L :=
      integral_indicator measurableSet_Icc
    _ = _ := by rw [integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le hL]

private theorem seedTerminal_eq_arms (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r L X k : ℝ) (hpL : p ≤ L) (hrL : r ≤ L) :
    seedTerminal q branch amp p r L X k=
      (∫ v in Ioi (0:ℝ), terminalArm q branch amp ((p+r)/2) ((p-r)/2) X k L v)-
        ∫ v in Ioi (0:ℝ), terminalArm q branch amp ((p+r)/2) (-((p-r)/2)) X k L v := by
  have hp : (p+r)/2+(p-r)/2=p := by ring
  have hr : (p+r)/2+ -((p-r)/2)=r := by ring
  rw [terminalArm_integral q branch amp ((p+r)/2) ((p-r)/2) X k L (by linarith),
    terminalArm_integral q branch amp ((p+r)/2) (-((p-r)/2)) X k L (by linarith),hp,hr]
  unfold seedTerminal
  congr 1
  · apply intervalIntegral.integral_congr
    intro v hv
    have hv' : v ∈ Icc p L := by simpa only [uIcc_of_le hpL] using hv
    dsimp only
    exact congrArg (fun z : ℂ => z*seedNullFirst q branch amp v L)
      (sourceKernel_moving q branch false p r X k v L hv'.1 hrL)
  · apply intervalIntegral.integral_congr
    intro v hv
    have hv' : v ∈ Icc r L := by simpa only [uIcc_of_le hrL] using hv
    dsimp only
    exact congrArg (fun z : ℂ => z*seedNullFirst q branch amp v L)
      (sourceKernel_moving q branch true p r X k v L hv'.1 hpL)

theorem seedCapField_arms (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (tau x X k : ℝ) :
    seedTraceCoefficient q branch amp*(∫ v in Ioi (0:ℝ), horizonDensity q branch tau x X k v)-
      seedTraceCoefficient q branch amp*(∫ v in Ioi (0:ℝ), horizonDensity q branch tau (-x) X k v)=
        -seedCapField q branch amp tau x X k := by
  have he : (fun v => timeOnsetFirst (2*physicalRate q branch) v*horizonKernel q branch tau x v X k)=
      fun v => (horizonDensity q branch tau x X k v-horizonDensity q branch tau (-x) X k v)/2 := by
    funext v
    dsimp only [horizonKernel,horizonDensity]
    ring
  rw [seedCapField,he,integral_div,integral_sub (horizonDensity_integrable q branch tau x X k)
    (horizonDensity_integrable q branch tau (-x) X k)]
  ring

/-- The actual outgoing-null terminal face converges to the independently
specified seed cap, with its full angular field, clock and orientation. -/
theorem seedTerminal_horizon_limit (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p r X k : ℝ) :
    Tendsto (fun L => seedTerminal q branch amp p r L X k) atTop
      (𝓝 (-seedCapField q branch amp ((p+r)/2) ((p-r)/2) X k)) := by
  have h := (terminalArm_limit q branch amp ((p+r)/2) ((p-r)/2) X k).sub
    (terminalArm_limit q branch amp ((p+r)/2) (-((p-r)/2)) X k)
  rw [seedCapField_arms] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (max p r)] with L hL
  exact (seedTerminal_eq_arms q branch amp p r L X k
    ((le_max_left _ _).trans hL) ((le_max_right _ _).trans hL)).symm

/-- The original pulse-minus-source finite future integrals have their exact
infinite null-exhaustion limit. Absolute pulse admission is a separate statement. -/
theorem finite_source_balance_limit (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p : ℝ) (width : NNReal) (X k : ℝ) :
    Tendsto (fun L => finiteFutureAction (fun t y z => fullSourceOnsetPulse q branch amp t y z-
        parameter q branch*timeReducedCoefficient (physicalRate q branch) amp t y*fullSquarePotential q z)
      p (p+width) L X k) atTop
      (𝓝 (timeAngularSeedField q branch amp ((2*p+width)/2) (-(width:ℝ)/2) ![X,Real.exp k]-
        seedCapField q branch amp ((2*p+width)/2) (-(width:ℝ)/2) X k)) := by
  have h := (seedTerminal_horizon_limit q branch amp p (p+width) X k).const_add
    (timeAngularSeedField q branch amp ((2*p+width)/2) (-(width:ℝ)/2) ![X,Real.exp k])
  have ht : (p+(p+width))/2=(2*p+width)/2 := by ring
  have hx : (p-(p+width))/2= -(width:ℝ)/2 := by ring
  rw [ht,hx] at h
  apply Filter.Tendsto.congr' (f₁ := fun L =>
    timeAngularSeedField q branch amp ((2*p+width)/2) (-(width:ℝ)/2) ![X,Real.exp k]+
      seedTerminal q branch amp p (p+width) L X k) ?_ (by simpa only [sub_eq_add_neg] using h)
  filter_upwards [eventually_ge_atTop (p+width)] with L hL
  let span : NNReal := ⟨L-(p+width),sub_nonneg.mpr hL⟩
  have he : p+width+(span:ℝ)=L := by
    change p+width+(L-(p+width))=L
    ring
  have hb := finite_future_source_balance q branch amp p width span X k
  rw [he] at hb
  exact hb.symm

end
end RHTower.D4BMFutureSeedHorizon
