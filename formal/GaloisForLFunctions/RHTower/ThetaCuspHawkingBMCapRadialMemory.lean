import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCapNormalTrace
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCharacteristicContact
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointCoordinate
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! The original scalar cap arm has a finite radial horizon derivative governed by
an admitted source memory. Its exact physical-time transport retains the finite source
work, with the original onset and Hawking rates. Both moving image coordinates are differentiated before taking the full two-arm
radial limit. Late source work is nonzero at every positive physical-clock step;
its vanishing after the cap coefficient is included is classified exactly.
Angular passage and nonlinear left-QNM cancellation are not asserted here. -/

set_option autoImplicit false
open Set MeasureTheory Filter Topology
namespace RHTower.D4BMCapRadialMemory
open D4BMNativeCircle D4BMFutureHorizon D4BMCapNormalTrace
open D4BMJointSource D4BMModularCore D4BMFullSourceAdvanced
noncomputable section

private theorem scale_pos (x : ℝ) : 0 < capScale x :=
  div_pos (Real.exp_pos x) (Real.cosh_pos x)

private theorem scale_limit : Tendsto capScale atBot (𝓝 (0:ℝ)) := by
  have ht : Tendsto (fun x : ℝ => 2*x) atBot atBot :=
    (tendsto_const_mul_atBot_of_pos (by norm_num : (0:ℝ)<2)).mpr tendsto_id
  have he := Real.tendsto_exp_atBot.comp ht
  have hc (x : ℝ) : capScale x=1-radialUnit x := by
    rw [capScale,radialUnit,← Real.cosh_add_sinh x]
    field_simp [(Real.cosh_pos x).ne']
    ring
  have hform : capScale=fun x => 2*Real.exp (2*x)/(1+Real.exp (2*x)) := by
    funext x
    rw [eq_div_iff (ne_of_gt (by positivity : 0 < 1+Real.exp (2*x))),hc]
    have hh := radialUnit_one_sub x
    nlinarith
  rw [hform]
  simpa only [Function.comp_def,Pi.div_apply,mul_zero,add_zero,zero_div]
    using! (he.const_mul 2).div (tendsto_const_nhds.add he) (by norm_num : (1:ℝ)+0 ≠ 0)

private theorem kernel_local_bound (q : XiZeroCopy) (X k : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      ‖angularKernel q (1+u) X k-fullSquarePotential q ![X,Real.exp k]‖ ≤ B*u := by
  have hc : ContinuousOn (fun z => characteristicFirst q z X k) (Icc 1 2) :=
    (characteristicFirst_continuousOn q X k).mono (fun _ hz => hz.1)
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max B 0,le_max_right _ _,fun u hu hu1 => ?_⟩
  have hz : 1 ≤ 1+u := by linarith
  rw [angularKernel_source_integral q X k ⟨1+u,hz⟩,add_sub_cancel_left]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (1:ℝ)) (b := 1+u) (C := max B 0) (fun z (hz' : z ∈ uIoc (1:ℝ) (1+u)) => by
      rw [uIoc_of_le hz] at hz'
      exact (hB z ⟨hz'.1.le,by linarith [hz'.2]⟩).trans (le_max_left _ _))
  simpa only [add_sub_cancel_left,abs_of_nonneg hu] using hi

private theorem large_radius_bound (b h : ℝ) (hb : 0 < b)
    (hu : 1 ≤ b*(Real.exp h-1)) :
    Real.arcosh (1+b*(Real.exp h-1)) ≤ Real.log 4+Real.log b+h := by
  have hbe : 1 < b*Real.exp h := by nlinarith
  have hp : 0 ≤ Real.log 4+Real.log b+h := by
    have ht : Real.log (b*Real.exp h) = Real.log b+h := by
      rw [Real.log_mul hb.ne' (Real.exp_pos h).ne',Real.log_exp]
    have hi := Real.log_nonneg hbe.le
    rw [ht] at hi
    linarith [Real.log_nonneg (by norm_num : (1:ℝ)≤4)]
  have hz : 1 ≤ 1+b*(Real.exp h-1) := by linarith
  have hx : 1+b*(Real.exp h-1) ≤ 2*b*Real.exp h := by nlinarith
  have he : Real.exp (Real.log 4+Real.log b+h)=4*b*Real.exp h := by
    rw [Real.exp_add,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<4),Real.exp_log hb]
  have hc : 2*b*Real.exp h ≤ Real.cosh (Real.log 4+Real.log b+h) := by
    rw [Real.cosh_eq,he]
    linarith [Real.exp_pos (-(Real.log 4+Real.log b+h))]
  have hl := Real.cosh_le_cosh.mp ((Real.cosh_arcosh hz).trans_le (hx.trans hc))
  simpa only [abs_of_nonneg (Real.arcosh_nonneg hz),abs_of_nonneg hp] using hl

private theorem kernel_scaled_bound (q : XiZeroCopy) (X k : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b h : ℝ, 0 < b → b ≤ 1 → 0 ≤ h →
      ‖angularKernel q (1+b*(Real.exp h-1)) X k-fullSquarePotential q ![X,Real.exp k]‖ ≤
        b*C*(Real.exp h+Real.exp (sourceGrowthExponent q*h)) := by
  obtain ⟨B,hB,hb⟩ := kernel_local_bound q X k
  obtain ⟨D,hD,hd⟩ := mean_global_growth q
  let A := D*Real.exp (sourceGrowthExponent q*(Real.log 4+|k|))
  let Q := fullSquarePotential q ![X,Real.exp k]
  have ha : 1 ≤ sourceGrowthExponent q := (sourceGrowthExponent_bounds q).1
  have ha0 : 0 ≤ sourceGrowthExponent q := by linarith
  have hA : 0 ≤ A := mul_nonneg hD (Real.exp_pos _).le
  refine ⟨B+A+‖Q‖,by positivity,fun b h hb0 hb1 hh => ?_⟩
  have he : 1 ≤ Real.exp h := Real.one_le_exp_iff.mpr hh
  have hu0 : 0 ≤ b*(Real.exp h-1) := by positivity
  by_cases hu : b*(Real.exp h-1) ≤ 1
  · apply (hb _ hu0 hu).trans
    have hprod : B*b*(Real.exp h-1) ≤ b*B*Real.exp h := by nlinarith
    have hm : b*B*Real.exp h ≤ b*(B+A+‖Q‖)*(Real.exp h+Real.exp (sourceGrowthExponent q*h)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (by linarith [norm_nonneg Q]) hb0.le)
        (by linarith [Real.exp_pos (sourceGrowthExponent q*h)]) (Real.exp_pos h).le (by positivity)
    nlinarith
  · have hu1 : 1 ≤ b*(Real.exp h-1) := (lt_of_not_ge hu).le
    have hz : 1 ≤ 1+b*(Real.exp h-1) := by linarith
    have hr0 := Real.arcosh_nonneg hz
    have hlog : Real.log b ≤ 0 := Real.log_nonpos hb0.le hb1
    have hpow : Real.exp (sourceGrowthExponent q*Real.log b) ≤ b := by
      calc
        _ ≤ Real.exp (Real.log b) := Real.exp_le_exp.mpr (by nlinarith)
        _ = b := Real.exp_log hb0
    have hg : ‖angularKernel q (1+b*(Real.exp h-1)) X k‖ ≤ A*b*Real.exp (sourceGrowthExponent q*h) := by
      apply (hd _ X k hr0).trans
      calc
        _ ≤ D*Real.exp (sourceGrowthExponent q*(Real.log 4+Real.log b+h+|k|)) := by
          apply mul_le_mul_of_nonneg_left _ hD
          apply Real.exp_le_exp.mpr
          apply mul_le_mul_of_nonneg_left _ ha0
          linarith [large_radius_bound b h hb0 hu1]
        _ = A*Real.exp (sourceGrowthExponent q*Real.log b)*Real.exp (sourceGrowthExponent q*h) := by
          have heq : Real.exp (sourceGrowthExponent q*(Real.log 4+Real.log b+h+|k|))=
              Real.exp (sourceGrowthExponent q*(Real.log 4+|k|))*
              Real.exp (sourceGrowthExponent q*Real.log b)*Real.exp (sourceGrowthExponent q*h) := by
            rw [← Real.exp_add,← Real.exp_add]
            congr 1
            ring
          rw [heq]
          dsimp [A]
          ring
        _ ≤ _ := by gcongr
    have hQ : ‖Q‖ ≤ b*‖Q‖*Real.exp h := by
      have hbe : 1 ≤ b*Real.exp h := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hbe (norm_nonneg Q)]
    apply (norm_sub_le _ _).trans
    change ‖angularKernel q (1+b*(Real.exp h-1)) X k‖+‖Q‖ ≤ _
    have hc : 0 ≤ b*B*(Real.exp h+Real.exp (sourceGrowthExponent q*h)) := by positivity
    have h1 : 0 ≤ b*A*Real.exp h := by positivity
    have h2 : 0 ≤ b*‖Q‖*Real.exp (sourceGrowthExponent q*h) := by positivity
    nlinarith

private theorem mean_eq_kernel (q : XiZeroCopy) (x X k h : ℝ) (hh : 0 ≤ h) :
    horizonMean q x h X k=angularKernel q (1+capScale x*(Real.exp h-1)) X k := by
  have hz : 1 ≤ 1+capScale x*(Real.exp h-1) := by
    have he := Real.one_le_exp_iff.mpr hh
    have hp := scale_pos x
    nlinarith
  change mean q (Real.arcosh (max 1 (1+capScale x*(Real.exp h-1)))) X k=_
  rw [max_eq_right hz]
  rfl

private def normalizedMean (q : XiZeroCopy) (x X k h : ℝ) : ℂ :=
  (horizonMean q x h X k-fullSquarePotential q ![X,Real.exp k])/(capScale x:ℂ)

private theorem normalizedMean_limit (q : XiZeroCopy) (X k h : ℝ) (hh : 0 < h) :
    Tendsto (fun x => normalizedMean q x X k h) atBot
      (𝓝 ((D4BMHorizon.scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]/2)*
        ((Real.exp h-1:ℝ):ℂ))) := by
  let K := fun z => angularKernel q z X k
  have hd := (angularKernel_closed_derivative q X k (⟨1,by norm_num⟩ : Ici (1:ℝ))).mono Ioi_subset_Ici_self
  rw [characteristicFirst_at_one] at hd
  have hs := (hasDerivWithinAt_iff_tendsto_slope' (by simp : (1:ℝ) ∉ Ioi (1:ℝ))).mp hd
  have hz : Tendsto (fun x => 1+capScale x*(Real.exp h-1)) atBot (𝓝[Ioi 1] (1:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [zero_mul,add_zero] using (tendsto_const_nhds (x := (1:ℝ))).add
        (scale_limit.mul_const (Real.exp h-1))
    · filter_upwards with x
      have he := Real.one_lt_exp_iff.mpr hh
      have hp := scale_pos x
      change 1 < 1+capScale x*(Real.exp h-1)
      nlinarith
  have ht := (hs.comp hz).mul_const (((Real.exp h-1:ℝ):ℂ))
  convert! ht using 1
  funext x
  rw [normalizedMean,mean_eq_kernel q x X k h hh.le]
  simp only [Function.comp_apply,slope_def_module,add_sub_cancel_left,Complex.real_smul,Complex.ofReal_inv,
    Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_one]
  have hc : (capScale x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (scale_pos x).ne'
  have he : (Real.exp h:ℂ)-1 ≠ 0 := by
    exact_mod_cast (ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr hh)))
  have hK : angularKernel q 1 X k=fullSquarePotential q ![X,Real.exp k] := by
    simp only [angularKernel,Real.arcosh_zero,mean_zero]
  rw [hK]
  field_simp [hc,he]

private theorem normalizedMean_bound (q : XiZeroCopy) (X k : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x h : ℝ, capScale x ≤ 1 → 0 ≤ h →
      ‖normalizedMean q x X k h‖ ≤ C*(Real.exp h+Real.exp (sourceGrowthExponent q*h)) := by
  obtain ⟨C,hC,hb⟩ := kernel_scaled_bound q X k
  refine ⟨C,hC,fun x h hx hh => ?_⟩
  rw [normalizedMean,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (scale_pos x)]
  rw [div_le_iff₀ (scale_pos x),mean_eq_kernel q x X k h hh]
  nlinarith [hb (capScale x) h (scale_pos x) hx hh]

private theorem normalWeight_continuous (q : XiZeroCopy) (branch : Bool) (v : ℝ) :
    Continuous (normalWeight q branch v) := by
  have h0 := timeOnsetSecond_continuous (2*physicalRate q branch)
  have h1 : Continuous (timeOnsetFirst (2*physicalRate q branch)) :=
    continuous_iff_continuousAt.mpr (fun u => (timeOnsetFirst_hasDerivAt _ u).continuousAt)
  exact ((h0.comp (continuous_const.add continuous_id)).mul
    (continuous_const.sub (Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)))).add
    ((h1.comp (continuous_const.add continuous_id)).mul
      (Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)))

private theorem normalWeight_bound (q : XiZeroCopy) (branch : Bool) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ v h : ℝ, 0 ≤ h →
      ‖normalWeight q branch v h‖ ≤ B*Real.exp (-decayExponent q*(v+h)) := by
  obtain ⟨B,hB,hb⟩ := onset_derivative_bound q branch
  refine ⟨B,hB,fun v h hh => ?_⟩
  have he : 0 ≤ Real.exp (-h) := (Real.exp_pos _).le
  have he1 : Real.exp (-h) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  unfold normalWeight
  apply (norm_add_le _ _).trans
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg he]
  rw [show (1:ℂ)-(Real.exp (-h):ℂ)=((1-Real.exp (-h):ℝ):ℂ) by push_cast; rfl]
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr he1)]
  have h0 := norm_nonneg (timeOnsetFirst (2*physicalRate q branch) (v+h))
  have h1 := norm_nonneg (timeOnsetSecond (2*physicalRate q branch) (v+h))
  nlinarith [hb (v+h)]

private theorem decay_gt_one (q : XiZeroCopy) : 1 < decayExponent q :=
  lt_of_le_of_lt (sourceGrowthExponent_bounds q).1 (decayExponent_bounds q).1

private def kernelMajorant (q : XiZeroCopy) (h : ℝ) : ℝ :=
  Real.exp ((1-decayExponent q)*h)+Real.exp ((sourceGrowthExponent q-decayExponent q)*h)

private theorem kernelMajorant_integrable (q : XiZeroCopy) :
    IntegrableOn (kernelMajorant q) (Ioi 0) :=
  (integrableOn_exp_mul_Ioi (sub_neg.mpr (decay_gt_one q)) 0).add
    (integrableOn_exp_mul_Ioi (sub_neg.mpr (decayExponent_bounds q).1) 0)

private def normalDensity (q : XiZeroCopy) (branch : Bool) (v x X k h : ℝ) : ℂ :=
  normalWeight q branch v h*normalizedMean q x X k h

private theorem normalDensity_continuous (q : XiZeroCopy) (branch : Bool) (v x X k : ℝ) :
    Continuous (normalDensity q branch v x X k) := by
  have hm : Continuous (fun h => horizonMean q x h X k) := by
    have hc : Continuous (fun z : ℝ => mean q (Real.arcosh (max 1 z)) X k) := by
      apply (mean_radial_smooth q X k).continuous.comp
      exact Real.continuousOn_arcosh.comp_continuous (continuous_const.max continuous_id)
        (fun z => le_max_left 1 z)
    exact hc.comp (continuous_const.add ((Real.continuous_exp.sub continuous_const).const_mul _))
  exact (normalWeight_continuous q branch v).mul ((hm.sub continuous_const).div_const _)

private theorem normalDensity_bound (q : XiZeroCopy) (branch : Bool) (v X k : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x h : ℝ, capScale x ≤ 1 → 0 ≤ h →
      ‖normalDensity q branch v x X k h‖ ≤ C*kernelMajorant q h := by
  obtain ⟨B,hB,hb⟩ := normalWeight_bound q branch
  obtain ⟨C,hC,hc⟩ := normalizedMean_bound q X k
  refine ⟨B*C*Real.exp (-decayExponent q*v),by positivity,fun x h hx hh => ?_⟩
  rw [normalDensity,norm_mul]
  calc
    _ ≤ (B*Real.exp (-decayExponent q*(v+h)))*(C*(Real.exp h+Real.exp (sourceGrowthExponent q*h))) :=
      mul_le_mul (hb v h hh) (hc x h hx hh) (norm_nonneg _) (by positivity)
    _ = _ := by
      have he1 : Real.exp (-decayExponent q*(v+h))*Real.exp h=
          Real.exp (-decayExponent q*v)*Real.exp ((1-decayExponent q)*h) := by
        rw [← Real.exp_add,← Real.exp_add]
        congr 1
        ring
      have he2 : Real.exp (-decayExponent q*(v+h))*Real.exp (sourceGrowthExponent q*h)=
          Real.exp (-decayExponent q*v)*Real.exp ((sourceGrowthExponent q-decayExponent q)*h) := by
        rw [← Real.exp_add,← Real.exp_add]
        congr 1
        ring
      calc
        _ = (B*C)*(Real.exp (-decayExponent q*(v+h))*Real.exp h+
          Real.exp (-decayExponent q*(v+h))*Real.exp (sourceGrowthExponent q*h)) := by ring
        _ = _ := by rw [he1,he2]; dsimp [kernelMajorant]; ring

private theorem normalDensity_integrable (q : XiZeroCopy) (branch : Bool) (v x X k : ℝ)
    (hx : capScale x ≤ 1) : IntegrableOn (normalDensity q branch v x X k) (Ioi 0) := by
  obtain ⟨C,hC,hb⟩ := normalDensity_bound q branch v X k
  apply ((kernelMajorant_integrable q).const_mul C).mono'
    (normalDensity_continuous q branch v x X k).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  exact hb x h hx hh.le

private theorem onset_pair_bound (q : XiZeroCopy) (branch : Bool) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ,
      ‖timeOnset (2*physicalRate q branch) u‖+‖timeOnsetFirst (2*physicalRate q branch) u‖ ≤
        B*Real.exp (-decayExponent q*u) := by
  apply timeOnset_pair_bound
  have hs := currentRate_re_lt q branch
  change (2*physicalRate q branch).re < -2 at hs
  linarith [(decayExponent_bounds q).2]

private theorem exp_shift (q : XiZeroCopy) (v h : ℝ) :
    Real.exp (-decayExponent q*(v+h))*Real.exp h=
      Real.exp (-decayExponent q*v)*Real.exp ((1-decayExponent q)*h) := by
  rw [← Real.exp_add,← Real.exp_add]
  congr 1
  ring

private def momentDensity (q : XiZeroCopy) (branch normal : Bool) (v h : ℝ) : ℂ :=
  if normal then normalWeight q branch v h*((Real.exp h:ℂ)-1)
  else timeOnset (2*physicalRate q branch) (v+h)*(Real.exp h:ℂ)

private theorem momentDensity_continuous (q : XiZeroCopy) (branch normal : Bool) (v : ℝ) :
    Continuous (momentDensity q branch normal v) := by
  have he := Complex.continuous_ofReal.comp Real.continuous_exp
  have hg : Continuous (timeOnset (2*physicalRate q branch)) :=
    continuous_iff_continuousAt.mpr (fun u => (timeOnset_hasDerivAt _ u).continuousAt)
  cases normal
  · exact (hg.comp (continuous_const.add continuous_id)).mul he
  · exact (normalWeight_continuous q branch v).mul (he.sub continuous_const)

private theorem momentDensity_bound (q : XiZeroCopy) (branch normal : Bool) (v : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 ≤ h →
      ‖momentDensity q branch normal v h‖ ≤ C*Real.exp ((1-decayExponent q)*h) := by
  cases normal
  · obtain ⟨B,hB,hb⟩ := onset_pair_bound q branch
    refine ⟨B*Real.exp (-decayExponent q*v),by positivity,fun h hh => ?_⟩
    change ‖timeOnset (2*physicalRate q branch) (v+h)*(Real.exp h:ℂ)‖ ≤ _
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos h)]
    calc
      _ ≤ (B*Real.exp (-decayExponent q*(v+h)))*Real.exp h := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos h).le
        linarith [hb (v+h),norm_nonneg (timeOnsetFirst (2*physicalRate q branch) (v+h))]
      _ = _ := by rw [mul_assoc,exp_shift]; ring
  · obtain ⟨B,hB,hb⟩ := normalWeight_bound q branch
    refine ⟨B*Real.exp (-decayExponent q*v),by positivity,fun h hh => ?_⟩
    change ‖normalWeight q branch v h*((Real.exp h:ℂ)-1)‖ ≤ _
    have he : 0 ≤ Real.exp h-1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr hh)
    have hn : ‖(Real.exp h:ℂ)-1‖=Real.exp h-1 := by
      rw [show (Real.exp h:ℂ)-1=((Real.exp h-1:ℝ):ℂ) by push_cast; rfl]
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg he]
    rw [norm_mul,hn]
    calc
      _ ≤ (B*Real.exp (-decayExponent q*(v+h)))*Real.exp h :=
        mul_le_mul (hb v h hh) (by linarith) he (by positivity)
      _ = _ := by rw [mul_assoc,exp_shift]; ring

private theorem momentDensity_integrable (q : XiZeroCopy) (branch normal : Bool) (v : ℝ) :
    IntegrableOn (momentDensity q branch normal v) (Ioi 0) := by
  obtain ⟨C,hC,hb⟩ := momentDensity_bound q branch normal v
  apply ((integrableOn_exp_mul_Ioi (sub_neg.mpr (decay_gt_one q)) 0).const_mul C).mono'
    (momentDensity_continuous q branch normal v).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  exact hb h hh.le

private def momentPrimitive (q : XiZeroCopy) (branch : Bool) (v h : ℝ) : ℂ :=
  timeOnsetFirst (2*physicalRate q branch) (v+h)*((Real.exp h:ℂ)-2+(Real.exp (-h):ℂ))-
    timeOnset (2*physicalRate q branch) (v+h)*((Real.exp h:ℂ)-1)

private theorem momentPrimitive_derivative (q : XiZeroCopy) (branch : Bool) (v h : ℝ) :
    HasDerivAt (momentPrimitive q branch v)
      (momentDensity q branch true v h-momentDensity q branch false v h) h := by
  have hg0 := HasDerivAt.comp_const_add v h (timeOnset_hasDerivAt (2*physicalRate q branch) (v+h))
  have hg1 := HasDerivAt.comp_const_add v h (timeOnsetFirst_hasDerivAt (2*physicalRate q branch) (v+h))
  have he := (Real.hasDerivAt_exp h).ofReal_comp
  have hn := ((Real.hasDerivAt_exp (-h)).comp h (hasDerivAt_neg h)).ofReal_comp
  convert! (hg1.mul ((he.sub_const 2).add hn)).sub (hg0.mul (he.sub_const 1)) using 1
  dsimp only [momentDensity,normalWeight,Function.comp_def]
  simp only [Bool.false_eq_true,↓reduceIte,Pi.add_apply,Real.exp_neg,Complex.ofReal_inv,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_one]
  have hE : (Real.exp h:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos h).ne'
  field_simp [hE]
  ring

private theorem momentPrimitive_zero (q : XiZeroCopy) (branch : Bool) (v : ℝ) :
    momentPrimitive q branch v 0=0 := by
  simp only [momentPrimitive,neg_zero,Real.exp_zero,Complex.ofReal_one]
  ring

private theorem momentPrimitive_limit (q : XiZeroCopy) (branch : Bool) (v : ℝ) :
    Tendsto (momentPrimitive q branch v) atTop (𝓝 0) := by
  obtain ⟨B,hB,hb⟩ := onset_pair_bound q branch
  have he := Real.tendsto_exp_atBot.comp
    ((tendsto_const_mul_atBot_of_neg (sub_neg.mpr (decay_gt_one q))).mpr tendsto_id)
  have ht : Tendsto (fun h => (4*B*Real.exp (-decayExponent q*v))*Real.exp ((1-decayExponent q)*h)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,id_eq,mul_zero] using he.const_mul (4*B*Real.exp (-decayExponent q*v))
  apply squeeze_zero_norm' _ ht
  filter_upwards [eventually_ge_atTop (0:ℝ)] with h hh
  have hE : 1 ≤ Real.exp h := Real.one_le_exp_iff.mpr hh
  have hN : Real.exp (-h) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hK1 : ‖(Real.exp h:ℂ)-2+(Real.exp (-h):ℂ)‖ ≤ 4*Real.exp h := by
    calc
      _ ≤ ‖(Real.exp h:ℂ)‖+‖(2:ℂ)‖+‖(Real.exp (-h):ℂ)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ _ := by
        simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Complex.norm_ofNat]
        linarith
  have hK0 : ‖(Real.exp h:ℂ)-1‖ ≤ 2*Real.exp h := by
    apply (norm_sub_le _ _).trans
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),norm_one]
    linarith
  have hg0 := norm_nonneg (timeOnset (2*physicalRate q branch) (v+h))
  have hg1 := norm_nonneg (timeOnsetFirst (2*physicalRate q branch) (v+h))
  unfold momentPrimitive
  calc
    _ ≤ ‖timeOnsetFirst (2*physicalRate q branch) (v+h)‖*‖(Real.exp h:ℂ)-2+(Real.exp (-h):ℂ)‖+
        ‖timeOnset (2*physicalRate q branch) (v+h)‖*‖(Real.exp h:ℂ)-1‖ := by
      simpa only [norm_mul] using norm_sub_le
        (timeOnsetFirst (2*physicalRate q branch) (v+h)*((Real.exp h:ℂ)-2+(Real.exp (-h):ℂ)))
        (timeOnset (2*physicalRate q branch) (v+h)*((Real.exp h:ℂ)-1))
    _ ≤ 4*(‖timeOnset (2*physicalRate q branch) (v+h)‖+
        ‖timeOnsetFirst (2*physicalRate q branch) (v+h)‖)*Real.exp h := by
      have h0 := mul_le_mul_of_nonneg_left hK0 hg0
      have h1 := mul_le_mul_of_nonneg_left hK1 hg1
      nlinarith [mul_nonneg hg0 (Real.exp_pos h).le]
    _ ≤ 4*(B*Real.exp (-decayExponent q*(v+h)))*Real.exp h := by gcongr; exact hb (v+h)
    _ = _ := by rw [mul_assoc,mul_assoc,exp_shift]; ring

/-- Source memory determined at the original Hawking rate. -/
def sourceMemory (q : XiZeroCopy) (branch : Bool) (v : ℝ) : ℂ :=
  ∫ h in Ioi (0:ℝ), timeOnset (2*physicalRate q branch) (v+h)*(Real.exp h:ℂ)

/-- Exact moment of the transferred normal weight, including both source endpoints. -/
theorem normalWeight_first_moment (q : XiZeroCopy) (branch : Bool) (v : ℝ) :
    (∫ h in Ioi (0:ℝ), normalWeight q branch v h*((Real.exp h:ℂ)-1))=sourceMemory q branch v := by
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun h (_ : h ∈ Ici (0:ℝ)) => momentPrimitive_derivative q branch v h)
    ((momentDensity_integrable q branch true v).sub (momentDensity_integrable q branch false v))
    (momentPrimitive_limit q branch v)
  rw [integral_sub (momentDensity_integrable q branch true v) (momentDensity_integrable q branch false v),
    momentPrimitive_zero,sub_self] at hi
  exact sub_eq_zero.mp hi

private theorem normalWeight_integrable (q : XiZeroCopy) (branch : Bool) (v : ℝ) :
    IntegrableOn (normalWeight q branch v) (Ioi 0) := by
  obtain ⟨B,hB,hb⟩ := normalWeight_bound q branch
  have hd : 0 < decayExponent q := by linarith [decay_gt_one q]
  apply ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hd) 0).const_mul
    (B*Real.exp (-decayExponent q*v))).mono'
    (normalWeight_continuous q branch v).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  have he : (B*Real.exp (-decayExponent q*v))*Real.exp (-decayExponent q*h)=
      B*Real.exp (-decayExponent q*(v+h)) := by
    rw [mul_assoc,← Real.exp_add]
    congr 2
    ring
  rw [he]
  exact hb v h hh.le

private theorem normalDensity_integral (q : XiZeroCopy) (branch : Bool) (v x X k : ℝ)
    (hx : capScale x ≤ 1) :
    (∫ h in Ioi (0:ℝ), normalDensity q branch v x X k h)=
      normalArm q branch v x X k/(capScale x:ℂ) := by
  have hc : (capScale x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (scale_pos x).ne'
  have hd := normalDensity_integrable q branch v x X k hx
  have hn := normalWeight_integrable q branch v
  have he : normalArm q branch v x X k=
      (capScale x:ℂ)*(∫ h in Ioi (0:ℝ), normalDensity q branch v x X k h) := by
    change (∫ h in Ioi (0:ℝ), normalWeight q branch v h*horizonMean q x h X k)=_
    calc
      _ = ∫ h in Ioi (0:ℝ), ((capScale x:ℂ)*normalDensity q branch v x X k h+
          normalWeight q branch v h*fullSquarePotential q ![X,Real.exp k]) := by
        apply integral_congr_ae
        filter_upwards with h
        dsimp [normalDensity,normalizedMean]
        field_simp [hc]
        ring
      _ = _ := by
        rw [integral_add (hd.const_mul (capScale x:ℂ))
          (hn.mul_const (fullSquarePotential q ![X,Real.exp k])),integral_const_mul,integral_mul_const,
          normalWeight_future_integral,zero_mul,add_zero]
  apply (eq_div_iff hc).mpr
  rw [he]
  ring

/-- The actual cap's normalized normal arm retains the literal angular source memory. -/
theorem normalArm_div_scale_ingoing (q : XiZeroCopy) (branch : Bool) (v X k : ℝ) :
    Tendsto (fun x => normalArm q branch v x X k/(capScale x:ℂ)) atBot
      (𝓝 ((D4BMHorizon.scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]/2)*sourceMemory q branch v)) := by
  obtain ⟨C,hC,hb⟩ := normalDensity_bound q branch v X k
  have hsmall : ∀ᶠ x in atBot, capScale x ≤ 1 :=
    (scale_limit.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))).mono (fun x hx => hx.le)
  have ht := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (0:ℝ))) (fun h => C*kernelMajorant q h)
    (Filter.Eventually.of_forall (fun x => (normalDensity_continuous q branch v x X k).aestronglyMeasurable))
    (by
      filter_upwards [hsmall] with x hx
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
      exact hb x h hx hh.le)
    ((kernelMajorant_integrable q).const_mul C)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
      exact (normalizedMean_limit q X k h hh).const_mul (normalWeight q branch v h))
  have he : (∫ h in Ioi (0:ℝ), normalWeight q branch v h*
      ((D4BMHorizon.scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]/2)*((Real.exp h-1:ℝ):ℂ)))=
      (D4BMHorizon.scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]/2)*sourceMemory q branch v := by
    calc
      _ = ∫ h in Ioi (0:ℝ), (D4BMHorizon.scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]/2)*
          (normalWeight q branch v h*((Real.exp h:ℂ)-1)) := by
        apply integral_congr_ae
        filter_upwards with h
        push_cast
        ring
      _ = _ := by rw [integral_const_mul,normalWeight_first_moment]
  rw [he] at ht
  apply ht.congr'
  filter_upwards [hsmall] with x hx
  exact normalDensity_integral q branch v x X k hx

/-- The actual normal derivative's first horizon coefficient is source-derived. -/
theorem boundaryArm_scaled_normal_ingoing (q : XiZeroCopy) (branch : Bool) (v X k : ℝ) :
    Tendsto (fun x => deriv (fun y => boundaryArm q branch v y X k) x/(capScale x:ℂ)) atBot
      (𝓝 (-D4BMHorizon.scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]*sourceMemory q branch v)) := by
  have hr : Tendsto (fun x => 2-capScale x) atBot (𝓝 (2:ℝ)) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := (2:ℝ))).sub scale_limit
  have hc : Tendsto (fun x => -((2-capScale x:ℝ):ℂ)) atBot (𝓝 (-2:ℂ)) := by
    simpa only [Complex.ofReal_ofNat,Function.comp_def] using! ((Complex.continuous_ofReal.tendsto (2:ℝ)).comp hr).neg
  have ht := hc.mul (normalArm_div_scale_ingoing q branch v X k)
  convert! ht using 1
  · funext x
    rw [(boundaryArm_normal_hasDerivAt q branch v x X k).deriv]
    ring
  · ring

open D4BMJointWave

private theorem radius_scale (x : ℝ) (hx : x < 0) :
    tortoiseRadius x=1/(1-capScale x) ∧
      (tortoiseRadius x)^2-1=(tortoiseRadius x)^2*capScale x*(2-capScale x) := by
  have hc := (Real.cosh_pos x).ne'
  have hs := (Real.sinh_neg_iff.mpr hx).ne
  have he : 1-capScale x= -Real.sinh x/Real.cosh x := by
    rw [capScale,← Real.cosh_add_sinh x]
    field_simp
    ring
  constructor
  · rw [he,tortoiseRadius]
    field_simp
  · rw [capScale,← Real.cosh_add_sinh x,tortoiseRadius]
    field_simp
    ring

private theorem radius_limit : Tendsto tortoiseRadius atBot (𝓝 (1:ℝ)) := by
  have ht : Tendsto (fun x => 1/(1-capScale x)) atBot (𝓝 (1:ℝ)) := by
    simpa only [sub_zero,div_one] using!
      (tendsto_const_nhds (x := (1:ℝ))).div ((tendsto_const_nhds (x := (1:ℝ))).sub scale_limit)
        (by norm_num : (1:ℝ)-0 ≠ 0)
  apply ht.congr'
  filter_upwards [eventually_lt_atBot (0:ℝ)] with x hx
  exact (radius_scale x hx).1.symm

/-- The original cap arm, expressed in the physical radius at fixed ingoing time. -/
def radialArm (q : XiZeroCopy) (branch : Bool) (v X k r : ℝ) : ℂ :=
  boundaryArm q branch v (D4BMIngoingCoordinates.tortoise r) X k

private theorem radialArm_derivative (q : XiZeroCopy) (branch : Bool) (v X k x : ℝ) (hx : x < 0) :
    HasDerivAt (radialArm q branch v X k)
      (-normalArm q branch v x X k/((tortoiseRadius x:ℂ)^2*(capScale x:ℂ))) (tortoiseRadius x) := by
  have hr := tortoiseRadius_exterior x hx
  have hR : (tortoiseRadius x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hF : (tortoiseRadius x:ℂ)^2-1 ≠ 0 := by
    exact_mod_cast (show (tortoiseRadius x)^2-1 ≠ 0 by nlinarith)
  have hC : (capScale x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (scale_pos x).ne'
  have hfac : (tortoiseRadius x:ℂ)^2-1=
      (tortoiseRadius x:ℂ)^2*(capScale x:ℂ)*(2-(capScale x:ℂ)) := by
    exact_mod_cast (radius_scale x hx).2
  have ht := (boundaryArm_normal_hasDerivAt q branch v
    (D4BMIngoingCoordinates.tortoise (tortoiseRadius x)) X k).scomp (tortoiseRadius x)
      (D4BMIngoingCoordinates.tortoise_hasDerivAt _ hr)
  rw [tortoise_original_inverse x hx] at ht
  convert! ht using 1
  simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_sub,Complex.ofReal_pow,Complex.ofReal_one,Complex.ofReal_ofNat]
  field_simp [hR,hF,hC]
  rw [hfac]
  ring

/-- The actual scalar cap arm has its finite source-derived radial horizon derivative. -/
theorem radialArm_derivative_ingoing (q : XiZeroCopy) (branch : Bool) (v X k : ℝ) :
    Tendsto (fun x => deriv (radialArm q branch v X k) (tortoiseRadius x)) atBot
      (𝓝 (-(D4BMHorizon.scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]/2)*sourceMemory q branch v)) := by
  have hr : Tendsto (fun x => (tortoiseRadius x:ℂ)) atBot (𝓝 (1:ℂ)) := by
    simpa only [Complex.ofReal_one,Function.comp_def] using!
      (Complex.continuous_ofReal.tendsto (1:ℝ)).comp radius_limit
  have ht := (normalArm_div_scale_ingoing q branch v X k).neg.div (hr.pow 2) (by norm_num : (1:ℂ)^2 ≠ 0)
  have hl : Tendsto (fun x => -(normalArm q branch v x X k/(capScale x:ℂ))/(tortoiseRadius x:ℂ)^2)
      atBot (𝓝 (-(D4BMHorizon.scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]/2)*sourceMemory q branch v)) := by
    simpa only [one_pow,div_one,neg_mul,Pi.div_apply] using! ht
  apply hl.congr'
  filter_upwards [eventually_lt_atBot (0:ℝ)] with x hx
  rw [(radialArm_derivative q branch v X k x hx).deriv]
  ring

private def memorySlope (q : XiZeroCopy) (branch : Bool) (v h : ℝ) : ℂ :=
  timeOnsetFirst (2*physicalRate q branch) (v+h)*(Real.exp h:ℂ)

private theorem memorySlope_continuous (q : XiZeroCopy) (branch : Bool) (v : ℝ) :
    Continuous (memorySlope q branch v) := by
  have hg : Continuous (timeOnsetFirst (2*physicalRate q branch)) :=
    continuous_iff_continuousAt.mpr (fun u => (timeOnsetFirst_hasDerivAt _ u).continuousAt)
  exact (hg.comp (continuous_const.add continuous_id)).mul (Complex.continuous_ofReal.comp Real.continuous_exp)

private theorem memorySlope_bound (q : XiZeroCopy) (branch : Bool) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ v h : ℝ,
      ‖memorySlope q branch v h‖ ≤ B*Real.exp (-decayExponent q*v)*Real.exp ((1-decayExponent q)*h) := by
  obtain ⟨B,hB,hb⟩ := onset_pair_bound q branch
  refine ⟨B,hB,fun v h => ?_⟩
  rw [memorySlope,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos h)]
  calc
    _ ≤ (B*Real.exp (-decayExponent q*(v+h)))*Real.exp h := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos h).le
      linarith [hb (v+h),norm_nonneg (timeOnset (2*physicalRate q branch) (v+h))]
    _ = _ := by rw [mul_assoc,exp_shift]; ring

private theorem memorySlope_integrable (q : XiZeroCopy) (branch : Bool) (v : ℝ) :
    IntegrableOn (memorySlope q branch v) (Ioi 0) := by
  obtain ⟨B,hB,hb⟩ := memorySlope_bound q branch
  exact ((integrableOn_exp_mul_Ioi (sub_neg.mpr (decay_gt_one q)) 0).const_mul
    (B*Real.exp (-decayExponent q*v))).mono'
    (memorySlope_continuous q branch v).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun h => hb v h))

private theorem memorySlope_integral (q : XiZeroCopy) (branch : Bool) (v : ℝ) :
    (∫ h in Ioi (0:ℝ), memorySlope q branch v h)=
      -timeOnset (2*physicalRate q branch) v-sourceMemory q branch v := by
  have hd (h : ℝ) (_ : h ∈ Ici (0:ℝ)) :
      HasDerivAt (momentDensity q branch false v)
        (memorySlope q branch v h+momentDensity q branch false v h) h := by
    have hg := HasDerivAt.comp_const_add v h (timeOnset_hasDerivAt (2*physicalRate q branch) (v+h))
    convert! hg.mul (Real.hasDerivAt_exp h).ofReal_comp using 1
  have hl : Tendsto (momentDensity q branch false v) atTop (𝓝 0) := by
    obtain ⟨C,hC,hb⟩ := momentDensity_bound q branch false v
    have he := Real.tendsto_exp_atBot.comp
      ((tendsto_const_mul_atBot_of_neg (sub_neg.mpr (decay_gt_one q))).mpr tendsto_id)
    have ht : Tendsto (fun h => C*Real.exp ((1-decayExponent q)*h)) atTop (𝓝 0) := by
      simpa only [Function.comp_def,id_eq,mul_zero] using he.const_mul C
    apply squeeze_zero_norm' _ ht
    filter_upwards [eventually_ge_atTop (0:ℝ)] with h hh
    exact hb h hh
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto' hd
    ((memorySlope_integrable q branch v).add (momentDensity_integrable q branch false v)) hl
  rw [integral_add (memorySlope_integrable q branch v) (momentDensity_integrable q branch false v)] at hi
  have hz : momentDensity q branch false v 0=timeOnset (2*physicalRate q branch) v := by
    simp only [momentDensity,Bool.false_eq_true,↓reduceIte,Real.exp_zero,Complex.ofReal_one,add_zero,mul_one]
  rw [hz,zero_sub] at hi
  exact (eq_sub_iff_add_eq).mpr hi

/-- The boundary memory obeys its original source-driven transport equation. -/
theorem sourceMemory_hasDerivAt (q : XiZeroCopy) (branch : Bool) (v : ℝ) :
    HasDerivAt (sourceMemory q branch)
      (-timeOnset (2*physicalRate q branch) v-sourceMemory q branch v) v := by
  obtain ⟨B,hB,hb⟩ := memorySlope_bound q branch
  let C := B*Real.exp (-decayExponent q*(v-1))
  have hn : Ioo (v-1) (v+1) ∈ 𝓝 v := Ioo_mem_nhds (by linarith) (by linarith)
  have ht := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0:ℝ)))
    (F := fun w h => momentDensity q branch false w h)
    (F' := fun w h => memorySlope q branch w h)
    (bound := fun h => C*Real.exp ((1-decayExponent q)*h)) hn
    (Filter.Eventually.of_forall (fun w => (momentDensity_continuous q branch false w).aestronglyMeasurable))
    (momentDensity_integrable q branch false v)
    (memorySlope_continuous q branch v).aestronglyMeasurable
    (by
      filter_upwards with h
      intro w hw
      apply (hb w h).trans
      dsimp only [C]
      have hd : 0 ≤ decayExponent q := by linarith [decay_gt_one q]
      have he := mul_le_mul_of_nonpos_left hw.1.le (neg_nonpos.mpr hd)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hB) (Real.exp_pos _).le)
    ((integrableOn_exp_mul_Ioi (sub_neg.mpr (decay_gt_one q)) 0).const_mul C)
    (by
      filter_upwards with h
      intro w hw
      simpa only [momentDensity,memorySlope,Bool.false_eq_true,↓reduceIte,add_comm] using!
        (HasDerivAt.comp_const_add h w (timeOnset_hasDerivAt (2*physicalRate q branch) (h+w))).mul_const
          (Real.exp h:ℂ))).2
  simpa only [memorySlope_integral,sourceMemory,momentDensity,Bool.false_eq_true,↓reduceIte] using! ht

/-- A fixed original-time translation retains the exact source work on its finite interval. -/
theorem sourceMemory_physical_translation (q : XiZeroCopy) (branch : Bool) (v T : ℝ) :
    (Real.exp T:ℂ)*sourceMemory q branch (v+T)-sourceMemory q branch v=
      -(∫ h in (0:ℝ)..T, timeOnset (2*physicalRate q branch) (v+h)*(Real.exp h:ℂ)) := by
  have hd (h : ℝ) (_ : h ∈ uIcc (0:ℝ) T) :
      HasDerivAt (fun t => sourceMemory q branch (v+t)*(Real.exp t:ℂ))
        (-momentDensity q branch false v h) h := by
    have hg := HasDerivAt.comp_const_add v h (sourceMemory_hasDerivAt q branch (v+h))
    convert! hg.mul (Real.hasDerivAt_exp h).ofReal_comp using 1
    simp only [momentDensity,Bool.false_eq_true,↓reduceIte]
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((momentDensity_continuous q branch false v).neg.intervalIntegrable _ _)
  rw [intervalIntegral.integral_neg] at hi
  simpa only [momentDensity,Bool.false_eq_true,↓reduceIte,add_zero,Real.exp_zero,Complex.ofReal_one,
    mul_one,mul_comm,one_mul] using hi.symm

/-- The actual direct arm radial derivative retains its finite physical-time source work. -/
theorem radialArm_derivative_physical_translation (q : XiZeroCopy) (branch : Bool)
    (v T X k : ℝ) :
    Tendsto (fun x => (Real.exp T:ℂ)*deriv (radialArm q branch (v+T) X k) (tortoiseRadius x)-
      deriv (radialArm q branch v X k) (tortoiseRadius x)) atBot
      (𝓝 ((D4BMHorizon.scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]/2)*
        (∫ h in (0:ℝ)..T, timeOnset (2*physicalRate q branch) (v+h)*(Real.exp h:ℂ)))) := by
  have ht := ((radialArm_derivative_ingoing q branch (v+T) X k).const_mul (Real.exp T:ℂ)).sub
    (radialArm_derivative_ingoing q branch v X k)
  have he : (Real.exp T:ℂ)*
      (-(D4BMHorizon.scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]/2)*sourceMemory q branch (v+T))-
      (-(D4BMHorizon.scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]/2)*sourceMemory q branch v)=
      (D4BMHorizon.scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]/2)*
        (∫ h in (0:ℝ)..T, timeOnset (2*physicalRate q branch) (v+h)*(Real.exp h:ℂ)) := by
    calc
      _ = -(D4BMHorizon.scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]/2)*
        ((Real.exp T:ℂ)*sourceMemory q branch (v+T)-sourceMemory q branch v) := by ring
      _ = _ := by rw [sourceMemory_physical_translation]; ring
  rw [he] at ht
  exact ht


private theorem cap_normal_scaled_limit (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ)
    (v X k : ℝ) :
    Tendsto (fun x => deriv (fun y => capBoundaryField q branch amplitude (v-y) y X k) x/(capScale x:ℂ))
      atBot (𝓝 (liftTraceCoefficient q branch amplitude*
        D4BMHorizon.scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]*sourceMemory q branch v)) := by
  have ht := ((boundaryArm_scaled_normal_ingoing q branch v X k).sub
    (boundaryArm_image_div_scale_ingoing q branch v X k)).const_mul (-liftTraceCoefficient q branch amplitude)
  have he (x : ℝ) :
      deriv (fun y => capBoundaryField q branch amplitude (v-y) y X k) x/(capScale x:ℂ)=
        -liftTraceCoefficient q branch amplitude*
          (deriv (fun y => boundaryArm q branch v y X k) x/(capScale x:ℂ)-
            deriv (fun y => boundaryArm q branch (v-2*y) (-y) X k) x/(capScale x:ℂ)) := by
    rw [(capBoundaryField_ingoing_normal_hasDerivAt q branch amplitude v x X k).deriv,
      (boundaryArm_normal_hasDerivAt q branch v x X k).deriv,
      (boundaryArm_image_hasDerivAt q branch v x X k).deriv]
    ring
  simpa only [he,sub_zero,neg_mul,mul_neg,neg_neg,mul_assoc] using ht

/-- The unchanged full cap, in physical radius and original ingoing time. -/
def radialCap (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ) (v X k r : ℝ) : ℂ :=
  capBoundaryField q branch amplitude (v-D4BMIngoingCoordinates.tortoise r)
    (D4BMIngoingCoordinates.tortoise r) X k

private theorem radialCap_derivative (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ)
    (v X k x : ℝ) (hx : x < 0) :
    deriv (radialCap q branch amplitude v X k) (tortoiseRadius x)=
      (deriv (fun y => capBoundaryField q branch amplitude (v-y) y X k) x/(capScale x:ℂ))/
        ((tortoiseRadius x:ℂ)^2*(2-(capScale x:ℂ))) := by
  have hr := tortoiseRadius_exterior x hx
  have hd := capBoundaryField_ingoing_normal_hasDerivAt q branch amplitude v
    (D4BMIngoingCoordinates.tortoise (tortoiseRadius x)) X k
  have ht := hd.scomp (tortoiseRadius x) (D4BMIngoingCoordinates.tortoise_hasDerivAt _ hr)
  rw [tortoise_original_inverse x hx] at hd ht
  have he : (tortoiseRadius x:ℂ)^2-1=
      (tortoiseRadius x:ℂ)^2*(capScale x:ℂ)*(2-(capScale x:ℂ)) := by
    exact_mod_cast (radius_scale x hx).2
  change deriv (fun r => capBoundaryField q branch amplitude (v-D4BMIngoingCoordinates.tortoise r)
    (D4BMIngoingCoordinates.tortoise r) X k) (tortoiseRadius x)=_
  simp only [Function.comp_def] at ht
  rw [ht.deriv,hd.deriv]
  simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_sub,Complex.ofReal_pow,Complex.ofReal_one]
  rw [he]
  simp only [div_eq_mul_inv,mul_inv_rev,Complex.ofReal_ofNat]
  ring

/-- Both actual cap arms yield the original source-memory radial trace. -/
theorem radialCap_derivative_ingoing (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ) (v X k : ℝ) :
    Tendsto (fun x => deriv (radialCap q branch amplitude v X k) (tortoiseRadius x)) atBot
      (𝓝 (liftTraceCoefficient q branch amplitude*
        (D4BMHorizon.scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]/2)*sourceMemory q branch v)) := by
  have hr : Tendsto (fun x => (tortoiseRadius x:ℂ)) atBot (𝓝 (1:ℂ)) := by
    simpa only [Complex.ofReal_one,Function.comp_def] using!
      (Complex.continuous_ofReal.tendsto (1:ℝ)).comp radius_limit
  have hc : Tendsto (fun x => (capScale x:ℂ)) atBot (𝓝 (0:ℂ)) := by
    simpa only [Complex.ofReal_zero,Function.comp_def] using!
      (Complex.continuous_ofReal.tendsto (0:ℝ)).comp scale_limit
  have ht := (cap_normal_scaled_limit q branch amplitude v X k).div
    ((hr.pow 2).mul ((tendsto_const_nhds (x := (2:ℂ))).sub hc)) (by norm_num : (1:ℂ)^2*(2-0) ≠ 0)
  have hl : Tendsto (fun x =>
      (deriv (fun y => capBoundaryField q branch amplitude (v-y) y X k) x/(capScale x:ℂ))/
        ((tortoiseRadius x:ℂ)^2*(2-(capScale x:ℂ)))) atBot
      (𝓝 (liftTraceCoefficient q branch amplitude*
        (D4BMHorizon.scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]/2)*sourceMemory q branch v)) := by
    convert! ht using 1
    ring
  apply hl.congr'
  filter_upwards [eventually_lt_atBot (0:ℝ)] with x hx
  exact (radialCap_derivative q branch amplitude v X k x hx).symm

/-- The full two-arm cap retains the finite source work at the same physical clock. -/
theorem radialCap_derivative_physical_translation (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ)
    (v T X k : ℝ) :
    Tendsto (fun x => (Real.exp T:ℂ)*deriv (radialCap q branch amplitude (v+T) X k) (tortoiseRadius x)-
      deriv (radialCap q branch amplitude v X k) (tortoiseRadius x)) atBot
      (𝓝 (-liftTraceCoefficient q branch amplitude*
        (D4BMHorizon.scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]/2)*
        (∫ h in (0:ℝ)..T, timeOnset (2*physicalRate q branch) (v+h)*(Real.exp h:ℂ)))) := by
  have ht := ((radialCap_derivative_ingoing q branch amplitude (v+T) X k).const_mul (Real.exp T:ℂ)).sub
    (radialCap_derivative_ingoing q branch amplitude v X k)
  have he : (Real.exp T:ℂ)*
      (liftTraceCoefficient q branch amplitude*
        (D4BMHorizon.scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]/2)*sourceMemory q branch (v+T))-
      (liftTraceCoefficient q branch amplitude*
        (D4BMHorizon.scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]/2)*sourceMemory q branch v)=
      -liftTraceCoefficient q branch amplitude*
        (D4BMHorizon.scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]/2)*
        (∫ h in (0:ℝ)..T, timeOnset (2*physicalRate q branch) (v+h)*(Real.exp h:ℂ)) := by
    calc
      _ = liftTraceCoefficient q branch amplitude*
          (D4BMHorizon.scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]/2)*
          ((Real.exp T:ℂ)*sourceMemory q branch (v+T)-sourceMemory q branch v) := by ring
      _ = _ := by rw [sourceMemory_physical_translation]; ring
  rw [he] at ht
  exact ht

private theorem memory_rate_re_neg (q : XiZeroCopy) (branch : Bool) :
    (2*physicalRate q branch+1).re < 0 := by
  have hs := currentRate_re_lt q branch
  change (2*physicalRate q branch).re < -2 at hs
  simp only [Complex.add_re,Complex.one_re]
  linarith

/-- Late source memory is an evaluation at the original source rate, with no new clock. -/
theorem sourceMemory_late (q : XiZeroCopy) (branch : Bool) (v : Ici (1:ℝ)) :
    sourceMemory q branch v = -Complex.exp ((2*physicalRate q branch)*(v.val:ℂ))/(2*physicalRate q branch+1) := by
  have he (h : ℝ) (hh : h ∈ Ioi (0:ℝ)) :
      timeOnset (2*physicalRate q branch) (v.val+h)*(Real.exp h:ℂ)=
        Complex.exp ((2*physicalRate q branch)*(v.val:ℂ))*
          Complex.exp ((2*physicalRate q branch+1)*(h:ℂ)) := by
    rw [timeOnset,Real.smoothTransition.one_of_one_le (v.property.trans (le_add_of_nonneg_right hh.le))]
    simp only [Complex.ofReal_one,one_mul,Complex.ofReal_exp,← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [sourceMemory,setIntegral_congr_fun measurableSet_Ioi he,integral_const_mul,
    integral_exp_mul_complex_Ioi (memory_rate_re_neg q branch) 0]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero]
  ring

/-- A positive physical-clock step has a nontrivial multiplier on the late boundary memory. -/
theorem late_memory_multiplier_ne_one (q : XiZeroCopy) (branch : Bool) (T : Ioi (0:ℝ)) :
    Complex.exp ((2*physicalRate q branch+1)*(T.val:ℂ)) ≠ 1 := by
  intro he
  have hn := congrArg norm he
  rw [Complex.norm_exp,norm_one] at hn
  have hr : ((2*physicalRate q branch+1)*(T.val:ℂ)).re < 0 := by
    simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
      using mul_neg_of_neg_of_pos (memory_rate_re_neg q branch) T.property
  have hh := Real.exp_lt_one_iff.mpr hr
  linarith

/-- The admitted memory itself cannot be fixed by a positive step of its physical transport. -/
theorem sourceMemory_physical_step_ne (q : XiZeroCopy) (branch : Bool)
    (v : Ici (1:ℝ)) (T : Ioi (0:ℝ)) :
    (Real.exp T.val:ℂ)*sourceMemory q branch (v.val+T.val) ≠ sourceMemory q branch v := by
  have hw : 2*physicalRate q branch+1 ≠ 0 := by
    intro he
    have hh := memory_rate_re_neg q branch
    rw [he,Complex.zero_re] at hh
    exact lt_irrefl 0 hh
  let vT : Ici (1:ℝ) := ⟨v.val+T.val,by
    change (1:ℝ) ≤ v.val+T.val
    linarith [show (1:ℝ) ≤ v.val from v.property,show (0:ℝ) < T.val from T.property]⟩
  have hm : sourceMemory q branch v ≠ 0 := by
    rw [sourceMemory_late]
    exact div_ne_zero (neg_ne_zero.mpr (Complex.exp_ne_zero _)) hw
  have ht : (Real.exp T.val:ℂ)*sourceMemory q branch (v.val+T.val)=
      Complex.exp ((2*physicalRate q branch+1)*(T.val:ℂ))*sourceMemory q branch v := by
    rw [show sourceMemory q branch (v.val+T.val)=sourceMemory q branch vT from rfl,
      sourceMemory_late,sourceMemory_late]
    dsimp only [vT]
    rw [Complex.ofReal_exp]
    have he : Complex.exp (T.val:ℂ)*Complex.exp ((2*physicalRate q branch)*((v.val+T.val:ℝ):ℂ))=
        Complex.exp ((2*physicalRate q branch+1)*(T.val:ℂ))*
          Complex.exp ((2*physicalRate q branch)*(v.val:ℂ)) := by
      rw [← Complex.exp_add,← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc
      _ = -(Complex.exp (T.val:ℂ)*Complex.exp ((2*physicalRate q branch)*((v.val+T.val:ℝ):ℂ)))/
          (2*physicalRate q branch+1) := by ring
      _ = _ := by rw [he]; ring
  intro he
  rw [ht] at he
  have hz : (Complex.exp ((2*physicalRate q branch+1)*(T.val:ℂ))-1)*sourceMemory q branch v=0 := by
    linear_combination he
  exact mul_ne_zero (sub_ne_zero.mpr (late_memory_multiplier_ne_one q branch T)) hm hz

/-- The finite physical-clock source work is nonzero throughout the unchanged late region. -/
theorem late_physical_source_work_ne_zero (q : XiZeroCopy) (branch : Bool)
    (v : Ici (1:ℝ)) (T : Ioi (0:ℝ)) :
    (∫ h in (0:ℝ)..T.val, timeOnset (2*physicalRate q branch) (v.val+h)*(Real.exp h:ℂ)) ≠ 0 := by
  intro hz
  have ht := sourceMemory_physical_translation q branch v.val T.val
  rw [hz,neg_zero] at ht
  exact sourceMemory_physical_step_ne q branch v T (sub_eq_zero.mp ht)

/-- Exact pointwise classification of the full cap's finite-clock radial source work.
This concerns the original cap datum before the independent left-QNM contraction. -/
theorem radialCap_clock_work_zero_iff (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ)
    (v : Ici (1:ℝ)) (T : Ioi (0:ℝ)) (X k : ℝ) :
    (-liftTraceCoefficient q branch amplitude*
      (D4BMHorizon.scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]/2)*
      (∫ h in (0:ℝ)..T.val, timeOnset (2*physicalRate q branch) (v.val+h)*(Real.exp h:ℂ))=0) ↔
    liftTraceCoefficient q branch amplitude*D4BMHorizon.scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]=0 := by
  rw [mul_eq_zero]
  simp only [late_physical_source_work_ne_zero q branch v T,or_false]
  rw [← mul_div_assoc,div_eq_zero_iff]
  norm_num only [OfNat.ofNat_ne_zero,or_false,neg_mul,neg_eq_zero]

end
end RHTower.D4BMCapRadialMemory
