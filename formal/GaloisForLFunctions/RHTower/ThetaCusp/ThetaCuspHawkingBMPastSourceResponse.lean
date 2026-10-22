import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFutureHorizonCap

/-!
The original full reduced advanced response has an admitted past-horizon datum.
An exact source-time translation and Fubini identity express the established
Bochner response in source ingoing coordinates. A target-uniform full theta
majorant admits both characteristic arms and their outgoing horizon limit.
This proves a field-value boundary datum, not an advanced wave equation,
a differentiated physical-action limit, or radiative extinction.
-/

open Set Filter Topology MeasureTheory
namespace RHTower.D4BMPastSourceResponse
open D4BMNativeCircle D4BMCausalKernel D4BMJointSource D4BMModularCore
open D4BMFullSourceAdvanced D4BMFutureHorizon
noncomputable section
set_option autoImplicit false

private theorem sinh_abs_bound (x : ℝ) : |Real.sinh x| ≤ Real.cosh x := by
  have hp := Real.exp_pos x
  have hm := Real.exp_pos (-x)
  rw [← Real.cosh_add_sinh] at hp
  rw [← Real.cosh_sub_sinh] at hm
  exact abs_le.mpr ⟨by linarith,by linarith⟩

private theorem sinh_product_bound (x y : ℝ) :
    |Real.sinh x*Real.sinh y| ≤ Real.cosh x*Real.cosh y := by
  rw [abs_mul]
  exact mul_le_mul (sinh_abs_bound x) (sinh_abs_bound y) (abs_nonneg _) (Real.cosh_pos x).le

private theorem exp_bound (x : ℝ) : Real.exp x ≤ 2*Real.cosh x := by
  rw [Real.cosh_eq]
  linarith [Real.exp_pos (-x)]

private theorem shifted_cosh_bound (a v y : ℝ) (ha : 0 ≤ a) :
    Real.cosh (a-y-v) ≤ 2*Real.exp (a+|v|)*Real.cosh y := by
  have hp : Real.exp (a-v) ≤ Real.exp (a+|v|) :=
    Real.exp_le_exp.mpr (by linarith [neg_le_abs v])
  have hm : Real.exp (-a+v) ≤ Real.exp (a+|v|) :=
    Real.exp_le_exp.mpr (by linarith [le_abs_self v])
  have h1 := mul_le_mul hp (exp_bound (-y)) (Real.exp_pos (-y)).le (Real.exp_pos (a+|v|)).le
  have h2 := mul_le_mul hm (exp_bound y) (Real.exp_pos y).le (Real.exp_pos (a+|v|)).le
  rw [Real.cosh_neg] at h1
  have e1 : Real.exp (a-y-v)=Real.exp (a-v)*Real.exp (-y) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have e2 : Real.exp (-(a-y-v))=Real.exp (-a+v)*Real.exp y := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Real.cosh_eq,e1,e2]
  linarith

private theorem invariant_bound (a v x y : ℝ) (ha : 0 ≤ a) :
    invariant (a-y-v-x) x y ≤ 5*Real.exp (a+|v|) ∧
      invariant (a-y-v-x) x (-y) ≤ 5*Real.exp (a+|v|) := by
  let A := a-y-v
  have hcosh : Real.cosh (A-x) ≤ 2*Real.cosh A*Real.cosh x := by
    rw [Real.cosh_sub]
    linarith [sinh_product_bound A x,neg_le_abs (Real.sinh A*Real.sinh x)]
  have hpair := sinh_product_bound x y
  have ht := shifted_cosh_bound a v y ha
  have hpos : 0 < Real.cosh x*Real.cosh y := mul_pos (Real.cosh_pos x) (Real.cosh_pos y)
  have hquot : 2*Real.cosh A/Real.cosh y ≤ 4*Real.exp (a+|v|) := by
    rw [div_le_iff₀ (Real.cosh_pos y)]
    dsimp [A]
    linarith
  have he : 1 ≤ Real.exp (a+|v|) := Real.one_le_exp_iff.mpr (add_nonneg ha (abs_nonneg v))
  have hbase : (2*Real.cosh A*Real.cosh x+Real.cosh x*Real.cosh y)/
      (Real.cosh x*Real.cosh y) ≤ 5*Real.exp (a+|v|) := by
    have hform : (2*Real.cosh A*Real.cosh x+Real.cosh x*Real.cosh y)/
        (Real.cosh x*Real.cosh y)=2*Real.cosh A/Real.cosh y+1 := by
      field_simp [(Real.cosh_pos x).ne',(Real.cosh_pos y).ne']
    rw [hform]
    linarith
  constructor
  · apply le_trans (b := (2*Real.cosh A*Real.cosh x+Real.cosh x*Real.cosh y)/
      (Real.cosh x*Real.cosh y)) ?_ hbase
    apply div_le_div_of_nonneg_right ?_ hpos.le
    change Real.cosh (A-x)+Real.sinh x*Real.sinh y ≤ _
    linarith [le_abs_self (Real.sinh x*Real.sinh y)]
  · unfold invariant
    rw [Real.cosh_neg,Real.sinh_neg]
    apply le_trans (b := (2*Real.cosh A*Real.cosh x+Real.cosh x*Real.cosh y)/
      (Real.cosh x*Real.cosh y)) ?_ hbase
    apply div_le_div_of_nonneg_right ?_ hpos.le
    change Real.cosh (A-x)+Real.sinh x*(-Real.sinh y) ≤ _
    linarith [neg_le_abs (Real.sinh x*Real.sinh y)]

private theorem radius_bound (a v z : ℝ) (ha : 0 ≤ a)
    (hz : z ≤ 5*Real.exp (a+|v|)) :
    Real.arcosh (max 1 z) ≤ a+|v|+Real.log 10 := by
  have he : 1 ≤ Real.exp (a+|v|) := Real.one_le_exp_iff.mpr (add_nonneg ha (abs_nonneg v))
  have hm : max 1 z ≤ 5*Real.exp (a+|v|) := max_le (by linarith) hz
  have hp : 0 ≤ a+|v|+Real.log 10 := by positivity
  have hc : 5*Real.exp (a+|v|) ≤ Real.cosh (a+|v|+Real.log 10) := by
    rw [Real.cosh_eq,Real.exp_add (a+|v|) (Real.log 10),
      Real.exp_log (by norm_num : (0:ℝ)<10)]
    linarith [Real.exp_pos (-(a+|v|+Real.log 10))]
  have hh := Real.cosh_le_cosh.mp ((Real.cosh_arcosh (le_max_left 1 z)).trans_le (hm.trans hc))
  simpa only [abs_of_nonneg (Real.arcosh_nonneg (le_max_left 1 z)),abs_of_nonneg hp] using hh

/-- Full theta growth in source ingoing time, uniform in both radial arguments. -/
theorem null_kernel_bound (q : XiZeroCopy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a v x y X k : ℝ, 0 ≤ a →
      ‖nativeDirichletCausalKernel q (a-y-v-x) x y X k‖ ≤
        C*Real.exp (sourceGrowthExponent q*(a+|v|+|k|)) := by
  obtain ⟨C,hC,hb⟩ := mean_global_growth q
  have ha0 : 0 ≤ sourceGrowthExponent q := (by norm_num : (0:ℝ)≤1).trans (sourceGrowthExponent_bounds q).1
  refine ⟨C*Real.exp (sourceGrowthExponent q*Real.log 10),by positivity,fun a v x y X k ha => ?_⟩
  let D := C*Real.exp (sourceGrowthExponent q*(a+|v|+Real.log 10+|k|))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have cone (Y : ℝ) (hY : invariant (a-y-v-x) x Y ≤ 5*Real.exp (a+|v|)) :
      ‖if |x-Y| ≤ a-y-v-x then nativeRiemannKernel q (a-y-v-x) x Y X k else 0‖ ≤ D := by
    split_ifs with hs
    · have hz := invariant_causal ⟨a-y-v-x,x,Y,hs⟩
      have hr := radius_bound a v (invariant (a-y-v-x) x Y) ha hY
      rw [max_eq_right hz] at hr
      exact (hb _ X k (Real.arcosh_nonneg hz)).trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (by linarith) ha0)) hC)
    · simpa only [norm_zero] using hD
  have h0 := cone y (invariant_bound a v x y ha).1
  have h1 := cone (-y) (invariant_bound a v x y ha).2
  simp only [sub_neg_eq_add] at h1
  have he : D=C*Real.exp (sourceGrowthExponent q*Real.log 10)*
      Real.exp (sourceGrowthExponent q*(a+|v|+|k|)) := by
    dsimp [D]
    rw [mul_assoc,← Real.exp_add]
    congr 2
    ring
  rw [← he]
  unfold nativeDirichletCausalKernel
  rw [norm_div,Complex.norm_ofNat]
  exact (div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num)).trans (by linarith)

private theorem kernel_measurable (q : XiZeroCopy) (x X k : ℝ) :
    Measurable (fun p : ℝ × ℝ => nativeDirichletCausalKernel q p.1 x p.2 X k) := by
  classical
  have cone (b : Bool) : Measurable (fun p : ℝ × ℝ =>
      if |x-(if b then -p.2 else p.2)| ≤ p.1 then
        nativeRiemannKernel q p.1 x (if b then -p.2 else p.2) X k else 0) := by
    let Y : ℝ × ℝ → ℝ := fun p => if b then -p.2 else p.2
    have hY : Continuous Y := by cases b <;> simp only [Y,Bool.false_eq_true,↓reduceIte] <;> fun_prop
    have hi : Continuous (fun p : ℝ × ℝ => invariant p.1 x (Y p)) := by
      unfold invariant
      exact (Real.continuous_cosh.comp continuous_fst |>.add
        ((Real.continuous_sinh.comp hY).const_mul (Real.sinh x))).div
        ((Real.continuous_cosh.comp hY).const_mul (Real.cosh x))
        (fun p => mul_ne_zero (Real.cosh_pos x).ne' (Real.cosh_pos (Y p)).ne')
    have hr : Continuous (fun p : ℝ × ℝ => Real.arcosh (max 1 (invariant p.1 x (Y p)))) :=
      Real.continuousOn_arcosh.comp_continuous (continuous_const.max hi)
        (fun p => le_max_left 1 (invariant p.1 x (Y p)))
    have hm := ((mean_radial_smooth q X k).continuous.comp hr).measurable
    have hs : MeasurableSet {p : ℝ × ℝ | |x-Y p| ≤ p.1} :=
      (isClosed_le (continuous_const.sub hY |>.abs) continuous_fst).measurableSet
    have ht : Measurable (fun p : ℝ × ℝ => if |x-Y p| ≤ p.1 then
        mean q (Real.arcosh (max 1 (invariant p.1 x (Y p)))) X k else 0) :=
      Measurable.ite hs hm measurable_const
    convert ht using 1
    funext p
    change (if |x-Y p| ≤ p.1 then nativeRiemannKernel q p.1 x (Y p) X k else 0)=_
    split_ifs with hc
    · simp only [nativeRiemannKernel,angularKernel,
        max_eq_right (invariant_causal ⟨p.1,x,Y p,hc⟩)]
    · rfl
  have h0 := cone false
  have h1 := cone true
  simpa only [Bool.false_eq_true,↓reduceIte,sub_neg_eq_add,nativeDirichletCausalKernel,
    Pi.sub_apply] using (h0.sub h1).div_const (2:ℂ)

/-- The original reduced source in its own ingoing time, at target outgoing time v. -/
def nullDensity (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v x X k : ℝ) (p : ℝ × ℝ) : ℂ :=
  nativeDirichletCausalKernel q (p.1-p.2-v-x) x p.2 X k*
    timeReducedCoefficient (physicalRate q branch) amp (p.1-p.2) p.2

private theorem nullDensity_measurable (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v x X k : ℝ) :
    Measurable (nullDensity q branch amp v x X k) := by
  have hK := (kernel_measurable q x X k).comp
    (show Continuous (fun p : ℝ × ℝ => (p.1-p.2-v-x,p.2)) by fun_prop).measurable
  have hS := (timeReducedCoefficient_joint_continuous (physicalRate q branch) amp).comp
    (show Continuous (fun p : ℝ × ℝ => (p.1-p.2,p.2)) by fun_prop)
  exact hK.mul hS.measurable

theorem nullDensity_bound (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a v x y X k : ℝ, 0 ≤ a → y < 0 →
      ‖nullDensity q branch amp v x X k (a,y)‖ ≤
        C*Real.exp (sourceGrowthExponent q*(|v|+|k|))*
          (Real.exp ((sourceGrowthExponent q-decayExponent q)*a)*Real.exp (2*y)) := by
  obtain ⟨C,hC,hK⟩ := null_kernel_bound q
  obtain ⟨B,hB,hS⟩ := timeReducedCoefficient_physical_bound q branch amp
    (decayExponent q) (decayExponent_bounds q).2
  refine ⟨C*B,mul_nonneg hC hB,fun a v x y X k ha hy => ?_⟩
  have h := mul_le_mul (hK a v x y X k ha) (hS (a-y) y hy)
    (norm_nonneg _) (by positivity : 0 ≤ C*Real.exp (sourceGrowthExponent q*(a+|v|+|k|)))
  rw [nullDensity,norm_mul]
  apply h.trans_eq
  have he : Real.exp (sourceGrowthExponent q*(a+|v|+|k|))*
      (Real.exp (-decayExponent q*(a-y))*Real.exp ((2-decayExponent q)*y))=
      Real.exp (sourceGrowthExponent q*(|v|+|k|))*
        (Real.exp ((sourceGrowthExponent q-decayExponent q)*a)*Real.exp (2*y)) := by
    simp only [← Real.exp_add]
    congr 1
    ring
  calc
    _ = C*B*(Real.exp (sourceGrowthExponent q*(a+|v|+|k|))*
        (Real.exp (-decayExponent q*(a-y))*Real.exp ((2-decayExponent q)*y))) := by ring
    _ = _ := by rw [he]; ring

private theorem majorant_integrable (q : XiZeroCopy) (D : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => D*(Real.exp ((sourceGrowthExponent q-decayExponent q)*p.1)*
      Real.exp (2*p.2))) (Ioi 0 ×ˢ Iio 0) := by
  have hh := integrableOn_exp_mul_Ioi (show sourceGrowthExponent q-decayExponent q < 0 from
    sub_neg.mpr (decayExponent_bounds q).1) 0
  have hy := (integrableOn_exp_mul_Iic (by norm_num : (0:ℝ)<2) 0).mono_set Iio_subset_Iic_self
  rw [IntegrableOn,Measure.volume_eq_prod,← Measure.prod_restrict]
  exact (hh.mul_prod hy).const_mul D

theorem nullDensity_integrable (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v x X k : ℝ) :
    IntegrableOn (nullDensity q branch amp v x X k) (Ioi 0 ×ˢ Iio 0) := by
  obtain ⟨C,hC,hb⟩ := nullDensity_bound q branch amp
  apply (majorant_integrable q (C*Real.exp (sourceGrowthExponent q*(|v|+|k|)))).mono'
    (nullDensity_measurable q branch amp v x X k).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Iio)] with p hp
  exact hb p.1 v x p.2 X k hp.1.le hp.2

private theorem kernel_negative (q : XiZeroCopy) (h x y X k : ℝ) (hh : h < 0) :
    nativeDirichletCausalKernel q h x y X k=0 := by
  have h0 : ¬ |x-y| ≤ h := by linarith [abs_nonneg (x-y)]
  have h1 : ¬ |x+y| ≤ h := by linarith [abs_nonneg (x+y)]
  simp only [nativeDirichletCausalKernel,if_neg h0,if_neg h1,sub_self,zero_div]

private theorem sourceCoordinatesIntegral (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (τ x y X k : ℝ) :
    (∫ h in Ioi (0:ℝ), nativeDirichletCausalKernel q h x y X k*
      timeReducedCoefficient (physicalRate q branch) amp (τ+h) y)=
    ∫ a in Ioi (0:ℝ), nativeDirichletCausalKernel q (a-y-τ) x y X k*
      timeReducedCoefficient (physicalRate q branch) amp (a-y) y := by
  let F := fun h : ℝ => nativeDirichletCausalKernel q h x y X k*
    timeReducedCoefficient (physicalRate q branch) amp (τ+h) y
  let N := fun a : ℝ => nativeDirichletCausalKernel q (a-y-τ) x y X k*
    timeReducedCoefficient (physicalRate q branch) amp (a-y) y
  have hF : (∫ h in Ioi (0:ℝ), F h)=∫ h : ℝ, F h := by
    rw [← integral_Ici_eq_integral_Ioi]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro h hh
    simp only [mem_Ici,not_le] at hh
    simp only [F,kernel_negative q h x y X k hh,zero_mul]
  have hN : (∫ a in Ioi (0:ℝ), N a)=∫ a : ℝ, N a := by
    rw [← integral_Ici_eq_integral_Ioi]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro a ha
    simp only [mem_Ici,not_le] at ha
    have hz := timeReducedCoefficient_zero_before_onset (physicalRate q branch) amp (a-y) y
      (by linarith : a-y+y < 0)
    simp only [N,hz,mul_zero]
  have he : (fun h : ℝ => N (h+(τ+y)))=F := by
    funext h
    dsimp [N,F]
    rw [show h+(τ+y)-y-τ=h by ring,show h+(τ+y)-y=τ+h by ring]
  change (∫ h in Ioi (0:ℝ),F h)=∫ a in Ioi (0:ℝ),N a
  rw [hF,hN]
  simpa only [he] using integral_add_right_eq_self N (τ+y)

private theorem set_fubini_y (f : ℝ × ℝ → ℂ)
    (hf : IntegrableOn f (Ioi 0 ×ˢ Iio 0)) :
    (∫ p in Ioi 0 ×ˢ Iio 0,f p)=∫ y in Iio (0:ℝ),∫ a in Ioi (0:ℝ),f (a,y) := by
  rw [IntegrableOn,Measure.volume_eq_prod,← Measure.prod_restrict] at hf
  rw [Measure.volume_eq_prod,← Measure.prod_restrict]
  exact integral_prod_symm _ hf

/-- This is an exact change of variables in the established original Bochner response. -/
theorem response_null_coordinates (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v x X k : ℝ) :
    D4BMFullSourceAdvanced.response q branch amp (v+x) x X k=
      ∫ p in Ioi 0 ×ˢ Iio 0,nullDensity q branch amp v x X k p := by
  rw [D4BMFullSourceAdvanced.response,set_fubini_y _ (density_integrable q branch amp (v+x) x X k),
    set_fubini_y _ (nullDensity_integrable q branch amp v x X k)]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [density]
  rw [sourceCoordinatesIntegral]
  apply integral_congr_ae
  filter_upwards [] with a
  rw [show a-y-(v+x)=a-y-v-x by ring]
  rfl

private theorem kernel_symm (q : XiZeroCopy) (h x y X k : ℝ) :
    nativeDirichletCausalKernel q h x y X k=nativeDirichletCausalKernel q h y x X k := by
  have h0 : invariant h x y=invariant h y x := by simp only [invariant,mul_comm]
  have h1 : invariant h x (-y)=invariant h y (-x) := by
    simp only [invariant,Real.cosh_neg,Real.sinh_neg]
    ring
  simp only [nativeDirichletCausalKernel,nativeRiemannKernel,h0,h1,abs_sub_comm,add_comm]

/-- The source-determined past-horizon integrand with both original characteristic supports. -/
def pastDensity (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v X k : ℝ) (p : ℝ × ℝ) : ℂ :=
  ((halfKernel q v p.2 (p.1-p.2) X k-halfKernel q v (-p.2) (p.1-p.2) X k)/2)*
    timeReducedCoefficient (physicalRate q branch) amp (p.1-p.2) p.2

theorem nullDensity_past_limit (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (v X k : ℝ) (p : ℝ × ℝ) :
    Tendsto (fun x => nullDensity q branch amp v x X k p) atBot
      (𝓝 (pastDensity q branch amp v X k p)) := by
  have h := (native_kernel_source_horizon q v p.2 (p.1-p.2) X k).mul_const
    (timeReducedCoefficient (physicalRate q branch) amp (p.1-p.2) p.2)
  apply h.congr'
  exact Eventually.of_forall (fun x => by
    dsimp [nullDensity]
    rw [kernel_symm q (p.1-p.2-v-x) p.2 x X k])

/-- The limiting full source density obeys the same admitted source-time majorant. -/
theorem pastDensity_bound (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a v y X k : ℝ, 0 ≤ a → y < 0 →
      ‖pastDensity q branch amp v X k (a,y)‖ ≤
        C*Real.exp (sourceGrowthExponent q*(|v|+|k|))*
          (Real.exp ((sourceGrowthExponent q-decayExponent q)*a)*Real.exp (2*y)) := by
  obtain ⟨C,hC,hb⟩ := nullDensity_bound q branch amp
  exact ⟨C,hC,fun a v y X k ha hy =>
    le_of_tendsto (nullDensity_past_limit q branch amp v X k (a,y)).norm
      (Eventually.of_forall (fun x => hb a v x y X k ha hy))⟩

/-- Absolute admission of the source-derived past datum, including both characteristic arms. -/
theorem pastDensity_integrable (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v X k : ℝ) :
    IntegrableOn (pastDensity q branch amp v X k) (Ioi 0 ×ˢ Iio 0) := by
  obtain ⟨C,hC,hb⟩ := pastDensity_bound q branch amp
  have hm : AEStronglyMeasurable (pastDensity q branch amp v X k)
      (volume.restrict (Ioi 0 ×ˢ Iio 0)) :=
    aestronglyMeasurable_of_tendsto_ae atBot
      (fun x => (nullDensity_measurable q branch amp v x X k).aestronglyMeasurable.restrict)
      (Eventually.of_forall (fun p => nullDensity_past_limit q branch amp v X k p))
  apply (majorant_integrable q (C*Real.exp (sourceGrowthExponent q*(|v|+|k|)))).mono' hm
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Iio)] with p hp
  exact hb p.1 v p.2 X k hp.1.le hp.2

/-- Actual source integral of the past datum; no principal theta channel is discarded. -/
def pastResponse (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v X k : ℝ) : ℂ :=
  ∫ p in Ioi 0 ×ˢ Iio 0,pastDensity q branch amp v X k p

/-- The original full reduced advanced response has this derived outgoing past-horizon value. -/
theorem response_past_horizon (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v X k : ℝ) :
    Tendsto (fun x => D4BMFullSourceAdvanced.response q branch amp (v+x) x X k) atBot
      (𝓝 (pastResponse q branch amp v X k)) := by
  obtain ⟨C,hC,hb⟩ := nullDensity_bound q branch amp
  let D := C*Real.exp (sourceGrowthExponent q*(|v|+|k|))
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi 0 ×ˢ Iio 0))
    (fun p : ℝ × ℝ => D*(Real.exp ((sourceGrowthExponent q-decayExponent q)*p.1)*Real.exp (2*p.2)))
    (Eventually.of_forall (fun x => (nullDensity_measurable q branch amp v x X k).aestronglyMeasurable.restrict))
    (Eventually.of_forall (fun x => (ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Iio)).mono
      (fun p hp => hb p.1 v x p.2 X k hp.1.le hp.2)))
    (majorant_integrable q D)
    (Eventually.of_forall (fun p => nullDensity_past_limit q branch amp v X k p))
  simpa only [← response_null_coordinates,pastResponse] using h

end
end RHTower.D4BMPastSourceResponse
