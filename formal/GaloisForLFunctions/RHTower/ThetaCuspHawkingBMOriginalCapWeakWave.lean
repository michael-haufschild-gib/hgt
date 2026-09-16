import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullSourceWeakWave
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFutureHorizonCap

/-!
# Homogeneous weak wave equation of the original horizon cap

The original source-horizon limit commutes with compact joint target tests.
The exact source vertex escapes every such support; the original
Dirichlet horizon kernel therefore has zero bulk weak wave action.
A compact bound on the radial source parameter admits this limit without
pointwise angular-jet estimates.

Original onset decay admits source-time/target Fubini for the literal cap
field. Its two characteristic arms, original lift coefficient and fixed
onset remain unchanged. The cap is a homogeneous weak solution; subtracting
it from the actual future response preserves the complete reduced source.

This closes the cap's reduced bulk equation, not full metric/QNM matching.
-/

open MeasureTheory Set Filter Topology
namespace RHTower.D4BMOriginalCapWave
open D4BMNativeCircle D4BMCausalKernel D4BMModularCore D4BMHorizon D4BMJointSource
open D4BMGeneralTemporalTransposition D4BMFullSourceWeakWave D4BMFullSourceAdvanced D4BMFutureHorizon
open scoped ContDiff ENNReal
noncomputable section
set_option autoImplicit false

private def closedMean (q : XiZeroCopy) (p : ℝ × ℂ) : ℂ :=
  angularKernel q (max 1 p.1) p.2.re p.2.im

private theorem closedMean_continuous (q : XiZeroCopy) : Continuous (closedMean q) := by
  unfold closedMean angularKernel
  have hd := Real.continuousOn_arcosh.comp_continuous
    (continuous_const.max (continuous_fst : Continuous (Prod.fst : ℝ × ℂ → ℝ)))
    (fun p => le_max_left (1:ℝ) p.1)
  have hm : Continuous (fun v : ℝ × ℝ × ℝ => mean q v.1 v.2.1 v.2.2) :=
    (D4BMNativeResponse.nativeMean_joint_smooth q).continuous
  have hP : Continuous (fun p : ℝ × ℂ => (Real.arcosh (max 1 p.1),p.2.re,p.2.im)) :=
    hd.prodMk ((Complex.continuous_re.comp continuous_snd).prodMk
      (Complex.continuous_im.comp continuous_snd))
  have h : Continuous ((fun v : ℝ × ℝ × ℝ => mean q v.1 v.2.1 v.2.2) ∘
      (fun p : ℝ × ℂ => (Real.arcosh (max 1 p.1),p.2.re,p.2.im))) := Continuous.comp hm hP
  dsimp only [Function.comp_def] at h
  exact h

private def family (q : XiZeroCopy) (v : ℝ) (X : Target → ℝ) (a : ℝ × Target) : ℂ :=
  closedMean q ((Real.cosh (v-a.2.1.1)+(Real.sinh (v-a.2.1.1)-Real.sinh (X a.2))*a.1)/Real.cosh (X a.2),a.2.2)

private theorem family_continuous (q : XiZeroCopy) (v : ℝ) (X : Target → ℝ)
    (hX : Continuous X) : Continuous (family q v X) := by
  have hx : Continuous (fun a : ℝ × Target => X a.2) := hX.comp continuous_snd
  have hf : Continuous (fun a : ℝ × Target => Real.cosh (v-a.2.1.1)) := by fun_prop
  have hg : Continuous (fun a : ℝ × Target => Real.sinh (v-a.2.1.1)) := by fun_prop
  have hd : Continuous (fun a : ℝ × Target =>
      (Real.cosh (v-a.2.1.1)+(Real.sinh (v-a.2.1.1)-Real.sinh (X a.2))*a.1)/Real.cosh (X a.2)) :=
    (hf.add ((hg.sub (Real.continuous_sinh.comp hx)).mul continuous_fst)).div
      (Real.continuous_cosh.comp hx) (fun a => (Real.cosh_pos _).ne')
  exact (closedMean_continuous q).comp (hd.prodMk continuous_snd.snd)

private theorem invariant_formula (tau x v y : ℝ) :
    invariant (v-y-tau) x y =
      (Real.cosh (v-tau)+(Real.sinh (v-tau)-Real.sinh x)*radialUnit y)/Real.cosh x := by
  rw [show v-y-tau=v-tau-y by ring,invariant,Real.cosh_sub,radialUnit]
  field_simp [(Real.cosh_pos x).ne',(Real.cosh_pos y).ne']
  ring

private def cone (q : XiZeroCopy) (v y : ℝ) (X : Target → ℝ) (r : Target) : ℂ :=
  if |X r-y| ≤ v-y-r.1.1 then family q v X (radialUnit y,r) else 0

private def approximation (q : XiZeroCopy) (v y : ℝ) (r : Target) : ℂ :=
  nativeDirichletCausalKernel q (v-y-r.1.1) r.1.2 y r.2.re r.2.im

private theorem approximation_cones (q : XiZeroCopy) (v y : ℝ) (r : Target) :
    approximation q v y r =
      (cone q v y (fun r => r.1.2) r-cone q v y (fun r => -r.1.2) r)/2 := by
  have he (X : Target → ℝ) :
      (if |X r-y| ≤ v-y-r.1.1 then nativeRiemannKernel q (v-y-r.1.1) (X r) y r.2.re r.2.im else 0) =
      cone q v y X r := by
    by_cases h : |X r-y| ≤ v-y-r.1.1
    · simp only [cone,if_pos h,family]
      rw [← invariant_formula]
      simp only [closedMean,max_eq_right (invariant_causal ⟨_,_,_,h⟩)]
      rfl
    · simp only [cone,if_neg h]
  have hd := he (fun r => r.1.2)
  have hi := he (fun r => -r.1.2)
  have ha : |-r.1.2-y|=|r.1.2+y| := by rw [show -r.1.2-y=-(r.1.2+y) by ring,abs_neg]
  have hv : invariant (v-y-r.1.1) (-r.1.2) y=invariant (v-y-r.1.1) r.1.2 (-y) := by
    simp only [invariant,Real.sinh_neg,Real.cosh_neg]
    ring
  simp only [ha,nativeRiemannKernel,hv] at hi
  exact congrArg₂ (fun a b : ℂ => (a-b)/2) hd hi

private theorem cone_measurable (q : XiZeroCopy) (v y : ℝ) (X : Target → ℝ)
    (hX : Continuous X) : Measurable (cone q v y X) := by
  have h : Continuous (fun r : Target => family q v X (radialUnit y,r)) :=
    (family_continuous q v X hX).comp (show Continuous (fun r : Target => (radialUnit y,r)) by fun_prop)
  exact Measurable.ite ((isClosed_le (by fun_prop) (by fun_prop)).measurableSet)
    h.measurable measurable_const

private theorem approximation_measurable (q : XiZeroCopy) (v y : ℝ) :
    Measurable (approximation q v y) := by
  have he : approximation q v y = fun r =>
      (cone q v y (fun r => r.1.2) r-cone q v y (fun r => -r.1.2) r)/2 :=
    funext (approximation_cones q v y)
  rw [he]
  exact ((cone_measurable q v y _ continuous_fst.snd).sub
    (cone_measurable q v y _ continuous_fst.snd.neg)).div_const (2:ℂ)

private theorem approximation_bound (q : XiZeroCopy) (v : ℝ) (phi : Target → ℂ)
    (hc : HasCompactSupport phi) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ, y < 0 → ∀ r ∈ tsupport phi, ‖approximation q v y r‖ ≤ M := by
  have hK : IsCompact ((Icc (0:ℝ) 1) ×ˢ tsupport phi) := isCompact_Icc.prod hc
  have bound (X : Target → ℝ) (hX : Continuous X) :
      ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ, y < 0 → ∀ r ∈ tsupport phi, ‖cone q v y X r‖ ≤ M := by
    obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn (family_continuous q v X hX).continuousOn
    refine ⟨max C 0,le_max_right _ _,?_⟩
    intro y hy r hr
    unfold cone
    split_ifs
    · exact (hC _ ⟨⟨(radialUnit_bounds y hy).1.le,(radialUnit_bounds y hy).2.le⟩,hr⟩).trans (le_max_left _ _)
    · simpa only [norm_zero] using le_max_right C 0
  obtain ⟨C,hC,hD⟩ := bound (fun r => r.1.2) continuous_fst.snd
  obtain ⟨D,hD0,hI⟩ := bound (fun r => -r.1.2) continuous_fst.snd.neg
  refine ⟨(C+D)/2,by positivity,?_⟩
  intro y hy r hr
  rw [approximation_cones,norm_div]
  have h2 : ‖(2:ℂ)‖=(2:ℝ) := by norm_num
  rw [h2]
  exact div_le_div_of_nonneg_right ((norm_sub_le _ _).trans (add_le_add (hD y hy r hr) (hI y hy r hr))) (by norm_num)

/-- The original direct-minus-image source-horizon kernel, including its half-factor. -/
def horizonKernel (q : XiZeroCopy) (v : ℝ) (r : Target) : ℂ :=
  (halfKernel q r.1.1 r.1.2 v r.2.re r.2.im-halfKernel q r.1.1 (-r.1.2) v r.2.re r.2.im)/2

private theorem approximation_tendsto (q : XiZeroCopy) (v : ℝ) (r : Target) :
    Tendsto (fun y => approximation q v y r) atBot (𝓝 (horizonKernel q v r)) := by
  have h := native_kernel_source_horizon q r.1.1 r.1.2 v r.2.re r.2.im
  have he : (fun y => approximation q v y r) =
      fun y => nativeDirichletCausalKernel q (v-r.1.1-y) r.1.2 y r.2.re r.2.im := by
    funext y
    simp only [approximation,show v-y-r.1.1=v-r.1.1-y by ring]
  rw [he]
  exact h

/-- The actual source-horizon limit commutes with every compact joint target pairing. -/
theorem horizon_kernel_test_limit (q : XiZeroCopy) (v : ℝ) (phi : Target → ℂ)
    (hp : Continuous phi) (hc : HasCompactSupport phi) :
    Tendsto (fun y => ∫ r : Target, nativeDirichletCausalKernel q (v-y-r.1.1) r.1.2 y r.2.re r.2.im*phi r)
      atBot (𝓝 (∫ r : Target, horizonKernel q v r*phi r)) := by
  obtain ⟨M,hM,hb⟩ := approximation_bound q v phi hc
  have hi : Integrable (fun r => M*‖phi r‖) := (hp.norm.integrable_of_hasCompactSupport hc.norm).const_mul M
  apply tendsto_integral_filter_of_dominated_convergence (fun r => M*‖phi r‖)
  · exact Eventually.of_forall (fun y => ((approximation_measurable q v y).mul hp.measurable).aestronglyMeasurable)
  · filter_upwards [eventually_lt_atBot (0:ℝ)] with y hy
    exact ae_of_all _ (fun r => by
      rw [norm_mul]
      by_cases hr : r ∈ tsupport phi
      · exact mul_le_mul_of_nonneg_right (hb y hy r hr) (norm_nonneg _)
      · rw [image_eq_zero_of_notMem_tsupport hr,norm_zero,mul_zero,mul_zero])
  · exact hi
  · exact ae_of_all _ (fun r => (approximation_tendsto q v r).mul_const (phi r))

/-- The original horizon kernel has no bulk source: its weak wave action is zero
for every joint smooth compact test supported in the physical radial half-plane. -/
theorem horizon_kernel_weak_wave (q : XiZeroCopy) (v : ℝ) (F : Target → ℂ)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hphysical : tsupport F ⊆ {r : Target | r.1.2 < 0}) :
    (∫ r : Target, horizonKernel q v r*weakWaveTest F r)=0 := by
  have hr := weakWaveTest_regular F hF hc
  have ht := horizon_kernel_test_limit q v (weakWaveTest F) hr.1 hr.2
  obtain ⟨a,ha⟩ := hc.bddBelow_image (continuous_fst.snd.continuousOn : ContinuousOn (fun r : Target => r.1.2) (tsupport F))
  have he : (fun y => ∫ r : Target, nativeDirichletCausalKernel q (v-y-r.1.1) r.1.2 y r.2.re r.2.im*weakWaveTest F r)
      =ᶠ[atBot] fun _ => (0:ℂ) := by
    filter_upwards [eventually_lt_atBot (min a 0)] with y hy
    have hy0 : y < 0 := hy.trans_le (min_le_right _ _)
    have hya : y < a := hy.trans_le (min_le_left _ _)
    rw [kernel_joint_transposition q (v-y) y hy0 F hF hc hphysical]
    have hz (z : ℂ) : F ((v-y,y),z)=0 := by
      by_contra hn
      have h := ha (Set.mem_image_of_mem (fun r : Target => r.1.2) (subset_tsupport F hn))
      exact (not_le.mpr hya) h
    simp only [hz,mul_zero,integral_zero]
  exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' he.symm)

private theorem halfKernel_joint_measurable (q : XiZeroCopy) (X : Target → ℝ)
    (hX : Continuous X) :
    Measurable (fun a : ℝ × Target => halfKernel q a.2.1.1 (X a.2) a.1 a.2.2.re a.2.2.im) := by
  have hx := hX.comp (continuous_snd : Continuous (Prod.snd : ℝ × Target → Target))
  have ht : Continuous (fun a : ℝ × Target => horizonArgument a.2.1.1 (X a.2) a.1) := by
    unfold horizonArgument
    exact ((Real.continuous_exp.comp (continuous_fst.sub continuous_snd.fst.fst)).sub
      (Real.continuous_sinh.comp hx)).div (Real.continuous_cosh.comp hx)
        (fun a => (Real.cosh_pos _).ne')
  have hmean := (closedMean_continuous q).comp (ht.prodMk continuous_snd.snd)
  change Measurable (fun a : ℝ × Target => if a.2.1.1+X a.2 ≤ a.1 then
    closedMean q (horizonArgument a.2.1.1 (X a.2) a.1,a.2.2) else 0)
  exact Measurable.ite ((isClosed_le (continuous_snd.fst.fst.add hx) continuous_fst).measurableSet)
    hmean.measurable measurable_const

private def halfDensity (q : XiZeroCopy) (branch : Bool) (tau x X k v : ℝ) : ℂ :=
  timeOnsetFirst (2*physicalRate q branch) v*halfKernel q tau x v X k

private theorem halfDensity_joint_measurable (q : XiZeroCopy) (branch : Bool)
    (X : Target → ℝ) (hX : Continuous X) :
    Measurable (fun a : ℝ × Target => halfDensity q branch a.2.1.1 (X a.2) a.2.2.re a.2.2.im a.1) := by
  have ht : Continuous (timeOnsetFirst (2*physicalRate q branch)) :=
    continuous_iff_continuousAt.mpr (fun v => (timeOnsetFirst_hasDerivAt _ v).continuousAt)
  exact (ht.measurable.comp measurable_fst).mul (halfKernel_joint_measurable q X hX)

private theorem halfDensity_bound (q : XiZeroCopy) (branch : Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ tau x X k v : ℝ,
      ‖halfDensity q branch tau x X k v‖ ≤
        C*Real.exp ((sourceGrowthExponent q-decayExponent q)*v)*
          Real.exp (sourceGrowthExponent q*(-tau-x+|k|)) := by
  obtain ⟨C,hC,hM⟩ := horizonMean_growth q
  have hs := currentRate_re_lt q branch
  change (2*physicalRate q branch).re < -2 at hs
  obtain ⟨B,hB,hT⟩ := timeOnset_pair_bound (2*physicalRate q branch) (decayExponent q)
    (by linarith [(decayExponent_bounds q).2])
  refine ⟨B*C,mul_nonneg hB hC,?_⟩
  intro tau x X k v
  have hb : ‖timeOnsetFirst (2*physicalRate q branch) v‖ ≤ B*Real.exp (-decayExponent q*v) :=
    (le_add_of_nonneg_left (norm_nonneg _)).trans (hT v)
  by_cases h : tau+x ≤ v
  · have he : halfKernel q tau x v X k=horizonMean q x (v-tau-x) X k := by
      convert halfKernel_at_delay q tau x (v-tau-x) X k (by linarith) using 1 <;> congr 1 <;> ring
    have hk := hM x (v-tau-x) X k (by linarith)
    unfold halfDensity
    rw [he,norm_mul]
    refine (mul_le_mul hb hk (norm_nonneg _) (by positivity)).trans_eq ?_
    simp only [sub_mul,mul_add,mul_sub,neg_mul,mul_neg,Real.exp_add,Real.exp_sub,Real.exp_neg]
    ring
  · simp only [halfDensity,halfKernel,if_neg h,mul_zero,norm_zero]
    positivity

private theorem halfDensity_integrable (q : XiZeroCopy) (branch : Bool) (tau x X k : ℝ) :
    IntegrableOn (halfDensity q branch tau x X k) (Ioi (0:ℝ)) := by
  obtain ⟨C,hC,hb⟩ := halfDensity_bound q branch
  have hi := ((integrableOn_exp_mul_Ioi (show sourceGrowthExponent q-decayExponent q<0 by
    linarith [(decayExponent_bounds q).1]) 0).const_mul C).mul_const
      (Real.exp (sourceGrowthExponent q*(-tau-x+|k|)))
  have hm := (halfDensity_joint_measurable q branch (fun _ : Target => x) continuous_const).comp
    (measurable_id.prodMk measurable_const : Measurable (fun v : ℝ => (v,((tau,x),(⟨X,k⟩:ℂ)))))
  apply hi.mono' hm.aestronglyMeasurable
  exact ae_of_all _ (fun v => hb tau x X k v)

/-- Exact source-time representation of an original characteristic cap arm. -/
theorem boundaryArm_source_integral (q : XiZeroCopy) (branch : Bool) (tau x X k : ℝ) :
    boundaryArm q branch (tau+x) x X k =
      ∫ v in Ioi (0:ℝ), halfDensity q branch tau x X k v := by
  let N := halfDensity q branch tau x X k
  have hN : (∫ v in Ioi (0:ℝ), N v)=∫ v : ℝ, N v := by
    rw [← integral_Ici_eq_integral_Ioi]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    simp only [mem_Ici,not_le] at hv
    simp only [N,halfDensity,timeOnsetFirst_zero_of_neg _ hv,zero_mul]
  have hR : (∫ r in Ioi (0:ℝ), N (r+(tau+x)))=∫ r : ℝ, N (r+(tau+x)) := by
    rw [← integral_Ici_eq_integral_Ioi]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro r hr
    simp only [mem_Ici,not_le] at hr
    have hn : ¬ tau+x ≤ r+(tau+x) := by linarith
    simp only [N,halfDensity,halfKernel,if_neg hn,mul_zero]
  rw [hN,← integral_add_right_eq_self N (tau+x),← hR]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  change boundaryDensity q branch (tau+x) x X k r=N (r+(tau+x))
  dsimp only [N,halfDensity,boundaryDensity]
  rw [show r+(tau+x)=tau+x+r by ring,halfKernel_at_delay q tau x r X k hr.le]

private theorem halfTestDensity_integrable (q : XiZeroCopy) (branch : Bool)
    (X : Target → ℝ) (hX : Continuous X) (phi : Target → ℂ) (hp : Continuous phi)
    (hc : HasCompactSupport phi) :
    Integrable (fun a : ℝ × Target => halfDensity q branch a.2.1.1 (X a.2) a.2.2.re a.2.2.im a.1*phi a.2)
      ((volume.restrict (Ioi (0:ℝ))).prod volume) := by
  obtain ⟨C,hC,hb⟩ := halfDensity_bound q branch
  let W := fun r : Target => Real.exp (sourceGrowthExponent q*(-r.1.1-X r+|r.2.im|))*‖phi r‖
  have hW : Continuous (fun r : Target => Real.exp (sourceGrowthExponent q*(-r.1.1-X r+|r.2.im|))) := by fun_prop
  have hw : Integrable W := (hW.mul hp.norm).integrable_of_hasCompactSupport hc.norm.mul_left
  have hi := ((integrableOn_exp_mul_Ioi (show sourceGrowthExponent q-decayExponent q<0 by
    linarith [(decayExponent_bounds q).1]) 0).mul_prod hw).const_mul C
  have hm := (halfDensity_joint_measurable q branch X hX).mul (hp.measurable.comp measurable_snd)
  apply hi.mono' hm.aestronglyMeasurable
  exact ae_of_all _ (fun a => by
    dsimp only [Pi.mul_apply,Function.comp_def]
    rw [norm_mul]
    refine (mul_le_mul_of_nonneg_right (hb a.2.1.1 (X a.2) a.2.2.re a.2.2.im a.1) (norm_nonneg _)).trans_eq ?_
    dsimp only [W]
    ring)

private def capTestDensity (q : XiZeroCopy) (branch : Bool) (phi : Target → ℂ)
    (a : ℝ × Target) : ℂ :=
  timeOnsetFirst (2*physicalRate q branch) a.1*horizonKernel q a.1 a.2*phi a.2

/-- Absolute admission of the original cap's source-time/target pairing. -/
theorem capTestDensity_integrable (q : XiZeroCopy) (branch : Bool)
    (phi : Target → ℂ) (hp : Continuous phi) (hc : HasCompactSupport phi) :
    Integrable (capTestDensity q branch phi) ((volume.restrict (Ioi (0:ℝ))).prod volume) := by
  have hd := halfTestDensity_integrable q branch (fun r => r.1.2) continuous_fst.snd phi hp hc
  have hi := halfTestDensity_integrable q branch (fun r => -r.1.2) continuous_fst.snd.neg phi hp hc
  have h := (hd.sub hi).div_const 2
  convert h using 1
  funext a
  dsimp only [capTestDensity,horizonKernel,halfDensity,Pi.sub_apply]
  ring

private theorem cap_source_pair (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ)
    (phi : Target → ℂ) (r : Target) :
    (-2*liftTraceCoefficient q branch amplitude)*(∫ v in Ioi (0:ℝ), capTestDensity q branch phi (v,r)) =
      capBoundaryField q branch amplitude r.1.1 r.1.2 r.2.re r.2.im*phi r := by
  have hd := halfDensity_integrable q branch r.1.1 r.1.2 r.2.re r.2.im
  have hi := halfDensity_integrable q branch r.1.1 (-r.1.2) r.2.re r.2.im
  have he (v : ℝ) : capTestDensity q branch phi (v,r) =
      ((halfDensity q branch r.1.1 r.1.2 r.2.re r.2.im v-
        halfDensity q branch r.1.1 (-r.1.2) r.2.re r.2.im v)/2)*phi r := by
    dsimp only [capTestDensity,horizonKernel,halfDensity]
    ring
  simp_rw [he]
  rw [integral_mul_const,integral_div,integral_sub hd hi,
    ← boundaryArm_source_integral,← boundaryArm_source_integral]
  simp only [capBoundaryField,sub_eq_add_neg]
  ring

/-- The original cap acts by an absolutely convergent integral on every compact joint test. -/
theorem cap_test_integrable (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ)
    (phi : Target → ℂ) (hp : Continuous phi) (hc : HasCompactSupport phi) :
    Integrable (fun r : Target => capBoundaryField q branch amplitude r.1.1 r.1.2 r.2.re r.2.im*phi r) := by
  have h := ((capTestDensity_integrable q branch phi hp hc).integral_prod_right).const_mul
    (-2*liftTraceCoefficient q branch amplitude)
  simpa only [cap_source_pair] using h

/-- Full admitted source-time transposition for the original cap. -/
theorem cap_source_test_fubini (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ)
    (phi : Target → ℂ) (hp : Continuous phi) (hc : HasCompactSupport phi) :
    (∫ r : Target, capBoundaryField q branch amplitude r.1.1 r.1.2 r.2.re r.2.im*phi r) =
      (-2*liftTraceCoefficient q branch amplitude)*∫ v in Ioi (0:ℝ),
        timeOnsetFirst (2*physicalRate q branch) v*(∫ r : Target, horizonKernel q v r*phi r) := by
  have h := integral_integral_swap (f := fun v r => capTestDensity q branch phi (v,r))
    (capTestDensity_integrable q branch phi hp hc)
  have he (v : ℝ) : (∫ r : Target, capTestDensity q branch phi (v,r)) =
      timeOnsetFirst (2*physicalRate q branch) v*∫ r : Target, horizonKernel q v r*phi r := by
    simp only [capTestDensity,mul_assoc,integral_const_mul]
  have hs : (∫ r : Target, capBoundaryField q branch amplitude r.1.1 r.1.2 r.2.re r.2.im*phi r) =
      (-2*liftTraceCoefficient q branch amplitude)*∫ r : Target, ∫ v in Ioi (0:ℝ), capTestDensity q branch phi (v,r) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun r => (cap_source_pair q branch amplitude phi r).symm)
  rw [hs,← h]
  simp only [he]

/-- The actual source-derived horizon cap is a homogeneous weak solution,
with no cap-equation, convergence or matching premise. -/
theorem original_cap_weak_wave (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ)
    (F : Target → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hphysical : tsupport F ⊆ {r : Target | r.1.2 < 0}) :
    (∫ r : Target, capBoundaryField q branch amplitude r.1.1 r.1.2 r.2.re r.2.im*weakWaveTest F r)=0 := by
  have hr := weakWaveTest_regular F hF hc
  rw [cap_source_test_fubini q branch amplitude (weakWaveTest F) hr.1 hr.2]
  simp only [horizon_kernel_weak_wave q _ F hF hc hphysical,mul_zero,integral_zero]

/-- Subtracting the original cap from the original future response changes
its boundary trace while preserving its complete reduced bulk source. -/
theorem original_future_sub_cap_weak_wave (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ)
    (F : Target → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hphysical : tsupport F ⊆ {r : Target | r.1.2 < 0}) :
    (∫ r : Target, (response q branch amplitude r.1.1 r.1.2 r.2.re r.2.im-
      capBoundaryField q branch amplitude r.1.1 r.1.2 r.2.re r.2.im)*weakWaveTest F r) =
        ∫ p, forcingTestPair q branch amplitude F p ∂D4BMFullSourceReciprocity.eventMeasure := by
  have hr := weakWaveTest_regular F hF hc
  simp_rw [sub_mul]
  rw [integral_sub (original_response_test_integrable q branch amplitude _ hr.1 hr.2)
    (cap_test_integrable q branch amplitude _ hr.1 hr.2),
    original_future_weak_wave q branch amplitude F hF hc hphysical,
    original_cap_weak_wave q branch amplitude F hF hc hphysical,sub_zero]

end
end RHTower.D4BMOriginalCapWave
