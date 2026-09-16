import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMGeneralTemporalTransposition
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMAdvancedKernelTransposition
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullSourceRadialReciprocity

/-!
# Full weak wave equation of the original future response

The literal infinite future response satisfies the reduced wave equation
against every joint smooth compact test in time, radius, horizontal position
and log-height, supported in the physical radial half-plane. The original
source, fixed onset, Dirichlet image and hyperbolic angular area are retained.

Kernel temporal transposition and angular transposition are combined before
source integration. A product majorant with the existing strict margin
`sourceGrowthExponent q < decayExponent q < 2` admits source/target Fubini.
No wave equation, source convergence or physical matching premise is assumed.

This identifies the reduced weak equation. Lift/cap equations and full
metric/QNM matching are separate obligations.
-/

open MeasureTheory Set Filter Topology
namespace RHTower.D4BMFullSourceWeakWave
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open D4BMNativeCircle D4BMCausalKernel D4BMModularCore D4BMHorizon D4BMJointSource
open D4BMGeneralTemporalTransposition D4BMAdvancedKernelTransposition D4BMFullSourceReciprocity
open D4BMFullSourceAdvanced
open scoped ContDiff ENNReal
noncomputable section
set_option autoImplicit false

abbrev Target := (ℝ × ℝ) × ℂ

private def targetDir (v : Target) (F : Target → ℂ) (p : Target) : ℂ := fderiv ℝ F p v

private theorem targetDir_smooth {F : Target → ℂ} (hF : ContDiff ℝ ∞ F) (v : Target) :
    ContDiff ℝ ∞ (targetDir v F) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private theorem event_slice_dir (F : Target → ℂ) (hF : ContDiff ℝ ∞ F)
    (p : ℝ × ℝ) (z : ℂ) (v : ℝ × ℝ) :
    eventDir v (fun r => F (r,z)) p = targetDir (v,0) F (p,z) := by
  have he : HasFDerivAt (fun r : ℝ × ℝ => (r,z))
      ((ContinuousLinearMap.id ℝ (ℝ × ℝ)).prod (0 : (ℝ × ℝ) →L[ℝ] ℂ)) p :=
    (hasFDerivAt_id p).prodMk (hasFDerivAt_const z p)
  have h := ((hF.differentiable (by simp) (p,z)).hasFDerivAt.comp p he).fderiv
  dsimp only [Function.comp_def] at h
  unfold eventDir targetDir
  rw [h]
  rfl

private theorem angular_slice_dir (F : Target → ℂ) (hF : ContDiff ℝ ∞ F)
    (p : ℝ × ℝ) (z v : ℂ) :
    fderiv ℝ (fun w => F (p,w)) z v = targetDir (0,v) F (p,z) := by
  have he : HasFDerivAt (fun w : ℂ => (p,w))
      ((0 : ℂ →L[ℝ] (ℝ × ℝ)).prod (ContinuousLinearMap.id ℝ ℂ)) z :=
    (hasFDerivAt_const p z).prodMk (hasFDerivAt_id z)
  have h := ((hF.differentiable (by simp) (p,z)).hasFDerivAt.comp z he).fderiv
  dsimp only [Function.comp_def] at h
  unfold targetDir
  rw [h]
  rfl

private theorem event_slice_second (F : Target → ℂ) (hF : ContDiff ℝ ∞ F)
    (p : ℝ × ℝ) (z : ℂ) (v w : ℝ × ℝ) :
    eventDir v (eventDir w (fun r => F (r,z))) p =
      targetDir (v,0) (targetDir (w,0) F) (p,z) := by
  have he : eventDir w (fun r => F (r,z)) = fun r => targetDir (w,0) F (r,z) :=
    funext (fun r => event_slice_dir F hF r z w)
  rw [he,event_slice_dir _ (targetDir_smooth hF (w,0))]

private theorem angular_slice_second (F : Target → ℂ) (hF : ContDiff ℝ ∞ F)
    (p : ℝ × ℝ) (z v w : ℂ) :
    fderiv ℝ (fun a => fderiv ℝ (fun b => F (p,b)) a w) z v =
      targetDir (0,v) (targetDir (0,w) F) (p,z) := by
  have he : (fun a => fderiv ℝ (fun b => F (p,b)) a w) =
      fun a => targetDir (0,w) F (p,a) :=
    funext (fun a => angular_slice_dir F hF p a w)
  rw [he,angular_slice_dir _ (targetDir_smooth hF (0,w))]

private def jointWave (F : Target → ℂ) (p : Target) : ℂ :=
  targetDir ((1,0),0) (targetDir ((1,0),0) F) p-
    targetDir ((0,1),0) (targetDir ((0,1),0) F) p

private def jointAngularTest (F : Target → ℂ) (p : Target) : ℂ :=
  targetDir (0,1) (targetDir (0,1) (fun r => (Real.exp r.2.im:ℂ)*F r)) p+
  targetDir (0,Complex.I) (targetDir (0,Complex.I) (fun r => (Real.exp (-r.2.im):ℂ)*F r)) p+
  targetDir (0,Complex.I) (fun r => (Real.exp (-r.2.im):ℂ)*F r) p

private theorem jointWave_slice (F : Target → ℂ) (hF : ContDiff ℝ ∞ F) (p : Target) :
    jointWave F p = eventWave (fun r => F (r,p.2)) p.1 := by
  unfold jointWave eventWave
  rw [event_slice_second F hF,event_slice_second F hF]

private theorem jointAngularTest_slice (F : Target → ℂ) (hF : ContDiff ℝ ∞ F) (p : Target) :
    jointAngularTest F p = angularTestAction (fun z => F (p.1,z)) p.2 := by
  have ha : ContDiff ℝ ∞ (fun r : Target => (Real.exp r.2.im:ℂ)*F r) :=
    (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (Complex.imCLM.contDiff.comp contDiff_snd))).mul hF
  have hb : ContDiff ℝ ∞ (fun r : Target => (Real.exp (-r.2.im):ℂ)*F r) :=
    (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (Complex.imCLM.contDiff.comp contDiff_snd).neg)).mul hF
  change _ = fderiv ℝ (fun z => fderiv ℝ (fun w => (Real.exp w.im:ℂ)*F (p.1,w)) z 1) p.2 1+
    fderiv ℝ (fun z => fderiv ℝ (fun w => (Real.exp (-w.im):ℂ)*F (p.1,w)) z Complex.I) p.2 Complex.I+
    fderiv ℝ (fun w => (Real.exp (-w.im):ℂ)*F (p.1,w)) p.2 Complex.I
  rw [angular_slice_second _ ha,angular_slice_second _ hb,angular_slice_dir _ hb]
  rfl

/-- Full reduced weak test operator in time, radius, horizontal position and log-height. -/
def weakWaveTest (F : Target → ℂ) (p : Target) : ℂ :=
  (Real.exp (-p.2.im):ℂ)*eventWave (fun r => F (r,p.2)) p.1-
    angularTestAction (fun z => F (p.1,z)) p.2/(Real.cosh p.1.2:ℂ)^2

private theorem joint_regular (F : Target → ℂ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) : ContDiff ℝ ∞ (jointWave F) ∧ HasCompactSupport (jointWave F) ∧
      ContDiff ℝ ∞ (jointAngularTest F) ∧ HasCompactSupport (jointAngularTest F) := by
  have ha : ContDiff ℝ ∞ (fun r : Target => (Real.exp r.2.im:ℂ)*F r) :=
    (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (Complex.imCLM.contDiff.comp contDiff_snd))).mul hF
  have hb : ContDiff ℝ ∞ (fun r : Target => (Real.exp (-r.2.im):ℂ)*F r) :=
    (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (Complex.imCLM.contDiff.comp contDiff_snd).neg)).mul hF
  have hw : ContDiff ℝ ∞ (jointWave F) :=
    (targetDir_smooth (targetDir_smooth hF ((1,0),0)) ((1,0),0)).sub
      (targetDir_smooth (targetDir_smooth hF ((0,1),0)) ((0,1),0))
  have ht : ContDiff ℝ ∞ (jointAngularTest F) :=
    ((targetDir_smooth (targetDir_smooth ha (0,1)) (0,1)).add
      (targetDir_smooth (targetDir_smooth hb (0,Complex.I)) (0,Complex.I))).add
      (targetDir_smooth hb (0,Complex.I))
  have hcw : HasCompactSupport (jointWave F) :=
    ((hc.fderiv_apply ℝ ((1,0),0)).fderiv_apply ℝ ((1,0),0)).sub
      ((hc.fderiv_apply ℝ ((0,1),0)).fderiv_apply ℝ ((0,1),0))
  have hca : HasCompactSupport (fun r : Target => (Real.exp r.2.im:ℂ)*F r) := hc.mul_left
  have hcb : HasCompactSupport (fun r : Target => (Real.exp (-r.2.im):ℂ)*F r) := hc.mul_left
  have hct : HasCompactSupport (jointAngularTest F) :=
    (((hca.fderiv_apply ℝ (0,1)).fderiv_apply ℝ (0,1)).add
      ((hcb.fderiv_apply ℝ (0,Complex.I)).fderiv_apply ℝ (0,Complex.I))).add
      (hcb.fderiv_apply ℝ (0,Complex.I))
  exact ⟨hw,hcw,ht,hct⟩

/-- The complete reduced test operator preserves continuity and compact support. -/
theorem weakWaveTest_regular (F : Target → ℂ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) : Continuous (weakWaveTest F) ∧ HasCompactSupport (weakWaveTest F) := by
  obtain ⟨hw,hcw,ht,hct⟩ := joint_regular F hF hc
  have he : weakWaveTest F = fun p =>
      (Real.exp (-p.2.im):ℂ)*jointWave F p-jointAngularTest F p/(Real.cosh p.1.2:ℂ)^2 := by
    funext p
    rw [jointWave_slice F hF,jointAngularTest_slice F hF]
    rfl
  rw [he]
  constructor
  · exact ((by fun_prop : Continuous (fun p : Target => (Real.exp (-p.2.im):ℂ))).mul hw.continuous).sub
      (ht.continuous.div (by fun_prop) (fun p => pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne')))
  · have hd : HasCompactSupport (fun p => jointAngularTest F p/(Real.cosh p.1.2:ℂ)^2) := by
      simp only [div_eq_mul_inv]
      exact hct.mul_right
    exact hcw.mul_left.sub hd

private def closedMean (q : XiZeroCopy) (p : ℝ × ℂ) : ℂ :=
  angularKernel q (max 1 p.1) p.2.re p.2.im

private def closedAction (q : XiZeroCopy) (p : ℝ × ℂ) : ℂ :=
  angularAction q (max 1 p.1) p.2.re p.2.im

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
      (fun p : ℝ × ℂ => (Real.arcosh (max 1 p.1),p.2.re,p.2.im))) :=
    Continuous.comp hm hP
  dsimp only [Function.comp_def] at h
  exact h

private theorem laplace_circle_joint_continuous (q : XiZeroCopy) :
    Continuous (fun r : (ℝ × ℂ) × ℝ => scalarLaplacian (fullSquarePotential q)
      (logCircle r.1.1 r.2 r.1.2.re r.1.2.im)) := by
  let Z := fun r : (ℝ × ℂ) × ℝ => logCircle r.1.1 r.2 r.1.2.re r.1.2.im
  have hp (r : (ℝ × ℂ) × ℝ) : 0 < Z r 1 :=
    mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))
  have hZ : Continuous Z := by
    have hd : Continuous (fun r : (ℝ × ℂ) × ℝ => denominator r.1.1 r.2) := by
      unfold denominator
      fun_prop
    have hn (r : (ℝ × ℂ) × ℝ) : denominator r.1.1 r.2 ≠ 0 := (denominator_pos _ _).ne'
    have ho := ((Real.continuous_sinh.comp continuous_fst.fst).mul
      (Real.continuous_sin.comp continuous_snd)).div hd hn
    have hh := ((continuous_const : Continuous (fun _ : (ℝ × ℂ) × ℝ => (1:ℝ)))).div hd hn
    apply continuous_pi
    intro i
    fin_cases i
    · exact (Complex.continuous_re.comp continuous_fst.snd).add
        ((Real.continuous_exp.comp (Complex.continuous_im.comp continuous_fst.snd)).mul ho)
    · exact (Real.continuous_exp.comp (Complex.continuous_im.comp continuous_fst.snd)).mul hh
  have he : (fun r : (ℝ × ℂ) × ℝ => scalarLaplacian (fullSquarePotential q) (Z r)) =
      fun r => (Z r 1:ℂ)^2 *
        (coordDeriv 0 (coordDeriv 0 (fullSquarePotential q)) (Z r)+
          coordDeriv 1 (coordDeriv 1 (fullSquarePotential q)) (Z r)) :=
    funext (fun r => scalarLaplacian_eq _ _ (hp r))
  change Continuous (fun r : (ℝ × ℂ) × ℝ => scalarLaplacian (fullSquarePotential q) (Z r))
  rw [he]
  apply continuous_iff_continuousAt.mpr
  intro r
  have hs : ContDiffAt ℝ ∞ (fullSquarePotential q) (Z r) :=
    contDiffAt_infty.mpr (fun n => fullSquarePotential_smooth q _ (hp r) n)
  have hj (i : Fin 2) : ContinuousAt (coordDeriv i (coordDeriv i (fullSquarePotential q))) (Z r) :=
    (coordDeriv_contDiffAt (m := ∞)
      (by simpa using coordDeriv_contDiffAt (m := ∞) (by simpa using hs) i) i).continuousAt
  exact ((Complex.continuous_ofReal.comp ((continuous_apply 1).comp hZ)).pow 2).continuousAt.mul
    (((hj 0).comp_of_eq (hZ.continuousAt (x := r)) rfl).add
      ((hj 1).comp_of_eq (hZ.continuousAt (x := r)) rfl))

private theorem closedAction_continuous (q : XiZeroCopy) : Continuous (closedAction q) := by
  have hM : Continuous (fun p : ℝ × ℂ => average (fun theta =>
      scalarLaplacian (fullSquarePotential q) (logCircle p.1 theta p.2.re p.2.im))) := by
    have he : (fun p : ℝ × ℂ => average (fun theta =>
        scalarLaplacian (fullSquarePotential q) (logCircle p.1 theta p.2.re p.2.im))) =
        fun p => (1/(2*Real.pi:ℂ))*∫ theta in (0:ℝ)..2*Real.pi,
          scalarLaplacian (fullSquarePotential q) (logCircle p.1 theta p.2.re p.2.im) := by
      funext p
      rw [intervalIntegral.integral_of_le (by positivity)]
      rfl
    rw [he]
    exact continuous_const.mul
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun p : ℝ × ℂ => fun theta : ℝ =>
          scalarLaplacian (fullSquarePotential q) (logCircle p.1 theta p.2.re p.2.im))
        (laplace_circle_joint_continuous q) 0 (2*Real.pi))
  have hR := Real.continuousOn_arcosh.comp_continuous
    (continuous_const.max (continuous_fst : Continuous (Prod.fst : ℝ × ℂ → ℝ)))
    (fun p => le_max_left (1:ℝ) p.1)
  convert hM.comp (hR.prodMk continuous_snd) using 1
  funext p
  exact mean_laplacian_commutes q (Real.arcosh (max 1 p.1)) p.2.re p.2.im

private theorem invariant_joint_continuous :
    Continuous (fun p : ℝ × ℝ × ℝ => invariant p.1 p.2.1 p.2.2) := by
  unfold invariant
  apply Continuous.div <;> try fun_prop
  intro p
  exact mul_ne_zero (Real.cosh_pos _).ne' (Real.cosh_pos _).ne'

private def coneSection (C : ℝ × ℂ → ℂ) (s y : ℝ) (p : Target) : ℂ :=
  if |p.1.2-y| ≤ s-p.1.1 then C (invariant (s-p.1.1) p.1.2 y,p.2) else 0

private theorem coneSection_integrable (C : ℝ × ℂ → ℂ) (hC : Continuous C)
    (s y : ℝ) (F : Target → ℂ) (hF : Continuous F) (hc : HasCompactSupport F) :
    Integrable (fun p => coneSection C s y p*F p) := by
  have hP : Continuous (fun p : Target => C (invariant (s-p.1.1) p.1.2 y,p.2)) :=
    hC.comp ((invariant_joint_continuous.comp
      (show Continuous (fun p : Target => (s-p.1.1,p.1.2,y)) by fun_prop)).prodMk continuous_snd)
  have hs : MeasurableSet {p : Target | |p.1.2-y| ≤ s-p.1.1} :=
    (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  have he : (fun p : Target => coneSection C s y p*F p) =
      {p : Target | |p.1.2-y| ≤ s-p.1.1}.indicator
        (fun p => C (invariant (s-p.1.1) p.1.2 y,p.2)*F p) := by
    funext p
    by_cases h : |p.1.2-y| ≤ s-p.1.1
    · simp only [coneSection, Set.indicator, Set.mem_setOf_eq, if_pos h]
    · simp only [coneSection, Set.indicator, Set.mem_setOf_eq, if_neg h, zero_mul]
  rw [he]
  exact ((hP.mul hF).integrable_of_hasCompactSupport hc.mul_left).indicator hs

private def kernelAt (q : XiZeroCopy) (s y : ℝ) (p : Target) : ℂ :=
  nativeDirichletCausalKernel q (s-p.1.1) p.1.2 y p.2.re p.2.im

private def angularAt (q : XiZeroCopy) (s y : ℝ) (p : Target) : ℂ :=
  ((if |p.1.2-y| ≤ s-p.1.1 then angularAction q (invariant (s-p.1.1) p.1.2 y) p.2.re p.2.im else 0)-
    (if |p.1.2+y| ≤ s-p.1.1 then angularAction q (invariant (s-p.1.1) p.1.2 (-y)) p.2.re p.2.im else 0))/2

private theorem kernelAt_split (q : XiZeroCopy) (s y : ℝ) (p : Target) :
    kernelAt q s y p = (coneSection (closedMean q) s y p-coneSection (closedMean q) s (-y) p)/2 := by
  have he (Y : ℝ) : (if |p.1.2-Y| ≤ s-p.1.1 then
        nativeRiemannKernel q (s-p.1.1) p.1.2 Y p.2.re p.2.im else 0) =
      coneSection (closedMean q) s Y p := by
    by_cases h : |p.1.2-Y| ≤ s-p.1.1
    · simp only [if_pos h,coneSection,closedMean,nativeRiemannKernel,
        max_eq_right (invariant_causal ⟨_,_,_,h⟩)]
    · simp only [if_neg h,coneSection]
  have hy := he y
  have hi := he (-y)
  simp only [sub_neg_eq_add] at hi
  exact congrArg₂ (fun a b : ℂ => (a-b)/2) hy hi

private theorem angularAt_split (q : XiZeroCopy) (s y : ℝ) (p : Target) :
    angularAt q s y p = (coneSection (closedAction q) s y p-coneSection (closedAction q) s (-y) p)/2 := by
  have he (Y : ℝ) : (if |p.1.2-Y| ≤ s-p.1.1 then
        angularAction q (invariant (s-p.1.1) p.1.2 Y) p.2.re p.2.im else 0) =
      coneSection (closedAction q) s Y p := by
    by_cases h : |p.1.2-Y| ≤ s-p.1.1
    · simp only [if_pos h,coneSection,closedAction,max_eq_right (invariant_causal ⟨_,_,_,h⟩)]
    · simp only [if_neg h,coneSection]
  have hy := he y
  have hi := he (-y)
  simp only [sub_neg_eq_add] at hi
  exact congrArg₂ (fun a b : ℂ => (a-b)/2) hy hi

private theorem kernelAt_integrable (q : XiZeroCopy) (s y : ℝ)
    (F : Target → ℂ) (hF : Continuous F) (hc : HasCompactSupport F) :
    Integrable (fun p => kernelAt q s y p*F p) := by
  have h1 := coneSection_integrable (closedMean q) (closedMean_continuous q) s y F hF hc
  have h2 := coneSection_integrable (closedMean q) (closedMean_continuous q) s (-y) F hF hc
  have hi := (h1.sub h2).div_const 2
  convert hi using 1
  funext p
  rw [kernelAt_split]
  dsimp only [Pi.sub_apply]
  ring

private theorem angularAt_integrable (q : XiZeroCopy) (s y : ℝ)
    (F : Target → ℂ) (hF : Continuous F) (hc : HasCompactSupport F) :
    Integrable (fun p => angularAt q s y p*F p) := by
  have h1 := coneSection_integrable (closedAction q) (closedAction_continuous q) s y F hF hc
  have h2 := coneSection_integrable (closedAction q) (closedAction_continuous q) s (-y) F hF hc
  have hi := (h1.sub h2).div_const 2
  convert hi using 1
  funext p
  rw [angularAt_split]
  dsimp only [Pi.sub_apply]
  ring

private theorem event_slice_compact {F : Target → ℂ} (hc : HasCompactSupport F) (z : ℂ) :
    HasCompactSupport (fun p : ℝ × ℝ => F (p,z)) := by
  apply hc.comp_isClosedEmbedding
  refine ⟨isEmbedding_prodMkLeft z,?_⟩
  have he : Set.range (fun p : ℝ × ℝ => (p,z)) = Set.univ ×ˢ ({z} : Set ℂ) := by
    ext ⟨p,w⟩
    simp [eq_comm]
  rw [he]
  exact isClosed_univ.prod isClosed_singleton

private theorem angular_slice_compact {F : Target → ℂ} (hc : HasCompactSupport F) (p : ℝ × ℝ) :
    HasCompactSupport (fun z : ℂ => F (p,z)) := by
  apply hc.comp_isClosedEmbedding
  refine ⟨isEmbedding_prodMkRight p,?_⟩
  have he : Set.range (fun z : ℂ => (p,z)) = ({p} : Set (ℝ × ℝ)) ×ˢ Set.univ := by
    ext ⟨r,z⟩
    simp [eq_comm]
  rw [he]
  exact isClosed_singleton.prod isClosed_univ

private theorem target_fubini (F : Target → ℂ) (hi : Integrable F) :
    (∫ r : Target, F r) = ∫ p : ℝ × ℝ, ∫ z : ℂ, F (p,z) := by
  rw [Measure.volume_eq_prod] at hi ⊢
  exact integral_prod F hi

private theorem target_fubini_swap (F : Target → ℂ) (hi : Integrable F) :
    (∫ r : Target, F r) = ∫ z : ℂ, ∫ p : ℝ × ℝ, F (p,z) := by
  rw [Measure.volume_eq_prod] at hi ⊢
  exact integral_prod_symm F hi

private theorem angularAt_pair (q : XiZeroCopy) (s y : ℝ) (p : ℝ × ℝ)
    (phi : ℂ → ℂ) (hp : Continuous phi) (hc : HasCompactSupport phi) :
    (∫ z : ℂ, (Real.exp (-z.im):ℂ)*phi z*angularAt q s y (p,z)) =
      testedDirichletAngularKernel q phi (s-p.1) p.2 y := by
  have hi (Y : ℝ) : Integrable (fun z : ℂ => (Real.exp (-z.im):ℂ)*phi z*
      (if |p.2-Y| ≤ s-p.1 then angularAction q (invariant (s-p.1) p.2 Y) z.re z.im else 0)) := by
    by_cases h : |p.2-Y| ≤ s-p.1
    · simp only [if_pos h]
      have hA := (closedAction_continuous q).comp
        (show Continuous (fun z : ℂ => (invariant (s-p.1) p.2 Y,z)) by fun_prop)
      have he : (fun z : ℂ => (Real.exp (-z.im):ℂ)*phi z*
          angularAction q (invariant (s-p.1) p.2 Y) z.re z.im) =
          fun z => (Real.exp (-z.im):ℂ)*phi z*closedAction q (invariant (s-p.1) p.2 Y,z) := by
        funext z
        simp only [closedAction,max_eq_right (invariant_causal ⟨_,_,_,h⟩)]
      rw [he]
      exact (((by fun_prop : Continuous (fun z : ℂ => (Real.exp (-z.im):ℂ))).mul hp).mul hA).integrable_of_hasCompactSupport
        hc.mul_left.mul_right
    · simp only [if_neg h,mul_zero]
      exact integrable_zero ℂ ℂ volume
  have hi' := hi (-y)
  simp only [sub_neg_eq_add] at hi'
  simp only [angularAt,← mul_div_assoc,mul_sub]
  rw [integral_div,integral_sub (hi y) hi']
  unfold testedDirichletAngularKernel
  split_ifs <;> simp only [mul_zero,integral_zero]

private theorem local_angular_transfer (q : XiZeroCopy) (s y : ℝ) (F : Target → ℂ)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (p : ℝ × ℝ) :
    (∫ z : ℂ, kernelAt q s y (p,z)*
      (jointAngularTest F (p,z)/(Real.cosh p.2:ℂ)^2)) =
    ∫ z : ℂ, angularAt q s y (p,z)*
      ((Real.exp (-z.im):ℂ)*F (p,z)/(Real.cosh p.2:ℂ)^2) := by
  let phi : ℂ → ℂ := fun z => F (p,z)
  have hp : ContDiff ℝ ∞ phi := hF.comp (contDiff_const.prodMk contDiff_id)
  have hcp : HasCompactSupport phi := angular_slice_compact hc p
  have h := dirichlet_angular_transposition q phi hp hcp (s-p.1) p.2 y
  have ha := angularAt_pair q s y p phi hp.continuous hcp
  have he (z : ℂ) : kernelAt q s y (p,z)*(jointAngularTest F (p,z)/(Real.cosh p.2:ℂ)^2) =
      (angularTestAction phi z*nativeDirichletCausalKernel q (s-p.1) p.2 y z.re z.im)/
        (Real.cosh p.2:ℂ)^2 := by
    rw [jointAngularTest_slice F hF]
    change kernelAt q s y (p,z)*(angularTestAction phi z/(Real.cosh p.2:ℂ)^2) = _
    unfold kernelAt
    ring
  simp_rw [he]
  rw [integral_div,h,← ha,← integral_div]
  apply integral_congr_ae
  filter_upwards with z
  dsimp only [phi]
  ring


/-- General four-variable compact tests of the original native kernel satisfy
its full weak wave equation, with the exact original source vertex. -/
theorem kernel_joint_transposition (q : XiZeroCopy) (s y : ℝ) (hy : y < 0)
    (F : Target → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hphysical : tsupport F ⊆ {r : Target | r.1.2 < 0}) :
    (∫ r : Target, nativeDirichletCausalKernel q (s-r.1.1) r.1.2 y r.2.re r.2.im*weakWaveTest F r) =
      ∫ z : ℂ, (Real.exp (-z.im):ℂ)*fullSquarePotential q ![z.re,Real.exp z.im]*F ((s,y),z) := by
  obtain ⟨hw,hcw,ht,hct⟩ := joint_regular F hF hc
  let W := fun p : Target => (Real.exp (-p.2.im):ℂ)*jointWave F p
  let A := fun p : Target => jointAngularTest F p/(Real.cosh p.1.2:ℂ)^2
  let B := fun p : Target => (Real.exp (-p.2.im):ℂ)*F p/(Real.cosh p.1.2:ℂ)^2
  have hW : Continuous W := (by fun_prop : Continuous (fun p : Target => (Real.exp (-p.2.im):ℂ))).mul hw.continuous
  have hcW : HasCompactSupport W := hcw.mul_left
  have hA : Continuous A := ht.continuous.div (by fun_prop)
    (fun p => pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'))
  have hcA : HasCompactSupport A := by
    dsimp only [A]
    simp only [div_eq_mul_inv]
    exact hct.mul_right
  have hB : Continuous B := ((by fun_prop : Continuous (fun p : Target => (Real.exp (-p.2.im):ℂ))).mul hF.continuous).div
    (by fun_prop) (fun p => pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'))
  have hcB : HasCompactSupport B := by
    dsimp only [B]
    simp only [div_eq_mul_inv]
    exact hc.mul_left.mul_right
  have hKW := kernelAt_integrable q s y W hW hcW
  have hKA := kernelAt_integrable q s y A hA hcA
  have hAB := angularAt_integrable q s y B hB hcB
  have hang : (∫ r : Target, kernelAt q s y r*A r) = ∫ r : Target, angularAt q s y r*B r := by
    rw [target_fubini _ hKA,target_fubini _ hAB]
    apply integral_congr_ae
    filter_upwards with p
    exact local_angular_transfer q s y F hF hc p
  have he (r : Target) : weakWaveTest F r = W r-A r := by
    dsimp only [W,A,weakWaveTest]
    rw [jointWave_slice F hF,jointAngularTest_slice F hF]
  change (∫ r : Target, kernelAt q s y r*weakWaveTest F r) = _
  simp_rw [he,mul_sub]
  rw [integral_sub hKW hKA,hang,← integral_sub hKW hAB]
  have hD : Integrable (fun r : Target => kernelAt q s y r*W r-angularAt q s y r*B r) := hKW.sub hAB
  rw [target_fubini_swap _ hD]
  apply integral_congr_ae
  filter_upwards with z
  let phi : ℝ × ℝ → ℂ := fun p => F (p,z)
  have hp : ContDiff ℝ ∞ phi := hF.comp (contDiff_id.prodMk contDiff_const)
  have hcp : HasCompactSupport phi := event_slice_compact hc z
  have himage : phi (s,-y)=0 := by
    by_contra hn
    have h := hphysical (subset_tsupport F (show ((s,-y),z) ∈ Function.support F from hn))
    change -y < 0 at h
    linarith
  have hd (p : ℝ × ℝ) : kernelAt q s y (p,z)*W (p,z)-angularAt q s y (p,z)*B (p,z) =
      (Real.exp (-z.im):ℂ)*dirichletWaveTest q s y z.re z.im phi p := by
    dsimp only [W,B]
    rw [jointWave_slice F hF]
    dsimp only [kernelAt,angularAt,dirichletWaveTest,phi]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  simp_rw [hd]
  rw [integral_const_mul,dirichletWaveTest_integral q s y z.re z.im phi hp hcp,himage,sub_zero]
  dsimp only [phi]
  ring

private theorem source_kernel_measurable (q : XiZeroCopy) :
    Measurable (fun r : Event × Target => kernelAt q r.1.1 r.1.2 r.2) := by
  have cone (Y : Event × Target → ℝ) (hY : Continuous Y) :
      Measurable (fun r : Event × Target =>
        if |r.2.1.2-Y r| ≤ r.1.1-r.2.1.1 then
          nativeRiemannKernel q (r.1.1-r.2.1.1) r.2.1.2 (Y r) r.2.2.re r.2.2.im else 0) := by
    have hi : Continuous (fun r : Event × Target => invariant (r.1.1-r.2.1.1) r.2.1.2 (Y r)) :=
      invariant_joint_continuous.comp
        (show Continuous (fun r : Event × Target => (r.1.1-r.2.1.1,r.2.1.2,Y r)) by fun_prop)
    have hC := (closedMean_continuous q).comp (hi.prodMk continuous_snd.snd)
    have hS : MeasurableSet {r : Event × Target | |r.2.1.2-Y r| ≤ r.1.1-r.2.1.1} :=
      (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
    have he : Measurable (fun r : Event × Target =>
        if |r.2.1.2-Y r| ≤ r.1.1-r.2.1.1 then
          closedMean q (invariant (r.1.1-r.2.1.1) r.2.1.2 (Y r),r.2.2) else 0) :=
      Measurable.ite hS hC.measurable measurable_const
    convert he using 1
    funext r
    by_cases h : |r.2.1.2-Y r| ≤ r.1.1-r.2.1.1
    · simp only [if_pos h,closedMean,nativeRiemannKernel,
        max_eq_right (invariant_causal ⟨_,_,_,h⟩)]
    · simp only [if_neg h]
  have hd := cone (fun r => r.1.2) continuous_fst.snd
  have hi := cone (fun r => -r.1.2) continuous_fst.snd.neg
  simpa only [kernelAt,nativeDirichletCausalKernel,sub_neg_eq_add,Pi.sub_apply] using
    (hd.sub hi).div_const (2:ℂ)

private def sourceWeight (q : XiZeroCopy) (p : Event) : ℝ :=
  Real.exp ((sourceGrowthExponent q-decayExponent q)*p.1)*Real.exp ((2-decayExponent q)*p.2)

private theorem sourceWeight_integrable (q : XiZeroCopy) : Integrable (sourceWeight q) eventMeasure := by
  have hc := decayExponent_bounds q
  have ht := integrableOn_exp_mul_Ioi (show sourceGrowthExponent q-decayExponent q < 0 by linarith) 0
  have hy := (integrableOn_exp_mul_Iic (show 0 < 2-decayExponent q by linarith) 0).mono_set Iio_subset_Iic_self
  exact ht.mul_prod hy

private theorem event_radius_negative : ∀ᵐ p : Event ∂eventMeasure, p.2 < 0 := by
  apply (Measure.ae_prod_iff_ae_ae
    ((isOpen_lt continuous_snd continuous_const).measurableSet : MeasurableSet {p : Event | p.2 < 0})).mpr
  exact ae_of_all _ (fun _ => ae_restrict_mem measurableSet_Iio)

private theorem original_density_bound (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : Event, ∀ r : Target, p.2 < 0 →
      ‖kernelAt q p.1 p.2 r*timeReducedCoefficient (physicalRate q branch) amplitude p.1 p.2‖ ≤
        C*sourceWeight q p*Real.exp (-sourceGrowthExponent q*r.1.1+sourceGrowthExponent q*|r.2.im|) := by
  obtain ⟨C,hC,hK⟩ := kernel_growth q
  obtain ⟨D,hD,hS⟩ := timeReducedCoefficient_physical_bound q branch amplitude _ (decayExponent_bounds q).2
  refine ⟨C*D,mul_nonneg hC hD,?_⟩
  intro p r hy
  by_cases ht : 0 ≤ p.1-r.1.1
  · have h := mul_le_mul (hK (p.1-r.1.1) r.1.2 p.2 r.2.re r.2.im ht)
      (hS p.1 p.2 hy) (norm_nonneg _) (mul_nonneg hC (Real.exp_pos _).le)
    rw [norm_mul]
    apply h.trans_eq
    simp only [sourceWeight,sub_mul,mul_add,mul_sub,neg_mul,Real.exp_add,Real.exp_sub,Real.exp_neg]
    ring
  · have hd : ¬ |r.1.2-p.2| ≤ p.1-r.1.1 := not_le.mpr ((lt_of_not_ge ht).trans_le (abs_nonneg _))
    have hi : ¬ |r.1.2+p.2| ≤ p.1-r.1.1 := not_le.mpr ((lt_of_not_ge ht).trans_le (abs_nonneg _))
    simp only [kernelAt,nativeDirichletCausalKernel,if_neg hd,if_neg hi,sub_self,zero_div,zero_mul,norm_zero]
    dsimp only [sourceWeight]
    positivity

private def originalTestDensity (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ)
    (phi : Target → ℂ) (r : Event × Target) : ℂ :=
  phi r.2*(kernelAt q r.1.1 r.1.2 r.2*
    timeReducedCoefficient (physicalRate q branch) amplitude r.1.1 r.1.2)

/-- Joint absolute admission of the original complete future source and a
compact four-variable test. All angular differentiation stays on the test. -/
theorem originalTestDensity_integrable (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ)
    (phi : Target → ℂ) (hp : Continuous phi) (hc : HasCompactSupport phi) :
    Integrable (originalTestDensity q branch amplitude phi) (eventMeasure.prod volume) := by
  let w : Target → ℝ := fun r => ‖phi r‖*
    Real.exp (-sourceGrowthExponent q*r.1.1+sourceGrowthExponent q*|r.2.im|)
  have hw : Integrable w := by
    apply (hp.norm.mul (by fun_prop)).integrable_of_hasCompactSupport
    exact hc.norm.mul_right
  obtain ⟨C,hC,hb⟩ := original_density_bound q branch amplitude
  have hm := ((sourceWeight_integrable q).mul_prod hw).const_mul C
  have hS := (timeReducedCoefficient_joint_continuous (physicalRate q branch) amplitude).measurable.comp
    (measurable_fst : Measurable (Prod.fst : Event × Target → Event))
  have hmeas : Measurable (originalTestDensity q branch amplitude phi) :=
    (hp.measurable.comp measurable_snd).mul ((source_kernel_measurable q).mul hS)
  apply hm.mono' hmeas.aestronglyMeasurable
  have hn : ∀ᵐ r : Event × Target ∂eventMeasure.prod volume, r.1.2 < 0 := by
    apply (Measure.ae_prod_iff_ae_ae
      ((isOpen_lt continuous_fst.snd continuous_const).measurableSet :
        MeasurableSet {r : Event × Target | r.1.2 < 0})).mpr
    filter_upwards [event_radius_negative] with p hp
    exact ae_of_all _ (fun _ => hp)
  filter_upwards [hn] with r hr
  change ‖phi r.2*(kernelAt q r.1.1 r.1.2 r.2*
    timeReducedCoefficient (physicalRate q branch) amplitude r.1.1 r.1.2)‖ ≤ _
  rw [norm_mul]
  have h := mul_le_mul_of_nonneg_left (hb r.1 r.2 hr) (norm_nonneg (phi r.2))
  refine h.trans_eq ?_
  dsimp only [w]
  ring


private theorem originalTestDensity_source_integral (q : XiZeroCopy) (branch : Bool)
    (amplitude : ℂ) (phi : Target → ℂ) (r : Target) :
    (∫ p : Event, originalTestDensity q branch amplitude phi (p,r) ∂eventMeasure) =
      response q branch amplitude r.1.1 r.1.2 r.2.re r.2.im*phi r := by
  rw [futureResponse_event_integral]
  change (∫ p : Event, phi r*directedSourceDensity q branch amplitude r.1.1 r.1.2 r.2.re r.2.im true p ∂eventMeasure) =
    (∫ p : Event, directedSourceDensity q branch amplitude r.1.1 r.1.2 r.2.re r.2.im true p ∂eventMeasure)*phi r
  rw [integral_const_mul]
  ring

private theorem originalTestDensity_target_integral (q : XiZeroCopy) (branch : Bool)
    (amplitude : ℂ) (phi : Target → ℂ) (p : Event) :
    (∫ r : Target, originalTestDensity q branch amplitude phi (p,r)) =
      timeReducedCoefficient (physicalRate q branch) amplitude p.1 p.2*
        ∫ r : Target, kernelAt q p.1 p.2 r*phi r := by
  have he (r : Target) : originalTestDensity q branch amplitude phi (p,r) =
      timeReducedCoefficient (physicalRate q branch) amplitude p.1 p.2*(kernelAt q p.1 p.2 r*phi r) := by
    unfold originalTestDensity
    ring
  simp_rw [he]
  exact integral_const_mul _ _

/-- The existing original future response acts on every continuous compact
joint target test by an absolutely convergent integral. -/
theorem original_response_test_integrable (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ)
    (phi : Target → ℂ) (hp : Continuous phi) (hc : HasCompactSupport phi) :
    Integrable (fun r : Target => response q branch amplitude r.1.1 r.1.2 r.2.re r.2.im*phi r) := by
  have h := (originalTestDensity_integrable q branch amplitude phi hp hc).integral_prod_right
  simpa only [originalTestDensity_source_integral] using h

/-- Admitted source/target transposition of the actual infinite future
response. The source event, fixed onset, radial ray and angular field are unchanged. -/
theorem original_source_test_fubini (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ)
    (phi : Target → ℂ) (hp : Continuous phi) (hc : HasCompactSupport phi) :
    (∫ r : Target, response q branch amplitude r.1.1 r.1.2 r.2.re r.2.im*phi r) =
      ∫ p : Event, timeReducedCoefficient (physicalRate q branch) amplitude p.1 p.2*
        (∫ r : Target, nativeDirichletCausalKernel q (p.1-r.1.1) r.1.2 p.2 r.2.re r.2.im*phi r)
          ∂eventMeasure := by
  have hi := originalTestDensity_integrable q branch amplitude phi hp hc
  have h := integral_integral_swap (f := fun p r => originalTestDensity q branch amplitude phi (p,r)) hi
  simpa only [originalTestDensity_source_integral,originalTestDensity_target_integral,kernelAt] using h.symm

/-- The literal full-square original source tested in hyperbolic angular area. -/
def forcingTestPair (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ)
    (F : Target → ℂ) (p : Event) : ℂ :=
  timeReducedCoefficient (physicalRate q branch) amplitude p.1 p.2*
    ∫ z : ℂ, (Real.exp (-z.im):ℂ)*fullSquarePotential q ![z.re,Real.exp z.im]*F (p,z)

/-- Absolute source admission of the forcing side of the full weak equation. -/
theorem forcingTestPair_integrable (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ)
    (F : Target → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hphysical : tsupport F ⊆ {r : Target | r.1.2 < 0}) :
    Integrable (forcingTestPair q branch amplitude F) eventMeasure := by
  have hr := weakWaveTest_regular F hF hc
  have h := (originalTestDensity_integrable q branch amplitude (weakWaveTest F) hr.1 hr.2).integral_prod_left
  apply h.congr
  filter_upwards [event_radius_negative] with p hp
  rw [originalTestDensity_target_integral]
  change timeReducedCoefficient (physicalRate q branch) amplitude p.1 p.2*
    (∫ r : Target, nativeDirichletCausalKernel q (p.1-r.1.1) r.1.2 p.2 r.2.re r.2.im*weakWaveTest F r) = _
  rw [kernel_joint_transposition q p.1 p.2 hp F hF hc hphysical]
  rfl

/-- The actual infinite future response satisfies the original full weak wave
equation for every joint smooth compact test in the physical half-plane.
No wave equation, source admission or matching premise is supplied. -/
theorem original_future_weak_wave (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ)
    (F : Target → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hphysical : tsupport F ⊆ {r : Target | r.1.2 < 0}) :
    (∫ r : Target, response q branch amplitude r.1.1 r.1.2 r.2.re r.2.im*weakWaveTest F r) =
      ∫ p : Event, forcingTestPair q branch amplitude F p ∂eventMeasure := by
  have hr := weakWaveTest_regular F hF hc
  rw [original_source_test_fubini q branch amplitude (weakWaveTest F) hr.1 hr.2]
  apply integral_congr_ae
  filter_upwards [event_radius_negative] with p hp
  rw [kernel_joint_transposition q p.1 p.2 hp F hF hc hphysical]
  rfl

end
end RHTower.D4BMFullSourceWeakWave
