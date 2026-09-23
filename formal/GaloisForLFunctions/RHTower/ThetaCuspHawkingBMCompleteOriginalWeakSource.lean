import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCapWeakWave

/-!
The original source lift, infinite future response and source-derived horizon cap
satisfy the complete original forcing equation against every smooth compact joint
test supported in the physical radial half-plane. All field and source pairings
are absolutely integrable; the source onset and angular-gradient terms are retained.
-/

open MeasureTheory Set Filter Topology
namespace RHTower.D4BMCompleteOriginalWeakSource
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open D4BMNativeCircle D4BMCausalKernel D4BMModularCore D4BMHorizon D4BMJointSource
open D4BMGeneralTemporalTransposition D4BMAdvancedKernelTransposition D4BMFullSourceWeakWave
open D4BMFullSourceReciprocity D4BMFullSourceAdvanced D4BMFutureHorizon D4BMOriginalCapWave
open scoped ContDiff ENNReal
noncomputable section
set_option autoImplicit false

private def square (q : XiZeroCopy) (z : ℂ) : ℂ :=
  fullSquarePotential q ![z.re,Real.exp z.im]

private def lapSquare (q : XiZeroCopy) (z : ℂ) : ℂ :=
  scalarLaplacian (fullSquarePotential q) ![z.re,Real.exp z.im]

private def radial (s a : ℂ) (p : Event) : ℂ := timeRadialLift s a p.1 p.2

private theorem radial_smooth (s a : ℂ) : ContDiff ℝ ∞ (radial s a) := by
  have hu : ContDiff ℝ ∞ radialUnit := by
    unfold radialUnit
    exact Real.contDiff_sinh.neg.div Real.contDiff_cosh (fun t => (Real.cosh_pos t).ne')
  have hlog : ContDiff ℝ ∞ (fun t => Real.log (1+radialUnit t)) :=
    (contDiff_const.add hu).log (fun t => (radialUnit_add_one_pos t).ne')
  have he (t : ℝ) : D4BMLaplaceRadial.power (2*s) (1+radialUnit t)=
      Complex.exp ((Real.log (1+radialUnit t):ℂ)*(2*s)) := by
    rw [D4BMLaplaceRadial.power,Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (radialUnit_add_one_pos t).ne'),← Complex.ofReal_log (radialUnit_add_one_pos t).le]
  have hpow : ContDiff ℝ ∞ (fun t => D4BMLaplaceRadial.power (2*s) (1+radialUnit t)) := by
    simp_rw [he]
    exact ((Complex.ofRealCLM.contDiff.comp hlog).mul contDiff_const).cexp
  have hl : ContDiff ℝ ∞ (radialLift s 0 a 1) := by
    unfold radialLift sourceAmplitude
    exact contDiff_const.mul
      ((((contDiff_const.mul Complex.ofRealCLM.contDiff).cexp.mul hpow).mul contDiff_const).mul
        contDiff_const |>.mul ((Complex.ofRealCLM.contDiff.comp hu).pow 3))
  have ht : ContDiff ℝ ∞ (timeOnset (2*s)) := by
    unfold timeOnset
    exact (Complex.ofRealCLM.contDiff.comp Real.smoothTransition.contDiff).mul
      ((contDiff_const.mul Complex.ofRealCLM.contDiff).cexp)
  exact (hl.comp contDiff_snd).mul (ht.comp (contDiff_fst.add contDiff_snd))

private theorem square_smooth (q : XiZeroCopy) : ContDiff ℝ ∞ (square q) := by
  have h : ContDiff ℝ ∞ ((fun v : ℝ × ℝ × ℝ => mean q v.1 v.2.1 v.2.2) ∘
      (fun z : ℂ => ((0:ℝ),z.re,z.im))) :=
    (D4BMNativeResponse.nativeMean_joint_smooth q).comp
      (contDiff_const.prodMk (Complex.reCLM.contDiff.prodMk Complex.imCLM.contDiff))
  have he : ((fun v : ℝ × ℝ × ℝ => mean q v.1 v.2.1 v.2.2) ∘
      (fun z : ℂ => ((0:ℝ),z.re,z.im)))=square q := by
    funext z
    exact mean_zero q z.re z.im
  rw [he] at h
  exact h

private theorem lapSquare_continuous (q : XiZeroCopy) : Continuous (lapSquare q) := by
  let Z : ℂ → Point := fun z => ![z.re,Real.exp z.im]
  have hz : Continuous Z := by fun_prop
  apply continuous_iff_continuousAt.mpr
  intro z
  have hp : 0 < Z z 1 := Real.exp_pos _
  have hs : ContDiffAt ℝ ∞ (fullSquarePotential q) (Z z) :=
    contDiffAt_infty.mpr (fun n => fullSquarePotential_smooth q _ hp n)
  have hj (i : Fin 2) : ContinuousAt (coordDeriv i (coordDeriv i (fullSquarePotential q))) (Z z) :=
    (coordDeriv_contDiffAt (m := ∞)
      (by simpa using coordDeriv_contDiffAt (m := ∞) (by simpa using hs) i) i).continuousAt
  have he : lapSquare q = fun w => (Z w 1:ℂ)^(2 : ℕ)*
      (coordDeriv 0 (coordDeriv 0 (fullSquarePotential q)) (Z w)+
        coordDeriv 1 (coordDeriv 1 (fullSquarePotential q)) (Z w)) :=
    funext (fun w => scalarLaplacian_eq _ _ (Real.exp_pos w.im))
  rw [he]
  exact ((Complex.continuous_ofReal.comp ((continuous_apply 1).comp hz)).pow 2).continuousAt.mul
    (((hj 0).comp_of_eq (hz.continuousAt (x := z)) rfl).add
      ((hj 1).comp_of_eq (hz.continuousAt (x := z)) rfl))

private theorem angularAction_one (q : XiZeroCopy) (z : ℂ) :
    angularAction q 1 z.re z.im=lapSquare q z := by
  have h := mean_laplacian_commutes q 0 z.re z.im
  have he : (fun theta => scalarLaplacian (fullSquarePotential q) (logCircle 0 theta z.re z.im))=
      fun _ => lapSquare q z := by
    funext theta
    simp [logCircle,circle,offset,height,denominator,lapSquare]
  rw [he] at h
  have hconst (c : ℂ) : D4BMNativeCircle.average (fun _ => c)=c := by
    have hpi : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    unfold D4BMNativeCircle.average
    rw [← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi)]
    simp only [intervalIntegral.integral_const,sub_zero,Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_ofNat]
    field_simp [hpi]
  rw [hconst] at h
  simpa only [angularAction,angularKernel,Real.arcosh_zero,lapSquare] using h

private theorem square_angular_transposition (q : XiZeroCopy) (phi : ℂ → ℂ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    (∫ z : ℂ, angularTestAction phi z*square q z) =
      ∫ z : ℂ, (Real.exp (-z.im):ℂ)*phi z*lapSquare q z := by
  have h := angularAction_compact_transposition q 1 phi hp hc
  simpa only [angularAction_one,angularKernel,Real.arcosh_zero,mean_zero,square] using h.symm

private theorem eventDir_smooth {G : Event → ℂ} (hG : ContDiff ℝ ∞ G) (v : Event) :
    ContDiff ℝ ∞ (eventDir v G) :=
  (hG.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private theorem eventWave_smooth {G : Event → ℂ} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (eventWave G) :=
  (eventDir_smooth (eventDir_smooth hG (1,0)) (1,0)).sub
    (eventDir_smooth (eventDir_smooth hG (0,1)) (0,1))

private theorem event_first_pair (phi G : Event → ℂ) (v : Event)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) (hG : ContDiff ℝ ∞ G) :
    (∫ p : Event, phi p*eventDir v G p) = -(∫ p : Event, eventDir v phi p*G p) := by
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (((eventDir_smooth hp v).continuous.mul hG.continuous).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ v).mul_right)
    ((hp.continuous.mul (eventDir_smooth hG v).continuous).integrable_of_hasCompactSupport hc.mul_right)
    ((hp.continuous.mul hG.continuous).integrable_of_hasCompactSupport hc.mul_right)
    (fun p _ => hp.differentiable (by simp) p)
    (fun p _ => hG.differentiable (by simp) p)

private theorem event_second_pair (phi G : Event → ℂ) (v : Event)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) (hG : ContDiff ℝ ∞ G) :
    (∫ p : Event, phi p*eventDir v (eventDir v G) p) =
      ∫ p : Event, eventDir v (eventDir v phi) p*G p := by
  rw [event_first_pair phi (eventDir v G) v hp hc (eventDir_smooth hG v),
    event_first_pair (eventDir v phi) G v (eventDir_smooth hp v) (hc.fderiv_apply ℝ v) hG,neg_neg]

private theorem event_wave_pair (phi G : Event → ℂ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) (hG : ContDiff ℝ ∞ G) :
    (∫ p : Event, G p*eventWave phi p)=∫ p : Event, eventWave G p*phi p := by
  have hi (v : Event) : Integrable (fun p => phi p*eventDir v (eventDir v G) p) :=
    (hp.continuous.mul (eventDir_smooth (eventDir_smooth hG v) v).continuous).integrable_of_hasCompactSupport hc.mul_right
  have hj (v : Event) : Integrable (fun p => eventDir v (eventDir v phi) p*G p) :=
    ((eventDir_smooth (eventDir_smooth hp v) v).continuous.mul hG.continuous).integrable_of_hasCompactSupport
      ((hc.fderiv_apply ℝ v).fderiv_apply ℝ v).mul_right
  have h : (∫ p : Event, phi p*eventWave G p)=∫ p : Event, eventWave phi p*G p := by
    simp only [eventWave,mul_sub,sub_mul]
    rw [integral_sub (hi (1,0)) (hi (0,1)),integral_sub (hj (1,0)) (hj (0,1)),
      event_second_pair phi G (1,0) hp hc hG,event_second_pair phi G (0,1) hp hc hG]
  simpa only [mul_comm] using h.symm

private theorem event_line_first (G : Event → ℂ) (hG : ContDiff ℝ ∞ G)
    (l : ℝ → Event) (v : Event) (hl : ∀ a, HasDerivAt l v a) (a : ℝ) :
    eventDir v G (l a)=deriv (fun r => G (l r)) a :=
  ((hG.differentiable (by simp) (l a)).hasFDerivAt.comp_hasDerivAt a (hl a)).deriv.symm

private theorem event_line_second (G : Event → ℂ) (hG : ContDiff ℝ ∞ G)
    (l : ℝ → Event) (v : Event) (hl : ∀ a, HasDerivAt l v a) (a : ℝ) :
    eventDir v (eventDir v G) (l a)=deriv (deriv (fun r => G (l r))) a := by
  have he : (fun r => eventDir v G (l r))=deriv (fun r => G (l r)) := funext (event_line_first G hG l v hl)
  rw [event_line_first (eventDir v G) (eventDir_smooth hG v) l v hl a,he]

private theorem radial_wave_actual (s a : ℂ) (p : Event) :
    eventWave (radial s a) p =
      deriv (deriv (fun tau => timeRadialLift s a tau p.2)) p.1-
        deriv (deriv (timeRadialLift s a p.1)) p.2 := by
  have ht (r : ℝ) : HasDerivAt (fun t : ℝ => (t,p.2)) ((1,0):Event) r :=
    (hasDerivAt_id r).prodMk (hasDerivAt_const r p.2)
  have hx (r : ℝ) : HasDerivAt (fun x : ℝ => (p.1,x)) ((0,1):Event) r :=
    (hasDerivAt_const r p.1).prodMk (hasDerivAt_id r)
  have h1 := event_line_second _ (radial_smooth s a) _ (1,0) ht p.1
  have h2 := event_line_second _ (radial_smooth s a) _ (0,1) hx p.2
  exact congrArg₂ (fun z w : ℂ => z-w) h1 h2

private def jointDir (v : Target) (F : Target → ℂ) (p : Target) : ℂ := fderiv ℝ F p v

private theorem jointDir_smooth {F : Target → ℂ} (hF : ContDiff ℝ ∞ F) (v : Target) :
    ContDiff ℝ ∞ (jointDir v F) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private theorem event_slice_dir (F : Target → ℂ) (hF : ContDiff ℝ ∞ F)
    (p : Event) (z : ℂ) (v : Event) :
    eventDir v (fun r => F (r,z)) p=jointDir (v,0) F (p,z) := by
  have he : HasFDerivAt (fun r : Event => (r,z))
      ((ContinuousLinearMap.id ℝ Event).prod (0 : Event →L[ℝ] ℂ)) p :=
    (hasFDerivAt_id p).prodMk (hasFDerivAt_const z p)
  have h := ((hF.differentiable (by simp) (p,z)).hasFDerivAt.comp p he).fderiv
  dsimp only [Function.comp_def] at h
  unfold eventDir jointDir
  rw [h]
  rfl

private theorem event_slice_second (F : Target → ℂ) (hF : ContDiff ℝ ∞ F)
    (p : Event) (z : ℂ) (v : Event) :
    eventDir v (eventDir v (fun r => F (r,z))) p=jointDir (v,0) (jointDir (v,0) F) (p,z) := by
  have he : eventDir v (fun r => F (r,z))=fun r => jointDir (v,0) F (r,z) :=
    funext (fun r => event_slice_dir F hF r z v)
  rw [he,event_slice_dir _ (jointDir_smooth hF (v,0))]

private theorem temporal_test_regular (F : Target → ℂ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) :
    ContDiff ℝ ∞ (fun r : Target => eventWave (fun p => F (p,r.2)) r.1) ∧
      HasCompactSupport (fun r : Target => eventWave (fun p => F (p,r.2)) r.1) := by
  have he : (fun r : Target => eventWave (fun p => F (p,r.2)) r.1)=
      fun r => jointDir ((1,0),0) (jointDir ((1,0),0) F) r-
        jointDir ((0,1),0) (jointDir ((0,1),0) F) r := by
    funext r
    unfold eventWave
    rw [event_slice_second F hF,event_slice_second F hF]
  rw [he]
  exact ⟨(jointDir_smooth (jointDir_smooth hF ((1,0),0)) ((1,0),0)).sub
    (jointDir_smooth (jointDir_smooth hF ((0,1),0)) ((0,1),0)),
    ((hc.fderiv_apply ℝ ((1,0),0)).fderiv_apply ℝ ((1,0),0)).sub
      ((hc.fderiv_apply ℝ ((0,1),0)).fderiv_apply ℝ ((0,1),0))⟩

private theorem event_slice_compact {F : Target → ℂ} (hc : HasCompactSupport F) (z : ℂ) :
    HasCompactSupport (fun p : Event => F (p,z)) := by
  apply hc.comp_isClosedEmbedding
  refine ⟨isEmbedding_prodMkLeft z,?_⟩
  have he : Set.range (fun p : Event => (p,z))=Set.univ ×ˢ ({z}:Set ℂ) := by
    ext ⟨p,w⟩
    simp [eq_comm]
  rw [he]
  exact isClosed_univ.prod isClosed_singleton

private theorem angular_slice_compact {F : Target → ℂ} (hc : HasCompactSupport F) (p : Event) :
    HasCompactSupport (fun z : ℂ => F (p,z)) := by
  apply hc.comp_isClosedEmbedding
  refine ⟨isEmbedding_prodMkRight p,?_⟩
  have he : Set.range (fun z : ℂ => (p,z))=({p}:Set Event) ×ˢ Set.univ := by
    ext ⟨r,z⟩
    simp [eq_comm]
  rw [he]
  exact isClosed_singleton.prod isClosed_univ

private theorem target_fubini (F : Target → ℂ) (hi : Integrable F) :
    (∫ r : Target, F r)=∫ p : Event, ∫ z : ℂ, F (p,z) := by
  rw [Measure.volume_eq_prod] at hi ⊢
  exact integral_prod F hi

private theorem target_fubini_swap (F : Target → ℂ) (hi : Integrable F) :
    (∫ r : Target, F r)=∫ z : ℂ, ∫ p : Event, F (p,z) := by
  rw [Measure.volume_eq_prod] at hi ⊢
  exact integral_prod_symm F hi

private def liftField (q : XiZeroCopy) (branch : Bool) (a : ℂ) (r : Target) : ℂ :=
  radial (physicalRate q branch) a r.1*square q r.2

private def liftWave (q : XiZeroCopy) (branch : Bool) (a : ℂ) (r : Target) : ℂ :=
  eventWave (radial (physicalRate q branch) a) r.1*square q r.2-
    radial (physicalRate q branch) a r.1*lapSquare q r.2/(Real.cosh r.1.2:ℂ)^(2 : ℕ)

private theorem liftField_continuous (q : XiZeroCopy) (branch : Bool) (a : ℂ) :
    Continuous (liftField q branch a) :=
  ((radial_smooth _ _).continuous.comp continuous_fst).mul ((square_smooth q).continuous.comp continuous_snd)

private theorem liftWave_continuous (q : XiZeroCopy) (branch : Bool) (a : ℂ) :
    Continuous (liftWave q branch a) :=
  (((eventWave_smooth (radial_smooth _ _)).continuous.comp continuous_fst).mul
    ((square_smooth q).continuous.comp continuous_snd)).sub
    ((((radial_smooth _ _).continuous.comp continuous_fst).mul
      ((lapSquare_continuous q).comp continuous_snd)).div (by fun_prop)
        (fun r => pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne')))

private theorem radial_metric (x : ℝ) : 1-(radialUnit x:ℂ)^(2 : ℕ)=1/(Real.cosh x:ℂ)^(2 : ℕ) := by
  have hn : (Real.cosh x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.cosh_pos x).ne'
  have he : (Real.cosh x:ℂ)^(2 : ℕ)-(Real.sinh x:ℂ)^(2 : ℕ)=1 := by exact_mod_cast Real.cosh_sq_sub_sinh_sq x
  dsimp only [radialUnit]
  simp only [Complex.ofReal_div,Complex.ofReal_neg]
  field_simp [hn]
  linear_combination he

private theorem liftWave_actual (q : XiZeroCopy) (branch : Bool) (a : ℂ) (r : Target) :
    liftWave q branch a r=timeFieldWave (timeLiftField q branch a) r.1.1 r.1.2 ![r.2.re,Real.exp r.2.im] := by
  rw [timeLiftField_wave q branch a _ _ _ (Real.exp_pos _),separatedScalarWave,
    (radialLift_derivatives (physicalRate q branch) 0 a 1).2,radial_metric]
  unfold liftWave
  rw [radial_wave_actual,timeRadialLift_wave]
  dsimp only [radial,timeRadialLift,square,lapSquare]
  ring

private theorem original_forcing_eq (q : XiZeroCopy) (branch : Bool) (a : ℂ) (r : Target) :
    timeOriginalForcing q branch a r.1.1 r.1.2 ![r.2.re,Real.exp r.2.im] =
      liftWave q branch a r+timeReducedCoefficient (physicalRate q branch) a r.1.1 r.1.2*square q r.2 := by
  rw [liftWave_actual]
  exact timeOriginalForcing_gradient_absorption q branch a _ _ _ (Real.exp_pos _)

/-- The unchanged source lift has an admitted pairing with every compact joint test. -/
theorem original_lift_test_integrable (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (phi : Target → ℂ) (hp : Continuous phi) (hc : HasCompactSupport phi) :
    Integrable (fun r : Target => timeLiftField q branch a r.1.1 r.1.2 ![r.2.re,Real.exp r.2.im]*phi r) :=
  ((liftField_continuous q branch a).mul hp).integrable_of_hasCompactSupport hc.mul_left

/-- The original source lift obeys its actual full weak wave identity on general
joint target tests, retaining the original hyperbolic area and radial coefficient. -/
theorem original_lift_weak_wave (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (F : Target → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    (∫ r : Target, timeLiftField q branch a r.1.1 r.1.2 ![r.2.re,Real.exp r.2.im]*weakWaveTest F r) =
      ∫ r : Target, (Real.exp (-r.2.im):ℂ)*
        timeFieldWave (timeLiftField q branch a) r.1.1 r.1.2 ![r.2.re,Real.exp r.2.im]*F r := by
  let G := radial (physicalRate q branch) a
  have hG : ContDiff ℝ ∞ G := radial_smooth _ _
  let W := fun r : Target => (Real.exp (-r.2.im):ℂ)*eventWave (fun p => F (p,r.2)) r.1
  let A := fun r : Target => angularTestAction (fun z => F (r.1,z)) r.2/(Real.cosh r.1.2:ℂ)^(2 : ℕ)
  let D := fun r : Target => (Real.exp (-r.2.im):ℂ)*eventWave G r.1*square q r.2*F r
  let B := fun r : Target => (Real.exp (-r.2.im):ℂ)*G r.1*lapSquare q r.2/(Real.cosh r.1.2:ℂ)^(2 : ℕ)*F r
  have hweight : Continuous (fun r : Target => (Real.exp (-r.2.im):ℂ)) := by fun_prop
  obtain ⟨hTW,hcTW⟩ := temporal_test_regular F hF hc
  have hW : Continuous W := hweight.mul hTW.continuous
  have hcW : HasCompactSupport W := hcTW.mul_left
  have htest := weakWaveTest_regular F hF hc
  have hAW : A=fun r => W r-weakWaveTest F r := by
    funext r
    dsimp only [A,W,weakWaveTest]
    ring
  have hA : Continuous A := by rw [hAW]; exact hW.sub htest.1
  have hcA : HasCompactSupport A := by rw [hAW]; exact hcW.sub htest.2
  have hLW : Integrable (fun r => liftField q branch a r*W r) :=
    ((liftField_continuous q branch a).mul hW).integrable_of_hasCompactSupport hcW.mul_left
  have hLA : Integrable (fun r => liftField q branch a r*A r) :=
    ((liftField_continuous q branch a).mul hA).integrable_of_hasCompactSupport hcA.mul_left
  have hD : Integrable D :=
    (((hweight.mul ((eventWave_smooth hG).continuous.comp continuous_fst)).mul
      ((square_smooth q).continuous.comp continuous_snd)).mul hF.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hB : Integrable B :=
    (((((hweight.mul (hG.continuous.comp continuous_fst)).mul
      ((lapSquare_continuous q).comp continuous_snd)).div (by fun_prop)
        (fun r => pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'))).mul
          hF.continuous).integrable_of_hasCompactSupport hc.mul_left)
  have htemporal : (∫ r : Target, liftField q branch a r*W r)=∫ r : Target, D r := by
    rw [target_fubini_swap _ hLW,target_fubini_swap _ hD]
    apply integral_congr_ae
    filter_upwards with z
    let phi : Event → ℂ := fun p => F (p,z)
    have hp : ContDiff ℝ ∞ phi := hF.comp (contDiff_id.prodMk contDiff_const)
    have he1 (p : Event) : liftField q branch a (p,z)*W (p,z)=
        ((Real.exp (-z.im):ℂ)*square q z)*(G p*eventWave phi p) := by
      dsimp only [liftField,W,G,phi]
      ring
    have he2 (p : Event) : D (p,z)=((Real.exp (-z.im):ℂ)*square q z)*(eventWave G p*phi p) := by
      dsimp only [D,phi]
      ring
    simp_rw [he1,he2]
    rw [integral_const_mul,integral_const_mul,event_wave_pair phi G hp (event_slice_compact hc z) hG]
  have hangular : (∫ r : Target, liftField q branch a r*A r)=∫ r : Target, B r := by
    rw [target_fubini _ hLA,target_fubini _ hB]
    apply integral_congr_ae
    filter_upwards with p
    let phi : ℂ → ℂ := fun z => F (p,z)
    have hp : ContDiff ℝ ∞ phi := hF.comp (contDiff_const.prodMk contDiff_id)
    have he1 (z : ℂ) : liftField q branch a (p,z)*A (p,z)=
        (G p/(Real.cosh p.2:ℂ)^(2 : ℕ))*(angularTestAction phi z*square q z) := by
      dsimp only [liftField,A,G,phi]
      ring
    have he2 (z : ℂ) : B (p,z)=(G p/(Real.cosh p.2:ℂ)^(2 : ℕ))*
        ((Real.exp (-z.im):ℂ)*phi z*lapSquare q z) := by
      dsimp only [B,phi]
      ring
    simp_rw [he1,he2]
    rw [integral_const_mul,integral_const_mul,square_angular_transposition q phi hp (angular_slice_compact hc p)]
  have he (r : Target) : weakWaveTest F r=W r-A r := rfl
  change (∫ r : Target, liftField q branch a r*weakWaveTest F r)=_
  simp_rw [he,mul_sub]
  rw [integral_sub hLW hLA,htemporal,hangular,← integral_sub hD hB]
  apply integral_congr_ae
  exact ae_of_all _ (fun r => by
    dsimp only
    rw [← liftWave_actual]
    dsimp only [D,B,liftWave,G]
    ring)

private def reducedTestDensity (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (F : Target → ℂ) (r : Target) : ℂ :=
  (Real.exp (-r.2.im):ℂ)*timeReducedCoefficient (physicalRate q branch) a r.1.1 r.1.2*square q r.2*F r

private theorem reducedTestDensity_integrable (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (F : Target → ℂ) (hF : Continuous F) (hc : HasCompactSupport F) :
    Integrable (reducedTestDensity q branch a F) := by
  have hS := (timeReducedCoefficient_joint_continuous (physicalRate q branch) a).comp
    (continuous_fst : Continuous (Prod.fst : Target → Event))
  exact (((((by fun_prop : Continuous (fun r : Target => (Real.exp (-r.2.im):ℂ))).mul hS).mul
    ((square_smooth q).continuous.comp continuous_snd)).mul hF).integrable_of_hasCompactSupport hc.mul_left)

/-- The reduced source-event pairing is exactly the full target pairing:
the original onset and the physical test support supply both domain restrictions. -/
theorem reduced_forcing_target_pair (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (F : Target → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hphysical : tsupport F ⊆ {r : Target | r.1.2 < 0}) :
    (∫ p : Event, forcingTestPair q branch a F p ∂eventMeasure) =
      ∫ r : Target, (Real.exp (-r.2.im):ℂ)*timeReducedCoefficient (physicalRate q branch) a r.1.1 r.1.2*
        fullSquarePotential q ![r.2.re,Real.exp r.2.im]*F r := by
  let D := reducedTestDensity q branch a F
  have hi : Integrable D := reducedTestDensity_integrable q branch a F hF.continuous hc
  have he (p : Event) : forcingTestPair q branch a F p=∫ z : ℂ, D (p,z) := by
    unfold forcingTestPair
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun z => by dsimp only [D,reducedTestDensity,square]; ring)
  simp_rw [he]
  rw [eventMeasure,Measure.prod_restrict,← Measure.volume_eq_prod]
  have hz (p : Event) (hp : p ∉ (Ioi (0:ℝ)) ×ˢ (Iio (0:ℝ))) (z : ℂ) : D (p,z)=0 := by
    by_cases hx : p.2 < 0
    · have ht : p.1 ≤ 0 := le_of_not_gt (fun h => hp ⟨h,hx⟩)
      have hs := timeReducedCoefficient_zero_before_onset (physicalRate q branch) a p.1 p.2 (by linarith)
      simp only [D,reducedTestDensity,hs,mul_zero,zero_mul]
    · have hf : F (p,z)=0 := by
        by_contra hn
        exact hx (hphysical (subset_tsupport F hn))
      simp only [D,reducedTestDensity,hf,mul_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by simp only [hz p hp,integral_zero])]
  exact (target_fubini D hi).symm

/-- Original corrected future field: fixed source lift, actual infinite future
response, and original source-derived horizon cap. -/
def correctedFutureField (q : XiZeroCopy) (branch : Bool) (a : ℂ) (r : Target) : ℂ :=
  timeLiftField q branch a r.1.1 r.1.2 ![r.2.re,Real.exp r.2.im]+
    response q branch a r.1.1 r.1.2 r.2.re r.2.im-capBoundaryField q branch a r.1.1 r.1.2 r.2.re r.2.im

/-- Absolute admission of the complete original forcing against compact joint tests. -/
theorem original_forcing_test_integrable (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (F : Target → ℂ) (hF : Continuous F) (hc : HasCompactSupport F) :
    Integrable (fun r : Target => (Real.exp (-r.2.im):ℂ)*
      timeOriginalForcing q branch a r.1.1 r.1.2 ![r.2.re,Real.exp r.2.im]*F r) := by
  have hS := ((timeReducedCoefficient_joint_continuous (physicalRate q branch) a).comp
    (continuous_fst : Continuous (Prod.fst : Target → Event))).mul
      ((square_smooth q).continuous.comp continuous_snd)
  simp_rw [original_forcing_eq]
  have hweight : Continuous (fun r : Target => (Real.exp (-r.2.im):ℂ)) := by fun_prop
  have hbody := (hweight.mul ((liftWave_continuous q branch a).add hS)).mul hF
  exact hbody.integrable_of_hasCompactSupport hc.mul_left

/-- The complete corrected field has an absolutely convergent action on every compact joint test. -/
theorem corrected_future_test_integrable (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (phi : Target → ℂ) (hp : Continuous phi) (hc : HasCompactSupport phi) :
    Integrable (fun r : Target => correctedFutureField q branch a r*phi r) := by
  have h := ((original_lift_test_integrable q branch a phi hp hc).add
    (original_response_test_integrable q branch a phi hp hc)).sub (cap_test_integrable q branch a phi hp hc)
  apply h.congr
  exact ae_of_all _ (fun r => by
    dsimp only [Pi.add_apply,Pi.sub_apply,correctedFutureField]
    ring)

/-- The actual lift-plus-future-minus-cap field satisfies the complete original
forcing equation for every general joint compact physical test. No forcing,
wave-equation, convergence or metric-matching premise is supplied. -/
theorem complete_original_weak_wave (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (F : Target → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hphysical : tsupport F ⊆ {r : Target | r.1.2 < 0}) :
    (∫ r : Target, correctedFutureField q branch a r*weakWaveTest F r)=
      ∫ r : Target, (Real.exp (-r.2.im):ℂ)*
        timeOriginalForcing q branch a r.1.1 r.1.2 ![r.2.re,Real.exp r.2.im]*F r := by
  have hr := weakWaveTest_regular F hF hc
  have he (r : Target) : correctedFutureField q branch a r*weakWaveTest F r=
      timeLiftField q branch a r.1.1 r.1.2 ![r.2.re,Real.exp r.2.im]*weakWaveTest F r+
        (response q branch a r.1.1 r.1.2 r.2.re r.2.im-
          capBoundaryField q branch a r.1.1 r.1.2 r.2.re r.2.im)*weakWaveTest F r := by
    unfold correctedFutureField
    ring
  simp_rw [he]
  have hRC : Integrable (fun r : Target =>
      (response q branch a r.1.1 r.1.2 r.2.re r.2.im-
        capBoundaryField q branch a r.1.1 r.1.2 r.2.re r.2.im)*weakWaveTest F r) := by
    apply ((original_response_test_integrable q branch a _ hr.1 hr.2).sub
      (cap_test_integrable q branch a _ hr.1 hr.2)).congr
    exact ae_of_all _ (fun r => by
      dsimp only [Pi.sub_apply]
      ring)
  rw [integral_add (original_lift_test_integrable q branch a _ hr.1 hr.2) hRC]
  rw [original_lift_weak_wave q branch a F hF hc,
    original_future_sub_cap_weak_wave q branch a F hF hc hphysical,
    reduced_forcing_target_pair q branch a F hF hc hphysical]
  have hl : Integrable (fun r : Target => (Real.exp (-r.2.im):ℂ)*
      timeFieldWave (timeLiftField q branch a) r.1.1 r.1.2 ![r.2.re,Real.exp r.2.im]*F r) := by
    simp_rw [← liftWave_actual]
    have hweight : Continuous (fun r : Target => (Real.exp (-r.2.im):ℂ)) := by fun_prop
    have hbody := (hweight.mul (liftWave_continuous q branch a)).mul hF.continuous
    exact hbody.integrable_of_hasCompactSupport hc.mul_left
  have hs : Integrable (fun r : Target =>
      (Real.exp (-r.2.im):ℂ)*timeReducedCoefficient (physicalRate q branch) a r.1.1 r.1.2*
        fullSquarePotential q ![r.2.re,Real.exp r.2.im]*F r) :=
    reducedTestDensity_integrable q branch a F hF.continuous hc
  rw [← integral_add hl hs]
  apply integral_congr_ae
  exact ae_of_all _ (fun r => by
    dsimp only
    rw [timeOriginalForcing_gradient_absorption q branch a _ _ _ (Real.exp_pos _)]
    ring)

end
end RHTower.D4BMCompleteOriginalWeakSource
