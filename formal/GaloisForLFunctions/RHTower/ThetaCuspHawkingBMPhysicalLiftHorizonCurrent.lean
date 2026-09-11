import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedRadialActionCurrent
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceTimeField

/-! The original fixed source lift's physical Einstein current in ingoing coordinates. -/
namespace RHTower.D4BMPhysicalLiftCurrent
open GaloisForLFunctions.HTGeometry D4BMMixedActionCurrent D4BMJointSource
open D4BMModularCore D4BMLaplaceRadial D4BMHorizon Set Filter Topology MeasureTheory
noncomputable section
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Original stream-lift radial coefficient, before its actual ingoing clock. -/
def profile (s a : ℂ) (r : ℝ) : ℂ :=
  (-s*(s-1)/4)*a^2*(r:ℂ)⁻¹^2*power (2*s) (1+r⁻¹)
private def rate (s : ℂ) (r : ℝ) : ℂ := -(2+2*s)/(r:ℂ)+2*s/(1+(r:ℂ))
private def rateFirst (s : ℂ) (r : ℝ) : ℂ := (2+2*s)/(r:ℂ)^2-2*s/(1+(r:ℂ))^2
/-- First original radial derivative at fixed ingoing time. -/
def profileFirst (s a : ℂ) (r : ℝ) : ℂ := profile s a r*rate s r
/-- Second original radial derivative at fixed ingoing time. -/
def profileSecond (s a : ℂ) (r : ℝ) : ℂ := profile s a r*((rate s r)^2+rateFirst s r)

private theorem profile_hasDerivAt (s a : ℂ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (profile s a) (profileFirst s a r) r := by
  have hi := hasDerivAt_inv hr.ne'
  have hp := (power_derivatives (2*s) (show 0 < 1+r⁻¹ by positivity)).1.scomp r (hi.const_add 1)
  have hc := hi.ofReal_comp
  convert! (((hc.pow 2).const_mul ((-s*(s-1)/4)*a^2)).mul hp) using 1
  · funext x
    simp [profile]
  dsimp only [profileFirst,profile,rate,powerFirst,Function.comp_apply,id_eq]
  simp only [Complex.real_smul,Pi.pow_apply]
  have hn : (r:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hn1 : 1+(r:ℂ) ≠ 0 := by exact_mod_cast (show 1+r ≠ 0 by positivity)
  have hn2 : 1+(r:ℂ)⁻¹ ≠ 0 := by exact_mod_cast (show 1+r⁻¹ ≠ 0 by positivity)
  push_cast
  field_simp [hn,hn1,hn2]
  ring_nf
  field_simp [hn1]
  ring

private theorem rate_hasDerivAt (s : ℂ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (rate s) (rateFirst s r) r := by
  have h0 := (hasDerivAt_inv hr.ne').ofReal_comp
  have h1 := ((hasDerivAt_inv (show 1+r ≠ 0 by positivity)).comp r
    ((hasDerivAt_id r).const_add 1)).ofReal_comp
  convert! (h0.const_mul (-(2+2*s))).add (h1.const_mul (2*s)) using 1
  · funext x
    simp [rate,div_eq_mul_inv]
  · dsimp [rateFirst,Function.comp_def]
    push_cast
    ring

private theorem profileFirst_hasDerivAt (s a : ℂ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (profileFirst s a) (profileSecond s a r) r := by
  apply ((profile_hasDerivAt s a hr).mul (rate_hasDerivAt s hr)).congr_deriv
  dsimp only [profileFirst,profileSecond]
  ring

/-- Both original radial jets are actual derivatives throughout the positive-radius chart. -/
theorem profile_derivatives (s a : ℂ) (r : Ioi (0:ℝ)) :
    HasDerivAt (profile s a) (profileFirst s a r) r.val ∧
    HasDerivAt (profileFirst s a) (profileSecond s a r) r.val :=
  ⟨profile_hasDerivAt s a r.property,profileFirst_hasDerivAt s a r.property⟩

/-- The coefficient is the literal scalar source lift divided by compact radius. -/
theorem profile_original (s a : ℂ) (x : Iio (0:ℝ)) (v : ℝ) :
    profile s a (D4BMJointWave.tortoiseRadius x)*timeOnset (2*s) v=
      timeRadialLift s a (v-x) x/(radialUnit x:ℂ) := by
  have hr : (D4BMJointWave.tortoiseRadius x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (lt_trans zero_lt_one (D4BMJointWave.tortoiseRadius_exterior x x.property)))
  rw [timeRadialLift,radialLift,sourceAmplitude]
  simp only [zero_mul,Complex.exp_zero,one_mul,mul_one,sub_add_cancel]
  rw [radialUnit_inverse_radius]
  dsimp only [profile]
  push_cast
  field_simp

/-- The complete angular two-jet is retained when transforming the original stream to the
static chart. The six coefficients are its value and ingoing time/radius derivatives. -/
def separatedJet (r c cv cr cvv crv crr : ℂ) (J : ScalarTwoJet (Fin 2) ℂ) :
    ScalarTwoJet (Fin 4) ℂ where
  value := c*J.value
  first := ![cv*J.value,(cr+cv/(r^2-1))*J.value,c*J.first 0,c*J.first 1]
  second :=
    ![![cvv*J.value,(crv+cvv/(r^2-1))*J.value,cv*J.first 0,cv*J.first 1],
      ![(crv+cvv/(r^2-1))*J.value,
        (crr+2*crv/(r^2-1)+cvv/(r^2-1)^2-2*r*cv/(r^2-1)^2)*J.value,
        (cr+cv/(r^2-1))*J.first 0,(cr+cv/(r^2-1))*J.first 1],
      ![cv*J.first 0,(cr+cv/(r^2-1))*J.first 0,c*J.second 0 0,c*J.second 0 1],
      ![cv*J.first 1,(cr+cv/(r^2-1))*J.first 1,c*J.second 1 0,c*J.second 1 1]]

private def orbitMaster (r cv cr crv crr : ℂ) : ℂ :=
  r^2*(r^2-1)*crr+2*r^2*crv+2*r*cr-2*r*cv

/-- The actual Einstein action current transformed to ingoing coordinates. -/
def ingoingAction (p : D4BMBackground.ExteriorPoint)
    (P Q : Fin 2 → ScalarTwoJet (Fin 4) ℂ) : Fin 4 → ℂ :=
  let w := fun j => (p.val 1:ℂ)^2/(p.val 3:ℂ)^2 * actionSymplectic
    (D4BMBackground.jet (p.val 1) (p.val 3))
    (streamMetricJet (p.val 1) P) (streamMetricJet (p.val 1) Q) j
  ![w 0+w 1/((p.val 1:ℂ)^2-1),w 1,w 2,w 3]

private theorem separated_action (p : D4BMBackground.ExteriorPoint)
    (c cv cr cvv crv crr d dv dr dvv drv drr : ℂ)
    (J : Fin 2 → ScalarTwoJet (Fin 2) ℂ) :
    ingoingAction p (fun j => separatedJet (p.val 1) c cv cr cvv crv crr (J j))
      (fun j => separatedJet (p.val 1) d dv dr dvv drv drr (J j)) =
    let r := (p.val 1:ℂ)
    let OC := orbitMaster r cv cr crv crr
    let OD := orbitMaster r dv dr drv drr
    let N := ∑ j : Fin 2, (J j).value^2
    ![(dr*OC-cr*OD)*N/r^2,
      (((r^2-1)*dr+dv)*OC-((r^2-1)*cr+cv)*OD)*N/r^2,0,0] := by
  have hr : (p.val 1:ℂ) ≠ 0 := by exact_mod_cast (show p.val 1 ≠ 0 by linarith [p.property.1])
  have hf : (p.val 1:ℂ)^2-1 ≠ 0 := by exact_mod_cast (show (p.val 1)^2-1 ≠ 0 by nlinarith [p.property.1])
  unfold ingoingAction
  simp only [stream_complete_action_current]
  ext j
  fin_cases j
  · simp [streamCurrentDensity,separatedJet,streamMasterValue,orbitMaster,Fin.sum_univ_succ]
    field_simp [hr,hf]
    ring
  · simp [streamCurrentDensity,separatedJet,streamMasterValue,orbitMaster,Fin.sum_univ_succ]
    field_simp [hr,hf]
    ring
  · let r := (p.val 1:ℂ)
    change (p.val 3:ℂ)^2/r^2*(-(r^2-1)*
      (((cr+cv/(r^2-1))*(J 1).value)*
        ((dr+dv/(r^2-1))*(J 1).first 0-(dr+dv/(r^2-1))*(J 0).first 1)-
       ((dr+dv/(r^2-1))*(J 1).value)*
        ((cr+cv/(r^2-1))*(J 1).first 0-(cr+cv/(r^2-1))*(J 0).first 1))+
      (cv*(J 1).value*(dv*(J 1).first 0-dv*(J 0).first 1)-
       dv*(J 1).value*(cv*(J 1).first 0-cv*(J 0).first 1))/(r^2-1))=0
    ring
  · let r := (p.val 1:ℂ)
    change (p.val 3:ℂ)^2/r^2*((r^2-1)*
      (((cr+cv/(r^2-1))*(J 0).value)*
        ((dr+dv/(r^2-1))*(J 1).first 0-(dr+dv/(r^2-1))*(J 0).first 1)-
       ((dr+dv/(r^2-1))*(J 0).value)*
        ((cr+cv/(r^2-1))*(J 1).first 0-(cr+cv/(r^2-1))*(J 0).first 1))-
      (cv*(J 0).value*(dv*(J 1).first 0-dv*(J 0).first 1)-
       dv*(J 0).value*(cv*(J 1).first 0-cv*(J 0).first 1))/(r^2-1))=0
    ring

/-- Literal two-jets of the original full-square covector. -/
def angularJets (q : XiZeroCopy) (z : D4BMHorizon.Point) (j : Fin 2) : ScalarTwoJet (Fin 2) ℂ :=
  ScalarTwoJet.ofField (fullSquareCovector q j) z
/-- The actual angular square in the complex bilinear physical current. -/
def angularSquare (q : XiZeroCopy) (z : D4BMHorizon.Point) : ℂ :=
  ∑ j : Fin 2, (fullSquareCovector q j z)^2

/-- Static stream jets of the original ingoing source lift, retaining every clock jet. -/
def liftJet (q : XiZeroCopy) (s a : ℂ) (r v : ℝ) (z : D4BMHorizon.Point) (j : Fin 2) :
    ScalarTwoJet (Fin 4) ℂ :=
  separatedJet r (profile s a r*timeOnset (2*s) v)
    (profile s a r*timeOnsetFirst (2*s) v) (profileFirst s a r*timeOnset (2*s) v)
    (profile s a r*timeOnsetSecond (2*s) v) (profileFirst s a r*timeOnsetFirst (2*s) v)
    (profileSecond s a r*timeOnset (2*s) v) (angularJets q z j)

/-- Regular original orbit master coefficient. -/
def liftOrbit (s a : ℂ) (r v : ℝ) : ℂ :=
  orbitMaster r (profile s a r*timeOnsetFirst (2*s) v)
    (profileFirst s a r*timeOnset (2*s) v) (profileFirst s a r*timeOnsetFirst (2*s) v)
    (profileSecond s a r*timeOnset (2*s) v)

/-- Both physical ingoing components remain regular at the horizon; both angular components
retain their exact zero from the original common covector. -/
def liftCurrent (q : XiZeroCopy) (s t a b : ℂ) (r v : ℝ) (z : D4BMHorizon.Point) : Fin 4 → ℂ :=
  let c := profile s a r*timeOnsetFirst (2*s) v
  let cr := profileFirst s a r*timeOnset (2*s) v
  let d := profile t b r*timeOnsetFirst (2*t) v
  let dr := profileFirst t b r*timeOnset (2*t) v
  ![(dr*liftOrbit s a r v-cr*liftOrbit t b r v)*angularSquare q z/(r:ℂ)^2,
    ((((r:ℂ)^2-1)*dr+d)*liftOrbit s a r v-(((r:ℂ)^2-1)*cr+c)*liftOrbit t b r v)*
      angularSquare q z/(r:ℂ)^2,0,0]

/-- Equality with all four components of the original volume-weighted Einstein action. -/
theorem lift_action_current (p : D4BMBackground.ExteriorPoint) (q : XiZeroCopy)
    (s t a b : ℂ) (v : ℝ) :
    ingoingAction p (liftJet q s a (p.val 1) v ![p.val 2,p.val 3])
      (liftJet q t b (p.val 1) v ![p.val 2,p.val 3]) =
    liftCurrent q s t a b (p.val 1) v ![p.val 2,p.val 3] := by
  exact separated_action p _ _ _ _ _ _ _ _ _ _ _ _ _

/-- Spectral and original amplitude factor of the physical lift horizon current. -/
def horizonFactor (s a b : ℂ) : ℂ :=
  (2*s+3)*((s+1)*(s+2)-2)*((s+1)*(s+2)-6)*a^2*b^2/512

private theorem profileFirst_one (s a : ℂ) :
    profileFirst s a 1=-(s+2)*profile s a 1 := by
  simp [profileFirst,rate]
  ring

private theorem factor_profile (s a b : ℂ) :
    2*(2*s+3)*profile s a 1*profile (-s-3) b 1=horizonFactor s a b := by
  have hp : power (2*s) 2*power (2*(-s-3)) 2=(1:ℂ)/64 := by
    unfold power
    norm_cast
    rw [← Complex.cpow_add _ _ (show (2:ℂ) ≠ 0 by norm_num),show 2*s+2*(-s-3)=-(6:ℂ) by ring,
      Complex.cpow_neg,Complex.cpow_ofNat]
    norm_num
  simp only [profile,Complex.ofReal_one,inv_one,one_pow,mul_one,show (1:ℝ)+1=2 by norm_num]
  calc
    _ = (2*(2*s+3)*(-s*(s-1)/4)*(-(-s-3)*(-s-3-1)/4)*a^2*b^2)*
        (power (2*s) 2*power (2*(-s-3)) 2) := by ring
    _ = horizonFactor s a b := by rw [hp]; unfold horizonFactor; ring

/-- Complete original onset expressions in both physical ingoing horizon components. -/
def horizonCurrent (q : XiZeroCopy) (s a b : ℂ) (v : ℝ) (z : D4BMHorizon.Point) : Fin 4 → ℂ :=
  let χ := (Real.smoothTransition v:ℂ)
  let χ1 := ((deriv Real.smoothTransition v:ℝ):ℂ)
  let lam := (s+1)*(s+2)
  let K := horizonFactor s a b*Complex.exp (-6*(v:ℂ))*angularSquare q z
  ![K*(-χ*χ1+2*(2-lam)*χ^2),K*(-χ1^2+5*χ*χ1+4*(lam-1)*χ^2),0,0]

/-- Evaluation of the regular physical current retains the first-onset square and mixed term. -/
theorem lift_current_horizon_value (q : XiZeroCopy) (s a b : ℂ) (v : ℝ) (z : D4BMHorizon.Point) :
    liftCurrent q s (-s-3) a b 1 v z=horizonCurrent q s a b v z := by
  have he : Complex.exp ((2*s)*(v:ℂ))*Complex.exp ((2*(-s-3))*(v:ℂ))=
      Complex.exp (-6*(v:ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  ext j
  fin_cases j <;> simp [liftCurrent,liftOrbit,orbitMaster,horizonCurrent,profileFirst_one]
  all_goals rw [← factor_profile,show -(6*(v:ℂ))=(-6:ℂ)*(v:ℂ) by ring,← he]
  all_goals unfold timeOnset timeOnsetFirst
  all_goals ring

private theorem profiles_continuousAt_one (s a : ℂ) :
    ContinuousAt (profile s a) 1 ∧ ContinuousAt (profileFirst s a) 1 ∧
    ContinuousAt (profileSecond s a) 1 := by
  obtain ⟨h0,h1⟩ := profile_derivatives s a ⟨1,by norm_num⟩
  have hz : ContinuousAt (fun r:ℝ => (r:ℂ)) 1 := Complex.continuous_ofReal.continuousAt
  have hn : ((1:ℝ):ℂ) ≠ 0 := by norm_num
  have hn1 : 1+((1:ℝ):ℂ) ≠ 0 := by norm_num
  have hr : ContinuousAt (rate s) 1 := by unfold rate; fun_prop
  have hn2 := pow_ne_zero 2 hn
  have hn3 := pow_ne_zero 2 hn1
  have hr1 : ContinuousAt (rateFirst s) 1 := by unfold rateFirst; fun_prop
  exact ⟨h0.continuousAt,h1.continuousAt,h0.continuousAt.mul ((hr.pow 2).add hr1)⟩

/-- Literal exterior-to-horizon limit of the current identified with the original Einstein
action; the common angular source and original onset derivatives are retained. -/
theorem lift_current_horizon_limit (q : XiZeroCopy) (s a b : ℂ) (v : ℝ) (z : D4BMHorizon.Point)
    (j : Fin 4) :
    Tendsto (fun r => liftCurrent q s (-s-3) a b r v z j) (𝓝[>] (1:ℝ))
      (𝓝 (horizonCurrent q s a b v z j)) := by
  obtain ⟨h0,h1,h2⟩ := profiles_continuousAt_one s a
  obtain ⟨g0,g1,g2⟩ := profiles_continuousAt_one (-s-3) b
  have hc : ContinuousAt (fun r => liftCurrent q s (-s-3) a b r v z j) 1 := by
    have hz : ContinuousAt (fun r:ℝ => (r:ℂ)) 1 := Complex.continuous_ofReal.continuousAt
    have hn : ((1:ℝ):ℂ)^2 ≠ 0 := by norm_num
    fin_cases j <;> dsimp [liftCurrent,liftOrbit,orbitMaster]
    all_goals fun_prop
  have ht := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (1:ℝ)))
  rw [lift_current_horizon_value] at ht
  exact ht

/-- The original squared onset with the fixed complementary exponential weight. -/
def onsetSquare (v : ℝ) : ℂ := Complex.exp (-6*(v:ℂ))*(Real.smoothTransition v:ℂ)^2
/-- The retained mixed onset insertion. -/
def onsetMixed (v : ℝ) : ℂ :=
  Complex.exp (-6*(v:ℂ))*(Real.smoothTransition v:ℂ)*((deriv Real.smoothTransition v:ℝ):ℂ)
/-- The original first-onset derivative square with its fixed weight. -/
def onsetDerivativeSquare (v : ℝ) : ℂ :=
  Complex.exp (-6*(v:ℂ))*((deriv Real.smoothTransition v:ℝ):ℂ)^2
/-- Original finite squared-clock mass. -/
def clockMass (V : ℝ) : ℂ := ∫ v in (0:ℝ)..V, onsetSquare v
/-- Original finite derivative-clock energy. -/
def clockEnergy (V : ℝ) : ℂ := ∫ v in (0:ℝ)..V, onsetDerivativeSquare v

private theorem onset_continuous : Continuous onsetSquare ∧ Continuous onsetMixed ∧
    Continuous onsetDerivativeSquare := by
  have h0 : Continuous Real.smoothTransition := (Real.smoothTransition.contDiff (n := 1)).continuous
  have h1 : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 2)).differentiable_deriv_two.continuous
  have hc0 := Complex.continuous_ofReal.comp h0
  have hc1 := Complex.continuous_ofReal.comp h1
  have he : Continuous (fun v:ℝ => Complex.exp (-6*(v:ℂ))) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.const_mul (-6))
  unfold onsetSquare onsetMixed onsetDerivativeSquare
  constructor
  · fun_prop
  constructor <;> fun_prop

private theorem onsetSquare_derivative (v : ℝ) :
    HasDerivAt onsetSquare (2*onsetMixed v-6*onsetSquare v) v := by
  have hχ : HasDerivAt (fun u:ℝ => (Real.smoothTransition u:ℂ))
      ((deriv Real.smoothTransition v:ℝ):ℂ) v :=
    (((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)).differentiableAt.hasDerivAt).ofReal_comp
  have he := ((hasDerivAt_id v).ofReal_comp.const_mul (-6:ℂ)).cexp
  apply (he.mul (hχ.pow 2)).congr_deriv
  dsimp [onsetSquare,onsetMixed]
  ring

/-- Exact finite onset transfer, retaining the terminal square. -/
theorem clock_mixed_integral (V : ℝ) :
    (∫ v in (0:ℝ)..V, onsetMixed v)=3*clockMass V+onsetSquare V/2 := by
  obtain ⟨h0,h1,_⟩ := onset_continuous
  have hI0 := h0.intervalIntegrable (μ := volume) (0:ℝ) V
  have hI1 := h1.intervalIntegrable (μ := volume) (0:ℝ) V
  have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v _ => onsetSquare_derivative v) ((hI1.const_mul 2).sub (hI0.const_mul 6))
  rw [intervalIntegral.integral_sub (hI1.const_mul 2) (hI0.const_mul 6),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at ht
  have hz : onsetSquare 0=0 := by simp [onsetSquare,Real.smoothTransition.zero_of_nonpos le_rfl]
  rw [hz,sub_zero] at ht
  change (∫ v in (0:ℝ)..V, onsetMixed v)=3*(∫ v in (0:ℝ)..V, onsetSquare v)+onsetSquare V/2
  linear_combination ht/2

/-- Both original finite physical horizon currents, including every onset term and terminal
correction. The source-contact current has not been substituted for the Einstein current. -/
theorem horizon_current_finite_integrals (q : XiZeroCopy) (s a b : ℂ) (V : ℝ)
    (z : D4BMHorizon.Point) :
    (∫ v in (0:ℝ)..V, horizonCurrent q s a b v z 1)=
      horizonFactor s a b*angularSquare q z*
        (-clockEnergy V+(4*((s+1)*(s+2))+11)*clockMass V+5/2*onsetSquare V) ∧
    (∫ v in (0:ℝ)..V, horizonCurrent q s a b v z 0)=
      horizonFactor s a b*angularSquare q z*
        ((1-2*((s+1)*(s+2)))*clockMass V-onsetSquare V/2) := by
  obtain ⟨h0,h1,h2⟩ := onset_continuous
  have hI0 := h0.intervalIntegrable (μ := volume) (0:ℝ) V
  have hI1 := h1.intervalIntegrable (μ := volume) (0:ℝ) V
  have hI2 := h2.intervalIntegrable (μ := volume) (0:ℝ) V
  have he1 : (fun v => horizonCurrent q s a b v z 1)=fun v =>
      horizonFactor s a b*angularSquare q z*
        (-onsetDerivativeSquare v+5*onsetMixed v+4*((s+1)*(s+2)-1)*onsetSquare v) := by
    funext v
    simp [horizonCurrent,onsetDerivativeSquare,onsetMixed,onsetSquare]
    ring
  have he0 : (fun v => horizonCurrent q s a b v z 0)=fun v =>
      horizonFactor s a b*angularSquare q z*
        (-onsetMixed v+2*(2-(s+1)*(s+2))*onsetSquare v) := by
    funext v
    simp [horizonCurrent,onsetMixed,onsetSquare]
    ring
  constructor
  · rw [he1,intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (f := fun v => -onsetDerivativeSquare v+5*onsetMixed v)
        (g := fun v => 4*((s+1)*(s+2)-1)*onsetSquare v) (hI2.neg.add (hI1.const_mul 5)) (hI0.const_mul _),
      intervalIntegral.integral_add (f := fun v => -onsetDerivativeSquare v)
        (g := fun v => 5*onsetMixed v) hI2.neg (hI1.const_mul 5),intervalIntegral.integral_neg,
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,clock_mixed_integral]
    unfold clockMass clockEnergy
    ring
  · rw [he0,intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (f := fun v => -onsetMixed v)
        (g := fun v => 2*(2-(s+1)*(s+2))*onsetSquare v) hI1.neg (hI0.const_mul _),intervalIntegral.integral_neg,
      intervalIntegral.integral_const_mul,clock_mixed_integral]
    unfold clockMass
    ring

/-- The original angular action on the full-square covector; no scalar eigenvalue replaces it. -/
def angularAction (q : XiZeroCopy) (z : D4BMHorizon.Point) (j : Fin 2) : ℂ :=
  let J := angularJets q z
  (z 1:ℂ)^2*((J j).second 0 0+(J j).second 1 1)+
    2*(z 1:ℂ)*(if j=0 then (J 0).first 1-(J 1).first 0 else (J 1).first 1+(J 0).first 0)-
    2*(J j).value
/-- The actual angular bilinear insertion in the complete master current. -/
def angularPair (q : XiZeroCopy) (z : D4BMHorizon.Point) : ℂ :=
  ∑ j : Fin 2, fullSquareCovector q j z*angularAction q z j
/-- Regular original master source, with both its orbit and full angular terms. -/
def liftMaster (q : XiZeroCopy) (s a : ℂ) (r v : ℝ) (z : D4BMHorizon.Point) (j : Fin 2) : ℂ :=
  liftOrbit s a r v*fullSquareCovector q j z+
    profile s a r*timeOnset (2*s) v*angularAction q z j

/-- The regular expression is the actual static master applied to the original stream jet. -/
theorem lift_master_original (p : D4BMBackground.ExteriorPoint) (q : XiZeroCopy)
    (s a : ℂ) (v : ℝ) (j : Fin 2) :
    streamMasterValue (p.val 1) (p.val 3) (liftJet q s a (p.val 1) v ![p.val 2,p.val 3]) j=
      liftMaster q s a (p.val 1) v ![p.val 2,p.val 3] j := by
  have hf : (p.val 1:ℂ)^2-1 ≠ 0 := by
    exact_mod_cast (show (p.val 1)^2-1 ≠ 0 by nlinarith [p.property.1])
  fin_cases j <;> simp [streamMasterValue,streamAngularAction,liftJet,separatedJet,
    liftMaster,liftOrbit,orbitMaster,angularAction,angularJets,ScalarTwoJet.ofField]
  all_goals field_simp [hf]
  all_goals ring

/-- Actual master-source contact in ingoing coordinates, formed before taking a horizon limit. -/
def ingoingContact (p : D4BMBackground.ExteriorPoint)
    (P Q : Fin 2 → ScalarTwoJet (Fin 4) ℂ) : Fin 4 → ℂ :=
  let r := (p.val 1:ℂ)
  let f := r^2-1
  let M := streamMasterValue r (p.val 3)
  ![(∑ j : Fin 2, (((P j).first 1-(P j).first 0/f)*M Q j-
      ((Q j).first 1-(Q j).first 0/f)*M P j))/r^2,
    f*(∑ j : Fin 2, ((P j).first 1*M Q j-(Q j).first 1*M P j))/r^2,0,0]

/-- Regular source contact of the literal lift, retaining its original master source. -/
def liftContact (q : XiZeroCopy) (s t a b : ℂ) (r v : ℝ) (z : D4BMHorizon.Point) : Fin 4 → ℂ :=
  let cr := profileFirst s a r*timeOnset (2*s) v
  let dr := profileFirst t b r*timeOnset (2*t) v
  let cv := profile s a r*timeOnsetFirst (2*s) v
  let dv := profile t b r*timeOnsetFirst (2*t) v
  ![(∑ j : Fin 2, (cr*fullSquareCovector q j z*liftMaster q t b r v z j-
      dr*fullSquareCovector q j z*liftMaster q s a r v z j))/(r:ℂ)^2,
    (∑ j : Fin 2, ((((r:ℂ)^2-1)*cr+cv)*fullSquareCovector q j z*liftMaster q t b r v z j-
      (((r:ℂ)^2-1)*dr+dv)*fullSquareCovector q j z*liftMaster q s a r v z j))/(r:ℂ)^2,0,0]

/-- The regular contact is the actual source contact of the original Einstein stream jet. -/
theorem lift_contact_original (p : D4BMBackground.ExteriorPoint) (q : XiZeroCopy)
    (s t a b : ℂ) (v : ℝ) :
    ingoingContact p (liftJet q s a (p.val 1) v ![p.val 2,p.val 3])
      (liftJet q t b (p.val 1) v ![p.val 2,p.val 3])=
      liftContact q s t a b (p.val 1) v ![p.val 2,p.val 3] := by
  have hf : (p.val 1:ℂ)^2-1 ≠ 0 := by
    exact_mod_cast (show (p.val 1)^2-1 ≠ 0 by nlinarith [p.property.1])
  unfold ingoingContact
  simp only [lift_master_original]
  ext j
  fin_cases j <;> simp [liftContact,liftJet,separatedJet,angularJets,ScalarTwoJet.ofField,Fin.sum_univ_succ]
  all_goals field_simp [hf]
  all_goals ring

/-- Complete angular master current obtained after adding the original source contact. -/
def liftAngularCurrent (q : XiZeroCopy) (s t a b : ℂ) (r v : ℝ) (z : D4BMHorizon.Point) : Fin 4 → ℂ :=
  let c := profile s a r*timeOnset (2*s) v
  let d := profile t b r*timeOnset (2*t) v
  let cr := profileFirst s a r*timeOnset (2*s) v
  let dr := profileFirst t b r*timeOnset (2*t) v
  let cv := profile s a r*timeOnsetFirst (2*s) v
  let dv := profile t b r*timeOnsetFirst (2*t) v
  ![(cr*d-dr*c)*angularPair q z/(r:ℂ)^2,
    ((((r:ℂ)^2-1)*cr+cv)*d-(((r:ℂ)^2-1)*dr+dv)*c)*angularPair q z/(r:ℂ)^2,0,0]

/-- Exact physical-current/source-contact decomposition with the full angular source. -/
theorem lift_current_add_contact (q : XiZeroCopy) (s t a b : ℂ) (r v : ℝ) (z : D4BMHorizon.Point) :
    liftCurrent q s t a b r v z+liftContact q s t a b r v z=liftAngularCurrent q s t a b r v z := by
  ext j
  fin_cases j <;> simp [liftCurrent,liftContact,liftMaster,liftAngularCurrent,angularPair,
    angularSquare,Fin.sum_univ_succ]
  all_goals ring

/-- The horizon master current has the full angular insertion; the physical current differs
by the explicitly identified source contact. -/
theorem lift_angular_horizon_value (q : XiZeroCopy) (s a b : ℂ) (v : ℝ) (z : D4BMHorizon.Point) :
    liftAngularCurrent q s (-s-3) a b 1 v z=
      ![-horizonFactor s a b/2*onsetSquare v*angularPair q z,
        horizonFactor s a b*onsetSquare v*angularPair q z,0,0] := by
  have he : Complex.exp ((2*s)*(v:ℂ))*Complex.exp ((2*(-s-3))*(v:ℂ))=
      Complex.exp (-(6*(v:ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  ext j
  fin_cases j <;> simp [liftAngularCurrent,profileFirst_one,onsetSquare]
  all_goals rw [← factor_profile,← he]
  all_goals apply Or.inl
  all_goals dsimp [timeOnset,timeOnsetFirst]
  all_goals ring

/-- Both original contact integrals are explicit. They retain the same finite endpoint and
onset energy needed to compare the physical Einstein current with the master source action. -/
theorem horizon_contact_finite_integrals (q : XiZeroCopy) (s a b : ℂ) (V : ℝ)
    (z : D4BMHorizon.Point) :
    (∫ v in (0:ℝ)..V, liftContact q s (-s-3) a b 1 v z 1)=
      horizonFactor s a b*(clockMass V*angularPair q z-
        angularSquare q z*(-clockEnergy V+(4*((s+1)*(s+2))+11)*clockMass V+5/2*onsetSquare V)) ∧
    (∫ v in (0:ℝ)..V, liftContact q s (-s-3) a b 1 v z 0)=
      horizonFactor s a b*(-clockMass V/2*angularPair q z-
        angularSquare q z*((1-2*((s+1)*(s+2)))*clockMass V-onsetSquare V/2)) := by
  have he (v : ℝ) : liftContact q s (-s-3) a b 1 v z=
      ![-horizonFactor s a b/2*onsetSquare v*angularPair q z,
        horizonFactor s a b*onsetSquare v*angularPair q z,0,0]-horizonCurrent q s a b v z := by
    have h := lift_current_add_contact q s (-s-3) a b 1 v z
    rw [lift_current_horizon_value,lift_angular_horizon_value] at h
    exact eq_sub_of_add_eq' h
  have hI := onset_continuous.1.intervalIntegrable (μ := volume) (0:ℝ) V
  have hC (j : Fin 4) : IntervalIntegrable (fun v => horizonCurrent q s a b v z j) volume 0 V := by
    apply Continuous.intervalIntegrable
    have h0 := Complex.continuous_ofReal.comp (Real.smoothTransition.contDiff (n := 1)).continuous
    have h1 := Complex.continuous_ofReal.comp
      (Real.smoothTransition.contDiff (n := 2)).differentiable_deriv_two.continuous
    have he : Continuous (fun v:ℝ => Complex.exp (-6*(v:ℂ))) :=
      Complex.continuous_exp.comp (Complex.continuous_ofReal.const_mul (-6))
    fin_cases j <;> dsimp [horizonCurrent]
    all_goals fun_prop
  constructor
  · simp only [he,Pi.sub_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
    rw [intervalIntegral.integral_sub ((hI.const_mul _).mul_const _) (hC 1),
      intervalIntegral.integral_mul_const,intervalIntegral.integral_const_mul,
      (horizon_current_finite_integrals q s a b V z).1]
    unfold clockMass
    ring
  · simp only [he,Pi.sub_apply,Matrix.cons_val_zero]
    rw [intervalIntegral.integral_sub ((hI.const_mul _).mul_const _) (hC 0),
      intervalIntegral.integral_mul_const,intervalIntegral.integral_const_mul,
      (horizon_current_finite_integrals q s a b V z).2]
    unfold clockMass
    ring

private theorem profiles_continuous (s a : ℂ) :
    Continuous (fun r : Ioi (0:ℝ) => profile s a r) ∧
    Continuous (fun r : Ioi (0:ℝ) => profileFirst s a r) ∧
    Continuous (fun r : Ioi (0:ℝ) => profileSecond s a r) := by
  have h0 : Continuous (fun r : Ioi (0:ℝ) => profile s a r) :=
    continuous_iff_continuousAt.mpr fun r =>
      ((profile_derivatives s a r).1.continuousAt).comp continuous_subtype_val.continuousAt
  have h1 : Continuous (fun r : Ioi (0:ℝ) => profileFirst s a r) :=
    continuous_iff_continuousAt.mpr fun r =>
      ((profile_derivatives s a r).2.continuousAt).comp continuous_subtype_val.continuousAt
  have hz : Continuous (fun r : Ioi (0:ℝ) => (r.val:ℂ)) :=
    Complex.continuous_ofReal.comp continuous_subtype_val
  have hn (r : Ioi (0:ℝ)) : (r.val:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt r.property)
  have hn1 (r : Ioi (0:ℝ)) : 1+(r.val:ℂ) ≠ 0 := by
    have hr : 0 < r.val := r.property
    exact_mod_cast (show 1+r.val ≠ 0 by linarith)
  have hn2 (r : Ioi (0:ℝ)) := pow_ne_zero 2 (hn r)
  have hn3 (r : Ioi (0:ℝ)) := pow_ne_zero 2 (hn1 r)
  have hr : Continuous (fun r : Ioi (0:ℝ) => rate s r) := by unfold rate; fun_prop
  have hr1 : Continuous (fun r : Ioi (0:ℝ) => rateFirst s r) := by unfold rateFirst; fun_prop
  exact ⟨h0,h1,h0.mul ((hr.pow 2).add hr1)⟩

private theorem liftCurrent_joint_continuous (q : XiZeroCopy) (s t a b : ℂ)
    (z : D4BMHorizon.Point) (j : Fin 4) :
    Continuous (fun p : Ioi (0:ℝ) × ℝ => liftCurrent q s t a b p.1 p.2 z j) := by
  obtain ⟨h0,h1,h2⟩ := profiles_continuous s a
  obtain ⟨g0,g1,g2⟩ := profiles_continuous t b
  have ht0 : Continuous (timeOnset (2*s)) := continuous_iff_continuousAt.mpr
    fun v => (timeOnset_hasDerivAt (2*s) v).continuousAt
  have ht1 : Continuous (timeOnsetFirst (2*s)) := continuous_iff_continuousAt.mpr
    fun v => (timeOnsetFirst_hasDerivAt (2*s) v).continuousAt
  have gt0 : Continuous (timeOnset (2*t)) := continuous_iff_continuousAt.mpr
    fun v => (timeOnset_hasDerivAt (2*t) v).continuousAt
  have gt1 : Continuous (timeOnsetFirst (2*t)) := continuous_iff_continuousAt.mpr
    fun v => (timeOnsetFirst_hasDerivAt (2*t) v).continuousAt
  have hz : Continuous (fun p : Ioi (0:ℝ) × ℝ => (p.1.val:ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
  have hn (p : Ioi (0:ℝ) × ℝ) : (p.1.val:ℂ)^2 ≠ 0 :=
    pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt p.1.property))
  have h0p := h0.comp (continuous_fst : Continuous (Prod.fst : Ioi (0:ℝ) × ℝ → Ioi (0:ℝ)))
  have h1p := h1.comp (continuous_fst : Continuous (Prod.fst : Ioi (0:ℝ) × ℝ → Ioi (0:ℝ)))
  have h2p := h2.comp (continuous_fst : Continuous (Prod.fst : Ioi (0:ℝ) × ℝ → Ioi (0:ℝ)))
  have g0p := g0.comp (continuous_fst : Continuous (Prod.fst : Ioi (0:ℝ) × ℝ → Ioi (0:ℝ)))
  have g1p := g1.comp (continuous_fst : Continuous (Prod.fst : Ioi (0:ℝ) × ℝ → Ioi (0:ℝ)))
  have g2p := g2.comp (continuous_fst : Continuous (Prod.fst : Ioi (0:ℝ) × ℝ → Ioi (0:ℝ)))
  have ht0p := ht0.comp (continuous_snd : Continuous (Prod.snd : Ioi (0:ℝ) × ℝ → ℝ))
  have ht1p := ht1.comp (continuous_snd : Continuous (Prod.snd : Ioi (0:ℝ) × ℝ → ℝ))
  have gt0p := gt0.comp (continuous_snd : Continuous (Prod.snd : Ioi (0:ℝ) × ℝ → ℝ))
  have gt1p := gt1.comp (continuous_snd : Continuous (Prod.snd : Ioi (0:ℝ) × ℝ → ℝ))
  fin_cases j <;> dsimp [liftCurrent,liftOrbit,orbitMaster]
  all_goals try exact continuous_const
  all_goals exact Continuous.div (by fun_prop) (hz.pow 2) hn

/-- The finite-time integral of the original exterior physical current reaches the displayed
horizon current integral. Joint continuity is derived from the original source and clock jets. -/
theorem lift_current_finite_horizon_limit (q : XiZeroCopy) (s a b : ℂ) (V : ℝ)
    (z : D4BMHorizon.Point) (j : Fin 4) :
    Tendsto (fun r => ∫ v in (0:ℝ)..V, liftCurrent q s (-s-3) a b r v z j) (𝓝[>] (1:ℝ))
      (𝓝 (∫ v in (0:ℝ)..V, horizonCurrent q s a b v z j)) := by
  have hc : Continuous (fun r : Ioi (0:ℝ) => ∫ v in (0:ℝ)..V,
      liftCurrent q s (-s-3) a b r v z j) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (liftCurrent_joint_continuous q s (-s-3) a b z j) 0 V
  have hr : ContinuousOn (fun r => ∫ v in (0:ℝ)..V, liftCurrent q s (-s-3) a b r v z j)
      (Ioi (0:ℝ)) := continuousOn_iff_continuous_restrict.mpr hc
  have h1 : (1:ℝ) ∈ Ioi (0:ℝ) := by norm_num
  have ht := (hr.continuousAt (isOpen_Ioi.mem_nhds h1)).tendsto.mono_left
    (nhdsWithin_le_nhds (s := Ioi (1:ℝ)))
  simpa only [lift_current_horizon_value] using ht

/-- Explicit finite-cutoff limits of both original ingoing physical currents, retaining the
clock energy, clock mass and the exact terminal correction. -/
theorem physical_finite_horizon_limits (q : XiZeroCopy) (s a b : ℂ) (V : ℝ)
    (z : D4BMHorizon.Point) :
    Tendsto (fun r => ∫ v in (0:ℝ)..V, liftCurrent q s (-s-3) a b r v z 1) (𝓝[>] (1:ℝ))
      (𝓝 (horizonFactor s a b*angularSquare q z*
        (-clockEnergy V+(4*((s+1)*(s+2))+11)*clockMass V+5/2*onsetSquare V))) ∧
    Tendsto (fun r => ∫ v in (0:ℝ)..V, liftCurrent q s (-s-3) a b r v z 0) (𝓝[>] (1:ℝ))
      (𝓝 (horizonFactor s a b*angularSquare q z*
        ((1-2*((s+1)*(s+2)))*clockMass V-onsetSquare V/2))) := by
  constructor
  · simpa only [(horizon_current_finite_integrals q s a b V z).1] using
      lift_current_finite_horizon_limit q s a b V z 1
  · simpa only [(horizon_current_finite_integrals q s a b V z).2] using
      lift_current_finite_horizon_limit q s a b V z 0

/-- Full-square/gradient-source pairing in the original complex bilinear contraction. -/
def gradientPair (q : XiZeroCopy) (branch : Bool) (z : D4BMHorizon.Point) : ℂ :=
  ∑ j : Fin 2, fullSquareCovector q j z*fullGradientCovector q branch j z

/-- The complete angular action resolves into the actual square and gradient sources. -/
theorem angular_action_original (q : XiZeroCopy) (branch : Bool)
    (z : {z : D4BMHorizon.Point // 0 < z 1}) (j : Fin 2) :
    angularAction q z j=
      (2*(physicalRate q branch+1)*(physicalRate q branch+2)-2)*fullSquareCovector q j z+
        2*fullGradientCovector q branch j z := by
  have h := fullSquareCovector_rough_equation q branch z z.property j
  rw [roughLaplacian_eq _ z z.property (fun k => fullSquareCovector_smooth q z z.property 2 k)] at h
  fin_cases j <;> simp [angularAction,angularJets,ScalarTwoJet.ofField,roughFormula] at h ⊢
  all_goals linear_combination h

/-- The angular insertion retains the full original gradient source, with its exact coefficient. -/
theorem angular_pair_original (q : XiZeroCopy) (branch : Bool)
    (z : {z : D4BMHorizon.Point // 0 < z 1}) :
    angularPair q z=(2*(physicalRate q branch+1)*(physicalRate q branch+2)-2)*angularSquare q z+
      2*gradientPair q branch z := by
  unfold angularPair
  simp_rw [angular_action_original q branch z]
  simp [angularSquare,gradientPair,Fin.sum_univ_succ]
  ring

/-- Both finite original source contacts expressed in the actual square and gradient source
pairings, with every fixed-clock and terminal term retained. -/
theorem physical_source_contact_integrals (q : XiZeroCopy) (branch : Bool) (a b : ℂ) (V : ℝ)
    (z : {z : D4BMHorizon.Point // 0 < z 1}) :
    let s := physicalRate q branch
    let lam := (s+1)*(s+2)
    (∫ v in (0:ℝ)..V, liftContact q s (-s-3) a b 1 v z 1)=
      horizonFactor s a b*(2*clockMass V*gradientPair q branch z+
        (clockEnergy V-(2*lam+13)*clockMass V-5/2*onsetSquare V)*angularSquare q z) ∧
    (∫ v in (0:ℝ)..V, liftContact q s (-s-3) a b 1 v z 0)=
      horizonFactor s a b*(-clockMass V*gradientPair q branch z+
        (lam*clockMass V+onsetSquare V/2)*angularSquare q z) := by
  dsimp only
  obtain ⟨h1,h0⟩ := horizon_contact_finite_integrals q (physicalRate q branch) a b V z
  rw [angular_pair_original q branch z] at h1 h0
  constructor
  · rw [h1]
    ring
  · rw [h0]
    ring

/-- Original stream-lift coefficient as a function of static time and radius. -/
def staticCoefficient (s a : ℂ) (tau r : ℝ) : ℂ :=
  profile s a r*timeOnset (2*s) (tau+D4BMIngoingCoordinates.tortoise r)
/-- Its static radial derivative, retaining the derivative of the ingoing clock. -/
def staticRadialFirst (s a : ℂ) (tau r : ℝ) : ℂ :=
  let v := tau+D4BMIngoingCoordinates.tortoise r
  profileFirst s a r*timeOnset (2*s) v+
    profile s a r*timeOnsetFirst (2*s) v/((r:ℂ)^2-1)
/-- Its complete static radial second derivative. -/
def staticRadialSecond (s a : ℂ) (tau r : ℝ) : ℂ :=
  let v := tau+D4BMIngoingCoordinates.tortoise r
  profileSecond s a r*timeOnset (2*s) v+
    2*profileFirst s a r*timeOnsetFirst (2*s) v/((r:ℂ)^2-1)+
    profile s a r*timeOnsetSecond (2*s) v/((r:ℂ)^2-1)^2-
    2*(r:ℂ)*profile s a r*timeOnsetFirst (2*s) v/((r:ℂ)^2-1)^2

/-- Both static radial jets used by the reconstructed Einstein current are actual derivatives
of the literal source lift after the differentiated tortoise coordinate change. -/
theorem static_radial_derivatives (s a : ℂ) (tau : ℝ) (r : Ioi (1:ℝ)) :
    HasDerivAt (staticCoefficient s a tau) (staticRadialFirst s a tau r) r.val ∧
    HasDerivAt (staticRadialFirst s a tau) (staticRadialSecond s a tau r) r.val := by
  have hr : 1 < r.val := r.property
  have hp := profile_derivatives s a ⟨r.val,lt_trans zero_lt_one hr⟩
  have ht := (D4BMIngoingCoordinates.tortoise_hasDerivAt r hr).const_add tau
  have hT := (timeOnset_hasDerivAt (2*s) (tau+D4BMIngoingCoordinates.tortoise r)).scomp r.val ht
  have hT1 := (timeOnsetFirst_hasDerivAt (2*s) (tau+D4BMIngoingCoordinates.tortoise r)).scomp r.val ht
  have hn : r.val^2-1 ≠ 0 := by nlinarith
  have hnC : (r.val:ℂ)^2-1 ≠ 0 := by exact_mod_cast hn
  have hF := ((((hasDerivAt_id r.val).pow 2).sub_const 1).inv hn).ofReal_comp
  constructor
  · convert! hp.1.mul hT using 1
    dsimp [staticRadialFirst,Function.comp_def]
    push_cast
    ring
  · convert! (hp.2.mul hT).add ((hp.1.mul hT1).mul hF) using 1
    · funext x
      simp [staticRadialFirst,Function.comp_def,div_eq_mul_inv]
    · dsimp [staticRadialSecond,Function.comp_def]
      push_cast
      field_simp [hnC]
      ring

end
end RHTower.D4BMPhysicalLiftCurrent
