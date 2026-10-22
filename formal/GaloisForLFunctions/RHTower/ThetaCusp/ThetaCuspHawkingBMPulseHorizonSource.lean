import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMIncomingClockTranslation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceHorizonFactor

/-!
# Original normalized pulse and radial source contact

The literal pulse has a scalar radial zero, but its original master-source
normalization cancels that zero before taking the horizon limit. The limiting
source is the actual incoming trace-minus-normal covector. Both differentiated
jets are retained in the original static-chart contact and its regular ingoing
form. Its horizon profile has mixed onset and derivative-square contributions.
This source/contact law does not evaluate the causal pulse response or establish
extinction of the completed radiative action.
-/

open Set Filter Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMPulseHorizonSource
open D4BMJointSource D4BMJointWave D4BMModularCore D4BMGlobalAngularResponse
open D4BMHorizon D4BMLaplaceRadial D4BMFullIncomingCurrent
open D4BMIncomingClockTranslation
noncomputable section
set_option autoImplicit false

/-- The literal pulse after its original scalar-source and radial normalization. -/
def normalizedPulseSource (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (v x : ℝ) (z : Point) (j : Fin 2) : ℂ :=
  -coexact (fullSourceOnsetPulse q branch a (v-x) x) j z /
    ((radialUnit x:ℂ)*(1-(radialUnit x:ℂ)^(2 : ℕ))*parameter q branch)

/-- Regular expression obtained by cancelling the source's radial zero. -/
def compactPulseSource (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (v u : ℝ) (z : Point) (j : Fin 2) : ℂ :=
  let s := physicalRate q branch
  2*power (2*s) (1+u)*a^(2 : ℕ)/((u:ℂ)*(1+(u:ℂ)))*
    (((2*s+1)*(u:ℂ)+1)*fullAngularCovector q branch j z-
      s*(s-1)/4*(u:ℂ)^(2 : ℕ)*((2*s+3)*(u:ℂ)+3)*fullSquareCovector q j z)*
    ((deriv Real.smoothTransition v:ℝ):ℂ)*Complex.exp (2*s*(v:ℂ))

/-- Horizon drive in terms of the actual incoming trace and normal covectors. -/
def horizonPulseSource (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (v : ℝ) (z : Point) (j : Fin 2) : ℂ :=
  2*responseProfile (physicalRate q branch) a 1*
    ((traceJet q branch z j).value-(normalJet q branch z j).value)*
    ((deriv Real.smoothTransition v:ℝ):ℂ)*
    Complex.exp (2*physicalRate q branch*(v:ℂ))

private theorem parameter_ne_zero (q : XiZeroCopy) (branch : Bool) :
    parameter q branch ≠ 0 := by
  have hi : (parameter q branch).im ≠ 0 := by
    cases branch
    · exact (D4BMQuadraticMixedSource.xi_resolvent_parameter_nonreal q).2
    · exact (D4BMQuadraticMixedSource.xi_resolvent_parameter_nonreal q).1
  intro he
  exact hi (by rw [he]; rfl)

private theorem coexact_response_linear (q : XiZeroCopy) (branch : Bool) (a b : ℂ)
    (z : UpperHalfPlane) (j : Fin 2) :
    coexact (fun w => a*fullAngularField q branch w+b*fullSquarePotential q w)
        j (coordinates z) =
      a*fullAngularCovector q branch j (coordinates z)+
        b*fullSquareCovector q j (coordinates z) := by
  have hH := ((fullAngularField_smooth q branch (coordinates z) z.im_pos).differentiableAt (by simp)).hasFDerivAt
  have hQ := ((fullSquarePotential_smooth q (coordinates z) z.im_pos 1).differentiableAt (by norm_num)).hasFDerivAt
  have hd := (hH.const_mul a).add (hQ.const_mul b)
  have hf : fderiv ℝ (fun w => a*fullAngularField q branch w+b*fullSquarePotential q w)
      (coordinates z) = a • fderiv ℝ (fullAngularField q branch) (coordinates z)+
        b • fderiv ℝ (fullSquarePotential q) (coordinates z) := hd.fderiv
  rw [← fullSquarePotential_coexact q _ z.im_pos]
  fin_cases j
  · change (fderiv ℝ (fun w => a*fullAngularField q branch w+b*fullSquarePotential q w)
        (coordinates z)) (Pi.single 1 1) =
      a*(fderiv ℝ (fullAngularField q branch) (coordinates z)) (Pi.single 1 1)+
        b*(fderiv ℝ (fullSquarePotential q) (coordinates z)) (Pi.single 1 1)
    rw [hf]
    rfl
  · change -(fderiv ℝ (fun w => a*fullAngularField q branch w+b*fullSquarePotential q w)
        (coordinates z)) (Pi.single 0 1) =
      a*(-(fderiv ℝ (fullAngularField q branch) (coordinates z)) (Pi.single 0 1))+
        b*(-(fderiv ℝ (fullSquarePotential q) (coordinates z)) (Pi.single 0 1))
    rw [hf]
    simp only [add_apply,smul_apply,smul_eq_mul]
    ring

private theorem pulse_coexact (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (v x : ℝ) (z : UpperHalfPlane) (j : Fin 2) :
    let s := physicalRate q branch
    let u : ℂ := radialUnit x
    coexact (fullSourceOnsetPulse q branch a (v-x) x) j (coordinates z) =
      2*parameter q branch*sourceAmplitude s 0 a 1 x*(1-u)*
        (-((2*s+1)*u+1)*fullAngularCovector q branch j (coordinates z)+
          s*(s-1)/4*u^(2 : ℕ)*((2*s+3)*u+3)*fullSquareCovector q j (coordinates z))*
        ((deriv Real.smoothTransition v:ℝ):ℂ)*Complex.exp (2*s*(v:ℂ)) := by
  dsimp only
  let s := physicalRate q branch
  let u : ℂ := radialUnit x
  let C := 2*parameter q branch*sourceAmplitude s 0 a 1 x*(1-u)*
    ((deriv Real.smoothTransition v:ℝ):ℂ)*Complex.exp (2*s*(v:ℂ))
  have he : fullSourceOnsetPulse q branch a (v-x) x =
      fun w => (C*(-((2*s+1)*u+1)))*fullAngularField q branch w+
        (C*(s*(s-1)/4*u^(2 : ℕ)*((2*s+3)*u+3)))*fullSquarePotential q w := by
    funext w
    rw [fullSourceOnsetPulse_radial_factor]
    dsimp only [C,s,u]
    simp only [sub_add_cancel]
    ring
  rw [he,coexact_response_linear]
  dsimp only [C,s,u]
  ring

/-- Cancelling the actual radial factor gives a regular source at the horizon. -/
theorem normalizedPulseSource_eq_compact (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (v : ℝ) (x : Iio (0:ℝ)) (z : UpperHalfPlane) (j : Fin 2) :
    normalizedPulseSource q branch a v x (coordinates z) j =
      compactPulseSource q branch a v (radialUnit x) (coordinates z) j := by
  obtain ⟨h0,h1⟩ := radialUnit_bounds x x.property
  have hu0 : (radialUnit x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt h0)
  have hu2 : 1-(radialUnit x:ℂ)^(2 : ℕ) ≠ 0 := by
    exact_mod_cast (show 1-(radialUnit x)^(2 : ℕ) ≠ 0 by nlinarith)
  have hu1 : 1+(radialUnit x:ℂ) ≠ 0 := by
    exact_mod_cast (show 1+radialUnit x ≠ 0 by linarith)
  have hp := parameter_ne_zero q branch
  rw [normalizedPulseSource,pulse_coexact]
  dsimp only [compactPulseSource,sourceAmplitude]
  simp only [zero_mul,Complex.exp_zero,one_mul,mul_one]
  field_simp [hu0,hu1,hu2,hp]
  ring

/-- The normalization is exactly the original radius factor, not a fitted weight. -/
theorem normalizedPulseSource_original_radius (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (v : ℝ) (x : Iio (0:ℝ)) (z : Point) (j : Fin 2) :
    normalizedPulseSource q branch a v x z j =
      -(tortoiseRadius x:ℂ)^(3 : ℕ)/
        (((tortoiseRadius x:ℂ)^(2 : ℕ)-1)*parameter q branch)*
          coexact (fullSourceOnsetPulse q branch a (v-x) x) j z := by
  have hR := tortoiseRadius_exterior x x.property
  have hr : (tortoiseRadius x:ℂ) ≠ 0 := by exact_mod_cast (show tortoiseRadius x ≠ 0 by linarith)
  have hf : (tortoiseRadius x:ℂ)^(2 : ℕ)-1 ≠ 0 := by
    exact_mod_cast (show (tortoiseRadius x)^(2 : ℕ)-1 ≠ 0 by nlinarith)
  have hp := parameter_ne_zero q branch
  rw [normalizedPulseSource,radialUnit_inverse_radius]
  push_cast
  field_simp [hr,hf,hp]

/-- The regular horizon value retains the incoming trace-minus-normal source. -/
theorem compactPulseSource_horizon (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (v : ℝ) (z : Point) (j : Fin 2) :
    compactPulseSource q branch a v 1 z j = horizonPulseSource q branch a v z j := by
  have hj : (traceJet q branch z j).value-(normalJet q branch z j).value =
      (physicalRate q branch+1)*fullAngularCovector q branch j z-
        physicalRate q branch*(physicalRate q branch-1)/4*(physicalRate q branch+3)*
          fullSquareCovector q j z := by
    change (1*fullAngularCovector q branch j z+
        (-physicalRate q branch*(physicalRate q branch-1)/4)*fullSquareCovector q j z)-
      (-physicalRate q branch*fullAngularCovector q branch j z+
        (physicalRate q branch*(physicalRate q branch-1)*(physicalRate q branch+2)/4)*
          fullSquareCovector q j z) = _
    ring
  rw [horizonPulseSource,hj]
  dsimp only [compactPulseSource,responseProfile]
  simp only [Complex.ofReal_one,inv_one,one_pow,mul_one,one_mul,
    show (1:ℝ)+1=2 by norm_num,show (1:ℂ)+1=2 by norm_num]
  ring

private theorem unit_tendsto_horizon : Tendsto radialUnit atBot (𝓝 (1:ℝ)) := by
  have ht : Tendsto (fun x : ℝ => 2*x) atBot atBot :=
    (tendsto_const_mul_atBot_of_pos (by norm_num : (0:ℝ)<2)).mpr tendsto_id
  have he := Real.tendsto_exp_atBot.comp ht
  have hform : radialUnit=fun x => (1-Real.exp (2*x))/(1+Real.exp (2*x)) := by
    funext x
    apply (eq_div_iff (ne_of_gt (by positivity : 0 < 1+Real.exp (2*x)))).mpr
    have hh := radialUnit_one_sub x
    nlinarith
  rw [hform]
  simpa [Function.comp_def,Pi.div_apply] using!
    (tendsto_const_nhds.sub he).div (tendsto_const_nhds.add he) (by norm_num : (1:ℝ)+0 ≠ 0)

/-- Actual exterior limit of the originally normalized coexact pulse. -/
theorem normalizedPulseSource_horizon_limit (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (v : ℝ) (z : UpperHalfPlane) (j : Fin 2) :
    Tendsto (fun x => normalizedPulseSource q branch a v x (coordinates z) j) atBot
      (𝓝 (horizonPulseSource q branch a v (coordinates z) j)) := by
  have hp : ContinuousAt (fun u : ℝ => power (2*physicalRate q branch) (1+u)) 1 :=
    (power_derivatives (2*physicalRate q branch) (by norm_num : 0 < (1+(1:ℝ)))).1.continuousAt.comp
      (f := fun u : ℝ => 1+u) (by fun_prop)
  have hc : ContinuousAt (fun u => compactPulseSource q branch a v u (coordinates z) j) 1 := by
    unfold compactPulseSource
    fun_prop (disch := norm_num)
  have ht := hc.tendsto.comp unit_tendsto_horizon
  rw [compactPulseSource_horizon] at ht
  apply ht.congr'
  filter_upwards [eventually_lt_atBot (0:ℝ)] with x hx
  exact (normalizedPulseSource_eq_compact q branch a v ⟨x,hx⟩ z j).symm

end
end RHTower.D4BMPulseHorizonSource

open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMPulseHorizonSource
open D4BMJointSource D4BMModularCore D4BMHorizon D4BMGlobalAngularResponse
open D4BMFullIncomingCurrent D4BMPhysicalLiftCurrent D4BMLaplaceRadial
open D4BMIncomingClockTranslation D4BMSourceClockTranslation
noncomputable section
set_option autoImplicit false

/-- The source-contact pairing of the actual incoming time jets and pulse horizon drive. -/
def horizonPulseContact (q : XiZeroCopy) (a b : ℂ) (v : ℝ) (z : Point) : ℂ :=
  ∑ j : Fin 2,
    ((incomingJet q true a 1 v z j).first 0*horizonPulseSource q false b v z j-
      (incomingJet q false b 1 v z j).first 0*horizonPulseSource q true a v z j)

private theorem incomingTime_horizon (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (v : ℝ) (z : Point) (j : Fin 2) :
    (incomingJet q branch a 1 v z j).first 0 =
      responseProfile (physicalRate q branch) a 1*(traceJet q branch z j).value*
        timeOnsetFirst (2*physicalRate q branch) v := by
  have hp : profile (physicalRate q branch) a 1 =
      (-physicalRate q branch*(physicalRate q branch-1)/4)*
        responseProfile (physicalRate q branch) a 1 := by
    simp [profile,responseProfile]
    ring
  change (responseProfile (physicalRate q branch) a 1*timeOnsetFirst (2*physicalRate q branch) v)*
      fullAngularCovector q branch j z+
      (profile (physicalRate q branch) a 1*timeOnsetFirst (2*physicalRate q branch) v)*
        fullSquareCovector q j z =
    responseProfile (physicalRate q branch) a 1*
      (1*fullAngularCovector q branch j z+
        (-physicalRate q branch*(physicalRate q branch-1)/4)*fullSquareCovector q j z)*
      timeOnsetFirst (2*physicalRate q branch) v
  rw [hp]
  ring

private theorem branch_factor (q : XiZeroCopy) (a b : ℂ) (v : ℝ) :
    (responseProfile (physicalRate q true) a 1*Complex.exp (2*physicalRate q true*(v:ℂ)))*
    (responseProfile (physicalRate q false) b 1*Complex.exp (2*physicalRate q false*(v:ℂ))) =
      a^(2 : ℕ)*b^(2 : ℕ)/64*Complex.exp (-6*(v:ℂ)) := by
  have ht : physicalRate q false= -physicalRate q true-3 := by simp [physicalRate]; ring
  have hp : power (2*physicalRate q true) 2*power (2*(-physicalRate q true-3)) 2=1/64 := by
    unfold power
    norm_cast
    rw [← Complex.cpow_add _ _ (show (2:ℂ) ≠ 0 by norm_num),
      show 2*physicalRate q true+2*(-physicalRate q true-3)=-(6:ℂ) by ring,
      Complex.cpow_neg,Complex.cpow_ofNat]
    norm_num
  have he : Complex.exp (2*physicalRate q true*(v:ℂ))*
      Complex.exp (2*(-physicalRate q true-3)*(v:ℂ))=Complex.exp (-6*(v:ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [ht]
  simp only [responseProfile,inv_one,show (1:ℝ)+1=2 by norm_num]
  calc
    _ = a^(2 : ℕ)*b^(2 : ℕ)*(power (2*physicalRate q true) 2*power (2*(-physicalRate q true-3)) 2)*
        (Complex.exp (2*physicalRate q true*(v:ℂ))*Complex.exp (2*(-physicalRate q true-3)*(v:ℂ))) := by ring
    _ = _ := by rw [hp,he]; ring

/-- The local pulse contact retains its mixed and derivative-square terms; its mass is zero. -/
theorem horizonPulseContact_profile (q : XiZeroCopy) (a b : ℂ) (v : ℝ) (z : Point) :
    let s := physicalRate q true
    let t := physicalRate q false
    let c := a^(2 : ℕ)*b^(2 : ℕ)/64
    let TT := ∑ j : Fin 2, (traceJet q true z j).value*(traceJet q false z j).value
    let X := ∑ j : Fin 2, (traceJet q false z j).value*(normalJet q true z j).value
    let Y := ∑ j : Fin 2, (traceJet q true z j).value*(normalJet q false z j).value
    horizonPulseContact q a b v z =
      horizonProfile 0 (4*c*((s-t)*TT+t*X-s*Y)) (2*c*(X-Y)) v*
        Complex.exp (-6*(v:ℂ)) := by
  dsimp only
  simp only [horizonPulseContact,incomingTime_horizon,horizonPulseSource,timeOnsetFirst,horizonProfile]
  have he := branch_factor q a b v
  simp only [Fin.sum_univ_two]
  let s := physicalRate q true
  let t := physicalRate q false
  let χ : ℂ := Real.smoothTransition v
  let dχ : ℂ := ((deriv Real.smoothTransition v:ℝ):ℂ)
  let TT := ∑ j : Fin 2, (traceJet q true z j).value*(traceJet q false z j).value
  let X := ∑ j : Fin 2, (traceJet q false z j).value*(normalJet q true z j).value
  let Y := ∑ j : Fin 2, (traceJet q true z j).value*(normalJet q false z j).value
  have hχ : (2*(X-Y)*dχ^(2 : ℕ)+4*((s-t)*TT+t*X-s*Y)*χ*dχ)*
      ((responseProfile s a 1*Complex.exp (2*s*(v:ℂ)))*
        (responseProfile t b 1*Complex.exp (2*t*(v:ℂ)))) =
      (2*(X-Y)*dχ^(2 : ℕ)+4*((s-t)*TT+t*X-s*Y)*χ*dχ)*
        (a^(2 : ℕ)*b^(2 : ℕ)/64*Complex.exp (-6*(v:ℂ))) := by rw [he]
  dsimp only [TT,X,Y,s,t,χ,dχ] at hχ
  simp only [Fin.sum_univ_two] at hχ
  linear_combination hχ

/-- The actual local pulse contact has zero mass at the unchanged common clock. -/
theorem horizonPulseContact_clockMoment (q : XiZeroCopy) (a b : ℂ) (z : Point) (h : NNReal) :
    clockMoment (-6) h (fun v => horizonPulseContact q a b v z) = 0 := by
  simp only [horizonPulseContact_profile]
  rw [horizonProfile_clockMoment]
  simp

end
end RHTower.D4BMPulseHorizonSource

open Set Filter Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMPulseHorizonSource
open D4BMJointSource D4BMJointWave D4BMModularCore D4BMHorizon D4BMGlobalAngularResponse
open D4BMFullIncomingCurrent D4BMPhysicalLiftCurrent D4BMLaplaceRadial
noncomputable section
set_option autoImplicit false

/-- Original radial source contact, before cancelling the static-chart singularity. -/
def originalPulseContact (q : XiZeroCopy) (a b : ℂ) (v x : ℝ) (z : Point) : ℂ :=
  let r := tortoiseRadius x
  ((r:ℂ)^(2 : ℕ)-1)/(r:ℂ)^(2 : ℕ)*(∑ j : Fin 2,
    ((staticJet r (incomingJet q true a r v z j)).first 1*
        normalizedPulseSource q false b v x z j-
      (staticJet r (incomingJet q false b r v z j)).first 1*
        normalizedPulseSource q true a v x z j))

/-- The regular ingoing contact retains both radial and temporal derivatives. -/
def compactPulseContact (q : XiZeroCopy) (a b : ℂ) (v u : ℝ) (z : Point) : ℂ :=
  let r := u⁻¹
  (∑ j : Fin 2,
    ((((r:ℂ)^(2 : ℕ)-1)*(incomingJet q true a r v z j).first 1+
        (incomingJet q true a r v z j).first 0)*compactPulseSource q false b v u z j-
      (((r:ℂ)^(2 : ℕ)-1)*(incomingJet q false b r v z j).first 1+
        (incomingJet q false b r v z j).first 0)*compactPulseSource q true a v u z j))/(r:ℂ)^(2 : ℕ)

/-- Cancellation of the actual static-chart factor preserves the full radial contact. -/
theorem originalPulseContact_eq_compact (q : XiZeroCopy) (a b : ℂ) (v : ℝ)
    (x : Iio (0:ℝ)) (z : UpperHalfPlane) :
    originalPulseContact q a b v x (coordinates z) =
      compactPulseContact q a b v (radialUnit x) (coordinates z) := by
  have hR := tortoiseRadius_exterior x x.property
  have hr : (tortoiseRadius x:ℂ) ≠ 0 := by exact_mod_cast (show tortoiseRadius x ≠ 0 by linarith)
  have hf : (tortoiseRadius x:ℂ)^(2 : ℕ)-1 ≠ 0 := by
    exact_mod_cast (show (tortoiseRadius x)^(2 : ℕ)-1 ≠ 0 by nlinarith)
  have hI : (radialUnit x)⁻¹ = tortoiseRadius x := by rw [radialUnit_inverse_radius,inv_inv]
  dsimp only [originalPulseContact,compactPulseContact]
  simp only [normalizedPulseSource_eq_compact q false b v x z,
    normalizedPulseSource_eq_compact q true a v x z,hI,staticJet,Matrix.cons_val_one,Matrix.cons_val_zero,
    Fin.sum_univ_two]
  field_simp [hr,hf]

/-- The horizon trace is obtained only after the retained radial term has its regular limit. -/
theorem compactPulseContact_horizon (q : XiZeroCopy) (a b : ℂ) (v : ℝ) (z : Point) :
    compactPulseContact q a b v 1 z = horizonPulseContact q a b v z := by
  simp only [compactPulseContact,inv_one,Complex.ofReal_one,one_pow,sub_self,
    zero_mul,zero_add,div_one,compactPulseSource_horizon,horizonPulseContact]

private theorem compactPulseSource_continuous (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (v : ℝ) (z : Point) (j : Fin 2) :
    ContinuousAt (fun u => compactPulseSource q branch a v u z j) 1 := by
  have hp : ContinuousAt (fun u : ℝ => power (2*physicalRate q branch) (1+u)) 1 :=
    (power_derivatives (2*physicalRate q branch) (by norm_num : 0 < (1+(1:ℝ)))).1.continuousAt.comp
      (f := fun u : ℝ => 1+u) (by fun_prop)
  unfold compactPulseSource
  fun_prop (disch := norm_num)

private theorem incomingFirst_continuous (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (v : ℝ) (z : Point) (j : Fin 2) :
    ContinuousAt (fun r => (incomingJet q branch a r v z j).first 0) 1 ∧
      ContinuousAt (fun r => (incomingJet q branch a r v z j).first 1) 1 := by
  have hR := responseProfile_derivatives (physicalRate q branch) a ⟨1,by norm_num⟩
  have hP := profile_derivatives (physicalRate q branch) a ⟨1,by norm_num⟩
  have hR0 := hR.1.continuousAt
  have hR1 := hR.2.continuousAt
  have hP0 := hP.1.continuousAt
  have hP1 := hP.2.continuousAt
  constructor
  · change ContinuousAt (fun r =>
      (responseProfile (physicalRate q branch) a r*timeOnsetFirst (2*physicalRate q branch) v)*
        fullAngularCovector q branch j z+
      (profile (physicalRate q branch) a r*timeOnsetFirst (2*physicalRate q branch) v)*
        fullSquareCovector q j z) 1
    fun_prop
  · change ContinuousAt (fun r =>
      (responseProfileFirst (physicalRate q branch) a r*timeOnset (2*physicalRate q branch) v)*
        fullAngularCovector q branch j z+
      (profileFirst (physicalRate q branch) a r*timeOnset (2*physicalRate q branch) v)*
        fullSquareCovector q j z) 1
    fun_prop

private theorem comp_inverse {f : ℝ → ℂ} (hf : ContinuousAt f 1) :
    ContinuousAt (fun u : ℝ => f u⁻¹) 1 := by
  have hf' : ContinuousAt f ((1:ℝ)⁻¹) := by simpa only [inv_one] using hf
  exact hf'.comp (by fun_prop (disch := norm_num))

private theorem compactPulseContact_continuous (q : XiZeroCopy) (a b : ℂ)
    (v : ℝ) (z : Point) : ContinuousAt (fun u => compactPulseContact q a b v u z) 1 := by
  unfold compactPulseContact
  apply ContinuousAt.div
  · have hterm (j : Fin 2) : ContinuousAt (fun u : ℝ =>
        ((((u⁻¹:ℝ):ℂ)^(2 : ℕ)-1)*(incomingJet q true a u⁻¹ v z j).first 1+
            (incomingJet q true a u⁻¹ v z j).first 0)*compactPulseSource q false b v u z j-
          ((((u⁻¹:ℝ):ℂ)^(2 : ℕ)-1)*(incomingJet q false b u⁻¹ v z j).first 1+
            (incomingJet q false b u⁻¹ v z j).first 0)*compactPulseSource q true a v u z j) 1 := by
      have hs := incomingFirst_continuous q true a v z j
      have ht := incomingFirst_continuous q false b v z j
      have hs0 := comp_inverse hs.1
      have hs1 := comp_inverse hs.2
      have ht0 := comp_inverse ht.1
      have ht1 := comp_inverse ht.2
      have ps := compactPulseSource_continuous q true a v z j
      have pt := compactPulseSource_continuous q false b v z j
      fun_prop (disch := norm_num)
    simpa only [Fin.sum_univ_two] using! (hterm 0).add (hterm 1)
  · fun_prop (disch := norm_num)
  · norm_num

/-- The original radial source-contact limit includes both differentiated incoming jets. -/
theorem originalPulseContact_horizon_limit (q : XiZeroCopy) (a b : ℂ)
    (v : ℝ) (z : UpperHalfPlane) :
    Tendsto (fun x => originalPulseContact q a b v x (coordinates z)) atBot
      (𝓝 (horizonPulseContact q a b v (coordinates z))) := by
  have ht := (compactPulseContact_continuous q a b v (coordinates z)).tendsto.comp
    unit_tendsto_horizon
  rw [compactPulseContact_horizon] at ht
  apply ht.congr'
  filter_upwards [eventually_lt_atBot (0:ℝ)] with x hx
  exact (originalPulseContact_eq_compact q a b v ⟨x,hx⟩ z).symm

end
end RHTower.D4BMPulseHorizonSource