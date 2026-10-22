import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalLiftHorizonCurrent
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullSourceOnsetReduction

/-! Full incoming wave-image current, including distinct angular profiles and all four faces. -/
namespace RHTower.D4BMFullIncomingCurrent
open GaloisForLFunctions.HTGeometry D4BMMixedActionCurrent D4BMJointSource
open D4BMModularCore D4BMLaplaceRadial D4BMHorizon D4BMPhysicalLiftCurrent
open D4BMGlobalAngularResponse D4BMAngularSeries
open Set Filter Topology MeasureTheory
noncomputable section
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- Pull an ingoing two-jet into the original static chart. Ordered mixed jets remain distinct. -/
def staticJet (r : ℂ) (P : ScalarTwoJet (Fin 4) ℂ) : ScalarTwoJet (Fin 4) ℂ where
  value := P.value
  first := ![P.first 0,P.first 1+P.first 0/(r^(2 : ℕ)-1),P.first 2,P.first 3]
  second :=
    ![![P.second 0 0,P.second 0 1+P.second 0 0/(r^(2 : ℕ)-1),P.second 0 2,P.second 0 3],
      ![P.second 1 0+P.second 0 0/(r^(2 : ℕ)-1),
        P.second 1 1+(P.second 0 1+P.second 1 0)/(r^(2 : ℕ)-1)+
          P.second 0 0/(r^(2 : ℕ)-1)^(2 : ℕ)-2*r*P.first 0/(r^(2 : ℕ)-1)^(2 : ℕ),
        P.second 1 2+P.second 0 2/(r^(2 : ℕ)-1),P.second 1 3+P.second 0 3/(r^(2 : ℕ)-1)],
      ![P.second 2 0,P.second 2 1+P.second 2 0/(r^(2 : ℕ)-1),P.second 2 2,P.second 2 3],
      ![P.second 3 0,P.second 3 1+P.second 3 0/(r^(2 : ℕ)-1),P.second 3 2,P.second 3 3]]

private def orbit (r : ℂ) (P : ScalarTwoJet (Fin 4) ℂ) : ℂ :=
  r^(2 : ℕ)*(r^(2 : ℕ)-1)*P.second 1 1+r^(2 : ℕ)*(P.second 0 1+P.second 1 0)+
    2*r*P.first 1-2*r*P.first 0

private def curl (P : Fin 2 → ScalarTwoJet (Fin 4) ℂ) (k : Fin 4) : ℂ :=
  (P 1).second 2 k-(P 0).second 3 k

private def cross (P Q : Fin 2 → ScalarTwoJet (Fin 4) ℂ)
    (k l : Fin 4) (a : Fin 2) : ℂ :=
  (P a).first k*curl Q l-(Q a).first l*curl P k

/-- The complete regular current. The two angular components retain the mixed time/radius curls. -/
def regularCurrent (r y : ℂ) (P Q : Fin 2 → ScalarTwoJet (Fin 4) ℂ) : Fin 4 → ℂ :=
  ![(∑ a : Fin 2, ((Q a).first 1*orbit r (P a)-(P a).first 1*orbit r (Q a)))/r^(2 : ℕ),
    (∑ a : Fin 2, (((r^(2 : ℕ)-1)*(Q a).first 1+(Q a).first 0)*orbit r (P a)-
      ((r^(2 : ℕ)-1)*(P a).first 1+(P a).first 0)*orbit r (Q a)))/r^(2 : ℕ),
    -y^(2 : ℕ)/r^(2 : ℕ)*((r^(2 : ℕ)-1)*cross P Q 1 1 1+cross P Q 1 0 1+cross P Q 0 1 1),
    y^(2 : ℕ)/r^(2 : ℕ)*((r^(2 : ℕ)-1)*cross P Q 1 1 0+cross P Q 1 0 0+cross P Q 0 1 0)]

/-- All four expressions are the original Einstein-action current in ingoing coordinates. -/
theorem regular_current_is_action (p : D4BMBackground.ExteriorPoint)
    (P Q : Fin 2 → ScalarTwoJet (Fin 4) ℂ) :
    ingoingAction p (fun a => staticJet (p.val 1) (P a))
      (fun a => staticJet (p.val 1) (Q a)) = regularCurrent (p.val 1) (p.val 3) P Q := by
  have hr : (p.val 1:ℂ) ≠ 0 := by exact_mod_cast (show p.val 1 ≠ 0 by linarith [p.property.1])
  have hf : (p.val 1:ℂ)^(2 : ℕ)-1 ≠ 0 := by exact_mod_cast (show (p.val 1)^(2 : ℕ)-1 ≠ 0 by nlinarith [p.property.1])
  unfold ingoingAction
  simp only [stream_complete_action_current]
  ext j
  fin_cases j
  · simp [streamCurrentDensity,streamMasterValue,staticJet,regularCurrent,orbit,Fin.sum_univ_succ]
    field_simp [hr,hf]
    ring
  · simp [streamCurrentDensity,streamMasterValue,staticJet,regularCurrent,orbit,Fin.sum_univ_succ]
    field_simp [hr,hf]
    ring
  · let r := (p.val 1:ℂ)
    let y := (p.val 3:ℂ)
    change y^(2 : ℕ)/r^(2 : ℕ)*(-(r^(2 : ℕ)-1)*
      (((P 1).first 1+(P 1).first 0/(r^(2 : ℕ)-1))*
        ((Q 1).second 2 1+(Q 1).second 2 0/(r^(2 : ℕ)-1)-((Q 0).second 3 1+(Q 0).second 3 0/(r^(2 : ℕ)-1)))-
       ((Q 1).first 1+(Q 1).first 0/(r^(2 : ℕ)-1))*
        ((P 1).second 2 1+(P 1).second 2 0/(r^(2 : ℕ)-1)-((P 0).second 3 1+(P 0).second 3 0/(r^(2 : ℕ)-1))))+
      ((P 1).first 0*((Q 1).second 2 0-(Q 0).second 3 0)-
       (Q 1).first 0*((P 1).second 2 0-(P 0).second 3 0))/(r^(2 : ℕ)-1)) =
      -y^(2 : ℕ)/r^(2 : ℕ)*((r^(2 : ℕ)-1)*cross P Q 1 1 1+cross P Q 1 0 1+cross P Q 0 1 1)
    dsimp [cross,curl,r,y]
    field_simp [hr,hf]
    ring
  · let r := (p.val 1:ℂ)
    let y := (p.val 3:ℂ)
    change y^(2 : ℕ)/r^(2 : ℕ)*((r^(2 : ℕ)-1)*
      (((P 0).first 1+(P 0).first 0/(r^(2 : ℕ)-1))*
        ((Q 1).second 2 1+(Q 1).second 2 0/(r^(2 : ℕ)-1)-((Q 0).second 3 1+(Q 0).second 3 0/(r^(2 : ℕ)-1)))-
       ((Q 0).first 1+(Q 0).first 0/(r^(2 : ℕ)-1))*
        ((P 1).second 2 1+(P 1).second 2 0/(r^(2 : ℕ)-1)-((P 0).second 3 1+(P 0).second 3 0/(r^(2 : ℕ)-1))))-
      ((P 0).first 0*((Q 1).second 2 0-(Q 0).second 3 0)-
       (Q 0).first 0*((P 1).second 2 0-(P 0).second 3 0))/(r^(2 : ℕ)-1)) =
      y^(2 : ℕ)/r^(2 : ℕ)*((r^(2 : ℕ)-1)*cross P Q 1 1 0+cross P Q 1 0 0+cross P Q 0 1 0)
    dsimp [cross,curl,r,y]
    field_simp [hr,hf]
    ring

/-- Radial factor multiplying the constructed full angular response. -/
def responseProfile (s a : ℂ) (r : ℝ) : ℂ := a^(2 : ℕ)*power (2*s) (1+r⁻¹)
private def responseRate (s : ℂ) (r : ℝ) : ℂ := -2*s/((r:ℂ)*(1+r))
private def responseRateFirst (s : ℂ) (r : ℝ) : ℂ := 2*s*(1+2*r)/((r:ℂ)^(2 : ℕ)*(1+r)^(2 : ℕ))
/-- First radial derivative of the full-response factor. -/
def responseProfileFirst (s a : ℂ) (r : ℝ) : ℂ := responseProfile s a r*responseRate s r
/-- Second radial derivative of the full-response factor. -/
def responseProfileSecond (s a : ℂ) (r : ℝ) : ℂ :=
  responseProfile s a r*((responseRate s r)^(2 : ℕ)+responseRateFirst s r)

/-- Actual first and second radial derivatives, at fixed ingoing time. -/
theorem responseProfile_derivatives (s a : ℂ) (r : Ioi (0:ℝ)) :
    HasDerivAt (responseProfile s a) (responseProfileFirst s a r) r ∧
    HasDerivAt (responseProfileFirst s a) (responseProfileSecond s a r) r := by
  have hr0 : 0 < r.val := r.property
  have hr : (r.val:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr0)
  have hr1 : 1+(r.val:ℂ) ≠ 0 := by exact_mod_cast (show 1+r.val ≠ 0 by linarith [hr0])
  have hr2 : 1+(r.val:ℂ)⁻¹ ≠ 0 := by
    exact_mod_cast (show 1+r.val⁻¹ ≠ 0 by positivity)
  have hi := hasDerivAt_inv (ne_of_gt hr0)
  have hp := (power_derivatives (2*s) (show 0 < 1+r.val⁻¹ by positivity)).1.scomp r.val (hi.const_add 1)
  have h0 : HasDerivAt (responseProfile s a) (responseProfileFirst s a r) r := by
    apply (hp.const_mul (a^(2 : ℕ))).congr_deriv
    dsimp [responseProfileFirst,responseProfile,responseRate,powerFirst]
    push_cast
    field_simp [hr,hr1,hr2]
    ring_nf
    field_simp [hr1]
    ring
  have hd := (((hasDerivAt_id r.val).ofReal_comp).mul
    (((hasDerivAt_id r.val).const_add 1).ofReal_comp)).inv (by simpa using mul_ne_zero hr hr1)
  have h1 : HasDerivAt (responseRate s) (responseRateFirst s r) r := by
    convert! (hd.const_mul (-2*s)) using 1
    · funext x; simp [responseRate,div_eq_mul_inv]
    · dsimp [responseRateFirst]; push_cast; ring
  exact ⟨h0,by
    apply (h0.mul h1).congr_deriv
    dsimp [responseProfileSecond,responseProfileFirst]
    ring⟩

private def tensorJet (c cv cr cvv crv crr : ℂ) (J : ScalarTwoJet (Fin 2) ℂ) :
    ScalarTwoJet (Fin 4) ℂ where
  value := c*J.value
  first := ![cv*J.value,cr*J.value,c*J.first 0,c*J.first 1]
  second := ![![cvv*J.value,crv*J.value,cv*J.first 0,cv*J.first 1],
    ![crv*J.value,crr*J.value,cr*J.first 0,cr*J.first 1],
    ![cv*J.first 0,cr*J.first 0,c*J.second 0 0,c*J.second 0 1],
    ![cv*J.first 1,cr*J.first 1,c*J.second 1 0,c*J.second 1 1]]
private def addJet (P Q : ScalarTwoJet (Fin 4) ℂ) : ScalarTwoJet (Fin 4) ℂ where
  value := P.value+Q.value
  first k := P.first k+Q.first k
  second k l := P.second k l+Q.second k l

/-- Full original wave-image jet: the constructed response and the retained half-square lift. -/
def incomingJet (q : XiZeroCopy) (branch : Bool) (a : ℂ) (r v : ℝ) (z : Point)
    (j : Fin 2) : ScalarTwoJet (Fin 4) ℂ :=
  let s := physicalRate q branch
  let h := timeOnset (2*s) v
  let dh := timeOnsetFirst (2*s) v
  let ddh := timeOnsetSecond (2*s) v
  addJet
    (tensorJet (responseProfile s a r*h) (responseProfile s a r*dh)
      (responseProfileFirst s a r*h) (responseProfile s a r*ddh)
      (responseProfileFirst s a r*dh) (responseProfileSecond s a r*h)
      (ScalarTwoJet.ofField (fullAngularCovector q branch j) z))
    (tensorJet (profile s a r*h) (profile s a r*dh) (profileFirst s a r*h)
      (profile s a r*ddh) (profileFirst s a r*dh) (profileSecond s a r*h) (angularJets q z j))


/-- The jet value is exactly the two original wave-image coefficients, with their original normalization. -/
theorem incoming_value_original (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (x : Iio (0:ℝ)) (v : ℝ) (z : Point) (j : Fin 2) :
    parameter q branch*(radialUnit x:ℂ)*
      (incomingJet q branch a (D4BMJointWave.tortoiseRadius x) v z j).value =
    parameter q branch*timeRadialLift (physicalRate q branch) a (v-x) x*fullSquareCovector q j z-
      timeSourceSeed (physicalRate q branch) a (parameter q branch) (v-x) x*fullAngularCovector q branch j z := by
  have hQ := profile_original (physicalRate q branch) a x v
  dsimp only [incomingJet,addJet,tensorJet,ScalarTwoJet.ofField,angularJets]
  rw [hQ]
  rw [timeSourceSeed,sourceSeedField,sourceAmplitude,sourceSeedPolynomial,parameter_physicalRate]
  simp only [zero_mul,Complex.exp_zero,one_mul,mul_one,sub_add_cancel]
  rw [radialUnit_inverse_radius]
  dsimp [responseProfile,D4BMQuadraticMixedSource.resolventParameter]
  push_cast
  have hr : (D4BMJointWave.tortoiseRadius x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (lt_trans zero_lt_one (D4BMJointWave.tortoiseRadius_exterior x x.property)))
  field_simp [hr]
  ring

/-- Both radial derivatives in the full incoming jet are actual derivatives at fixed ingoing time. -/
theorem incoming_radial_jets (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (r : Ioi (0:ℝ)) (v : ℝ) (z : Point) (j : Fin 2) :
    HasDerivAt (fun x => (incomingJet q branch a x v z j).value)
      ((incomingJet q branch a r v z j).first 1) r ∧
    HasDerivAt (fun x => (incomingJet q branch a x v z j).first 1)
      ((incomingJet q branch a r v z j).second 1 1) r := by
  obtain ⟨h0,h1⟩ := responseProfile_derivatives (physicalRate q branch) a r
  obtain ⟨g0,g1⟩ := profile_derivatives (physicalRate q branch) a r
  constructor
  · convert! ((h0.mul_const (timeOnset (2*physicalRate q branch) v*fullAngularCovector q branch j z)).add
      (g0.mul_const (timeOnset (2*physicalRate q branch) v*fullSquareCovector q j z))) using 1
    · funext x; simp [incomingJet,addJet,tensorJet,ScalarTwoJet.ofField,angularJets]; ring
    · simp [incomingJet,addJet,tensorJet,ScalarTwoJet.ofField,angularJets]; ring
  · convert! ((h1.mul_const (timeOnset (2*physicalRate q branch) v*fullAngularCovector q branch j z)).add
      (g1.mul_const (timeOnset (2*physicalRate q branch) v*fullSquareCovector q j z))) using 1
    · funext x; simp [incomingJet,addJet,tensorJet,ScalarTwoJet.ofField,angularJets]; ring
    · simp [incomingJet,addJet,tensorJet,ScalarTwoJet.ofField,angularJets]; ring

/-- Actual time and mixed time/radius derivatives, preserving the fixed onset. -/
theorem incoming_time_jets (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (r v : ℝ) (z : Point) (j : Fin 2) :
    HasDerivAt (fun w => (incomingJet q branch a r w z j).value)
      ((incomingJet q branch a r v z j).first 0) v ∧
    HasDerivAt (fun w => (incomingJet q branch a r w z j).first 1)
      ((incomingJet q branch a r v z j).second 0 1) v := by
  have h := timeOnset_hasDerivAt (2*physicalRate q branch) v
  constructor
  · convert! h.const_mul (responseProfile (physicalRate q branch) a r*fullAngularCovector q branch j z+
      profile (physicalRate q branch) a r*fullSquareCovector q j z) using 1
    · funext w; simp [incomingJet,addJet,tensorJet,ScalarTwoJet.ofField,angularJets]; ring
    · simp [incomingJet,addJet,tensorJet,ScalarTwoJet.ofField,angularJets]; ring
  · convert! h.const_mul (responseProfileFirst (physicalRate q branch) a r*fullAngularCovector q branch j z+
      profileFirst (physicalRate q branch) a r*fullSquareCovector q j z) using 1
    · funext w; simp [incomingJet,addJet,tensorJet,ScalarTwoJet.ofField,angularJets]; ring
    · simp [incomingJet,addJet,tensorJet,ScalarTwoJet.ofField,angularJets]; ring


/-- The angular derivatives of both orbit derivatives are actual coordinate derivatives.
These are precisely the mixed angular jets entering the two physical cusp-current components. -/
theorem incoming_angular_mixed_jets (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (r v : ℝ) (z : UpperHalfPlane) (j k : Fin 2) :
    ScalarTwoJet.coordDeriv k (fun w => (incomingJet q branch a r v w j).first 0) (coordinates z) =
      (incomingJet q branch a r v (coordinates z) j).second (![2,3] k) 0 ∧
    ScalarTwoJet.coordDeriv k (fun w => (incomingJet q branch a r v w j).first 1) (coordinates z) =
      (incomingJet q branch a r v (coordinates z) j).second (![2,3] k) 1 := by
  have hH := ((fullAngularCovector_smooth q branch (coordinates z) z.im_pos j).differentiableAt (by simp)).hasFDerivAt
  have hQ := ((fullSquareCovector_smooth q (coordinates z) z.im_pos 1 j).differentiableAt (by norm_num)).hasFDerivAt
  have htime := (hH.const_mul (responseProfile (physicalRate q branch) a r*timeOnsetFirst (2*physicalRate q branch) v)).add
    (hQ.const_mul (profile (physicalRate q branch) a r*timeOnsetFirst (2*physicalRate q branch) v))
  have hrad := (hH.const_mul (responseProfileFirst (physicalRate q branch) a r*timeOnset (2*physicalRate q branch) v)).add
    (hQ.const_mul (profileFirst (physicalRate q branch) a r*timeOnset (2*physicalRate q branch) v))
  constructor
  · have hh := congrArg (fun L => L (Pi.single k 1)) htime.fderiv
    fin_cases k <;>
      simpa [incomingJet,addJet,tensorJet,ScalarTwoJet.ofField,angularJets,
        ScalarTwoJet.coordDeriv,add_apply,smul_apply,smul_eq_mul] using! hh
  · have hh := congrArg (fun L => L (Pi.single k 1)) hrad.fderiv
    fin_cases k <;>
      simpa [incomingJet,addJet,tensorJet,ScalarTwoJet.ofField,angularJets,
        ScalarTwoJet.coordDeriv,add_apply,smul_apply,smul_eq_mul] using! hh


/-- Full current of the explicit incoming wave image, keeping both physical branches. -/
def incomingCurrent (q : XiZeroCopy) (a b : ℂ) (r v : ℝ) (z : Point) : Fin 4 → ℂ :=
  regularCurrent r (z 1) (incomingJet q true a r v z) (incomingJet q false b r v z)

/-- Exact identity with the original reconstructed Einstein action, including angular cross terms. -/
theorem incoming_current_is_action (p : D4BMBackground.ExteriorPoint) (q : XiZeroCopy)
    (a b : ℂ) (v : ℝ) :
    ingoingAction p
      (fun j => staticJet (p.val 1) (incomingJet q true a (p.val 1) v ![p.val 2,p.val 3] j))
      (fun j => staticJet (p.val 1) (incomingJet q false b (p.val 1) v ![p.val 2,p.val 3] j)) =
    incomingCurrent q a b (p.val 1) v ![p.val 2,p.val 3] :=
  regular_current_is_action p _ _


private def angularCombine (c d : ℂ) (H Q : ScalarTwoJet (Fin 2) ℂ) : ScalarTwoJet (Fin 2) ℂ where
  value := c*H.value+d*Q.value
  first j := c*H.first j+d*Q.first j
  second j k := c*H.second j k+d*Q.second j k

/-- Normalized original incoming horizon covector, with its actual angular jets. -/
def traceJet (q : XiZeroCopy) (branch : Bool) (z : Point) (j : Fin 2) : ScalarTwoJet (Fin 2) ℂ :=
  let s := physicalRate q branch
  angularCombine 1 (-s*(s-1)/4)
    (ScalarTwoJet.ofField (fullAngularCovector q branch j) z) (angularJets q z j)

/-- Normal derivative of the full incoming field at fixed ingoing time, including the lift term. -/
def normalJet (q : XiZeroCopy) (branch : Bool) (z : Point) (j : Fin 2) : ScalarTwoJet (Fin 2) ℂ :=
  let s := physicalRate q branch
  angularCombine (-s) (s*(s-1)*(s+2)/4)
    (ScalarTwoJet.ofField (fullAngularCovector q branch j) z) (angularJets q z j)

private def pair (P Q : Fin 2 → ScalarTwoJet (Fin 2) ℂ) : ℂ :=
  ∑ j : Fin 2, (P j).value*(Q j).value
private def angularGreen (y : ℂ) (P Q : Fin 2 → ScalarTwoJet (Fin 2) ℂ) : Fin 2 → ℂ :=
  let CP := (P 1).first 0-(P 0).first 1
  let CQ := (Q 1).first 0-(Q 0).first 1
  ![y^(2 : ℕ)*((P 1).value*CQ-(Q 1).value*CP),
    -y^(2 : ℕ)*((P 0).value*CQ-(Q 0).value*CP)]

/-- Exact coefficients of the fixed clock's mass, mixed term and derivative energy.
Rows are the four physical current components; columns are mass, mixed, energy. -/
def clockCoefficients (q : XiZeroCopy) (a b : ℂ) (z : Point) : Fin 4 → Fin 3 → ℂ :=
  let s := physicalRate q true
  let t := physicalRate q false
  let c := a^(2 : ℕ)*b^(2 : ℕ)/64
  let U := traceJet q true z
  let V := traceJet q false z
  let N := normalJet q true z
  let M := normalJet q false z
  let A := pair N M
  let X := pair V N
  let Y := pair U M
  let G := angularGreen (z 1) N V
  let H := angularGreen (z 1) U M
  ![![4*c*((s-t)*A+t*X-s*Y),2*c*(X-Y),0],
    ![4*c*(t*(2*s+1)*X-s*(2*t+1)*Y),-10*c*(X-Y),2*c*(X-Y)],
    ![-2*c*(t*G 0+s*H 0),-c*(G 0+H 0),0],
    ![-2*c*(t*G 1+s*H 1),-c*(G 1+H 1),0]]

/-- All four full incoming horizon components with the original smooth clock. -/
def incomingHorizonCurrent (q : XiZeroCopy) (a b : ℂ) (v : ℝ) (z : Point) (j : Fin 4) : ℂ :=
  clockCoefficients q a b z j 0*onsetSquare v+
    clockCoefficients q a b z j 1*onsetMixed v+
    clockCoefficients q a b z j 2*onsetDerivativeSquare v

private theorem responseProfile_one (s a : ℂ) : responseProfile s a 1=a^(2 : ℕ)*power (2*s) 2 := by
  norm_num [responseProfile]
private theorem responseProfileFirst_one (s a : ℂ) :
    responseProfileFirst s a 1=-s*responseProfile s a 1 := by
  simp [responseProfileFirst,responseRate]; ring
private theorem profile_one (s a : ℂ) : profile s a 1=(-s*(s-1)/4)*responseProfile s a 1 := by
  simp [profile,responseProfile]; ring
private theorem profileFirst_one (s a : ℂ) :
    profileFirst s a 1=(s*(s-1)*(s+2)/4)*responseProfile s a 1 := by
  change profile s a 1*(-(2+2*s)/(1:ℂ)+2*s/(1+1))=_
  rw [profile_one]
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
    rw [← Complex.exp_add]; congr 1; ring
  rw [ht,responseProfile_one,responseProfile_one]
  calc
    _ = a^(2 : ℕ)*b^(2 : ℕ)*(power (2*physicalRate q true) 2*power (2*(-physicalRate q true-3)) 2)*
        (Complex.exp (2*physicalRate q true*(v:ℂ))*Complex.exp (2*(-physicalRate q true-3)*(v:ℂ))) := by ring
    _ = _ := by rw [hp,he]; ring

/-- Actual horizon evaluation of the complete Einstein current, with no shared-profile substitution. -/
theorem incoming_current_horizon_value (q : XiZeroCopy) (a b : ℂ) (v : ℝ) (z : Point) :
    incomingCurrent q a b 1 v z = incomingHorizonCurrent q a b v z := by
  have ht : physicalRate q false= -physicalRate q true-3 := by simp [physicalRate]; ring
  have hp : responseProfile (physicalRate q true) a 1*responseProfile (physicalRate q false) b 1=a^(2 : ℕ)*b^(2 : ℕ)/64 := by
    simpa using branch_factor q a b 0
  have he : Complex.exp (2*physicalRate q true*(v:ℂ))*Complex.exp (2*physicalRate q false*(v:ℂ))=
      Complex.exp (-6*(v:ℂ)) := by
    rw [← Complex.exp_add,ht]; congr 1; ring
  ext j
  fin_cases j <;>
    simp [incomingCurrent,regularCurrent,orbit,cross,curl,incomingJet,addJet,tensorJet,
      incomingHorizonCurrent,clockCoefficients,pair,angularGreen,traceJet,normalJet,angularCombine,
      responseProfileFirst_one,profile_one,profileFirst_one,Fin.sum_univ_succ]
  all_goals simp only [timeOnset,timeOnsetFirst,onsetSquare,onsetMixed,onsetDerivativeSquare]
  all_goals rw [← hp]
  all_goals rw [← he]
  all_goals rw [ht]
  all_goals ring

/-- The original fixed-clock integral of every component, retaining the onset endpoint. -/
theorem incoming_horizon_finite_integral (q : XiZeroCopy) (a b : ℂ) (V : ℝ) (z : Point)
    (j : Fin 4) :
    (∫ v in (0:ℝ)..V, incomingHorizonCurrent q a b v z j) =
      clockCoefficients q a b z j 0*clockMass V+
      clockCoefficients q a b z j 1*(3*clockMass V+onsetSquare V/2)+
      clockCoefficients q a b z j 2*clockEnergy V := by
  have h0 : Continuous Real.smoothTransition := (Real.smoothTransition.contDiff (n := 1)).continuous
  have h1 : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 2)).differentiable_deriv_two.continuous
  have hc0 := Complex.continuous_ofReal.comp h0
  have hc1 := Complex.continuous_ofReal.comp h1
  have he : Continuous (fun v:ℝ => Complex.exp (-6*(v:ℂ))) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.const_mul (-6))
  have hS : Continuous onsetSquare := by unfold onsetSquare; fun_prop
  have hM : Continuous onsetMixed := by unfold onsetMixed; fun_prop
  have hE : Continuous onsetDerivativeSquare := by unfold onsetDerivativeSquare; fun_prop
  have hIS := (hS.intervalIntegrable (μ := volume) (a := 0) (b := V)).const_mul (clockCoefficients q a b z j 0)
  have hIM := (hM.intervalIntegrable (μ := volume) (a := 0) (b := V)).const_mul (clockCoefficients q a b z j 1)
  have hIE := (hE.intervalIntegrable (μ := volume) (a := 0) (b := V)).const_mul (clockCoefficients q a b z j 2)
  simp only [incomingHorizonCurrent]
  rw [intervalIntegral.integral_add (hIS.add hIM) hIE,
    intervalIntegral.integral_add hIS hIM]
  simp only [intervalIntegral.integral_const_mul,clock_mixed_integral,clockMass,clockEnergy]


private theorem all_profiles_continuous (s a : ℂ) :
    ContinuousAt (responseProfile s a) 1 ∧ ContinuousAt (responseProfileFirst s a) 1 ∧
    ContinuousAt (responseProfileSecond s a) 1 ∧ ContinuousAt (profile s a) 1 ∧
    ContinuousAt (profileFirst s a) 1 ∧ ContinuousAt (profileSecond s a) 1 := by
  obtain ⟨h0,h1⟩ := responseProfile_derivatives s a ⟨1,by norm_num⟩
  obtain ⟨g0,g1⟩ := profile_derivatives s a ⟨1,by norm_num⟩
  have hz : ContinuousAt (fun r:ℝ => (r:ℂ)) 1 := Complex.continuous_ofReal.continuousAt
  have hn : ((1:ℝ):ℂ) ≠ 0 := by norm_num
  have hn1 : 1+((1:ℝ):ℂ) ≠ 0 := by norm_num
  have hn2 : ((1:ℝ):ℂ)^(2 : ℕ) ≠ 0 := by norm_num
  have hn3 : (1+((1:ℝ):ℂ))^(2 : ℕ) ≠ 0 := by norm_num
  have hnr : ((1:ℝ):ℂ)*(1+((1:ℝ):ℂ)) ≠ 0 := by norm_num
  have hnrr : ((1:ℝ):ℂ)^(2 : ℕ)*(1+((1:ℝ):ℂ))^(2 : ℕ) ≠ 0 := by norm_num
  have hR : ContinuousAt (responseRate s) 1 := by unfold responseRate; fun_prop
  have hRR : ContinuousAt (responseRateFirst s) 1 := by unfold responseRateFirst; fun_prop
  refine ⟨h0.continuousAt,h1.continuousAt,?_,g0.continuousAt,g1.continuousAt,?_⟩
  · exact h0.continuousAt.mul ((hR.pow 2).add hRR)
  · change ContinuousAt (fun r:ℝ => profile s a r*
      ((-(2+2*s)/(r:ℂ)+2*s/(1+(r:ℂ)))^(2 : ℕ)+((2+2*s)/(r:ℂ)^(2 : ℕ)-2*s/(1+(r:ℂ))^(2 : ℕ)))) 1
    have hg := g0.continuousAt
    fun_prop

/-- Exterior limit of all four original incoming Einstein-current components. -/
theorem incoming_current_horizon_limit (q : XiZeroCopy) (a b : ℂ) (v : ℝ) (z : Point)
    (j : Fin 4) :
    Tendsto (fun r => incomingCurrent q a b r v z j) (𝓝[>] (1:ℝ))
      (𝓝 (incomingHorizonCurrent q a b v z j)) := by
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := all_profiles_continuous (physicalRate q true) a
  obtain ⟨g0,g1,g2,g3,g4,g5⟩ := all_profiles_continuous (physicalRate q false) b
  have hz : ContinuousAt (fun r:ℝ => (r:ℂ)) 1 := Complex.continuous_ofReal.continuousAt
  have hn : ((1:ℝ):ℂ)^(2 : ℕ) ≠ 0 := by norm_num
  have hc : ContinuousAt (fun r => incomingCurrent q a b r v z j) 1 := by
    fin_cases j <;> simp only [incomingCurrent,regularCurrent,orbit,cross,curl,incomingJet,
      addJet,tensorJet,Fin.sum_univ_succ]
    all_goals fun_prop
  have ht := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (1:ℝ)))
  rw [incoming_current_horizon_value] at ht
  exact ht

end
end RHTower.D4BMFullIncomingCurrent
