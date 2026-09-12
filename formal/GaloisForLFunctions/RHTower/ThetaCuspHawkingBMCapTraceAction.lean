import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullIncomingCurrent
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFutureHorizonCap

/-! Original Einstein stream current plus its actual source contact, on all four faces.
The radial horizon expression retains only time/angular jets, while the finite-radius
identity retains the weighted normal derivative. The source cap's derived scalar trace
has actual coexact, time and angular derivatives; their radial pairing equals the original
lift trace expression, with the full square/gradient source and unchanged clock.

This leaf does not interchange derivatives with the cap's infinite integral or horizon
limit. It asserts no cap-current admission, complete nonlinear SS/SV/VV assembly,
physical left-QNM extinction, or Riemann hypothesis.
-/

open Set Filter Topology MeasureTheory
namespace RHTower.D4BMCapTraceAction
open GaloisForLFunctions.HTGeometry D4BMMixedActionCurrent
open D4BMFullIncomingCurrent D4BMPhysicalLiftCurrent D4BMFutureHorizon
open D4BMJointSource D4BMModularCore
noncomputable section
set_option autoImplicit false

/-- The regular original master, including its angular term. -/
def master (r y : ℂ) (P : Fin 2 → ScalarTwoJet (Fin 4) ℂ) (a : Fin 2) : ℂ :=
  r^2*(r^2-1)*(P a).second 1 1+r^2*((P a).second 0 1+(P a).second 1 0)+
    2*r*(P a).first 1-2*r*(P a).first 0+streamAngularAction y P a

/-- Source contact before deleting any wave residual or boundary component. -/
def contact (r y : ℂ) (P Q : Fin 2 → ScalarTwoJet (Fin 4) ℂ) : Fin 4 → ℂ :=
  ![(∑ a : Fin 2, ((P a).first 1*master r y Q a-(Q a).first 1*master r y P a))/r^2,
    (∑ a : Fin 2, (((r^2-1)*(P a).first 1+(P a).first 0)*master r y Q a-
      ((r^2-1)*(Q a).first 1+(Q a).first 0)*master r y P a))/r^2,0,0]

/-- All four faces after the original master contact is included. -/
def angularCurrent (r y : ℂ) (P Q : Fin 2 → ScalarTwoJet (Fin 4) ℂ) : Fin 4 → ℂ :=
  ![(∑ a : Fin 2, ((P a).first 1*streamAngularAction y Q a-
      (Q a).first 1*streamAngularAction y P a))/r^2,
    (∑ a : Fin 2, (((r^2-1)*(P a).first 1+(P a).first 0)*streamAngularAction y Q a-
      ((r^2-1)*(Q a).first 1+(Q a).first 0)*streamAngularAction y P a))/r^2,
    regularCurrent r y P Q 2,regularCurrent r y P Q 3]

theorem current_add_contact (r y : ℂ) (P Q : Fin 2 → ScalarTwoJet (Fin 4) ℂ) :
    regularCurrent r y P Q+contact r y P Q=angularCurrent r y P Q := by
  let O := fun J : ScalarTwoJet (Fin 4) ℂ =>
    r^2*(r^2-1)*J.second 1 1+r^2*(J.second 0 1+J.second 1 0)+
      2*r*J.first 1-2*r*J.first 0
  ext j
  fin_cases j
  · change ((∑ a : Fin 2, ((Q a).first 1*O (P a)-(P a).first 1*O (Q a)))/r^2)+
      ((∑ a : Fin 2, ((P a).first 1*master r y Q a-(Q a).first 1*master r y P a))/r^2)=_
    rw [← add_div,← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    dsimp [O,master]
    ring
  · change ((∑ a : Fin 2, (((r^2-1)*(Q a).first 1+(Q a).first 0)*O (P a)-
        ((r^2-1)*(P a).first 1+(P a).first 0)*O (Q a)))/r^2)+
      ((∑ a : Fin 2, (((r^2-1)*(P a).first 1+(P a).first 0)*master r y Q a-
        ((r^2-1)*(Q a).first 1+(Q a).first 0)*master r y P a))/r^2)=_
    rw [← add_div,← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    dsimp [O,master]
    ring
  · exact add_zero _
  · exact add_zero _

theorem contact_is_original (p : D4BMBackground.ExteriorPoint)
    (P Q : Fin 2 → ScalarTwoJet (Fin 4) ℂ) :
    ingoingContact p (fun a => staticJet (p.val 1) (P a))
      (fun a => staticJet (p.val 1) (Q a))=contact (p.val 1) (p.val 3) P Q := by
  have hr : (p.val 1:ℂ) ≠ 0 := by exact_mod_cast (show p.val 1 ≠ 0 by linarith [p.property.1])
  have hf : (p.val 1:ℂ)^2-1 ≠ 0 := by
    exact_mod_cast (show (p.val 1)^2-1 ≠ 0 by nlinarith [p.property.1])
  ext j
  fin_cases j
  all_goals simp [ingoingContact,contact,staticJet,streamMasterValue,streamAngularAction,
    master,Fin.sum_univ_two]
  all_goals field_simp [hr,hf]
  all_goals ring

theorem physical_current_add_contact (p : D4BMBackground.ExteriorPoint)
    (P Q : Fin 2 → ScalarTwoJet (Fin 4) ℂ) :
    ingoingAction p (fun a => staticJet (p.val 1) (P a))
      (fun a => staticJet (p.val 1) (Q a))+
    ingoingContact p (fun a => staticJet (p.val 1) (P a))
      (fun a => staticJet (p.val 1) (Q a))=
      angularCurrent (p.val 1) (p.val 3) P Q := by
  rw [regular_current_is_action,contact_is_original,current_add_contact]

/-- A radial horizon trace identity, not an assertion that arbitrary jets have a limit. -/
theorem radial_horizon (y : ℂ) (P Q : Fin 2 → ScalarTwoJet (Fin 4) ℂ) :
    (regularCurrent 1 y P Q+contact 1 y P Q) 1=
      ∑ a : Fin 2, ((P a).first 0*streamAngularAction y Q a-
        (Q a).first 0*streamAngularAction y P a) := by
  rw [current_add_contact]
  simp [angularCurrent]

open D4BMHorizon

/-- The already derived scalar boundary value of the original future cap. -/
def scalarTrace (q : XiZeroCopy) (branch : Bool) (a : ℂ) (v : ℝ) (z : Point) : ℂ :=
  liftTraceCoefficient q branch a*timeOnset (2*physicalRate q branch) v*fullSquarePotential q z

theorem scalarTrace_is_cap_limit (q : XiZeroCopy) (branch : Bool) (a : ℂ) (v X k : ℝ) :
    Tendsto (fun x => capBoundaryField q branch a (v-x) x X k) atBot
      (𝓝 (scalarTrace q branch a v ![X,Real.exp k])) :=
  capBoundaryField_ingoing q branch a v X k

/-- The literal angular covector trace, before any angular principal-part truncation. -/
def covectorTrace (q : XiZeroCopy) (branch : Bool) (a : ℂ) (v : ℝ) : Covector :=
  fun j z => liftTraceCoefficient q branch a*timeOnset (2*physicalRate q branch) v*
    fullSquareCovector q j z

theorem covectorTrace_is_coexact (q : XiZeroCopy) (branch : Bool) (a : ℂ) (v : ℝ)
    (z : {z : Point // 0 < z 1}) (j : Fin 2) :
    coexact (scalarTrace q branch a v) j z=covectorTrace q branch a v j z := by
  have hf := (fullSquarePotential_smooth q z z.property 1).differentiableAt (by norm_num)
  unfold scalarTrace covectorTrace
  rw [← fullSquarePotential_coexact q z z.property j]
  fin_cases j <;> simp [coexact,ScalarTwoJet.coordDeriv,fderiv_const_mul hf,smul_eq_mul]

theorem covectorTrace_time_derivative (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (v : ℝ) (z : Point) (j : Fin 2) :
    HasDerivAt (fun u => covectorTrace q branch a u j z)
      (liftTraceCoefficient q branch a*timeOnsetFirst (2*physicalRate q branch) v*
        fullSquareCovector q j z) v :=
  ((timeOnset_hasDerivAt (2*physicalRate q branch) v).const_mul
    (liftTraceCoefficient q branch a)).mul_const (fullSquareCovector q j z)

private theorem trace_jets (q : XiZeroCopy) (branch : Bool) (a : ℂ) (v : ℝ)
    (z : {z : Point // 0 < z 1}) (j : Fin 2) :
    ScalarTwoJet.ofField (covectorTrace q branch a v j) z=
      ScalarTwoJet.mul (ScalarTwoJet.constant
        (liftTraceCoefficient q branch a*timeOnset (2*physicalRate q branch) v))
        (angularJets q z j) := by
  change ScalarTwoJet.ofField (fun w =>
    (liftTraceCoefficient q branch a*timeOnset (2*physicalRate q branch) v)*
      fullSquareCovector q j w) z=_
  rw [ScalarTwoJet.ofField_mul contDiffAt_const
    (fullSquareCovector_smooth q z z.property 2 j),ScalarTwoJet.ofField_constant]
  rfl

/-- The angular action is evaluated on actual derivatives of the trace field. -/
def traceAction (q : XiZeroCopy) (branch : Bool) (a : ℂ) (v : ℝ) (z : Point) (j : Fin 2) : ℂ :=
  roughLaplacian (covectorTrace q branch a v) j z-covectorTrace q branch a v j z

theorem traceAction_original (q : XiZeroCopy) (branch : Bool) (a : ℂ) (v : ℝ)
    (z : {z : Point // 0 < z 1}) (j : Fin 2) :
    traceAction q branch a v z j=
      liftTraceCoefficient q branch a*timeOnset (2*physicalRate q branch) v*angularAction q z j := by
  have hs (j : Fin 2) : ContDiffAt ℝ 2 (covectorTrace q branch a v j) z :=
    contDiffAt_const.mul (fullSquareCovector_smooth q z z.property 2 j)
  unfold traceAction
  rw [roughLaplacian_eq _ z z.property hs]
  have h1 (j i : Fin 2) := congrArg (fun J : ScalarTwoJet (Fin 2) ℂ => J.first i)
    (trace_jets q branch a v z j)
  have h2 (j i k : Fin 2) := congrArg (fun J : ScalarTwoJet (Fin 2) ℂ => J.second i k)
    (trace_jets q branch a v z j)
  simp only [ScalarTwoJet.mul,ScalarTwoJet.constant,ScalarTwoJet.ofField,
    angularJets,zero_mul,add_zero,zero_add] at h1 h2
  fin_cases j <;> simp [roughFormula,h1,h2,angularAction,angularJets,
    ScalarTwoJet.ofField,covectorTrace]
  all_goals ring

/-- The radial angular Wronskian of the two actual source boundary traces.
This does not assert interchange of a horizon limit and derivatives of the cap integral. -/
def traceFlux (q : XiZeroCopy) (a b : ℂ) (v : ℝ) (z : Point) : ℂ :=
  ∑ j : Fin 2,
    (deriv (fun u => covectorTrace q true a u j z) v*traceAction q false b v z j-
      deriv (fun u => covectorTrace q false b u j z) v*traceAction q true a v z j)

private theorem opposite_rate (q : XiZeroCopy) :
    physicalRate q false = -physicalRate q true-3 := by
  simp [physicalRate]
  ring

private theorem trace_coefficient_profile (q : XiZeroCopy) (branch : Bool) (a : ℂ) :
    liftTraceCoefficient q branch a=profile (physicalRate q branch) a 1 := by
  simp only [liftTraceCoefficient,profile,Complex.ofReal_one,inv_one,one_pow,mul_one,
    show (1:ℝ)+1=2 by norm_num]
  ring

theorem traceFlux_eq_lift_angular (q : XiZeroCopy) (a b : ℂ) (v : ℝ)
    (z : {z : Point // 0 < z 1}) :
    traceFlux q a b v z=liftAngularCurrent q (physicalRate q true)
      (physicalRate q false) a b 1 v z 1 := by
  unfold traceFlux
  simp_rw [(covectorTrace_time_derivative q true a v z _).deriv,
    (covectorTrace_time_derivative q false b v z _).deriv,
    traceAction_original,trace_coefficient_profile]
  simp [liftAngularCurrent,angularPair,Fin.sum_univ_two]
  ring

private theorem profile_factor (s a b : ℂ) :
    2*(2*s+3)*profile s a 1*profile (-s-3) b 1=horizonFactor s a b := by
  have hp : D4BMLaplaceRadial.power (2*s) 2*D4BMLaplaceRadial.power (2*(-s-3)) 2=(1:ℂ)/64 := by
    unfold D4BMLaplaceRadial.power
    norm_cast
    rw [← Complex.cpow_add _ _ (show (2:ℂ) ≠ 0 by norm_num),
      show 2*s+2*(-s-3)=-(6:ℂ) by ring,Complex.cpow_neg,Complex.cpow_ofNat]
    norm_num
  simp only [profile,Complex.ofReal_one,inv_one,one_pow,mul_one,show (1:ℝ)+1=2 by norm_num]
  calc
    _ = (2*(2*s+3)*(-s*(s-1)/4)*(-(-s-3)*(-s-3-1)/4)*a^2*b^2)*
        (D4BMLaplaceRadial.power (2*s) 2*D4BMLaplaceRadial.power (2*(-s-3)) 2) := by ring
    _ = horizonFactor s a b := by rw [hp]; unfold horizonFactor; ring

/-- The fixed onset derivative cancels in this antisymmetric trace pairing; the angular
source term and the original clock mass remain. -/
theorem traceFlux_original_clock (q : XiZeroCopy) (a b : ℂ) (v : ℝ)
    (z : {z : Point // 0 < z 1}) :
    traceFlux q a b v z=horizonFactor (physicalRate q true) a b*onsetSquare v*angularPair q z := by
  rw [traceFlux_eq_lift_angular,opposite_rate]
  let s := physicalRate q true
  have he : Complex.exp ((2*s)*(v:ℂ))*Complex.exp ((2*(-s-3))*(v:ℂ))=
      Complex.exp (-(6*(v:ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  change liftAngularCurrent q s (-s-3) a b 1 v z 1=_
  simp only [liftAngularCurrent,Complex.ofReal_one,one_pow,sub_self,zero_mul,zero_add,div_one]
  change (profile s a 1*timeOnsetFirst (2*s) v*(profile (-s-3) b 1*timeOnset (2*(-s-3)) v)-
    profile (-s-3) b 1*timeOnsetFirst (2*(-s-3)) v*(profile s a 1*timeOnset (2*s) v))*
      angularPair q z=horizonFactor s a b*onsetSquare v*angularPair q z
  rw [← profile_factor]
  unfold onsetSquare
  rw [show (-6:ℂ)*(v:ℂ)=-(6*(v:ℂ)) by ring,he.symm]
  dsimp [timeOnset,timeOnsetFirst]
  ring

/-- Complete square and gradient-source insertion in the literal cap trace expression. -/
theorem traceFlux_square_gradient (q : XiZeroCopy) (a b : ℂ) (v : ℝ)
    (z : {z : Point // 0 < z 1}) :
    traceFlux q a b v z=horizonFactor (physicalRate q true) a b*onsetSquare v*
      ((2*(physicalRate q true+1)*(physicalRate q true+2)-2)*angularSquare q z+
        2*gradientPair q true z) := by
  rw [traceFlux_original_clock,angular_pair_original q true z]

theorem traceFlux_finite_integral (q : XiZeroCopy) (a b : ℂ) (V : ℝ)
    (z : {z : Point // 0 < z 1}) :
    (∫ v in (0:ℝ)..V,traceFlux q a b v z)=
      horizonFactor (physicalRate q true) a b*clockMass V*angularPair q z := by
  simp_rw [traceFlux_original_clock]
  rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_const_mul]
  rfl

/-- A fixed physical-time translation of the late source trace has the original damping
factor. No source-dependent frequency or adjusted clock is introduced. -/
theorem traceFlux_physical_step (q : XiZeroCopy) (a b : ℂ) (T : Ici (0:ℝ)) (v : Ici (1:ℝ))
    (z : {z : Point // 0 < z 1}) :
    traceFlux q a b (v+T) z=Complex.exp (-6*(T:ℂ))*traceFlux q a b v z := by
  rw [traceFlux_original_clock,traceFlux_original_clock]
  have hvT : 1 ≤ (v:ℝ)+T := v.property.trans (le_add_of_nonneg_right T.property)
  simp only [onsetSquare,Real.smoothTransition.one_of_one_le v.property,
    Real.smoothTransition.one_of_one_le hvT,Complex.ofReal_one,one_pow,mul_one,
    Complex.ofReal_add]
  rw [show (-6:ℂ)*((v:ℂ)+(T:ℂ))=-6*(T:ℂ)+(-6)*(v:ℂ) by ring,Complex.exp_add]
  ring

end
end RHTower.D4BMCapTraceAction
