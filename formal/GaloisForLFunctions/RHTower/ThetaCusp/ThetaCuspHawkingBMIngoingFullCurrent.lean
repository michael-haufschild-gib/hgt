import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalLiftHorizonCurrent

/-! Complete original Einstein current in ingoing stream coordinates.
Every ordered second derivative, angular flux and master-source contact is retained. -/
open Set Filter Topology
open scoped ContDiff
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace
namespace RHTower.D4BMIngoingFullCurrent
open GaloisForLFunctions.HTGeometry D4BMMixedActionCurrent

/-- Exact ordered two-jet for the original shift `p=t+tortoise(R)`. -/
def toStatic (r : ℂ) (P : ScalarTwoJet (Fin 4) ℂ) : ScalarTwoJet (Fin 4) ℂ where
  value := P.value
  first i := P.first i+(if i=1 then P.first 0/(r^(2 : ℕ)-1) else 0)
  second i j := P.second i j+
    (if i=1 then P.second 0 j/(r^(2 : ℕ)-1) else 0)+
    (if j=1 then P.second i 0/(r^(2 : ℕ)-1) else 0)+
    (if i=1 ∧ j=1 then P.second 0 0/(r^(2 : ℕ)-1)^(2 : ℕ)-2*r*P.first 0/(r^(2 : ℕ)-1)^(2 : ℕ) else 0)

def master (r y : ℂ) (P : Fin 2 → ScalarTwoJet (Fin 4) ℂ) (a : Fin 2) : ℂ :=
  r^(2 : ℕ)*(r^(2 : ℕ)-1)*(P a).second 1 1+r^(2 : ℕ)*((P a).second 0 1+(P a).second 1 0)+
    2*r*(P a).first 1-2*r*(P a).first 0+streamAngularAction y P a

def contact (r y : ℂ) (P : Fin 2 → ScalarTwoJet (Fin 4) ℂ) (a : Fin 2) : ℂ :=
  streamAngularAction y P a-master r y P a

def curl (P : Fin 2 → ScalarTwoJet (Fin 4) ℂ) (i : Fin 4) : ℂ :=
  (P 1).second 2 i-(P 0).second 3 i

def angularCurrent (r : ℂ) (P Q : Fin 2 → ScalarTwoJet (Fin 4) ℂ) (a : Fin 2) : ℂ :=
  (r^(2 : ℕ)-1)*((P a).first 1*curl Q 1-(Q a).first 1*curl P 1)+
    (P a).first 1*curl Q 0+(P a).first 0*curl Q 1-
    (Q a).first 1*curl P 0-(Q a).first 0*curl P 1

/-- All four current components, with no inverse power of the horizon factor. -/
def current (r y : ℂ) (P Q : Fin 2 → ScalarTwoJet (Fin 4) ℂ) : Fin 4 → ℂ :=
  ![1/r^(2 : ℕ)*(∑ a : Fin 2, ((P a).first 1*contact r y Q a-(Q a).first 1*contact r y P a)),
    1/r^(2 : ℕ)*(∑ a : Fin 2, (((r^(2 : ℕ)-1)*(P a).first 1+(P a).first 0)*contact r y Q a-
      ((r^(2 : ℕ)-1)*(Q a).first 1+(Q a).first 0)*contact r y P a)),
    -y^(2 : ℕ)/r^(2 : ℕ)*angularCurrent r P Q 1,y^(2 : ℕ)/r^(2 : ℕ)*angularCurrent r P Q 0]

theorem angular_toStatic (r y : ℂ) (P : Fin 2 → ScalarTwoJet (Fin 4) ℂ) (a : Fin 2) :
    streamAngularAction y (fun a => toStatic r (P a)) a=streamAngularAction y P a := by
  simp [streamAngularAction,toStatic]

theorem master_toStatic (r y : ℂ) (hf : r^(2 : ℕ)-1 ≠ 0)
    (P : Fin 2 → ScalarTwoJet (Fin 4) ℂ) (a : Fin 2) :
    streamMasterValue r y (fun a => toStatic r (P a)) a=master r y P a := by
  unfold streamMasterValue
  rw [angular_toStatic]
  simp only [toStatic,ite_true,zero_ne_one,ite_false,add_zero, and_self]
  unfold master
  field_simp [hf]
  ring

private theorem stream_density (r y : ℂ) (P Q : Fin 2 → ScalarTwoJet (Fin 4) ℂ) :
    streamCurrentDensity r y P Q =
    ![-1/((r^(2 : ℕ)-1)*r^(2 : ℕ))*(∑ a : Fin 2, ((P a).first 0*(streamAngularAction y Q a-streamMasterValue r y Q a)-
        (Q a).first 0*(streamAngularAction y P a-streamMasterValue r y P a))),
      (r^(2 : ℕ)-1)/r^(2 : ℕ)*(∑ a : Fin 2, ((P a).first 1*(streamAngularAction y Q a-streamMasterValue r y Q a)-
        (Q a).first 1*(streamAngularAction y P a-streamMasterValue r y P a))),
      y^(2 : ℕ)/r^(2 : ℕ)*(-(r^(2 : ℕ)-1)*((P 1).first 1*curl Q 1-(Q 1).first 1*curl P 1)+
        ((P 1).first 0*curl Q 0-(Q 1).first 0*curl P 0)/(r^(2 : ℕ)-1)),
      y^(2 : ℕ)/r^(2 : ℕ)*((r^(2 : ℕ)-1)*((P 0).first 1*curl Q 1-(Q 0).first 1*curl P 1)-
        ((P 0).first 0*curl Q 0-(Q 0).first 0*curl P 0)/(r^(2 : ℕ)-1))] := by
  rfl

private theorem static_current (r y : ℂ) (hf : r^(2 : ℕ)-1 ≠ 0)
    (P Q : Fin 2 → ScalarTwoJet (Fin 4) ℂ) :
    streamCurrentDensity r y (fun a => toStatic r (P a)) (fun a => toStatic r (Q a))=
    ![-1/((r^(2 : ℕ)-1)*r^(2 : ℕ))*(∑ a : Fin 2, ((P a).first 0*contact r y Q a-(Q a).first 0*contact r y P a)),
      (r^(2 : ℕ)-1)/r^(2 : ℕ)*(∑ a : Fin 2, (((P a).first 1+(P a).first 0/(r^(2 : ℕ)-1))*contact r y Q a-
        ((Q a).first 1+(Q a).first 0/(r^(2 : ℕ)-1))*contact r y P a)),
      y^(2 : ℕ)/r^(2 : ℕ)*(-(r^(2 : ℕ)-1)*(((P 1).first 1+(P 1).first 0/(r^(2 : ℕ)-1))*(curl Q 1+curl Q 0/(r^(2 : ℕ)-1))-
        ((Q 1).first 1+(Q 1).first 0/(r^(2 : ℕ)-1))*(curl P 1+curl P 0/(r^(2 : ℕ)-1)))+
        ((P 1).first 0*curl Q 0-(Q 1).first 0*curl P 0)/(r^(2 : ℕ)-1)),
      y^(2 : ℕ)/r^(2 : ℕ)*((r^(2 : ℕ)-1)*(((P 0).first 1+(P 0).first 0/(r^(2 : ℕ)-1))*(curl Q 1+curl Q 0/(r^(2 : ℕ)-1))-
        ((Q 0).first 1+(Q 0).first 0/(r^(2 : ℕ)-1))*(curl P 1+curl P 0/(r^(2 : ℕ)-1)))-
        ((P 0).first 0*curl Q 0-(Q 0).first 0*curl P 0)/(r^(2 : ℕ)-1))] := by
  rw [stream_density]
  simp only [angular_toStatic,master_toStatic r y hf]
  ext j
  fin_cases j <;> simp [toStatic,contact,curl,Fin.sum_univ_succ]
  all_goals (ring_nf; simp)

/-- The transformed current is the complete original Einstein action current. -/
theorem original_ingoing_current (p : D4BMBackground.ExteriorPoint)
    (P Q : Fin 2 → ScalarTwoJet (Fin 4) ℂ) :
    D4BMPhysicalLiftCurrent.ingoingAction p (fun a => toStatic (p.val 1) (P a))
      (fun a => toStatic (p.val 1) (Q a))=current (p.val 1) (p.val 3) P Q := by
  have hr : (p.val 1:ℂ) ≠ 0 := by exact_mod_cast (show p.val 1 ≠ 0 by linarith [p.property.1])
  have hf : (p.val 1:ℂ)^(2 : ℕ)-1 ≠ 0 := by exact_mod_cast (show (p.val 1)^(2 : ℕ)-1 ≠ 0 by nlinarith [p.property.1])
  unfold D4BMPhysicalLiftCurrent.ingoingAction
  simp only [stream_complete_action_current,static_current _ _ hf]
  ext j
  fin_cases j <;> simp [current,angularCurrent,Fin.sum_univ_succ]
  all_goals field_simp [hr,hf]
  all_goals ring_nf <;> simp

/-- Radial horizon coefficient of the ingoing jet formula, with every source contact retained. -/
theorem current_horizon_radial (y : ℂ) (P Q : Fin 2 → ScalarTwoJet (Fin 4) ℂ) :
    current 1 y P Q 1=∑ a : Fin 2, ((P a).first 0*contact 1 y Q a-(Q a).first 0*contact 1 y P a) := by
  simp [current]

end RHTower.D4BMIngoingFullCurrent
