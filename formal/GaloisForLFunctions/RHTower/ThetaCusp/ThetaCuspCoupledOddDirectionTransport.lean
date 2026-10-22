import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCoupledOddSeamDirection
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspGlobalOddCompensation
import Mathlib.Analysis.Calculus.DSlope

/-!
# Actual-source regular direction transport

The canonical coefficient forces transportP(0)=1. Removing this singular
part by a divided difference yields an explicit integrating-factor solution.
Its continuous direction has the optimal literal seam value and cancels the
complete Schur transport residual at every center. Positivity of the scalar
Schur gap and a controlled join to the established tail direction remain open.
-/

namespace RHTower.ThetaCuspOddDirectionTransport
noncomputable section
open GaloisForLFunctions.HTGeometry
open scoped ContDiff

def moment (k : Fin 7) (x : ℝ) : ℝ :=
  (-1:ℝ)^(k.val+1)*thetaCuspNativeReflectionJet (2*(k.val+1)) x

local notation "H" => thetaCuspNativeOddHeadDet
local notation "D" => thetaCuspNativeOddHankelThreeDet
local notation "G" => thetaCuspCenterCompensationSource
local notation "C3" => thetaCuspNativeOddCompensationCoefficient
local notation "Phi" => thetaCuspFullSource

def cofactorA (x : ℝ) : ℝ :=
  let m := fun k : Fin 7 => moment k x;
  m 0*m 2*m 6-m 0*(m 4)^2-(m 1)^2*m 6+2*m 1*m 3*m 4-m 2*(m 3)^2

def cofactorB (x : ℝ) : ℝ :=
  let m := fun k : Fin 7 => moment k x;
  -(m 0*m 2*m 5-m 0*m 3*m 4-(m 1)^2*m 5+
    m 1*m 2*m 4+m 1*(m 3)^2-(m 2)^2*m 3)

def transportWeight (x : ℝ) : ℝ := C3*Phi x^2*H x

def transportP (x : ℝ) : ℝ := -D x/transportWeight x

def transportF (x : ℝ) : ℝ := cofactorB x/transportWeight x

theorem transportWeight_pos (x : ℝ) : 0 < transportWeight x := by
  exact mul_pos (mul_pos thetaCuspNativeOddCompensationCoefficient_pos
    (sq_pos_of_pos (thetaCuspFullSource_pos_all x))) (thetaCuspNativeOddHeadDet_pos x)

private theorem transportWeight_zero : transportWeight 0 = -D 0 := by
  have hp := (thetaCuspFullSource_pos_all 0).ne'
  have hh := (thetaCuspNativeOddHeadDet_pos 0).ne'
  unfold transportWeight thetaCuspNativeOddCompensationCoefficient
  field_simp

theorem transportP_zero : transportP 0=1 := by
  unfold transportP
  rw [transportWeight_zero]
  exact div_self (neg_ne_zero.mpr thetaCuspNativeOddHankelThreeDet_zero_neg.ne)

theorem transportF_zero : transportF 0=ThetaCuspCoupledSeamDirection.optimalDirection := by
  unfold transportF ThetaCuspCoupledSeamDirection.optimalDirection
  rw [transportWeight_zero]
  have hb : cofactorB 0=ThetaCuspCoupledSeamDirection.borderCofactor := rfl
  rw [hb]
  ring

private theorem differentiable_jet (n : ℕ) : Differentiable ℝ (thetaCuspNativeReflectionJet n) := by
  have hj (k : ℕ) : Differentiable ℝ (iteratedDeriv k thetaCuspFullSource) :=
    contDiff_thetaCuspFullSource.differentiable_iteratedDeriv k
      (by exact_mod_cast ENat.coe_lt_top k)
  change Differentiable ℝ (fun x => thetaCuspNativeReflectionJet n x)
  simp_rw [thetaCuspNativeReflectionJet_eq]
  fun_prop

private theorem differentiable_moment (k : Fin 7) : Differentiable ℝ (moment k) := by
  exact (differentiable_jet _).const_mul _

private theorem differentiable_head : Differentiable ℝ H := by
  unfold thetaCuspNativeOddHeadDet
  have := differentiable_jet
  fun_prop

private theorem differentiable_three : Differentiable ℝ D := by
  unfold thetaCuspNativeOddHankelThreeDet HilbertMetric.signedEvenHankelThreeDet
  have := differentiable_jet
  fun_prop

private theorem differentiable_B : Differentiable ℝ cofactorB := by
  unfold cofactorB
  have := differentiable_moment
  fun_prop

private theorem differentiable_weight : Differentiable ℝ transportWeight := by
  exact ((contDiff_thetaCuspFullSource.differentiable (by simp)).pow 2).const_mul C3 |>.mul
    differentiable_head

theorem differentiable_transportP : Differentiable ℝ transportP :=
  differentiable_three.neg.div differentiable_weight (fun x => (transportWeight_pos x).ne')

theorem differentiable_transportF : Differentiable ℝ transportF :=
  differentiable_B.div differentiable_weight (fun x => (transportWeight_pos x).ne')

/-- The singular coefficient has a canonical continuous removable quotient. -/
def regularCoefficient : ℝ → ℝ := dslope transportP 0

theorem continuous_regularCoefficient : Continuous regularCoefficient := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x=0
  · subst x
    exact continuousAt_dslope_same.mpr (differentiable_transportP 0)
  · exact (continuousAt_dslope_of_ne hx).mpr (differentiable_transportP.continuous.continuousAt)

theorem regularCoefficient_identity (x : ℝ) : x*regularCoefficient x=transportP x-1 := by
  have h := sub_smul_dslope transportP 0 x
  simpa [regularCoefficient,transportP_zero,smul_eq_mul] using h

def logFactor (x : ℝ) : ℝ := ∫ t in (0:ℝ)..x, regularCoefficient t

def integratingFactor (x : ℝ) : ℝ := Real.exp (logFactor x)

private theorem factor_pos (x : ℝ) : 0 < integratingFactor x := Real.exp_pos _

private theorem logFactor_deriv (x : ℝ) : HasDerivAt logFactor (regularCoefficient x) x :=
  intervalIntegral.integral_hasDerivAt_right (continuous_regularCoefficient.intervalIntegrable 0 x)
    (continuous_regularCoefficient.stronglyMeasurableAtFilter _ _)
    continuous_regularCoefficient.continuousAt

private theorem factor_deriv (x : ℝ) :
    HasDerivAt integratingFactor (integratingFactor x*regularCoefficient x) x :=
  (logFactor_deriv x).exp

private theorem factor_continuous : Continuous integratingFactor :=
  continuous_iff_continuousAt.mpr fun x => (factor_deriv x).continuousAt

def primitive (x : ℝ) : ℝ := ∫ t in (0:ℝ)..x, integratingFactor t*transportF t

private theorem primitive_deriv (x : ℝ) :
    HasDerivAt primitive (integratingFactor x*transportF x) x := by
  have hc := factor_continuous.mul differentiable_transportF.continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

def regularNumerator (x : ℝ) : ℝ := primitive x/integratingFactor x

private theorem numerator_zero : regularNumerator 0=0 := by simp [regularNumerator,primitive]

private theorem numerator_deriv (x : ℝ) :
    HasDerivAt regularNumerator (transportF x-regularCoefficient x*regularNumerator x) x := by
  have hd := (primitive_deriv x).div (factor_deriv x) (factor_pos x).ne'
  have he : (integratingFactor x*transportF x*integratingFactor x-
      primitive x*(integratingFactor x*regularCoefficient x))/(integratingFactor x)^2 =
      transportF x-regularCoefficient x*regularNumerator x := by
    unfold regularNumerator
    field_simp [(factor_pos x).ne']
  rw [he] at hd
  exact hd

/-- Canonical regular solution selected by the actual infinite source. -/
def direction : ℝ → ℝ := dslope regularNumerator 0

theorem continuous_direction : Continuous direction := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x=0
  · subst x
    exact continuousAt_dslope_same.mpr (numerator_deriv 0).differentiableAt
  · exact (continuousAt_dslope_of_ne hx).mpr (numerator_deriv x).continuousAt

private theorem numerator_eq (x : ℝ) : x*direction x=regularNumerator x := by
  simpa [direction,smul_eq_mul] using sub_smul_dslope_of_zero numerator_zero x

theorem direction_zero : direction 0=ThetaCuspCoupledSeamDirection.optimalDirection := by
  unfold direction
  rw [dslope_same,(numerator_deriv 0).deriv,numerator_zero,mul_zero,sub_zero,transportF_zero]

theorem differentiableAt_direction {x : ℝ} (hx : x ≠ 0) :
    DifferentiableAt ℝ direction x :=
  (differentiableAt_dslope_of_ne hx).mpr (numerator_deriv x).differentiableAt

theorem direction_ode (x : ℝ) :
    x*deriv direction x+transportP x*direction x=transportF x := by
  by_cases hx : x=0
  · subst x
    rw [transportP_zero,direction_zero,transportF_zero]
    ring
  · have he := differentiableAt_direction hx
    have hn : HasDerivAt (fun t => t*direction t)
        (direction x+x*deriv direction x) x := by
      convert (hasDerivAt_id' x).mul he.hasDerivAt using 1 <;> first | rfl | ring
    have heq : (fun t => t*direction t)=regularNumerator := funext numerator_eq
    rw [heq] at hn
    have hder := hn.unique (numerator_deriv x)
    have hc := regularCoefficient_identity x
    rw [← numerator_eq] at hder
    have hp : transportP x=1+x*regularCoefficient x := by linarith only [hc]
    rw [hp]
    nlinarith only [hder]

/-- The literal source direction cancels the complete squared Schur transport residual. -/
theorem direction_cancels_residual (x : ℝ) :
    transportWeight x*x*deriv direction x-D x*direction x-cofactorB x=0 := by
  have h := direction_ode x
  unfold transportP transportF at h
  have hw := (transportWeight_pos x).ne'
  field_simp [hw] at h
  nlinarith only [h]

end
end RHTower.ThetaCuspOddDirectionTransport
