import GaloisForLFunctions.RHTower.ThetaCuspCoupledOddDirectionTransport
import GaloisForLFunctions.RHTower.ThetaCuspCoupledOddSeamObstruction

/-!
# Exact source Schur gap along regular direction transport

The complete corrected determinant splits into the already positive third
minor times one scalar gap, minus the exact squared transport residual.
The source-derived direction cancels that residual and starts with a strictly
positive gap. Global gap positivity and tail compatibility remain open.
-/

namespace RHTower.ThetaCuspOddDirectionTransport
noncomputable section
open Filter Topology

private theorem determinant_schur {a b c d e f g s t r L : ℝ} :
    (a*c-b^2)*Matrix.det
      !![a,b,c,d; b,c,d,e; c,d,e+s,f+s*t+r; d,e,f+s*t+r,g+s*t^2+2*t*r+L] =
    (a*c*e-a*d^2-b^2*e+2*b*c*d-c^3+s*(a*c-b^2))*
      (a*c*g-a*e^2-b^2*g+2*b*d*e-c*d^2+L*(a*c-b^2)+
        (a*c*e-a*d^2-b^2*e+2*b*c*d-c^3)*t^2-
        2*(a*c*f-a*d*e-b^2*f+b*c*e+b*d^2-c^2*d)*t)-
      ((a*c-b^2)*r-(a*c*e-a*d^2-b^2*e+2*b*c*d-c^3)*t+
        (a*c*f-a*d*e-b^2*f+b*c*e+b*d^2-c^2*d))^2 := by
  have hcast : Fin.castSucc (2 : Fin 3) = (2 : Fin 4) := rfl
  rw [Matrix.det_succ_row_zero]
  norm_num [Matrix.det_fin_three, Fin.sum_univ_succ, Fin.succAbove,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
    hcast, Fin.lt_def, Fin.le_def, Fin.isValue, -Fin.val_fin_lt, -Fin.val_fin_le, -Fin.val_pos_iff]
  ring

local notation "H" => thetaCuspNativeOddHeadDet
local notation "D" => thetaCuspNativeOddHankelThreeDet
local notation "G" => thetaCuspCenterCompensationSource
local notation "C3" => thetaCuspNativeOddCompensationCoefficient
local notation "Phi" => thetaCuspFullSource

/-- Full source correction with an independently displayed direction and its derivative. -/
def correctedMatrix (C x t v : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  let m := fun k : Fin 7 => moment k x;
  let s := C3*G x
  let r := C3*x*Phi x^2*v
  !![m 0,m 1,m 2,m 3; m 1,m 2,m 3,m 4;
     m 2,m 3,m 4+s,m 5+s*t+r; m 3,m 4,m 5+s*t+r,m 6+s*t^2+2*t*r+C*G x]

def schurGap (C x t : ℝ) : ℝ :=
  cofactorA x+C*G x*H x+D x*t^2+2*cofactorB x*t

def transportResidual (x t v : ℝ) : ℝ := transportWeight x*x*v-D x*t-cofactorB x

private theorem native_head_eq (x : ℝ) : moment 0 x*moment 2 x-(moment 1 x)^2=H x := by
  norm_num [moment,thetaCuspNativeOddHeadDet]

private theorem native_three_eq (x : ℝ) :
    moment 0 x*moment 2 x*moment 4 x-moment 0 x*(moment 3 x)^2-(moment 1 x)^2*moment 4 x+
      2*moment 1 x*moment 2 x*moment 3 x-(moment 2 x)^3=D x := by
  norm_num [moment,thetaCuspNativeOddHankelThreeDet,HilbertMetric.signedEvenHankelThreeDet]

/-- Exact source Schur identity, retaining the squared transport defect. -/
theorem determinant_residual_square (C x t v : ℝ) :
    H x*(correctedMatrix C x t v).det=
      thetaCuspNativeOddCompensatedDet C3 x*schurGap C x t-transportResidual x t v^2 := by
  have h := determinant_schur (a:=moment 0 x) (b:=moment 1 x) (c:=moment 2 x)
    (d:=moment 3 x) (e:=moment 4 x) (f:=moment 5 x) (g:=moment 6 x)
    (s:=C3*G x) (t:=t) (r:=C3*x*Phi x^2*v) (L:=C*G x)
  rw [native_head_eq,native_three_eq] at h
  dsimp only [correctedMatrix]
  rw [h]
  unfold thetaCuspNativeOddCompensatedDet schurGap transportResidual transportWeight
    cofactorA cofactorB
  ring

/-- The constructed source direction removes the residual at every center. -/
theorem determinant_direction (C x : ℝ) :
    H x*(correctedMatrix C x (direction x) (deriv direction x)).det=
      thetaCuspNativeOddCompensatedDet C3 x*schurGap C x (direction x) := by
  rw [determinant_residual_square]
  have h := direction_cancels_residual x
  change transportResidual x (direction x) (deriv direction x)=0 at h
  rw [h]
  ring

/-- The only remaining determinant sign is the actual scalar Schur gap. -/
theorem determinant_direction_pos_iff (C : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    0 < (correctedMatrix C x (direction x) (deriv direction x)).det ↔
      0 < schurGap C x (direction x) := by
  have hH := thetaCuspNativeOddHeadDet_pos x
  have hD := thetaCuspNativeOddCanonicalCompensatedDet_pos_global x hx
  have he := determinant_direction C x
  constructor
  · intro hp
    have hm := mul_pos hH hp
    rw [he] at hm
    by_contra hn
    exact (not_le_of_gt hm) (mul_nonpos_of_nonneg_of_nonpos hD.le (le_of_not_gt hn))
  · intro hp
    have hm := mul_pos hD hp
    rw [← he] at hm
    by_contra hn
    exact (not_le_of_gt hm) (mul_nonpos_of_nonneg_of_nonpos hH.le (le_of_not_gt hn))

private theorem correctedMatrix_zero (C : ℝ) :
    correctedMatrix C 0 (direction 0) (deriv direction 0)=
      ThetaCuspCoupledSeamDirection.seamMatrix C ThetaCuspCoupledSeamDirection.optimalDirection := by
  rw [direction_zero]
  unfold correctedMatrix ThetaCuspCoupledSeamDirection.seamMatrix
  simp only [mul_zero,zero_mul,add_zero]
  rfl

/-- The actual regular transport starts strictly inside the positive Schur chamber. -/
theorem schurGap_zero_pos : 0 < schurGap 10000000000000 0 (direction 0) := by
  apply (determinant_direction_pos_iff 10000000000000 (by norm_num : (0:ℝ) ≤ 0)).mp
  rw [correctedMatrix_zero]
  exact ThetaCuspCoupledSeamObstruction.actual_optimal_seam_determinant_pos

private theorem continuous_gap : Continuous (fun x => schurGap 10000000000000 x (direction x)) := by
  have hj (k : Fin 7) : Continuous (moment k) :=
    (continuous_thetaCuspNativeReflectionJet _).const_mul _
  have hP : Continuous Phi := contDiff_thetaCuspFullSource.continuous
  have hP' : Continuous (deriv Phi) :=
    (contDiff_thetaCuspFullSource.continuous_iteratedDeriv 1 (by simp)).congr
      (fun x => by rw [iteratedDeriv_one])
  unfold schurGap cofactorA cofactorB thetaCuspCenterCompensationSource
    thetaCuspNativeOddHeadDet thetaCuspNativeOddHankelThreeDet HilbertMetric.signedEvenHankelThreeDet
  have hn := continuous_thetaCuspNativeReflectionJet
  have he := continuous_direction
  fun_prop

/-- A source-derived transport solution exists inside a nontrivial positive seam chamber. -/
theorem eventually_schurGap_pos :
    ∀ᶠ x : ℝ in nhds 0, 0 < schurGap 10000000000000 x (direction x) :=
  continuous_gap.continuousAt.eventually (eventually_gt_nhds schurGap_zero_pos)

end
end RHTower.ThetaCuspOddDirectionTransport
