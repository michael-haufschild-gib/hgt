import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMForcedMetricField
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMInverseRadiusCoordinates

/-! The reconstructed metric in actual ingoing inverse-radius coordinates. -/

open GaloisForLFunctions.HTGeometry Filter Topology
open scoped ContDiff
namespace RHTower.D4BMModularCore
open D4BMHorizon D4BMMetricReconstruction D4BMIngoingCoordinates D4BMGlobalAngularResponse
noncomputable section

/-- The complete forced metric in ingoing inverse-radius coordinates, including the du components. -/
def compactForcedMetric (q : XiZeroCopy) (branch : Bool) (a : ℂ) (v : ℝ) (u : ℂ) (z : Point) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  let s := physicalRate q branch
  let c := s*(s-1)/4
  let E := compactEnvelope (2*s) (a^(2 : ℕ)) v u
  let A := fullAngularCovector q branch
  let J := fullSquareCovector q
  let T := fun k => E*(2*s*u*A k z+2*c*u*(1-(s+1)*u^(2 : ℕ))*J k z)
  let U := fun k => E*(-2*s/(1+u)*A k z+2*c*u*(1+(s+1)*u)/(1+u)*J k z)
  !![0,0,T 0,T 1; 0,0,U 0,U 1; T 0,U 0,0,0; T 1,U 1,0,0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Both coordinate differentials pull the actual reconstructed metric to this regular expression. -/
theorem compactForcedMetric_actual (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (x : Fin 4 → ℝ) (hr : 1 < x 1) :
    inverseRadiusPullback (x 1 : ℂ)⁻¹
      (pullback (x 1) (forcedMetricField q branch a (staticPoint x))) =
      compactForcedMetric q branch a (x 0) (x 1 : ℂ)⁻¹ (angularPoint x) := by
  have hr0 : (x 1 : ℂ) ≠ 0 := by exact_mod_cast (by linarith : x 1 ≠ 0)
  have hp : (x 1 : ℂ)+1 ≠ 0 := by exact_mod_cast (by linarith : x 1+1 ≠ 0)
  have hf : (x 1 : ℂ)^(2 : ℕ)-1 ≠ 0 := by exact_mod_cast (by nlinarith : (x 1)^(2 : ℕ)-1 ≠ 0)
  have hu : 1+(x 1 : ℂ)⁻¹ ≠ 0 := by
    have he : 1+(x 1 : ℂ)⁻¹ = ((x 1 : ℂ)+1)/(x 1 : ℂ) := by field_simp
    rw [he]
    exact div_ne_zero hp hr0
  have hE := envelope_staticPoint (2*physicalRate q branch) (a^(2 : ℕ)) x hr
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [inverseRadiusPullback,inverseRadiusJacobian,pullback,jacobian,
    forcedMetricField,streamMetricField,streamTimeBlock,streamRadiusBlock,streamRadialField,
    streamRadialDerivative,Matrix.mul_apply,Fin.sum_univ_succ,staticPoint,angularPoint,
    compactForcedMetric] at hE ⊢
  all_goals try rw [hE]
  all_goals try simp only [← pow_two,← sub_eq_add_neg]
  all_goals field_simp [hr0,hf,hp,hu]
  all_goals ring

/-- The actual reconstructed metric extends holomorphically in inverse radius near both physical endpoints. -/
theorem compactForcedMetric_smooth (q : XiZeroCopy) (branch : Bool) (a : ℂ) (v : ℝ)
    (u : ℂ) (z : Point) (hu : 1+u ∈ Complex.slitPlane) (m : WithTop ℕ∞) (i j : Fin 4) :
    ContDiffAt ℂ m (fun t => compactForcedMetric q branch a v t z i j) u := by
  have hE := compactEnvelope_contDiffAt (2*physicalRate q branch) (a^(2 : ℕ)) v u hu m
  have hi : ContDiffAt ℂ m (fun t : ℂ => (1+t)⁻¹) u :=
    (contDiffAt_const.add contDiffAt_id).inv (Complex.slitPlane_ne_zero hu)
  fin_cases i <;> fin_cases j <;> simp [compactForcedMetric,div_eq_mul_inv]
  all_goals fun_prop

end
end RHTower.D4BMModularCore
