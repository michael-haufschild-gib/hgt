import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarLinearizedRicciJet

namespace RHTower.D4BMVectorLinearEquation
open GaloisForLFunctions.HTGeometry
open D4BMScalarLinearEquation
noncomputable section

private abbrev Jet := ScalarTwoJet (Fin 4) ℂ

/-- First covector component jet under the actual divergence and rough equations. -/
def angular0 (s y A P Q R U W : ℂ) : Jet where
  value := A
  first := ![0,0,P,Q]
  second := !![0,0,0,0; 0,0,0,0;
    0,0,U,W; 0,0,W,((s+1)*(s+2)*A-2*y*(Q-R))/y^2-U]

/-- Second covector component jet, retaining the differentiated divergence constraints. -/
def angular1 (s y C P R U W : ℂ) : Jet where
  value := C
  first := ![0,0,R,-P]
  second := !![0,0,0,0; 0,0,0,0;
    0,0,W+(s+1)*(s+2)*C/y^2,-U; 0,0,-U,-W]

/-- Complete separated vector metric jet, including all symmetric and mixed components. -/
def vectorJet (s r y B A C P Q R U W : ℂ) : CoordinateMetricTwoJet 4 ℂ :=
  let rJ := coord r 1
  let F := (rJ.mul rJ).add (ScalarTwoJet.constant (-1))
  let common := (ScalarTwoJet.constant (-s)).mul (temporalRadial s r B)
  let t := common.mul rJ.inv
  let v := common.mul F.inv
  let V0 := angular0 s y A P Q R U W
  let V1 := angular1 s y C P R U W
  let Z : Jet := ScalarTwoJet.constant 0
  let J := !![Z,Z,t.mul V0,t.mul V1; Z,Z,v.mul V0,v.mul V1;
    t.mul V0,v.mul V0,Z,Z; t.mul V1,v.mul V1,Z,Z]
  ⟨fun i j => (J i j).value, fun k i j => (J i j).first k,
    fun k l i j => (J i j).second k l⟩

private theorem background_metric (r y : ℂ) :
    (D4BMBackground.jet r y).metric = D4BMBackground.metric r y := rfl

private theorem background_first (r y : ℂ) (k : Fin 4) :
    (D4BMBackground.jet r y).first k = Matrix.diagonal
      (if k = 1 then ![-2*r, -2*r*(r^2-1)⁻¹^2, 2*r*y⁻¹^2, 2*r*y⁻¹^2]
       else if k = 3 then ![0, 0, -2*r^2*y⁻¹^3, -2*r^2*y⁻¹^3] else 0) := rfl

private theorem background_second (r y : ℂ) (k l : Fin 4) :
    (D4BMBackground.jet r y).second k l = Matrix.diagonal
      (if k = 1 ∧ l = 1 then ![-2, -2*(r^2-1)⁻¹^2+8*r^2*(r^2-1)⁻¹^3,
        2*y⁻¹^2, 2*y⁻¹^2]
       else if (k = 1 ∧ l = 3) ∨ (k = 3 ∧ l = 1) then ![0,0,-4*r*y⁻¹^3,-4*r*y⁻¹^3]
       else if k = 3 ∧ l = 3 then ![0,0,6*r^2*y⁻¹^4,6*r^2*y⁻¹^4] else 0) := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- Every vector coordinate component satisfies the linearized Ricci equation. -/
theorem ricci_component (s r y B A C P Q R U W : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (vectorJet s r y B A C P Q R U W) i j +
      3*(vectorJet s r y B A C P Q R U W).metric i j = 0 := by
  generalize hK : vectorJet s r y B A C P Q R U W = K
  fin_cases i <;> fin_cases j
  all_goals simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, background_first, background_second,
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals simp [Fin.sum_univ_succ, Matrix.mul_apply]
  all_goals rw [← hK]
  all_goals simp [vectorJet, temporalRadial, angular0, angular1,
    coord, ScalarTwoJet.add, ScalarTwoJet.mul,
    ScalarTwoJet.inv, ScalarTwoJet.constant]
  all_goals try simp only [← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hf, hr, hy]
  all_goals ring

/-- The complete vector cosmological Einstein residual vanishes. -/
theorem cosmological_component (s r y B A C P Q R U W : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet r y)
      (vectorJet s r y B A C P Q R U W) (-3) i j = 0 := by
  apply D4BMLinearizedRicci.cosmological_zero_of_ricci r y _ hr hy hf
  intro k l
  have hz := ricci_component s r y B A C P Q R U W hr hy hf k l
  linear_combination hz

end
end RHTower.D4BMVectorLinearEquation
