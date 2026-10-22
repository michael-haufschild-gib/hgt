import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMVectorLinearizedRicciJet

/-!
# The complete BM vector Einstein operator as a master curl

Evaluate every component of the actual linearized Einstein contraction on a
complete divergence-free vector-stream metric jet. The operator has only mixed
components, fixed by one master expression and its full radial derivative.
Neither an angular eigen-equation nor a homogeneous radial equation is assumed.
-/

namespace RHTower.D4BMVectorStream
open GaloisForLFunctions.HTGeometry D4BMScalarLinearEquation
noncomputable section
private abbrev Jet := ScalarTwoJet (Fin 4) ℂ

/-- Time-separated radial two-jet, with free radial derivatives. -/
def radialJet (w H H1 H2 : ℂ) : Jet where
  value := H
  first := ![w*H,H1,0,0]
  second := !![w^(2 : ℕ)*H,w*H1,0,0; w*H1,H2,0,0; 0,0,0,0; 0,0,0,0]

/-- First component of a divergence-free angular covector jet. -/
def covector0 (A P Q U V Z : ℂ) : Jet where
  value := A
  first := ![0,0,P,Q]
  second := !![0,0,0,0; 0,0,0,0; 0,0,U,V; 0,0,V,Z]

/-- Second component, retaining both differentiated divergence identities. -/
def covector1 (C P R U V W : ℂ) : Jet where
  value := C
  first := ![0,0,R,-P]
  second := !![0,0,0,0; 0,0,0,0; 0,0,W,-U; 0,0,-U,-V]

/-- Complete metric jet of the orbit stream: temporal component f times its
radial derivative and radial component w/f times its value. -/
def metricJet (w r H H1 H2 H3 A C P Q R U V W Z : ℂ) : CoordinateMetricTwoJet 4 ℂ :=
  let rJ := coord r 1
  let F := (rJ.mul rJ).add (ScalarTwoJet.constant (-1))
  let t := F.mul (radialJet w H1 H2 H3)
  let v := ((ScalarTwoJet.constant w).mul (radialJet w H H1 H2)).mul F.inv
  let V0 := covector0 A P Q U V Z
  let V1 := covector1 C P R U V W
  let zero : Jet := ScalarTwoJet.constant 0
  let M := !![zero,zero,t.mul V0,t.mul V1; zero,zero,v.mul V0,v.mul V1;
    t.mul V0,v.mul V0,zero,zero; t.mul V1,v.mul V1,zero,zero]
  ⟨fun i j => (M i j).value, fun k i j => (M i j).first k,
    fun k l i j => (M i j).second k l⟩

/-- Forced vector master expression, with the actual angular Laplacian component. -/
def master (w r H H1 H2 A D : ℂ) : ℂ :=
  (r^(2 : ℕ)*(r^(2 : ℕ)-1)*H2+2*r*H1-(w^(2 : ℕ)*r^(2 : ℕ)/(r^(2 : ℕ)-1)+2)*H)*A+H*D

/-- Full radial derivative of the forced vector master expression. -/
def masterFirst (w r H H1 H2 H3 A D : ℂ) : ℂ :=
  (r^(2 : ℕ)*(r^(2 : ℕ)-1)*H3+4*r^(3 : ℕ)*H2-w^(2 : ℕ)*r^(2 : ℕ)/(r^(2 : ℕ)-1)*H1+
    2*w^(2 : ℕ)*r/(r^(2 : ℕ)-1)^(2 : ℕ)*H)*A+H1*D

private theorem background_metric (r y : ℂ) :
    (D4BMBackground.jet r y).metric = D4BMBackground.metric r y := rfl

private theorem background_first (r y : ℂ) (k : Fin 4) :
    (D4BMBackground.jet r y).first k = Matrix.diagonal
      (if k = 1 then ![-2*r, -2*r*(r^(2 : ℕ)-1)⁻¹^(2 : ℕ), 2*r*y⁻¹^(2 : ℕ), 2*r*y⁻¹^(2 : ℕ)]
       else if k = 3 then ![0, 0, -2*r^(2 : ℕ)*y⁻¹^(3 : ℕ), -2*r^(2 : ℕ)*y⁻¹^(3 : ℕ)] else 0) := rfl

private theorem background_second (r y : ℂ) (k l : Fin 4) :
    (D4BMBackground.jet r y).second k l = Matrix.diagonal
      (if k = 1 ∧ l = 1 then ![-2, -2*(r^(2 : ℕ)-1)⁻¹^(2 : ℕ)+8*r^(2 : ℕ)*(r^(2 : ℕ)-1)⁻¹^(3 : ℕ),
        2*y⁻¹^(2 : ℕ), 2*y⁻¹^(2 : ℕ)]
       else if (k = 1 ∧ l = 3) ∨ (k = 3 ∧ l = 1) then ![0,0,-4*r*y⁻¹^(3 : ℕ),-4*r*y⁻¹^(3 : ℕ)]
       else if k = 3 ∧ l = 3 then ![0,0,6*r^(2 : ℕ)*y⁻¹^(4 : ℕ),6*r^(2 : ℕ)*y⁻¹^(4 : ℕ)] else 0) := rfl

/-- Background first/second entries with the index conditionals already resolved, so the
expansion below never evaluates a decidable branch. -/

private theorem background_first_0 (r y : ℂ) :
    (D4BMBackground.jet r y).first 0 = Matrix.diagonal 0 := rfl

private theorem background_first_1 (r y : ℂ) :
    (D4BMBackground.jet r y).first 1 = Matrix.diagonal ![-2*r, -2*r*(r^(2 : ℕ)-1)⁻¹^(2 : ℕ), 2*r*y⁻¹^(2 : ℕ), 2*r*y⁻¹^(2 : ℕ)] := rfl

private theorem background_first_2 (r y : ℂ) :
    (D4BMBackground.jet r y).first 2 = Matrix.diagonal 0 := rfl

private theorem background_first_3 (r y : ℂ) :
    (D4BMBackground.jet r y).first 3 = Matrix.diagonal ![0, 0, -2*r^(2 : ℕ)*y⁻¹^(3 : ℕ), -2*r^(2 : ℕ)*y⁻¹^(3 : ℕ)] := rfl

private theorem background_second_0_0 (r y : ℂ) :
    (D4BMBackground.jet r y).second 0 0 = Matrix.diagonal 0 := rfl

private theorem background_second_0_1 (r y : ℂ) :
    (D4BMBackground.jet r y).second 0 1 = Matrix.diagonal 0 := rfl

private theorem background_second_0_2 (r y : ℂ) :
    (D4BMBackground.jet r y).second 0 2 = Matrix.diagonal 0 := rfl

private theorem background_second_0_3 (r y : ℂ) :
    (D4BMBackground.jet r y).second 0 3 = Matrix.diagonal 0 := rfl

private theorem background_second_1_0 (r y : ℂ) :
    (D4BMBackground.jet r y).second 1 0 = Matrix.diagonal 0 := rfl

private theorem background_second_1_1 (r y : ℂ) :
    (D4BMBackground.jet r y).second 1 1 = Matrix.diagonal ![-2, -2*(r^(2 : ℕ)-1)⁻¹^(2 : ℕ)+8*r^(2 : ℕ)*(r^(2 : ℕ)-1)⁻¹^(3 : ℕ), 2*y⁻¹^(2 : ℕ), 2*y⁻¹^(2 : ℕ)] := rfl

private theorem background_second_1_2 (r y : ℂ) :
    (D4BMBackground.jet r y).second 1 2 = Matrix.diagonal 0 := rfl

private theorem background_second_1_3 (r y : ℂ) :
    (D4BMBackground.jet r y).second 1 3 = Matrix.diagonal ![0,0,-4*r*y⁻¹^(3 : ℕ),-4*r*y⁻¹^(3 : ℕ)] := rfl

private theorem background_second_2_0 (r y : ℂ) :
    (D4BMBackground.jet r y).second 2 0 = Matrix.diagonal 0 := rfl

private theorem background_second_2_1 (r y : ℂ) :
    (D4BMBackground.jet r y).second 2 1 = Matrix.diagonal 0 := rfl

private theorem background_second_2_2 (r y : ℂ) :
    (D4BMBackground.jet r y).second 2 2 = Matrix.diagonal 0 := rfl

private theorem background_second_2_3 (r y : ℂ) :
    (D4BMBackground.jet r y).second 2 3 = Matrix.diagonal 0 := rfl

private theorem background_second_3_0 (r y : ℂ) :
    (D4BMBackground.jet r y).second 3 0 = Matrix.diagonal 0 := rfl

private theorem background_second_3_1 (r y : ℂ) :
    (D4BMBackground.jet r y).second 3 1 = Matrix.diagonal ![0,0,-4*r*y⁻¹^(3 : ℕ),-4*r*y⁻¹^(3 : ℕ)] := rfl

private theorem background_second_3_2 (r y : ℂ) :
    (D4BMBackground.jet r y).second 3 2 = Matrix.diagonal 0 := rfl

private theorem background_second_3_3 (r y : ℂ) :
    (D4BMBackground.jet r y).second 3 3 = Matrix.diagonal ![0,0,6*r^(2 : ℕ)*y⁻¹^(4 : ℕ),6*r^(2 : ℕ)*y⁻¹^(4 : ℕ)] := rfl


/-- Complete mixed source tensor determined by the vector master and its radial derivative. -/
def sourceTensor (w r y H H1 H2 H3 A C Q R U V W Z : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  let D0 := y^(2 : ℕ)*(U+Z)+2*y*(Q-R)
  let D1 := y^(2 : ℕ)*(W-V)
  let T0 := -(r^(2 : ℕ)-1)/(2*r^(2 : ℕ))*masterFirst w r H H1 H2 H3 A D0
  let T1 := -(r^(2 : ℕ)-1)/(2*r^(2 : ℕ))*masterFirst w r H H1 H2 H3 C D1
  let R0 := -w/(2*r^(2 : ℕ)*(r^(2 : ℕ)-1))*master w r H H1 H2 A D0
  let R1 := -w/(2*r^(2 : ℕ)*(r^(2 : ℕ)-1))*master w r H H1 H2 C D1
  !![0,0,T0,T1; 0,0,R0,R1; T0,R0,0,0; T1,R1,0,0]

/-! The sixteen coordinate components, each as its own declaration: a single `fin_cases`
fan would pay all sixteen expansions of the nested `Fin 4` curvature contraction inside
one elaboration. -/

set_option maxRecDepth 8192 in
private theorem ricci_0_0 (w r y H H1 H2 H3 A C P Q R U V W Z : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (metricJet w r H H1 H2 H3 A C P Q R U V W Z) 0 0 +
      3*(metricJet w r H H1 H2 H3 A C P Q R U V W Z).metric 0 0 =
    sourceTensor w r y H H1 H2 H3 A C Q R U V W Z 0 0 := by
  generalize hK : metricJet w r H H1 H2 H3 A C P Q R U V W Z = K
  all_goals simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals rw [← hK]
  all_goals simp [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply, metricJet, radialJet, covector0, covector1,
    coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.inv, ScalarTwoJet.constant,
    sourceTensor]
  all_goals simp only [master, masterFirst, ← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hf, hr, hy]
  all_goals ring

set_option maxRecDepth 8192 in
private theorem ricci_0_1 (w r y H H1 H2 H3 A C P Q R U V W Z : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (metricJet w r H H1 H2 H3 A C P Q R U V W Z) 0 1 +
      3*(metricJet w r H H1 H2 H3 A C P Q R U V W Z).metric 0 1 =
    sourceTensor w r y H H1 H2 H3 A C Q R U V W Z 0 1 := by
  generalize hK : metricJet w r H H1 H2 H3 A C P Q R U V W Z = K
  all_goals simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals rw [← hK]
  all_goals simp [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply, metricJet, radialJet, covector0, covector1,
    coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.inv, ScalarTwoJet.constant,
    sourceTensor]
  all_goals simp only [master, masterFirst, ← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hf, hr, hy]
  all_goals ring

set_option maxRecDepth 8192 in
private theorem ricci_0_2 (w r y H H1 H2 H3 A C P Q R U V W Z : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (metricJet w r H H1 H2 H3 A C P Q R U V W Z) 0 2 +
      3*(metricJet w r H H1 H2 H3 A C P Q R U V W Z).metric 0 2 =
    sourceTensor w r y H H1 H2 H3 A C Q R U V W Z 0 2 := by
  generalize hK : metricJet w r H H1 H2 H3 A C P Q R U V W Z = K
  all_goals simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals rw [← hK]
  all_goals simp [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply, metricJet, radialJet, covector0, covector1,
    coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.inv, ScalarTwoJet.constant,
    sourceTensor]
  all_goals simp only [master, masterFirst, ← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hf, hr, hy]
  all_goals ring

set_option maxRecDepth 8192 in
private theorem ricci_0_3 (w r y H H1 H2 H3 A C P Q R U V W Z : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (metricJet w r H H1 H2 H3 A C P Q R U V W Z) 0 3 +
      3*(metricJet w r H H1 H2 H3 A C P Q R U V W Z).metric 0 3 =
    sourceTensor w r y H H1 H2 H3 A C Q R U V W Z 0 3 := by
  generalize hK : metricJet w r H H1 H2 H3 A C P Q R U V W Z = K
  all_goals simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals rw [← hK]
  all_goals simp [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply, metricJet, radialJet, covector0, covector1,
    coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.inv, ScalarTwoJet.constant,
    sourceTensor]
  all_goals simp only [master, masterFirst, ← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hf, hr, hy]
  all_goals ring

set_option maxRecDepth 8192 in
private theorem ricci_1_0 (w r y H H1 H2 H3 A C P Q R U V W Z : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (metricJet w r H H1 H2 H3 A C P Q R U V W Z) 1 0 +
      3*(metricJet w r H H1 H2 H3 A C P Q R U V W Z).metric 1 0 =
    sourceTensor w r y H H1 H2 H3 A C Q R U V W Z 1 0 := by
  generalize hK : metricJet w r H H1 H2 H3 A C P Q R U V W Z = K
  all_goals simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals rw [← hK]
  all_goals simp [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply, metricJet, radialJet, covector0, covector1,
    coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.inv, ScalarTwoJet.constant,
    sourceTensor]
  all_goals simp only [master, masterFirst, ← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hf, hr, hy]
  all_goals ring

set_option maxRecDepth 8192 in
private theorem ricci_1_1 (w r y H H1 H2 H3 A C P Q R U V W Z : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (metricJet w r H H1 H2 H3 A C P Q R U V W Z) 1 1 +
      3*(metricJet w r H H1 H2 H3 A C P Q R U V W Z).metric 1 1 =
    sourceTensor w r y H H1 H2 H3 A C Q R U V W Z 1 1 := by
  generalize hK : metricJet w r H H1 H2 H3 A C P Q R U V W Z = K
  all_goals simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals rw [← hK]
  all_goals simp [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply, metricJet, radialJet, covector0, covector1,
    coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.inv, ScalarTwoJet.constant,
    sourceTensor]
  all_goals simp only [master, masterFirst, ← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hf, hr, hy]
  all_goals ring

set_option maxRecDepth 8192 in
private theorem ricci_1_2 (w r y H H1 H2 H3 A C P Q R U V W Z : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (metricJet w r H H1 H2 H3 A C P Q R U V W Z) 1 2 +
      3*(metricJet w r H H1 H2 H3 A C P Q R U V W Z).metric 1 2 =
    sourceTensor w r y H H1 H2 H3 A C Q R U V W Z 1 2 := by
  generalize hK : metricJet w r H H1 H2 H3 A C P Q R U V W Z = K
  all_goals simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals rw [← hK]
  all_goals simp [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply, metricJet, radialJet, covector0, covector1,
    coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.inv, ScalarTwoJet.constant,
    sourceTensor]
  all_goals simp only [master, masterFirst, ← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hf, hr, hy]
  all_goals ring

set_option maxRecDepth 8192 in
private theorem ricci_1_3 (w r y H H1 H2 H3 A C P Q R U V W Z : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (metricJet w r H H1 H2 H3 A C P Q R U V W Z) 1 3 +
      3*(metricJet w r H H1 H2 H3 A C P Q R U V W Z).metric 1 3 =
    sourceTensor w r y H H1 H2 H3 A C Q R U V W Z 1 3 := by
  generalize hK : metricJet w r H H1 H2 H3 A C P Q R U V W Z = K
  all_goals simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals rw [← hK]
  all_goals simp [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply, metricJet, radialJet, covector0, covector1,
    coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.inv, ScalarTwoJet.constant,
    sourceTensor]
  all_goals simp only [master, masterFirst, ← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hf, hr, hy]
  all_goals ring

set_option maxRecDepth 8192 in
private theorem ricci_2_0 (w r y H H1 H2 H3 A C P Q R U V W Z : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (metricJet w r H H1 H2 H3 A C P Q R U V W Z) 2 0 +
      3*(metricJet w r H H1 H2 H3 A C P Q R U V W Z).metric 2 0 =
    sourceTensor w r y H H1 H2 H3 A C Q R U V W Z 2 0 := by
  generalize hK : metricJet w r H H1 H2 H3 A C P Q R U V W Z = K
  all_goals simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals rw [← hK]
  all_goals simp [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply, metricJet, radialJet, covector0, covector1,
    coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.inv, ScalarTwoJet.constant,
    sourceTensor]
  all_goals simp only [master, masterFirst, ← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hf, hr, hy]
  all_goals ring

set_option maxRecDepth 8192 in
private theorem ricci_2_1 (w r y H H1 H2 H3 A C P Q R U V W Z : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (metricJet w r H H1 H2 H3 A C P Q R U V W Z) 2 1 +
      3*(metricJet w r H H1 H2 H3 A C P Q R U V W Z).metric 2 1 =
    sourceTensor w r y H H1 H2 H3 A C Q R U V W Z 2 1 := by
  generalize hK : metricJet w r H H1 H2 H3 A C P Q R U V W Z = K
  all_goals simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals rw [← hK]
  all_goals simp [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply, metricJet, radialJet, covector0, covector1,
    coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.inv, ScalarTwoJet.constant,
    sourceTensor]
  all_goals simp only [master, masterFirst, ← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hf, hr, hy]
  all_goals ring

set_option maxRecDepth 8192 in
private theorem ricci_2_2 (w r y H H1 H2 H3 A C P Q R U V W Z : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (metricJet w r H H1 H2 H3 A C P Q R U V W Z) 2 2 +
      3*(metricJet w r H H1 H2 H3 A C P Q R U V W Z).metric 2 2 =
    sourceTensor w r y H H1 H2 H3 A C Q R U V W Z 2 2 := by
  generalize hK : metricJet w r H H1 H2 H3 A C P Q R U V W Z = K
  all_goals simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals rw [← hK]
  all_goals simp [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply, metricJet, radialJet, covector0, covector1,
    coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.inv, ScalarTwoJet.constant,
    sourceTensor]
  all_goals simp only [master, masterFirst, ← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hf, hr, hy]
  all_goals ring

set_option maxRecDepth 8192 in
private theorem ricci_2_3 (w r y H H1 H2 H3 A C P Q R U V W Z : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (metricJet w r H H1 H2 H3 A C P Q R U V W Z) 2 3 +
      3*(metricJet w r H H1 H2 H3 A C P Q R U V W Z).metric 2 3 =
    sourceTensor w r y H H1 H2 H3 A C Q R U V W Z 2 3 := by
  generalize hK : metricJet w r H H1 H2 H3 A C P Q R U V W Z = K
  all_goals simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals rw [← hK]
  all_goals simp [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply, metricJet, radialJet, covector0, covector1,
    coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.inv, ScalarTwoJet.constant,
    sourceTensor]
  all_goals simp only [master, masterFirst, ← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hf, hr, hy]
  all_goals ring

set_option maxRecDepth 8192 in
private theorem ricci_3_0 (w r y H H1 H2 H3 A C P Q R U V W Z : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (metricJet w r H H1 H2 H3 A C P Q R U V W Z) 3 0 +
      3*(metricJet w r H H1 H2 H3 A C P Q R U V W Z).metric 3 0 =
    sourceTensor w r y H H1 H2 H3 A C Q R U V W Z 3 0 := by
  generalize hK : metricJet w r H H1 H2 H3 A C P Q R U V W Z = K
  all_goals simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals rw [← hK]
  all_goals simp [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply, metricJet, radialJet, covector0, covector1,
    coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.inv, ScalarTwoJet.constant,
    sourceTensor]
  all_goals simp only [master, masterFirst, ← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hf, hr, hy]
  all_goals ring

set_option maxRecDepth 8192 in
private theorem ricci_3_1 (w r y H H1 H2 H3 A C P Q R U V W Z : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (metricJet w r H H1 H2 H3 A C P Q R U V W Z) 3 1 +
      3*(metricJet w r H H1 H2 H3 A C P Q R U V W Z).metric 3 1 =
    sourceTensor w r y H H1 H2 H3 A C Q R U V W Z 3 1 := by
  generalize hK : metricJet w r H H1 H2 H3 A C P Q R U V W Z = K
  all_goals simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals rw [← hK]
  all_goals simp [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply, metricJet, radialJet, covector0, covector1,
    coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.inv, ScalarTwoJet.constant,
    sourceTensor]
  all_goals simp only [master, masterFirst, ← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hf, hr, hy]
  all_goals ring

set_option maxRecDepth 8192 in
private theorem ricci_3_2 (w r y H H1 H2 H3 A C P Q R U V W Z : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (metricJet w r H H1 H2 H3 A C P Q R U V W Z) 3 2 +
      3*(metricJet w r H H1 H2 H3 A C P Q R U V W Z).metric 3 2 =
    sourceTensor w r y H H1 H2 H3 A C Q R U V W Z 3 2 := by
  generalize hK : metricJet w r H H1 H2 H3 A C P Q R U V W Z = K
  all_goals simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals rw [← hK]
  all_goals simp [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply, metricJet, radialJet, covector0, covector1,
    coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.inv, ScalarTwoJet.constant,
    sourceTensor]
  all_goals simp only [master, masterFirst, ← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hf, hr, hy]
  all_goals ring

set_option maxRecDepth 8192 in
private theorem ricci_3_3 (w r y H H1 H2 H3 A C P Q R U V W Z : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (metricJet w r H H1 H2 H3 A C P Q R U V W Z) 3 3 +
      3*(metricJet w r H H1 H2 H3 A C P Q R U V W Z).metric 3 3 =
    sourceTensor w r y H H1 H2 H3 A C Q R U V W Z 3 3 := by
  generalize hK : metricJet w r H H1 H2 H3 A C P Q R U V W Z = K
  all_goals simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals rw [← hK]
  all_goals simp [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply, metricJet, radialJet, covector0, covector1,
    coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.inv, ScalarTwoJet.constant,
    sourceTensor]
  all_goals simp only [master, masterFirst, ← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hf, hr, hy]
  all_goals ring

/-- All sixteen actual Ricci residual components are the displayed master curl.
No angular eigen-equation or radial field equation is assumed. -/
theorem ricci_component (w r y H H1 H2 H3 A C P Q R U V W Z : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (metricJet w r H H1 H2 H3 A C P Q R U V W Z) i j +
      3*(metricJet w r H H1 H2 H3 A C P Q R U V W Z).metric i j =
    sourceTensor w r y H H1 H2 H3 A C Q R U V W Z i j := by
  fin_cases i <;> fin_cases j
  · exact ricci_0_0 w r y H H1 H2 H3 A C P Q R U V W Z hr hy hf
  · exact ricci_0_1 w r y H H1 H2 H3 A C P Q R U V W Z hr hy hf
  · exact ricci_0_2 w r y H H1 H2 H3 A C P Q R U V W Z hr hy hf
  · exact ricci_0_3 w r y H H1 H2 H3 A C P Q R U V W Z hr hy hf
  · exact ricci_1_0 w r y H H1 H2 H3 A C P Q R U V W Z hr hy hf
  · exact ricci_1_1 w r y H H1 H2 H3 A C P Q R U V W Z hr hy hf
  · exact ricci_1_2 w r y H H1 H2 H3 A C P Q R U V W Z hr hy hf
  · exact ricci_1_3 w r y H H1 H2 H3 A C P Q R U V W Z hr hy hf
  · exact ricci_2_0 w r y H H1 H2 H3 A C P Q R U V W Z hr hy hf
  · exact ricci_2_1 w r y H H1 H2 H3 A C P Q R U V W Z hr hy hf
  · exact ricci_2_2 w r y H H1 H2 H3 A C P Q R U V W Z hr hy hf
  · exact ricci_2_3 w r y H H1 H2 H3 A C P Q R U V W Z hr hy hf
  · exact ricci_3_0 w r y H H1 H2 H3 A C P Q R U V W Z hr hy hf
  · exact ricci_3_1 w r y H H1 H2 H3 A C P Q R U V W Z hr hy hf
  · exact ricci_3_2 w r y H H1 H2 H3 A C P Q R U V W Z hr hy hf
  · exact ricci_3_3 w r y H H1 H2 H3 A C P Q R U V W Z hr hy hf

/-- The actual scalar variation vanishes because both the metric and source have only mixed entries. -/
theorem scalar_zero (w r y H H1 H2 H3 A C P Q R U V W Z : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.scalar (D4BMBackground.jet r y)
      (metricJet w r H H1 H2 H3 A C P Q R U V W Z) = 0 := by
  have hR (i j : Fin 4) := eq_sub_iff_add_eq.mpr
    (ricci_component w r y H H1 H2 H3 A C P Q R U V W Z hr hy hf i j)
  simp only [CoordinateMetricTwoJet.Linearization.scalar, hR,
    D4BMBackground.jet_ricci r y hr hy hf, CoordinateMetricTwoJet.Linearization.inverse,
    background_metric, D4BMBackground.metric_inverse r y hr hy hf]
  simp [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply, D4BMBackground.metric, sourceTensor,
    metricJet, ScalarTwoJet.mul, ScalarTwoJet.constant]

/-- The complete cosmological Einstein operator is the derived vector master curl. -/
theorem cosmological_component (w r y H H1 H2 H3 A C P Q R U V W Z : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet r y)
      (metricJet w r H H1 H2 H3 A C P Q R U V W Z) (-3) i j =
    sourceTensor w r y H H1 H2 H3 A C Q R U V W Z i j := by
  rw [CoordinateMetricTwoJet.Linearization.cosmological,
    CoordinateMetricTwoJet.Linearization.einstein,
    scalar_zero w r y H H1 H2 H3 A C P Q R U V W Z hr hy hf,
    D4BMBackground.jet_scalar r y hr hy hf]
  convert! ricci_component w r y H H1 H2 H3 A C P Q R U V W Z hr hy hf i j using 1
  ring

/-- Restoring the fundamental envelope gives the exact polynomial-coefficient
master operator on the remaining radial factor. -/
theorem master_dressing (w r B F F1 F2 A D : ℂ) (hr : r ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    master w r (B*F) (B*(F1+w*F/(r*(r^(2 : ℕ)-1))))
      (B*(F2+2*w*F1/(r*(r^(2 : ℕ)-1))+
        (w^(2 : ℕ)-w*(3*r^(2 : ℕ)-1))*F/(r^(2 : ℕ)*(r^(2 : ℕ)-1)^(2 : ℕ)))) A D =
    B*((r^(2 : ℕ)*(r^(2 : ℕ)-1)*F2+2*r*(w+1)*F1-(w+1)*(w+2)*F)*A+F*D) := by
  dsimp [master]
  field_simp [hr, hf]
  ring

/-- The constant radial factor exposes the angular resolvent at the shifted frequency. -/
theorem master_constant_factor (w r B A D : ℂ) (hr : r ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    master w r B (B*w/(r*(r^(2 : ℕ)-1)))
      (B*(w^(2 : ℕ)-w*(3*r^(2 : ℕ)-1))/(r^(2 : ℕ)*(r^(2 : ℕ)-1)^(2 : ℕ))) A D =
      B*(D-(w+1)*(w+2)*A) := by
  dsimp [master]
  field_simp [hr, hf]
  ring

/-- The inverse-square radial factor produces the shifted angular operator and
its exact constant remainder. -/
theorem master_inverse_square_factor (w r B A D : ℂ) (hr : r ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    master w r (B/r^(2 : ℕ)) (B*(-2/r^(3 : ℕ)+w/(r^(3 : ℕ)*(r^(2 : ℕ)-1))))
      (B*(6/r^(4 : ℕ)-4*w/(r^(4 : ℕ)*(r^(2 : ℕ)-1))+
        (w^(2 : ℕ)-w*(3*r^(2 : ℕ)-1))/(r^(4 : ℕ)*(r^(2 : ℕ)-1)^(2 : ℕ)))) A D =
      B*(6*A+(D-(w+3)*(w+4)*A)/r^(2 : ℕ)) := by
  dsimp [master]
  field_simp [hr, hf]
  ring

end
end RHTower.D4BMVectorStream
