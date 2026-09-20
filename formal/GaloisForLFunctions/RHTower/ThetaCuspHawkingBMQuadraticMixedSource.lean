import GaloisForLFunctions.HTGeometry.CoordinateEinsteinComplexMixedQuadratic
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuadraticIngoingCorrection

/-!
# Complete scalar--vector quadratic Einstein source

Evaluate all sixteen components at arbitrary height, retaining the actual Einstein
Hessian and the linear image of the mixed ingoing correction. The combined scalar
contraction is proved to vanish. The surviving source is one completely specified
mixed tensor. No causal response, angular inverse, or extinction law is assumed.
-/

namespace RHTower.D4BMQuadraticMixedSource
open GaloisForLFunctions.HTGeometry D4BMScalarLinearEquation D4BMQuadraticAngularSource
noncomputable section

/-- Complete correction jet in the scalar--vector amplitude slot. -/
def correctionJet (s r y B S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ) : CoordinateMetricTwoJet 4 ℂ :=
  let R := coord r 1
  let F := (R.mul R).add (ScalarTwoJet.constant (-1))
  let U := angular s y S Sx Sy Sxx Sxy
  let V0 := D4BMVectorLinearEquation.angular0 s y Sy Sxy
    ((s+1)*(s+2)*S/y^2-Sxx) (-Sxx) Sxxy ((s+1)*(s+2)*Sx/y^2-Sxxx)
  let V1 := D4BMVectorLinearEquation.angular1 s y (-Sx) Sxy (-Sxx)
    Sxxy ((s+1)*(s+2)*Sx/y^2-Sxxx)
  let T := ((((ScalarTwoJet.constant (s*(s+1)/2)).mul
    (temporalRadial (2*s) r (B^2))).mul F).mul ((R.inv.mul R.inv).mul R.inv)).mul U
  let X := T.mul V0
  let Y := T.mul V1
  let Z : ScalarTwoJet (Fin 4) ℂ := ScalarTwoJet.constant 0
  let A := !![Z,Z,X,Y; Z,Z,Z,Z; X,Z,Z,Z; Y,Z,Z,Z]
  ⟨fun i j => (A i j).value, fun k i j => (A i j).first k,
    fun k l i j => (A i j).second k l⟩

/-- Half the coexact derivative of the squared scalar. -/
def squareCovector (S Sx Sy : ℂ) : ℂ × ℂ := (S*Sy,-S*Sx)

/-- Half the coexact derivative of the full hyperbolic gradient norm square. -/
def gradientCovector (s y S Sx Sy Sxx Sxy : ℂ) : ℂ × ℂ :=
  (y*(Sx^2+Sy^2)+y^2*(Sx*Sxy-Sy*Sxx)+(s+1)*(s+2)*S*Sy,
    -y^2*(Sx*Sxx+Sy*Sxy))

def timeSquare (s r : ℂ) : ℂ :=
  s*(r^2*(-s^3+2*s^2+15*s+8)+(s-1)*(s+1)*(s+2)^2)/(2*r^5)
def timeGradient (s r : ℂ) : ℂ := s*(s-1)*(r^2-s-1)/(2*r^5)
def radialSquare (s r : ℂ) : ℂ :=
  s*(r^2*(5*s^2+15*s+4)+s*(s-1)*(s+2)^2)/(2*r^4*(r^2-1))
def radialGradient (s r : ℂ) : ℂ := -s^2*(s-1)/(2*r^4*(r^2-1))

/-- Full source tensor, without an angular or radial projection. -/
def tensor (s r y B S Sx Sy Sxx Sxy : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  let J := squareCovector S Sx Sy
  let K := gradientCovector s y S Sx Sy Sxx Sxy
  let T0 := B^2*(timeSquare s r*J.1+timeGradient s r*K.1)
  let T1 := B^2*(timeSquare s r*J.2+timeGradient s r*K.2)
  let R0 := B^2*(radialSquare s r*J.1+radialGradient s r*K.1)
  let R1 := B^2*(radialSquare s r*J.2+radialGradient s r*K.2)
  !![0,0,T0,T1; 0,0,R0,R1; T0,R0,0,0; T1,R1,0,0]

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

/-- Background first/second entries with the index conditionals already resolved, so the
expansion below never evaluates a decidable branch. -/

private theorem background_first_0 (r y : ℂ) :
    (D4BMBackground.jet r y).first 0 = Matrix.diagonal 0 := rfl

private theorem background_first_1 (r y : ℂ) :
    (D4BMBackground.jet r y).first 1 = Matrix.diagonal ![-2*r, -2*r*(r^2-1)⁻¹^2, 2*r*y⁻¹^2, 2*r*y⁻¹^2] := rfl

private theorem background_first_2 (r y : ℂ) :
    (D4BMBackground.jet r y).first 2 = Matrix.diagonal 0 := rfl

private theorem background_first_3 (r y : ℂ) :
    (D4BMBackground.jet r y).first 3 = Matrix.diagonal ![0, 0, -2*r^2*y⁻¹^3, -2*r^2*y⁻¹^3] := rfl

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
    (D4BMBackground.jet r y).second 1 1 = Matrix.diagonal ![-2, -2*(r^2-1)⁻¹^2+8*r^2*(r^2-1)⁻¹^3, 2*y⁻¹^2, 2*y⁻¹^2] := rfl

private theorem background_second_1_2 (r y : ℂ) :
    (D4BMBackground.jet r y).second 1 2 = Matrix.diagonal 0 := rfl

private theorem background_second_1_3 (r y : ℂ) :
    (D4BMBackground.jet r y).second 1 3 = Matrix.diagonal ![0,0,-4*r*y⁻¹^3,-4*r*y⁻¹^3] := rfl

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
    (D4BMBackground.jet r y).second 3 1 = Matrix.diagonal ![0,0,-4*r*y⁻¹^3,-4*r*y⁻¹^3] := rfl

private theorem background_second_3_2 (r y : ℂ) :
    (D4BMBackground.jet r y).second 3 2 = Matrix.diagonal 0 := rfl

private theorem background_second_3_3 (r y : ℂ) :
    (D4BMBackground.jet r y).second 3 3 = Matrix.diagonal ![0,0,6*r^2*y⁻¹^4,6*r^2*y⁻¹^4] := rfl



set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem ricci_0_0 (s r y B S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    CoordinateMetricTwoJet.MixedQuadratic.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy)
      (coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 0 0 +
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 0 0 +
      3*(correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy).metric 0 0 =
      tensor s r y B S Sx Sy Sxx Sxy 0 0 := by
  generalize hK : scalarJet s r y B S Sx Sy Sxx Sxy = K
  generalize hV : coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy = V
  generalize hM : correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy = M
  all_goals simp only [CoordinateMetricTwoJet.MixedQuadratic.ricci,
    CoordinateMetricTwoJet.MixedQuadratic.curvature,
    CoordinateMetricTwoJet.MixedQuadratic.connectionSpatial,
    CoordinateMetricTwoJet.MixedQuadratic.connection,
    CoordinateMetricTwoJet.MixedQuadratic.inverseSpatial,
    CoordinateMetricTwoJet.MixedQuadratic.inverse,
    CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals simp (config := { maxSteps := 400000 }) [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply]
  all_goals rw [← hK, ← hV, ← hM]
  all_goals simp (config := { maxSteps := 400000 }) [
    correctionJet, scalarJet, radialEntries, coexactJet, D4BMVectorLinearEquation.vectorJet,
    D4BMVectorLinearEquation.angular0, D4BMVectorLinearEquation.angular1,
    temporalRadial, angular, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.neg,
    ScalarTwoJet.inv, ScalarTwoJet.constant, tensor, squareCovector, gradientCovector]
  all_goals simp only [← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hr, hy, hf]
  all_goals ring


set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem ricci_0_1 (s r y B S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    CoordinateMetricTwoJet.MixedQuadratic.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy)
      (coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 0 1 +
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 0 1 +
      3*(correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy).metric 0 1 =
      tensor s r y B S Sx Sy Sxx Sxy 0 1 := by
  generalize hK : scalarJet s r y B S Sx Sy Sxx Sxy = K
  generalize hV : coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy = V
  generalize hM : correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy = M
  all_goals simp only [CoordinateMetricTwoJet.MixedQuadratic.ricci,
    CoordinateMetricTwoJet.MixedQuadratic.curvature,
    CoordinateMetricTwoJet.MixedQuadratic.connectionSpatial,
    CoordinateMetricTwoJet.MixedQuadratic.connection,
    CoordinateMetricTwoJet.MixedQuadratic.inverseSpatial,
    CoordinateMetricTwoJet.MixedQuadratic.inverse,
    CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals simp (config := { maxSteps := 400000 }) [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply]
  all_goals rw [← hK, ← hV, ← hM]
  all_goals simp (config := { maxSteps := 400000 }) [
    correctionJet, scalarJet, radialEntries, coexactJet, D4BMVectorLinearEquation.vectorJet,
    D4BMVectorLinearEquation.angular0, D4BMVectorLinearEquation.angular1,
    temporalRadial, angular, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.neg,
    ScalarTwoJet.inv, ScalarTwoJet.constant, tensor, squareCovector, gradientCovector]
  all_goals simp only [← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hr, hy, hf]
  all_goals ring


set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem ricci_0_2 (s r y B S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    CoordinateMetricTwoJet.MixedQuadratic.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy)
      (coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 0 2 +
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 0 2 +
      3*(correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy).metric 0 2 =
      tensor s r y B S Sx Sy Sxx Sxy 0 2 := by
  generalize hK : scalarJet s r y B S Sx Sy Sxx Sxy = K
  generalize hV : coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy = V
  generalize hM : correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy = M
  all_goals simp only [CoordinateMetricTwoJet.MixedQuadratic.ricci,
    CoordinateMetricTwoJet.MixedQuadratic.curvature,
    CoordinateMetricTwoJet.MixedQuadratic.connectionSpatial,
    CoordinateMetricTwoJet.MixedQuadratic.connection,
    CoordinateMetricTwoJet.MixedQuadratic.inverseSpatial,
    CoordinateMetricTwoJet.MixedQuadratic.inverse,
    CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals simp (config := { maxSteps := 400000 }) [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply]
  all_goals rw [← hK, ← hV, ← hM]
  all_goals simp (config := { maxSteps := 400000 }) [
    correctionJet, scalarJet, radialEntries, coexactJet, D4BMVectorLinearEquation.vectorJet,
    D4BMVectorLinearEquation.angular0, D4BMVectorLinearEquation.angular1,
    temporalRadial, angular, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.neg,
    ScalarTwoJet.inv, ScalarTwoJet.constant, tensor, squareCovector, gradientCovector]
  all_goals simp only [timeSquare, timeGradient, ← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hr, hy, hf]
  all_goals ring


set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem ricci_0_3 (s r y B S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    CoordinateMetricTwoJet.MixedQuadratic.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy)
      (coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 0 3 +
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 0 3 +
      3*(correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy).metric 0 3 =
      tensor s r y B S Sx Sy Sxx Sxy 0 3 := by
  generalize hK : scalarJet s r y B S Sx Sy Sxx Sxy = K
  generalize hV : coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy = V
  generalize hM : correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy = M
  all_goals simp only [CoordinateMetricTwoJet.MixedQuadratic.ricci,
    CoordinateMetricTwoJet.MixedQuadratic.curvature,
    CoordinateMetricTwoJet.MixedQuadratic.connectionSpatial,
    CoordinateMetricTwoJet.MixedQuadratic.connection,
    CoordinateMetricTwoJet.MixedQuadratic.inverseSpatial,
    CoordinateMetricTwoJet.MixedQuadratic.inverse,
    CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals simp (config := { maxSteps := 400000 }) [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply]
  all_goals rw [← hK, ← hV, ← hM]
  all_goals simp (config := { maxSteps := 400000 }) [
    correctionJet, scalarJet, radialEntries, coexactJet, D4BMVectorLinearEquation.vectorJet,
    D4BMVectorLinearEquation.angular0, D4BMVectorLinearEquation.angular1,
    temporalRadial, angular, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.neg,
    ScalarTwoJet.inv, ScalarTwoJet.constant, tensor, squareCovector, gradientCovector]
  all_goals simp only [timeSquare, timeGradient, ← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hr, hy, hf]
  all_goals ring


set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem ricci_1_0 (s r y B S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    CoordinateMetricTwoJet.MixedQuadratic.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy)
      (coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 1 0 +
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 1 0 +
      3*(correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy).metric 1 0 =
      tensor s r y B S Sx Sy Sxx Sxy 1 0 := by
  generalize hK : scalarJet s r y B S Sx Sy Sxx Sxy = K
  generalize hV : coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy = V
  generalize hM : correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy = M
  all_goals simp only [CoordinateMetricTwoJet.MixedQuadratic.ricci,
    CoordinateMetricTwoJet.MixedQuadratic.curvature,
    CoordinateMetricTwoJet.MixedQuadratic.connectionSpatial,
    CoordinateMetricTwoJet.MixedQuadratic.connection,
    CoordinateMetricTwoJet.MixedQuadratic.inverseSpatial,
    CoordinateMetricTwoJet.MixedQuadratic.inverse,
    CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals simp (config := { maxSteps := 400000 }) [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply]
  all_goals rw [← hK, ← hV, ← hM]
  all_goals simp (config := { maxSteps := 400000 }) [
    correctionJet, scalarJet, radialEntries, coexactJet, D4BMVectorLinearEquation.vectorJet,
    D4BMVectorLinearEquation.angular0, D4BMVectorLinearEquation.angular1,
    temporalRadial, angular, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.neg,
    ScalarTwoJet.inv, ScalarTwoJet.constant, tensor, squareCovector, gradientCovector]
  all_goals simp only [← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hr, hy, hf]
  all_goals ring


set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem ricci_1_1 (s r y B S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    CoordinateMetricTwoJet.MixedQuadratic.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy)
      (coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 1 1 +
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 1 1 +
      3*(correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy).metric 1 1 =
      tensor s r y B S Sx Sy Sxx Sxy 1 1 := by
  generalize hK : scalarJet s r y B S Sx Sy Sxx Sxy = K
  generalize hV : coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy = V
  generalize hM : correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy = M
  all_goals simp only [CoordinateMetricTwoJet.MixedQuadratic.ricci,
    CoordinateMetricTwoJet.MixedQuadratic.curvature,
    CoordinateMetricTwoJet.MixedQuadratic.connectionSpatial,
    CoordinateMetricTwoJet.MixedQuadratic.connection,
    CoordinateMetricTwoJet.MixedQuadratic.inverseSpatial,
    CoordinateMetricTwoJet.MixedQuadratic.inverse,
    CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals simp (config := { maxSteps := 400000 }) [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply]
  all_goals rw [← hK, ← hV, ← hM]
  all_goals simp (config := { maxSteps := 400000 }) [
    correctionJet, scalarJet, radialEntries, coexactJet, D4BMVectorLinearEquation.vectorJet,
    D4BMVectorLinearEquation.angular0, D4BMVectorLinearEquation.angular1,
    temporalRadial, angular, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.neg,
    ScalarTwoJet.inv, ScalarTwoJet.constant, tensor, squareCovector, gradientCovector]
  all_goals simp only [← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hr, hy, hf]
  all_goals ring


set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem ricci_1_2 (s r y B S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    CoordinateMetricTwoJet.MixedQuadratic.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy)
      (coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 1 2 +
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 1 2 +
      3*(correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy).metric 1 2 =
      tensor s r y B S Sx Sy Sxx Sxy 1 2 := by
  generalize hK : scalarJet s r y B S Sx Sy Sxx Sxy = K
  generalize hV : coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy = V
  generalize hM : correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy = M
  all_goals simp only [CoordinateMetricTwoJet.MixedQuadratic.ricci,
    CoordinateMetricTwoJet.MixedQuadratic.curvature,
    CoordinateMetricTwoJet.MixedQuadratic.connectionSpatial,
    CoordinateMetricTwoJet.MixedQuadratic.connection,
    CoordinateMetricTwoJet.MixedQuadratic.inverseSpatial,
    CoordinateMetricTwoJet.MixedQuadratic.inverse,
    CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals simp (config := { maxSteps := 400000 }) [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply]
  all_goals rw [← hK, ← hV, ← hM]
  all_goals simp (config := { maxSteps := 400000 }) [
    correctionJet, scalarJet, radialEntries, coexactJet, D4BMVectorLinearEquation.vectorJet,
    D4BMVectorLinearEquation.angular0, D4BMVectorLinearEquation.angular1,
    temporalRadial, angular, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.neg,
    ScalarTwoJet.inv, ScalarTwoJet.constant, tensor, squareCovector, gradientCovector]
  all_goals simp only [radialSquare, radialGradient, ← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hr, hy, hf]
  all_goals ring


set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem ricci_1_3 (s r y B S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    CoordinateMetricTwoJet.MixedQuadratic.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy)
      (coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 1 3 +
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 1 3 +
      3*(correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy).metric 1 3 =
      tensor s r y B S Sx Sy Sxx Sxy 1 3 := by
  generalize hK : scalarJet s r y B S Sx Sy Sxx Sxy = K
  generalize hV : coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy = V
  generalize hM : correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy = M
  all_goals simp only [CoordinateMetricTwoJet.MixedQuadratic.ricci,
    CoordinateMetricTwoJet.MixedQuadratic.curvature,
    CoordinateMetricTwoJet.MixedQuadratic.connectionSpatial,
    CoordinateMetricTwoJet.MixedQuadratic.connection,
    CoordinateMetricTwoJet.MixedQuadratic.inverseSpatial,
    CoordinateMetricTwoJet.MixedQuadratic.inverse,
    CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals simp (config := { maxSteps := 400000 }) [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply]
  all_goals rw [← hK, ← hV, ← hM]
  all_goals simp (config := { maxSteps := 400000 }) [
    correctionJet, scalarJet, radialEntries, coexactJet, D4BMVectorLinearEquation.vectorJet,
    D4BMVectorLinearEquation.angular0, D4BMVectorLinearEquation.angular1,
    temporalRadial, angular, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.neg,
    ScalarTwoJet.inv, ScalarTwoJet.constant, tensor, squareCovector, gradientCovector]
  all_goals simp only [radialSquare, radialGradient, ← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hr, hy, hf]
  all_goals ring


set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem ricci_2_0 (s r y B S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    CoordinateMetricTwoJet.MixedQuadratic.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy)
      (coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 2 0 +
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 2 0 +
      3*(correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy).metric 2 0 =
      tensor s r y B S Sx Sy Sxx Sxy 2 0 := by
  generalize hK : scalarJet s r y B S Sx Sy Sxx Sxy = K
  generalize hV : coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy = V
  generalize hM : correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy = M
  all_goals simp only [CoordinateMetricTwoJet.MixedQuadratic.ricci,
    CoordinateMetricTwoJet.MixedQuadratic.curvature,
    CoordinateMetricTwoJet.MixedQuadratic.connectionSpatial,
    CoordinateMetricTwoJet.MixedQuadratic.connection,
    CoordinateMetricTwoJet.MixedQuadratic.inverseSpatial,
    CoordinateMetricTwoJet.MixedQuadratic.inverse,
    CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals simp (config := { maxSteps := 400000 }) [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply]
  all_goals rw [← hK, ← hV, ← hM]
  all_goals simp (config := { maxSteps := 400000 }) [
    correctionJet, scalarJet, radialEntries, coexactJet, D4BMVectorLinearEquation.vectorJet,
    D4BMVectorLinearEquation.angular0, D4BMVectorLinearEquation.angular1,
    temporalRadial, angular, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.neg,
    ScalarTwoJet.inv, ScalarTwoJet.constant, tensor, squareCovector, gradientCovector]
  all_goals simp only [timeSquare, timeGradient, ← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hr, hy, hf]
  all_goals ring


set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem ricci_2_1 (s r y B S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    CoordinateMetricTwoJet.MixedQuadratic.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy)
      (coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 2 1 +
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 2 1 +
      3*(correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy).metric 2 1 =
      tensor s r y B S Sx Sy Sxx Sxy 2 1 := by
  generalize hK : scalarJet s r y B S Sx Sy Sxx Sxy = K
  generalize hV : coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy = V
  generalize hM : correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy = M
  all_goals simp only [CoordinateMetricTwoJet.MixedQuadratic.ricci,
    CoordinateMetricTwoJet.MixedQuadratic.curvature,
    CoordinateMetricTwoJet.MixedQuadratic.connectionSpatial,
    CoordinateMetricTwoJet.MixedQuadratic.connection,
    CoordinateMetricTwoJet.MixedQuadratic.inverseSpatial,
    CoordinateMetricTwoJet.MixedQuadratic.inverse,
    CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals simp (config := { maxSteps := 400000 }) [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply]
  all_goals rw [← hK, ← hV, ← hM]
  all_goals simp (config := { maxSteps := 400000 }) [
    correctionJet, scalarJet, radialEntries, coexactJet, D4BMVectorLinearEquation.vectorJet,
    D4BMVectorLinearEquation.angular0, D4BMVectorLinearEquation.angular1,
    temporalRadial, angular, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.neg,
    ScalarTwoJet.inv, ScalarTwoJet.constant, tensor, squareCovector, gradientCovector]
  all_goals simp only [radialSquare, radialGradient, ← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hr, hy, hf]
  all_goals ring


set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem ricci_2_2 (s r y B S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    CoordinateMetricTwoJet.MixedQuadratic.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy)
      (coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 2 2 +
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 2 2 +
      3*(correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy).metric 2 2 =
      tensor s r y B S Sx Sy Sxx Sxy 2 2 := by
  generalize hK : scalarJet s r y B S Sx Sy Sxx Sxy = K
  generalize hV : coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy = V
  generalize hM : correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy = M
  all_goals simp only [CoordinateMetricTwoJet.MixedQuadratic.ricci,
    CoordinateMetricTwoJet.MixedQuadratic.curvature,
    CoordinateMetricTwoJet.MixedQuadratic.connectionSpatial,
    CoordinateMetricTwoJet.MixedQuadratic.connection,
    CoordinateMetricTwoJet.MixedQuadratic.inverseSpatial,
    CoordinateMetricTwoJet.MixedQuadratic.inverse,
    CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals simp (config := { maxSteps := 400000 }) [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply]
  all_goals rw [← hK, ← hV, ← hM]
  all_goals simp (config := { maxSteps := 400000 }) [
    correctionJet, scalarJet, radialEntries, coexactJet, D4BMVectorLinearEquation.vectorJet,
    D4BMVectorLinearEquation.angular0, D4BMVectorLinearEquation.angular1,
    temporalRadial, angular, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.neg,
    ScalarTwoJet.inv, ScalarTwoJet.constant, tensor, squareCovector, gradientCovector]
  all_goals simp only [← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hr, hy, hf]
  all_goals ring


set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem ricci_2_3 (s r y B S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    CoordinateMetricTwoJet.MixedQuadratic.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy)
      (coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 2 3 +
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 2 3 +
      3*(correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy).metric 2 3 =
      tensor s r y B S Sx Sy Sxx Sxy 2 3 := by
  generalize hK : scalarJet s r y B S Sx Sy Sxx Sxy = K
  generalize hV : coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy = V
  generalize hM : correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy = M
  all_goals simp only [CoordinateMetricTwoJet.MixedQuadratic.ricci,
    CoordinateMetricTwoJet.MixedQuadratic.curvature,
    CoordinateMetricTwoJet.MixedQuadratic.connectionSpatial,
    CoordinateMetricTwoJet.MixedQuadratic.connection,
    CoordinateMetricTwoJet.MixedQuadratic.inverseSpatial,
    CoordinateMetricTwoJet.MixedQuadratic.inverse,
    CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals simp (config := { maxSteps := 400000 }) [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply]
  all_goals rw [← hK, ← hV, ← hM]
  all_goals simp (config := { maxSteps := 400000 }) [
    correctionJet, scalarJet, radialEntries, coexactJet, D4BMVectorLinearEquation.vectorJet,
    D4BMVectorLinearEquation.angular0, D4BMVectorLinearEquation.angular1,
    temporalRadial, angular, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.neg,
    ScalarTwoJet.inv, ScalarTwoJet.constant, tensor, squareCovector, gradientCovector]
  all_goals simp only [← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hr, hy, hf]
  all_goals ring


set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem ricci_3_0 (s r y B S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    CoordinateMetricTwoJet.MixedQuadratic.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy)
      (coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 3 0 +
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 3 0 +
      3*(correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy).metric 3 0 =
      tensor s r y B S Sx Sy Sxx Sxy 3 0 := by
  generalize hK : scalarJet s r y B S Sx Sy Sxx Sxy = K
  generalize hV : coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy = V
  generalize hM : correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy = M
  all_goals simp only [CoordinateMetricTwoJet.MixedQuadratic.ricci,
    CoordinateMetricTwoJet.MixedQuadratic.curvature,
    CoordinateMetricTwoJet.MixedQuadratic.connectionSpatial,
    CoordinateMetricTwoJet.MixedQuadratic.connection,
    CoordinateMetricTwoJet.MixedQuadratic.inverseSpatial,
    CoordinateMetricTwoJet.MixedQuadratic.inverse,
    CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals simp (config := { maxSteps := 400000 }) [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply]
  all_goals rw [← hK, ← hV, ← hM]
  all_goals simp (config := { maxSteps := 400000 }) [
    correctionJet, scalarJet, radialEntries, coexactJet, D4BMVectorLinearEquation.vectorJet,
    D4BMVectorLinearEquation.angular0, D4BMVectorLinearEquation.angular1,
    temporalRadial, angular, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.neg,
    ScalarTwoJet.inv, ScalarTwoJet.constant, tensor, squareCovector, gradientCovector]
  all_goals simp only [timeSquare, timeGradient, ← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hr, hy, hf]
  all_goals ring


set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem ricci_3_1 (s r y B S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    CoordinateMetricTwoJet.MixedQuadratic.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy)
      (coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 3 1 +
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 3 1 +
      3*(correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy).metric 3 1 =
      tensor s r y B S Sx Sy Sxx Sxy 3 1 := by
  generalize hK : scalarJet s r y B S Sx Sy Sxx Sxy = K
  generalize hV : coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy = V
  generalize hM : correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy = M
  all_goals simp only [CoordinateMetricTwoJet.MixedQuadratic.ricci,
    CoordinateMetricTwoJet.MixedQuadratic.curvature,
    CoordinateMetricTwoJet.MixedQuadratic.connectionSpatial,
    CoordinateMetricTwoJet.MixedQuadratic.connection,
    CoordinateMetricTwoJet.MixedQuadratic.inverseSpatial,
    CoordinateMetricTwoJet.MixedQuadratic.inverse,
    CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals simp (config := { maxSteps := 400000 }) [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply]
  all_goals rw [← hK, ← hV, ← hM]
  all_goals simp (config := { maxSteps := 400000 }) [
    correctionJet, scalarJet, radialEntries, coexactJet, D4BMVectorLinearEquation.vectorJet,
    D4BMVectorLinearEquation.angular0, D4BMVectorLinearEquation.angular1,
    temporalRadial, angular, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.neg,
    ScalarTwoJet.inv, ScalarTwoJet.constant, tensor, squareCovector, gradientCovector]
  all_goals simp only [radialSquare, radialGradient, ← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hr, hy, hf]
  all_goals ring


set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem ricci_3_2 (s r y B S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    CoordinateMetricTwoJet.MixedQuadratic.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy)
      (coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 3 2 +
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 3 2 +
      3*(correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy).metric 3 2 =
      tensor s r y B S Sx Sy Sxx Sxy 3 2 := by
  generalize hK : scalarJet s r y B S Sx Sy Sxx Sxy = K
  generalize hV : coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy = V
  generalize hM : correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy = M
  all_goals simp only [CoordinateMetricTwoJet.MixedQuadratic.ricci,
    CoordinateMetricTwoJet.MixedQuadratic.curvature,
    CoordinateMetricTwoJet.MixedQuadratic.connectionSpatial,
    CoordinateMetricTwoJet.MixedQuadratic.connection,
    CoordinateMetricTwoJet.MixedQuadratic.inverseSpatial,
    CoordinateMetricTwoJet.MixedQuadratic.inverse,
    CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals simp (config := { maxSteps := 400000 }) [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply]
  all_goals rw [← hK, ← hV, ← hM]
  all_goals simp (config := { maxSteps := 400000 }) [
    correctionJet, scalarJet, radialEntries, coexactJet, D4BMVectorLinearEquation.vectorJet,
    D4BMVectorLinearEquation.angular0, D4BMVectorLinearEquation.angular1,
    temporalRadial, angular, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.neg,
    ScalarTwoJet.inv, ScalarTwoJet.constant, tensor, squareCovector, gradientCovector]
  all_goals simp only [← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hr, hy, hf]
  all_goals ring


set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem ricci_3_3 (s r y B S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    CoordinateMetricTwoJet.MixedQuadratic.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy)
      (coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 3 3 +
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 3 3 +
      3*(correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy).metric 3 3 =
      tensor s r y B S Sx Sy Sxx Sxy 3 3 := by
  generalize hK : scalarJet s r y B S Sx Sy Sxx Sxy = K
  generalize hV : coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy = V
  generalize hM : correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy = M
  all_goals simp only [CoordinateMetricTwoJet.MixedQuadratic.ricci,
    CoordinateMetricTwoJet.MixedQuadratic.curvature,
    CoordinateMetricTwoJet.MixedQuadratic.connectionSpatial,
    CoordinateMetricTwoJet.MixedQuadratic.connection,
    CoordinateMetricTwoJet.MixedQuadratic.inverseSpatial,
    CoordinateMetricTwoJet.MixedQuadratic.inverse,
    CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals simp (config := { maxSteps := 400000 }) [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply]
  all_goals rw [← hK, ← hV, ← hM]
  all_goals simp (config := { maxSteps := 400000 }) [
    correctionJet, scalarJet, radialEntries, coexactJet, D4BMVectorLinearEquation.vectorJet,
    D4BMVectorLinearEquation.angular0, D4BMVectorLinearEquation.angular1,
    temporalRadial, angular, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.neg,
    ScalarTwoJet.inv, ScalarTwoJet.constant, tensor, squareCovector, gradientCovector]
  all_goals simp only [← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hr, hy, hf]
  all_goals ring


theorem ricci_component (s r y B S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) (i j : Fin 4) :
    CoordinateMetricTwoJet.MixedQuadratic.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy)
      (coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) i j +
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) i j +
      3*(correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy).metric i j =
      tensor s r y B S Sx Sy Sxx Sxy i j := by
  fin_cases i <;> fin_cases j
  · exact ricci_0_0 s r y B S Sx Sy Sxx Sxy Sxxx Sxxy hr hy hf
  · exact ricci_0_1 s r y B S Sx Sy Sxx Sxy Sxxx Sxxy hr hy hf
  · exact ricci_0_2 s r y B S Sx Sy Sxx Sxy Sxxx Sxxy hr hy hf
  · exact ricci_0_3 s r y B S Sx Sy Sxx Sxy Sxxx Sxxy hr hy hf
  · exact ricci_1_0 s r y B S Sx Sy Sxx Sxy Sxxx Sxxy hr hy hf
  · exact ricci_1_1 s r y B S Sx Sy Sxx Sxy Sxxx Sxxy hr hy hf
  · exact ricci_1_2 s r y B S Sx Sy Sxx Sxy Sxxx Sxxy hr hy hf
  · exact ricci_1_3 s r y B S Sx Sy Sxx Sxy Sxxx Sxxy hr hy hf
  · exact ricci_2_0 s r y B S Sx Sy Sxx Sxy Sxxx Sxxy hr hy hf
  · exact ricci_2_1 s r y B S Sx Sy Sxx Sxy Sxxx Sxxy hr hy hf
  · exact ricci_2_2 s r y B S Sx Sy Sxx Sxy Sxxx Sxxy hr hy hf
  · exact ricci_2_3 s r y B S Sx Sy Sxx Sxy Sxxx Sxxy hr hy hf
  · exact ricci_3_0 s r y B S Sx Sy Sxx Sxy Sxxx Sxxy hr hy hf
  · exact ricci_3_1 s r y B S Sx Sy Sxx Sxy Sxxx Sxxy hr hy hf
  · exact ricci_3_2 s r y B S Sx Sy Sxx Sxy Sxxx Sxxy hr hy hf
  · exact ricci_3_3 s r y B S Sx Sy Sxx Sxy Sxxx Sxxy hr hy hf

end
end RHTower.D4BMQuadraticMixedSource

namespace RHTower.D4BMQuadraticMixedSource
open GaloisForLFunctions.HTGeometry D4BMScalarLinearEquation D4BMQuadraticAngularSource
noncomputable section

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- The combined scalar contraction vanishes, including both inverse--Ricci cross terms. -/
theorem scalar_cancel (s r y B S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    CoordinateMetricTwoJet.MixedQuadratic.scalar (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy)
      (coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) +
    CoordinateMetricTwoJet.Linearization.scalar (D4BMBackground.jet r y)
      (correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) = 0 := by
  have hS (i j : Fin 4) := eq_neg_of_add_eq_zero_left
    (D4BMScalarLinearEquation.ricci_component s r y B S Sx Sy Sxx Sxy hr hy hf i j)
  have hV (i j : Fin 4) := eq_neg_of_add_eq_zero_left
    (D4BMVectorLinearEquation.ricci_component s r y B Sy (-Sx) Sxy
      ((s+1)*(s+2)*S/y^2-Sxx) (-Sxx) Sxxy ((s+1)*(s+2)*Sx/y^2-Sxxx) hr hy hf i j)
  have hM (i j : Fin 4) := eq_sub_iff_add_eq.mpr (eq_sub_iff_add_eq.mpr
    (ricci_component s r y B S Sx Sy Sxx Sxy Sxxx Sxxy hr hy hf i j))
  simp only [CoordinateMetricTwoJet.MixedQuadratic.scalar,
    CoordinateMetricTwoJet.Linearization.scalar]
  simp only [hM, hS]
  simp only [coexactJet, hV,
    D4BMBackground.jet_ricci r y hr hy hf,
    CoordinateMetricTwoJet.MixedQuadratic.inverse, CoordinateMetricTwoJet.Linearization.inverse,
    background_metric, D4BMBackground.metric_inverse r y hr hy hf]
  simp [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply, D4BMBackground.metric, tensor,
    scalarJet, radialEntries, correctionJet, D4BMVectorLinearEquation.vectorJet,
    ScalarTwoJet.mul, ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv,
    ScalarTwoJet.constant, coord, temporalRadial, angular,
    D4BMVectorLinearEquation.angular0, D4BMVectorLinearEquation.angular1]
  ring

/-- Complete mixed cosmological Einstein source at arbitrary height. -/
theorem einstein_component (s r y B S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) (i j : Fin 4) :
    CoordinateMetricTwoJet.MixedQuadratic.einstein (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy)
      (coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) i j +
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet r y)
      (correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) (-3) i j =
      tensor s r y B S Sx Sy Sxx Sxy i j := by
  have hS := D4BMLinearizedRicci.scalar_zero_of_ricci r y
    (scalarJet s r y B S Sx Sy Sxx Sxy) hr hy hf (by
      intro k l
      have h := D4BMScalarLinearEquation.ricci_component s r y B S Sx Sy Sxx Sxy hr hy hf k l
      linear_combination h)
  have hV := D4BMLinearizedRicci.scalar_zero_of_ricci r y
    (coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) hr hy hf (by
      intro k l
      have h := D4BMVectorLinearEquation.ricci_component s r y B Sy (-Sx) Sxy
        ((s+1)*(s+2)*S/y^2-Sxx) (-Sxx) Sxxy ((s+1)*(s+2)*Sx/y^2-Sxxx) hr hy hf k l
      dsimp only [coexactJet]
      linear_combination h)
  have hc := scalar_cancel s r y B S Sx Sy Sxx Sxy Sxxx Sxxy hr hy hf
  have hR := ricci_component s r y B S Sx Sy Sxx Sxy Sxxx Sxxy hr hy hf i j
  simp only [CoordinateMetricTwoJet.MixedQuadratic.einstein,
    CoordinateMetricTwoJet.Linearization.cosmological, CoordinateMetricTwoJet.Linearization.einstein,
    hS, hV, D4BMBackground.jet_scalar r y hr hy hf]
  linear_combination hR - (D4BMBackground.jet r y).metric i j / 2 * hc

end
end RHTower.D4BMQuadraticMixedSource
