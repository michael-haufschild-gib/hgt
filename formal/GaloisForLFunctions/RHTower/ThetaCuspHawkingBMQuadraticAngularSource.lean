import GaloisForLFunctions.HTGeometry.CoordinateEinsteinComplexQuadratic
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMVectorLinearizedRicciJet

/-!
# Full fundamental BM quadratic angular Einstein source

Evaluate the actual Einstein Hessian on the complete fundamental scalar metric
and its coexact-vector partner, with independent amplitudes. The scalar--scalar,
scalar--vector and vector--vector terms are fixed by the complete coordinate
contraction. Every free third scalar angular derivative cancels. All identities
hold at arbitrary height and complex parameters on the nondegenerate radial chart.

The result separates a Hessian of the squared scalar, its oriented rotation,
and a gradient-square remainder. A left pairing must retain the derivatives of
its actual test and all boundary terms; none of these tensors is discarded here.
The source's physical constrained response and universal extinction remain open.
-/

namespace RHTower.D4BMQuadraticAngularSource
open GaloisForLFunctions.HTGeometry
open D4BMScalarLinearEquation
noncomputable section

/-- Complete coexact vector metric jet from the same scalar three-jet. -/
def coexactJet (s r y B S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ) : CoordinateMetricTwoJet 4 ℂ :=
  D4BMVectorLinearEquation.vectorJet s r y B Sy (-Sx) Sxy
    ((s+1)*(s+2)*S/y^(2 : ℕ)-Sxx) (-Sxx) Sxxy ((s+1)*(s+2)*Sx/y^(2 : ℕ)-Sxxx)

/-- Full fundamental scalar/vector jet with independent amplitudes. -/
def combinedJet (s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ) : CoordinateMetricTwoJet 4 ℂ :=
  let U := scalarJet s r y (aS*B) S Sx Sy Sxx Sxy
  let V := coexactJet s r y (aV*B) S Sx Sy Sxx Sxy Sxxx Sxxy
  ⟨U.metric + V.metric, fun k => U.first k + V.first k,
    fun k l => U.second k l + V.second k l⟩

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

/-- Scalar--scalar radial coefficient in the actual angular quadratic source. -/
def scalarWeight (s r : ℂ) : ℂ := s^(2 : ℕ)*((s+1)^(2 : ℕ)-4*r^(2 : ℕ))/(8*r^(4 : ℕ))

/-- Vector--vector radial coefficient in the actual angular quadratic source. -/
def vectorWeight (s r : ℂ) : ℂ := s^(2 : ℕ)*(3*s^(2 : ℕ)+12*s+11)/(2*r^(4 : ℕ))

/-- Scalar--vector radial coefficient in the actual angular quadratic source. -/
def mixedWeight (s r : ℂ) : ℂ := s^(2 : ℕ)*(s+1)/r^(3 : ℕ)

/-- Background first/second derivative entries with the index conditionals already
resolved: the big expansion below then never evaluates a decidable branch. -/

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

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem ricci_offdiagonal (s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Quadratic.ricci (D4BMBackground.jet r y)
      (combinedJet s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy) 2 3 / 2 =
      B^(2 : ℕ) * (aS^(2 : ℕ) * scalarWeight s r * (2*S*(Sxy+Sx/y)+Sx*Sy) -
        aS*aV*mixedWeight s r*(S*(2*Sxx-(s+1)*(s+2)*S/y^(2 : ℕ)-2*Sy/y)+Sx^(2 : ℕ)-Sy^(2 : ℕ))/2 +
        aV^(2 : ℕ)*vectorWeight s r*Sx*Sy) := by
  generalize hK : combinedJet s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy = K
  simp only [CoordinateMetricTwoJet.Quadratic.ricci,
    CoordinateMetricTwoJet.Quadratic.curvature, CoordinateMetricTwoJet.Quadratic.connectionSpatial,
    CoordinateMetricTwoJet.Quadratic.connection, CoordinateMetricTwoJet.Quadratic.inverseSpatial,
    CoordinateMetricTwoJet.Quadratic.inverse,
    CoordinateMetricTwoJet.Linearization.connection, CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel,
    background_metric,
    D4BMBackground.metric_inverse r y hr hy hf]
  rw [← hK]
  simp (config := { maxSteps := 400000 }) [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply, combinedJet, scalarJet, angular, radialEntries, ScalarTwoJet.neg, coexactJet, D4BMVectorLinearEquation.vectorJet, D4BMVectorLinearEquation.angular0,
    D4BMVectorLinearEquation.angular1, temporalRadial, coord, ScalarTwoJet.add,
    ScalarTwoJet.mul, ScalarTwoJet.inv, ScalarTwoJet.constant]
  simp only [scalarWeight, vectorWeight, mixedWeight, ← pow_two, ← sub_eq_add_neg]
  field_simp [hf, hr, hy]
  ring


set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem ricci_difference (s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    (CoordinateMetricTwoJet.Quadratic.ricci (D4BMBackground.jet r y)
      (combinedJet s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy) 2 2 -
      CoordinateMetricTwoJet.Quadratic.ricci (D4BMBackground.jet r y)
      (combinedJet s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy) 3 3) / 2 =
      B^(2 : ℕ) * (aS^(2 : ℕ) * scalarWeight s r *
        (2*S*(2*Sxx-(s+1)*(s+2)*S/y^(2 : ℕ)-2*Sy/y)+Sx^(2 : ℕ)-Sy^(2 : ℕ)) +
        2*aS*aV*mixedWeight s r*(S*(Sxy+Sx/y)+Sx*Sy) +
        aV^(2 : ℕ)*vectorWeight s r*(Sx^(2 : ℕ)-Sy^(2 : ℕ))) := by
  generalize hK : combinedJet s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy = K
  simp only [CoordinateMetricTwoJet.Quadratic.ricci,
    CoordinateMetricTwoJet.Quadratic.curvature, CoordinateMetricTwoJet.Quadratic.connectionSpatial,
    CoordinateMetricTwoJet.Quadratic.connection, CoordinateMetricTwoJet.Quadratic.inverseSpatial,
    CoordinateMetricTwoJet.Quadratic.inverse,
    CoordinateMetricTwoJet.Linearization.connection, CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel,
    background_metric,
    D4BMBackground.metric_inverse r y hr hy hf]
  rw [← hK]
  simp (config := { maxSteps := 400000 }) [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply, combinedJet, scalarJet, angular, radialEntries, ScalarTwoJet.neg, coexactJet, D4BMVectorLinearEquation.vectorJet, D4BMVectorLinearEquation.angular0,
    D4BMVectorLinearEquation.angular1, temporalRadial, coord, ScalarTwoJet.add,
    ScalarTwoJet.mul, ScalarTwoJet.inv, ScalarTwoJet.constant]
  simp only [scalarWeight, vectorWeight, mixedWeight, ← pow_two, ← sub_eq_add_neg]
  field_simp [hf, hr, hy]
  ring


end
end RHTower.D4BMQuadraticAngularSource
namespace RHTower.D4BMQuadraticAngularSource
open GaloisForLFunctions.HTGeometry
open D4BMScalarLinearEquation
noncomputable section

/-- Actual Einstein Hessian's angular trace-free coefficient: diagonal difference
and off-diagonal entry, both normalized as the coefficient of epsilon squared. -/
def angularCoefficient (s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ) : ℂ × ℂ :=
  let J := ComplexCoordinateMetricTwoJet.toSpace (D4BMBackground.jet r y)
  let K := ComplexCoordinateMetricTwoJet.toSpace
    (combinedJet s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy)
  let E := fun i j => ComplexCoordinateMetricTwoJet.secondVariation J i j K K
  ((E 2 2-E 3 3)/2, E 2 3/2)

private theorem combined_angular (s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ) :
    let K := combinedJet s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy
    K.metric 2 3 = 0 ∧ K.metric 2 2 = K.metric 3 3 := by
  simp [combinedJet, coexactJet, scalarJet, radialEntries, D4BMVectorLinearEquation.vectorJet,
    ScalarTwoJet.mul, ScalarTwoJet.constant]

/-- All three scalar/vector channels of the actual complex quadratic Einstein
source, at arbitrary height. No second or third free scalar angular derivative
survives in the vector--vector channel. -/
theorem angularCoefficient_eq (s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    angularCoefficient s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy =
      (B^(2 : ℕ) * (aS^(2 : ℕ) * scalarWeight s r *
        (2*S*(2*Sxx-(s+1)*(s+2)*S/y^(2 : ℕ)-2*Sy/y)+Sx^(2 : ℕ)-Sy^(2 : ℕ)) +
        2*aS*aV*mixedWeight s r*(S*(Sxy+Sx/y)+Sx*Sy) +
        aV^(2 : ℕ)*vectorWeight s r*(Sx^(2 : ℕ)-Sy^(2 : ℕ))),
       B^(2 : ℕ) * (aS^(2 : ℕ) * scalarWeight s r * (2*S*(Sxy+Sx/y)+Sx*Sy) -
        aS*aV*mixedWeight s r*(S*(2*Sxx-(s+1)*(s+2)*S/y^(2 : ℕ)-2*Sy/y)+Sx^(2 : ℕ)-Sy^(2 : ℕ))/2 +
        aV^(2 : ℕ)*vectorWeight s r*Sx*Sy)) := by
  let J := D4BMBackground.jet r y
  let K := combinedJet s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy
  have hJ : J.metric.det ≠ 0 := by
    change (D4BMBackground.metric r y).det ≠ 0
    rw [D4BMBackground.metric_det r y hf]
    exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 4 hr) (pow_ne_zero 4 (inv_ne_zero hy)))
  have hv := CoordinateMetricTwoJet.Quadratic.einstein_eq_secondVariation J K hJ
  change ((ComplexCoordinateMetricTwoJet.secondVariation _ 2 2 _ _ -
    ComplexCoordinateMetricTwoJet.secondVariation _ 3 3 _ _)/2,
    ComplexCoordinateMetricTwoJet.secondVariation _ 2 3 _ _/2) = _
  rw [← hv 2 2, ← hv 3 3, ← hv 2 3]
  have hm : K.metric 2 3 = 0 ∧ K.metric 2 2 = K.metric 3 3 := combined_angular s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy
  have hj0 : J.metric 2 3 = 0 := by simp [J, D4BMBackground.jet, D4BMBackground.metric]
  have hjd : J.metric 2 2 = J.metric 3 3 := by rfl
  have hd := ricci_difference s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy hr hy hf
  have ho := ricci_offdiagonal s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy hr hy hf
  apply Prod.ext
  · change (CoordinateMetricTwoJet.Quadratic.einstein J K 2 2 -
      CoordinateMetricTwoJet.Quadratic.einstein J K 3 3)/2 = _
    rw [← hd]
    change _ = (CoordinateMetricTwoJet.Quadratic.ricci J K 2 2 -
      CoordinateMetricTwoJet.Quadratic.ricci J K 3 3)/2
    simp only [CoordinateMetricTwoJet.Quadratic.einstein, hjd, hm.2]
    ring
  · change CoordinateMetricTwoJet.Quadratic.einstein J K 2 3 / 2 = _
    rw [CoordinateMetricTwoJet.Quadratic.einstein, hj0, hm.1]
    simpa only [mul_zero, sub_zero, add_zero] using ho

/-- Scalar times the actual trace-free hyperbolic Hessian, in the same two components. -/
def hessianPair (s y S Sx Sy Sxx Sxy : ℂ) : ℂ × ℂ :=
  (S*(2*Sxx-(s+1)*(s+2)*S/y^(2 : ℕ)-2*Sy/y), S*(Sxy+Sx/y))

/-- Trace-free gradient square in the same two components. -/
def gradientPair (Sx Sy : ℂ) : ℂ × ℂ := (Sx^(2 : ℕ)-Sy^(2 : ℕ), Sx*Sy)

/-- Oriented rotation of a symmetric trace-free angular tensor. -/
def rotatePair (T : ℂ × ℂ) : ℂ × ℂ := (2*T.2, -T.1/2)

/-- Exact source decomposition into a Hessian of the squared scalar, its rotation,
and a gradient-square remainder. The first two terms still require the actual
left-test derivatives and boundary terms when integrated. -/
theorem angularCoefficient_decomposition (s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    let H := hessianPair s y S Sx Sy Sxx Sxy
    let G := gradientPair Sx Sy
    angularCoefficient s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy =
      B^(2 : ℕ) • ((2*aS^(2 : ℕ)*scalarWeight s r) • (H+G) +
        (aS*aV*mixedWeight s r) • rotatePair (H+G) +
        (aV^(2 : ℕ)*vectorWeight s r-aS^(2 : ℕ)*scalarWeight s r) • G) := by
  rw [angularCoefficient_eq s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy hr hy hf]
  apply Prod.ext <;> dsimp [hessianPair, gradientPair, rotatePair] <;> ring

end
end RHTower.D4BMQuadraticAngularSource
