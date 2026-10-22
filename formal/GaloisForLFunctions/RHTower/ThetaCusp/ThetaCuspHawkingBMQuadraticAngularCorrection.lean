import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMQuadraticAngularSource
import GaloisForLFunctions.HTGeometry.CoordinateEinsteinCubicPath

/-!
# Explicit second-order correction of the BM angular source

A fully specified correction two-jet cancels the two Hessian terms in the actual
quadratic angular Einstein source. Insert it into the original nonlinear Einstein
contraction along the corrected metric-jet path. The exact remaining angular
coefficient is the gradient square multiplied by its derived radial coefficient.

This constructs a particular angular correction. It does not solve all Einstein
components, impose the nonlinear gauge, establish a global field realization or
physical endpoint admission, or identify the causal response and its left pairing.
-/

namespace RHTower.D4BMQuadraticAngularCorrection
open GaloisForLFunctions.HTGeometry
open D4BMScalarLinearEquation D4BMQuadraticAngularSource
noncomputable section

/-- Explicit complete second-order correction jet. Its temporal entry cancels
the scalar Hessian source; its temporal--angular entries cancel the rotated Hessian.
This is a particular angular correction, not a solution of all Einstein components. -/
def correctionJet (s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ) : CoordinateMetricTwoJet 4 ℂ :=
  let R := coord r 1
  let R2 := R.mul R
  let F := R2.add (ScalarTwoJet.constant (-1))
  let Rinv := R.inv
  let U := angular s y S Sx Sy Sxx Sxy
  let V0 := D4BMVectorLinearEquation.angular0 s y Sy Sxy
    ((s+1)*(s+2)*S/y^(2 : ℕ)-Sxx) (-Sxx) Sxxy ((s+1)*(s+2)*Sx/y^(2 : ℕ)-Sxxx)
  let V1 := D4BMVectorLinearEquation.angular1 s y (-Sx) Sxy (-Sxx)
    Sxxy ((s+1)*(s+2)*Sx/y^(2 : ℕ)-Sxxx)
  let W := temporalRadial (2*s) r (B^(2 : ℕ))
  let T := (((((ScalarTwoJet.constant (-aS^(2 : ℕ)*s^(2 : ℕ)/4)).mul W).mul F).mul
    ((ScalarTwoJet.constant ((s+1)^(2 : ℕ))).add ((ScalarTwoJet.constant (-4)).mul R2))).mul
    ((Rinv.mul Rinv).mul (Rinv.mul Rinv))).mul (U.mul U)
  let V := ((((ScalarTwoJet.constant (aS*aV*s*(s+1)/2)).mul W).mul F).mul
    ((Rinv.mul Rinv).mul Rinv)).mul U
  let X := V.mul V0
  let Y := V.mul V1
  let Z : ScalarTwoJet (Fin 4) ℂ := ScalarTwoJet.constant 0
  let A := !![T,Z,X,Y; Z,Z,Z,Z; X,Z,Z,Z; Y,Z,Z,Z]
  ⟨fun i j => (A i j).value, fun k i j => (A i j).first k,
    fun k l i j => (A i j).second k l⟩

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


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem ricci_offdiagonal (s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (correctionJet s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy) 2 3 =
      B^(2 : ℕ) * (-2*aS^(2 : ℕ)*scalarWeight s r*(S*(Sxy+Sx/y)+Sx*Sy) +
        aS*aV*mixedWeight s r*(S*(2*Sxx-(s+1)*(s+2)*S/y^(2 : ℕ)-2*Sy/y)+Sx^(2 : ℕ)-Sy^(2 : ℕ))/2) := by
  generalize hK : correctionJet s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy = K
  simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, background_first, background_second,
    D4BMBackground.metric_inverse r y hr hy hf]
  rw [← hK]
  simp [Fin.sum_univ_succ, Matrix.mul_apply, correctionJet, angular,
    D4BMVectorLinearEquation.angular0, D4BMVectorLinearEquation.angular1,
    temporalRadial, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.inv,
    ScalarTwoJet.constant]
  simp only [scalarWeight, mixedWeight, ← pow_two, ← sub_eq_add_neg]
  field_simp [hf, hr, hy]
  ring

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem ricci_difference (s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (correctionJet s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy) 2 2 -
      CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (correctionJet s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy) 3 3 =
      B^(2 : ℕ) * (-2*aS^(2 : ℕ)*scalarWeight s r*
        (S*(2*Sxx-(s+1)*(s+2)*S/y^(2 : ℕ)-2*Sy/y)+Sx^(2 : ℕ)-Sy^(2 : ℕ)) -
        2*aS*aV*mixedWeight s r*(S*(Sxy+Sx/y)+Sx*Sy)) := by
  generalize hK : correctionJet s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy = K
  simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, background_first, background_second,
    D4BMBackground.metric_inverse r y hr hy hf]
  rw [← hK]
  simp [Fin.sum_univ_succ, Matrix.mul_apply, correctionJet, angular,
    D4BMVectorLinearEquation.angular0, D4BMVectorLinearEquation.angular1,
    temporalRadial, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.inv,
    ScalarTwoJet.constant]
  simp only [scalarWeight, mixedWeight, ← pow_two, ← sub_eq_add_neg]
  field_simp [hf, hr, hy]
  ring

end
end RHTower.D4BMQuadraticAngularCorrection
namespace RHTower.D4BMQuadraticAngularCorrection
open GaloisForLFunctions.HTGeometry
open D4BMQuadraticAngularSource
noncomputable section

/-- Angular part of the actual first Einstein variation of the explicit correction. -/
def linearAngularCoefficient (s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ) : ℂ × ℂ :=
  let L := CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet r y)
    (correctionJet s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy) (-3)
  (L 2 2-L 3 3, L 2 3)

/-- The constructed correction cancels exactly the squared-scalar Hessian and its
rotation. It does not assert the other Einstein equations or physical endpoint admission. -/
theorem linearAngularCoefficient_eq (s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    let H := hessianPair s y S Sx Sy Sxx Sxy
    let G := gradientPair Sx Sy
    linearAngularCoefficient s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy =
      -(B^(2 : ℕ) • ((2*aS^(2 : ℕ)*scalarWeight s r) • (H+G) +
        (aS*aV*mixedWeight s r) • rotatePair (H+G))) := by
  let J := D4BMBackground.jet r y
  let K := correctionJet s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy
  have hk22 : K.metric 2 2 = 0 := by simp [K, correctionJet, ScalarTwoJet.constant]
  have hk33 : K.metric 3 3 = 0 := by simp [K, correctionJet, ScalarTwoJet.constant]
  have hk23 : K.metric 2 3 = 0 := by simp [K, correctionJet, ScalarTwoJet.constant]
  have hj23 : J.metric 2 3 = 0 := by simp [J, D4BMBackground.jet, D4BMBackground.metric]
  have hjd : J.metric 2 2 = J.metric 3 3 := by rfl
  have hd := ricci_difference s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy hr hy hf
  have ho := ricci_offdiagonal s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy hr hy hf
  have hd' : CoordinateMetricTwoJet.Linearization.cosmological J K (-3) 2 2 -
      CoordinateMetricTwoJet.Linearization.cosmological J K (-3) 3 3 =
      CoordinateMetricTwoJet.Linearization.ricci J K 2 2 -
        CoordinateMetricTwoJet.Linearization.ricci J K 3 3 := by
    simp only [CoordinateMetricTwoJet.Linearization.cosmological,
      CoordinateMetricTwoJet.Linearization.einstein, hk22, hk33, hjd, mul_zero, add_zero]
    ring
  have ho' : CoordinateMetricTwoJet.Linearization.cosmological J K (-3) 2 3 =
      CoordinateMetricTwoJet.Linearization.ricci J K 2 3 := by
    simp only [CoordinateMetricTwoJet.Linearization.cosmological,
      CoordinateMetricTwoJet.Linearization.einstein, hk23, hj23, mul_zero, add_zero, sub_zero]
  change (CoordinateMetricTwoJet.Linearization.cosmological J K (-3) 2 2 -
      CoordinateMetricTwoJet.Linearization.cosmological J K (-3) 3 3,
      CoordinateMetricTwoJet.Linearization.cosmological J K (-3) 2 3) = _
  rw [hd', ho']
  change (CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y) _ 2 2 -
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y) _ 3 3,
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y) _ 2 3) = _
  rw [hd, ho]
  apply Prod.ext <;> dsimp [hessianPair, gradientPair, rotatePair] <;> ring

/-- Literal cosmological Einstein source on the complete corrected metric-jet path. -/
def correctedSource (s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (i j : Fin 4) : ℂ → ℂ :=
  ComplexCoordinateMetricTwoJet.CubicSource.source (D4BMBackground.jet r y)
    (combinedJet s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy)
    (correctionJet s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy)
    ⟨0, fun _ => 0, fun _ _ => 0⟩ (-3) i j

/-- The actual epsilon-squared angular coefficient after inserting the correction. -/
def correctedAngularCoefficient (s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ) : ℂ × ℂ :=
  let E := fun i j => iteratedDeriv 2
    (correctedSource s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy i j) 0 / 2
  (E 2 2-E 3 3, E 2 3)

/-- The actual corrected source keeps both the correction's first variation and
the original field's quadratic Hessian, with their forced normalization. -/
theorem correctedAngularCoefficient_eq_sum (s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    correctedAngularCoefficient s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy =
      linearAngularCoefficient s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy +
        angularCoefficient s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy := by
  have hJ : (D4BMBackground.jet r y).metric.det ≠ 0 := by
    change (D4BMBackground.metric r y).det ≠ 0
    rw [D4BMBackground.metric_det r y hf]
    exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 4 hr) (pow_ne_zero 4 (inv_ne_zero hy)))
  unfold correctedAngularCoefficient correctedSource
  simp only [ComplexCoordinateMetricTwoJet.CubicSource.quadratic_coefficient _ _ _ _ hJ]
  apply Prod.ext <;> (dsimp [linearAngularCoefficient, angularCoefficient] <;> ring)

/-- Exact remaining angular source after the explicit correction: one gradient
square with a completely determined radial coefficient. No physical response or
extinction hypothesis is used. -/
theorem correctedAngularCoefficient_eq (s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    correctedAngularCoefficient s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy =
      (B^(2 : ℕ)*(aV^(2 : ℕ)*vectorWeight s r-aS^(2 : ℕ)*scalarWeight s r)) • gradientPair Sx Sy := by
  rw [correctedAngularCoefficient_eq_sum s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy hr hy hf,
    linearAngularCoefficient_eq s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy hr hy hf,
    angularCoefficient_decomposition s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy hr hy hf]
  apply Prod.ext <;> dsimp [hessianPair, gradientPair, rotatePair] <;> ring

end
end RHTower.D4BMQuadraticAngularCorrection
