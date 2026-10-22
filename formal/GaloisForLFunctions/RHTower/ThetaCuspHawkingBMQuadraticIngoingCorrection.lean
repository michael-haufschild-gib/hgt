import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuadraticAngularCorrection
import GaloisForLFunctions.HTGeometry.CoordinateEinsteinCubicPath

/-!
# Quadratic angular correction with an ingoing-regular orbit block

The scalar orbit block has the same background trace as the temporal-only
correction, but its ingoing radial--radial entry vanishes. The complete jet's
actual linear Einstein image cancels the same Hessian channels. The corrected
nonlinear angular source retains its exact gradient-square remainder.
-/

namespace RHTower.D4BMQuadraticIngoingCorrection
open GaloisForLFunctions.HTGeometry
open D4BMScalarLinearEquation D4BMQuadraticAngularSource
noncomputable section

/-- Explicit complete second-order correction jet. Its orbit trace cancels
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
  let T := (((((ScalarTwoJet.constant (aS^(2 : ℕ)*s^(2 : ℕ)/8)).mul W).mul
    ((ScalarTwoJet.constant ((s+1)^(2 : ℕ))).add ((ScalarTwoJet.constant (-4)).mul R2))).mul
    ((Rinv.mul Rinv).mul (Rinv.mul Rinv))).mul (U.mul U))
  let RR := ((ScalarTwoJet.constant 2).mul T).mul F.inv
  let V := ((((ScalarTwoJet.constant (aS*aV*s*(s+1)/2)).mul W).mul F).mul
    ((Rinv.mul Rinv).mul Rinv)).mul U
  let X := V.mul V0
  let Y := V.mul V1
  let Z : ScalarTwoJet (Fin 4) ℂ := ScalarTwoJet.constant 0
  let A := !![Z,T,X,Y; T,RR,Z,Z; X,Z,Z,Z; Y,Z,Z,Z]
  ⟨fun i j => (A i j).value, fun k i j => (A i j).first k,
    fun k l i j => (A i j).second k l⟩

private theorem background_metric (r y : ℂ) :
    (D4BMBackground.jet r y).metric = D4BMBackground.metric r y := rfl
  _root_.RHTower.D4BMVectorLinearEquation.background_metric r y

private theorem background_first (r y : ℂ) (k : Fin 4) :
    (D4BMBackground.jet r y).first k = Matrix.diagonal
      (if k = 1 then ![-2*r, -2*r*(r^(2 : ℕ)-1)⁻¹^(2 : ℕ), 2*r*y⁻¹^(2 : ℕ), 2*r*y⁻¹^(2 : ℕ)]
       else if k = 3 then ![0, 0, -2*r^(2 : ℕ)*y⁻¹^(3 : ℕ), -2*r^(2 : ℕ)*y⁻¹^(3 : ℕ)] else 0) := rfl
  _root_.RHTower.D4BMVectorLinearEquation.background_first r y k

private theorem background_second (r y : ℂ) (k l : Fin 4) :
    (D4BMBackground.jet r y).second k l = Matrix.diagonal
      (if k = 1 ∧ l = 1 then ![-2, -2*(r^(2 : ℕ)-1)⁻¹^(2 : ℕ)+8*r^(2 : ℕ)*(r^(2 : ℕ)-1)⁻¹^(3 : ℕ),
        2*y⁻¹^(2 : ℕ), 2*y⁻¹^(2 : ℕ)]
       else if (k = 1 ∧ l = 3) ∨ (k = 3 ∧ l = 1) then ![0,0,-4*r*y⁻¹^(3 : ℕ),-4*r*y⁻¹^(3 : ℕ)]
       else if k = 3 ∧ l = 3 then ![0,0,6*r^(2 : ℕ)*y⁻¹^(4 : ℕ),6*r^(2 : ℕ)*y⁻¹^(4 : ℕ)] else 0) := rfl
  _root_.RHTower.D4BMVectorLinearEquation.background_second r y k l
set_option maxHeartbeats 1000000 in
private theorem ricci_offdiagonal (s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (correctionJet s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy) 2 3 =
      B^(2 : ℕ) * (-2*aS^(2 : ℕ)*scalarWeight s r*(S*(Sxy+Sx/y)+Sx*Sy) +
        aS*aV*mixedWeight s r*(S*(2*Sxx-(s+1)*(s+2)*S/y^(2 : ℕ)-2*Sy/y)+Sx^(2 : ℕ)-Sy^(2 : ℕ))/2) :=
  _root_.RHTower.D4BMQuadraticAngularCorrection.ricci_offdiagonal s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy hr hy hf
set_option maxHeartbeats 1000000 in
private theorem ricci_difference (s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (correctionJet s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy) 2 2 -
      CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (correctionJet s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy) 3 3 =
      B^(2 : ℕ) * (-2*aS^(2 : ℕ)*scalarWeight s r*
        (S*(2*Sxx-(s+1)*(s+2)*S/y^(2 : ℕ)-2*Sy/y)+Sx^(2 : ℕ)-Sy^(2 : ℕ)) -
        2*aS*aV*mixedWeight s r*(S*(Sxy+Sx/y)+Sx*Sy)) :=
  _root_.RHTower.D4BMQuadraticAngularCorrection.ricci_difference s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy hr hy hf

end
end RHTower.D4BMQuadraticIngoingCorrection
namespace RHTower.D4BMQuadraticIngoingCorrection
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
        (aS*aV*mixedWeight s r) • rotatePair (H+G))) :=
  _root_.RHTower.D4BMQuadraticAngularCorrection.linearAngularCoefficient_eq s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy hr hy hf

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
        angularCoefficient s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy :=
  _root_.RHTower.D4BMQuadraticAngularCorrection.correctedAngularCoefficient_eq_sum s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy hr hy hf

/-- Exact remaining angular source after the explicit correction: one gradient
square with a completely determined radial coefficient. No physical response or
extinction hypothesis is used. -/
theorem correctedAngularCoefficient_eq (s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    correctedAngularCoefficient s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy =
      (B^(2 : ℕ)*(aV^(2 : ℕ)*vectorWeight s r-aS^(2 : ℕ)*scalarWeight s r)) • gradientPair Sx Sy :=
  _root_.RHTower.D4BMQuadraticAngularCorrection.correctedAngularCoefficient_eq s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy hr hy hf

end
end RHTower.D4BMQuadraticIngoingCorrection
