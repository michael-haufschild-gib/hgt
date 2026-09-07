import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLinearizedEinsteinSource

/-!
# Fundamental scalar metric jets and the linearized Ricci equation

The temporal/radial rate and scalar harmonic equation fix the displayed complete
metric jet. Every coordinate component of its linearized Ricci residual vanishes.
The scalar variation and fixed cosmological term then give the Einstein residual.
Identifying a particular field with this full jet is a separate derivative statement.
-/

namespace RHTower.D4BMScalarLinearEquation
open GaloisForLFunctions.HTGeometry
open scoped BigOperators
noncomputable section

private abbrev Jet := ScalarTwoJet (Fin 4) ℂ

/-- Complete coordinate jet used in the rational radial coefficients. -/
def coord (v : ℂ) (i : Fin 4) : Jet :=
  ⟨v, fun k => if k = i then 1 else 0, fun _ _ => 0⟩

/-- Temporal/radial two-jet with every mixed derivative retained. -/
def temporalRadial (s r B : ℂ) : Jet where
  value := B
  first := ![s*B, s*B/(r*(r^2-1)), 0, 0]
  second := !![s^2*B, s^2*B/(r*(r^2-1)), 0, 0;
    s^2*B/(r*(r^2-1)), B*(s^2-s*(3*r^2-1))/(r^2*(r^2-1)^2), 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0]

/-- Full angular two-jet under the scalar Laplacian relation, retaining free first
and traceless second derivatives. -/
def angular (s y S Sx Sy Sxx Sxy : ℂ) : Jet where
  value := S
  first := ![0, 0, Sx, Sy]
  second := !![0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, Sxx, Sxy;
    0, 0, Sxy, (s+1)*(s+2)*S/y^2-Sxx]

/-- Rational scalar radial coefficients, evaluated by the full two-jet calculus. -/
def radialEntries (s r y : ℂ) : Matrix (Fin 4) (Fin 4) Jet :=
  let R := coord r 1
  let Y := coord y 3
  let F := (R.mul R).add (ScalarTwoJet.constant (-1))
  let T := (ScalarTwoJet.constant (s*(s-3)/2)).add
    ((ScalarTwoJet.constant (s*(s+1)/2)).mul (R.inv.mul R.inv))
  let M := (ScalarTwoJet.constant (-s)).mul
    (((R.mul R).add (ScalarTwoJet.constant (-s))).mul (R.mul F).inv)
  let A := ((R.mul R).neg.add (ScalarTwoJet.constant (-s*(s+1)/2))).mul (Y.inv.mul Y.inv)
  let Z : Jet := ScalarTwoJet.constant 0
  !![T, M, Z, Z;
    M, T.mul (F.inv.mul F.inv), Z, Z;
    Z, Z, A, Z;
    Z, Z, Z, A]

/-- Complete separated metric jet including temporal, radial, angular and mixed derivatives. -/
def scalarJet (s r y B S Sx Sy Sxx Sxy : ℂ) : CoordinateMetricTwoJet 4 ℂ :=
  let J := fun i j => ((temporalRadial s r B).mul (angular s y S Sx Sy Sxx Sxy)).mul
    (radialEntries s r y i j)
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
/-- Every coordinate component satisfies the linearized Ricci equation. -/
theorem ricci_component (s r y B S Sx Sy Sxx Sxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy) i j +
      3*(scalarJet s r y B S Sx Sy Sxx Sxy).metric i j = 0 := by
  generalize hK : scalarJet s r y B S Sx Sy Sxx Sxy = K
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
  all_goals simp [scalarJet, temporalRadial, angular,
    radialEntries, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.neg,
    ScalarTwoJet.inv, ScalarTwoJet.constant]
  all_goals simp only [← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hf, hr, hy]
  all_goals ring

end
end RHTower.D4BMScalarLinearEquation

namespace RHTower.D4BMLinearizedRicci
open GaloisForLFunctions.HTGeometry
open CoordinateMetricTwoJet.Linearization
open scoped BigOperators
noncomputable section

/-- A solution of the linearized Ricci equation has zero actual scalar variation. -/
theorem scalar_zero_of_ricci (r y : ℂ) (K : CoordinateMetricTwoJet 4 ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0)
    (hR : ∀ i j, ricci (D4BMBackground.jet r y) K i j = -3*K.metric i j) :
    scalar (D4BMBackground.jet r y) K = 0 := by
  simp only [scalar, hR, D4BMBackground.jet_ricci r y hr hy hf]
  simp only [inverse, D4BMBackground.jet, D4BMBackground.metric_inverse r y hr hy hf]
  simp [D4BMBackground.metric, Matrix.mul_apply, Fin.sum_univ_succ]
  field_simp
  ring

/-- On the proved vacuum background, the full linearized Ricci equation implies
the complete cosmological Einstein equation, with its scalar term retained. -/
theorem cosmological_zero_of_ricci (r y : ℂ) (K : CoordinateMetricTwoJet 4 ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0)
    (hR : ∀ i j, ricci (D4BMBackground.jet r y) K i j = -3*K.metric i j)
    (i j : Fin 4) : cosmological (D4BMBackground.jet r y) K (-3) i j = 0 := by
  rw [cosmological, einstein, scalar_zero_of_ricci r y K hr hy hf hR,
    D4BMBackground.jet_scalar r y hr hy hf, hR]
  ring

end
end RHTower.D4BMLinearizedRicci

namespace RHTower.D4BMScalarLinearEquation
open GaloisForLFunctions.HTGeometry
noncomputable section

/-- The complete cosmological Einstein residual vanishes on the derived scalar jet. -/
theorem cosmological_component (s r y B S Sx Sy Sxx Sxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy) (-3) i j = 0 := by
  apply D4BMLinearizedRicci.cosmological_zero_of_ricci r y _ hr hy hf
  intro k l
  have hz := ricci_component s r y B S Sx Sy Sxx Sxy hr hy hf k l
  linear_combination hz

end
end RHTower.D4BMScalarLinearEquation
