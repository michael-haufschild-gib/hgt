import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLinearizedEinsteinSource

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
  first := ![s*B, s*B/(r*(r^(2 : ℕ)-1)), 0, 0]
  second := !![s^(2 : ℕ)*B, s^(2 : ℕ)*B/(r*(r^(2 : ℕ)-1)), 0, 0;
    s^(2 : ℕ)*B/(r*(r^(2 : ℕ)-1)), B*(s^(2 : ℕ)-s*(3*r^(2 : ℕ)-1))/(r^(2 : ℕ)*(r^(2 : ℕ)-1)^(2 : ℕ)), 0, 0;
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
    0, 0, Sxy, (s+1)*(s+2)*S/y^(2 : ℕ)-Sxx]

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

/-! The sixteen coordinate components of the linearized Ricci residual. Each component is
its own declaration: a single `fin_cases` fan would pay all sixteen expansions of the
nested `Fin 4` curvature contraction inside one elaboration. -/

set_option maxRecDepth 4096 in
private theorem ricci_0_0 (s r y B S Sx Sy Sxx Sxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 +
      3*(scalarJet s r y B S Sx Sy Sxx Sxy).metric 0 0 = 0 := by
  generalize hK : scalarJet s r y B S Sx Sy Sxx Sxy = K
  all_goals simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals simp [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply]
  all_goals rw [← hK]
  all_goals simp [scalarJet, temporalRadial, angular,
    radialEntries, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.neg,
    ScalarTwoJet.inv, ScalarTwoJet.constant]
  all_goals simp only [← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hf, hr, hy]
  all_goals ring

set_option maxRecDepth 4096 in
private theorem ricci_0_1 (s r y B S Sx Sy Sxx Sxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 +
      3*(scalarJet s r y B S Sx Sy Sxx Sxy).metric 0 1 = 0 := by
  generalize hK : scalarJet s r y B S Sx Sy Sxx Sxy = K
  all_goals simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals simp [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply]
  all_goals rw [← hK]
  all_goals simp [scalarJet, temporalRadial, angular,
    radialEntries, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.neg,
    ScalarTwoJet.inv, ScalarTwoJet.constant]
  all_goals simp only [← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hf, hr, hy]
  all_goals ring

set_option maxRecDepth 4096 in
private theorem ricci_0_2 (s r y B S Sx Sy Sxx Sxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2 +
      3*(scalarJet s r y B S Sx Sy Sxx Sxy).metric 0 2 = 0 := by
  generalize hK : scalarJet s r y B S Sx Sy Sxx Sxy = K
  all_goals simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals simp [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply]
  all_goals rw [← hK]
  all_goals simp [scalarJet, temporalRadial, angular,
    radialEntries, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.neg,
    ScalarTwoJet.inv, ScalarTwoJet.constant]
  all_goals simp only [← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hf, hr, hy]
  all_goals ring

set_option maxRecDepth 4096 in
private theorem ricci_0_3 (s r y B S Sx Sy Sxx Sxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy) 0 3 +
      3*(scalarJet s r y B S Sx Sy Sxx Sxy).metric 0 3 = 0 := by
  generalize hK : scalarJet s r y B S Sx Sy Sxx Sxy = K
  all_goals simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals simp [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply]
  all_goals rw [← hK]
  all_goals simp [scalarJet, temporalRadial, angular,
    radialEntries, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.neg,
    ScalarTwoJet.inv, ScalarTwoJet.constant]
  all_goals simp only [← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hf, hr, hy]
  all_goals ring

set_option maxRecDepth 4096 in
private theorem ricci_1_0 (s r y B S Sx Sy Sxx Sxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 +
      3*(scalarJet s r y B S Sx Sy Sxx Sxy).metric 1 0 = 0 := by
  generalize hK : scalarJet s r y B S Sx Sy Sxx Sxy = K
  all_goals simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals simp [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply]
  all_goals rw [← hK]
  all_goals simp [scalarJet, temporalRadial, angular,
    radialEntries, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.neg,
    ScalarTwoJet.inv, ScalarTwoJet.constant]
  all_goals simp only [← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hf, hr, hy]
  all_goals ring

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
private theorem ricci_1_1 (s r y B S Sx Sy Sxx Sxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 +
      3*(scalarJet s r y B S Sx Sy Sxx Sxy).metric 1 1 = 0 := by
  generalize hK : scalarJet s r y B S Sx Sy Sxx Sxy = K
  all_goals simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals simp [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply]
  all_goals rw [← hK]
  all_goals simp [scalarJet, temporalRadial, angular,
    radialEntries, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.neg,
    ScalarTwoJet.inv, ScalarTwoJet.constant]
  all_goals simp only [← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hf, hr, hy]
  all_goals ring

set_option maxRecDepth 4096 in
private theorem ricci_1_2 (s r y B S Sx Sy Sxx Sxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2 +
      3*(scalarJet s r y B S Sx Sy Sxx Sxy).metric 1 2 = 0 := by
  generalize hK : scalarJet s r y B S Sx Sy Sxx Sxy = K
  all_goals simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals simp [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply]
  all_goals rw [← hK]
  all_goals simp [scalarJet, temporalRadial, angular,
    radialEntries, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.neg,
    ScalarTwoJet.inv, ScalarTwoJet.constant]
  all_goals simp only [← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hf, hr, hy]
  all_goals ring

set_option maxRecDepth 4096 in
private theorem ricci_1_3 (s r y B S Sx Sy Sxx Sxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy) 1 3 +
      3*(scalarJet s r y B S Sx Sy Sxx Sxy).metric 1 3 = 0 := by
  generalize hK : scalarJet s r y B S Sx Sy Sxx Sxy = K
  all_goals simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals simp [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply]
  all_goals rw [← hK]
  all_goals simp [scalarJet, temporalRadial, angular,
    radialEntries, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.neg,
    ScalarTwoJet.inv, ScalarTwoJet.constant]
  all_goals simp only [← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hf, hr, hy]
  all_goals ring

set_option maxRecDepth 4096 in
private theorem ricci_2_0 (s r y B S Sx Sy Sxx Sxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy) 2 0 +
      3*(scalarJet s r y B S Sx Sy Sxx Sxy).metric 2 0 = 0 := by
  generalize hK : scalarJet s r y B S Sx Sy Sxx Sxy = K
  all_goals simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals simp [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply]
  all_goals rw [← hK]
  all_goals simp [scalarJet, temporalRadial, angular,
    radialEntries, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.neg,
    ScalarTwoJet.inv, ScalarTwoJet.constant]
  all_goals simp only [← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hf, hr, hy]
  all_goals ring

set_option maxRecDepth 4096 in
private theorem ricci_2_1 (s r y B S Sx Sy Sxx Sxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy) 2 1 +
      3*(scalarJet s r y B S Sx Sy Sxx Sxy).metric 2 1 = 0 := by
  generalize hK : scalarJet s r y B S Sx Sy Sxx Sxy = K
  all_goals simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals simp [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply]
  all_goals rw [← hK]
  all_goals simp [scalarJet, temporalRadial, angular,
    radialEntries, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.neg,
    ScalarTwoJet.inv, ScalarTwoJet.constant]
  all_goals simp only [← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hf, hr, hy]
  all_goals ring

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
private theorem ricci_2_2 (s r y B S Sx Sy Sxx Sxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy) 2 2 +
      3*(scalarJet s r y B S Sx Sy Sxx Sxy).metric 2 2 = 0 := by
  generalize hK : scalarJet s r y B S Sx Sy Sxx Sxy = K
  all_goals simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals simp [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply]
  all_goals rw [← hK]
  all_goals simp [scalarJet, temporalRadial, angular,
    radialEntries, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.neg,
    ScalarTwoJet.inv, ScalarTwoJet.constant]
  all_goals simp only [← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hf, hr, hy]
  all_goals ring

set_option maxRecDepth 4096 in
private theorem ricci_2_3 (s r y B S Sx Sy Sxx Sxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy) 2 3 +
      3*(scalarJet s r y B S Sx Sy Sxx Sxy).metric 2 3 = 0 := by
  generalize hK : scalarJet s r y B S Sx Sy Sxx Sxy = K
  all_goals simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals simp [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply]
  all_goals rw [← hK]
  all_goals simp [scalarJet, temporalRadial, angular,
    radialEntries, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.neg,
    ScalarTwoJet.inv, ScalarTwoJet.constant]
  all_goals simp only [← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hf, hr, hy]
  all_goals ring

set_option maxRecDepth 4096 in
private theorem ricci_3_0 (s r y B S Sx Sy Sxx Sxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy) 3 0 +
      3*(scalarJet s r y B S Sx Sy Sxx Sxy).metric 3 0 = 0 := by
  generalize hK : scalarJet s r y B S Sx Sy Sxx Sxy = K
  all_goals simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals simp [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply]
  all_goals rw [← hK]
  all_goals simp [scalarJet, temporalRadial, angular,
    radialEntries, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.neg,
    ScalarTwoJet.inv, ScalarTwoJet.constant]
  all_goals simp only [← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hf, hr, hy]
  all_goals ring

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
private theorem ricci_3_1 (s r y B S Sx Sy Sxx Sxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy) 3 1 +
      3*(scalarJet s r y B S Sx Sy Sxx Sxy).metric 3 1 = 0 := by
  generalize hK : scalarJet s r y B S Sx Sy Sxx Sxy = K
  all_goals simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals simp [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply]
  all_goals rw [← hK]
  all_goals simp [scalarJet, temporalRadial, angular,
    radialEntries, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.neg,
    ScalarTwoJet.inv, ScalarTwoJet.constant]
  all_goals simp only [← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hf, hr, hy]
  all_goals ring

set_option maxRecDepth 4096 in
private theorem ricci_3_2 (s r y B S Sx Sy Sxx Sxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy) 3 2 +
      3*(scalarJet s r y B S Sx Sy Sxx Sxy).metric 3 2 = 0 := by
  generalize hK : scalarJet s r y B S Sx Sy Sxx Sxy = K
  all_goals simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals simp [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply]
  all_goals rw [← hK]
  all_goals simp [scalarJet, temporalRadial, angular,
    radialEntries, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.neg,
    ScalarTwoJet.inv, ScalarTwoJet.constant]
  all_goals simp only [← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hf, hr, hy]
  all_goals ring

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
private theorem ricci_3_3 (s r y B S Sx Sy Sxx Sxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy) 3 3 +
      3*(scalarJet s r y B S Sx Sy Sxx Sxy).metric 3 3 = 0 := by
  generalize hK : scalarJet s r y B S Sx Sy Sxx Sxy = K
  all_goals simp only [CoordinateMetricTwoJet.Linearization.ricci,
    CoordinateMetricTwoJet.Linearization.curvature,
    CoordinateMetricTwoJet.Linearization.connectionSpatial,
    CoordinateMetricTwoJet.Linearization.connection,
    CoordinateMetricTwoJet.Linearization.inverseSpatial,
    CoordinateMetricTwoJet.Linearization.inverse,
    CoordinateMetricTwoJet.christoffel, CoordinateMetricTwoJet.inverseDerivative,
    background_metric, 
    D4BMBackground.metric_inverse r y hr hy hf]
  all_goals simp [Fin.sum_univ_four, background_first_0, background_first_1, background_first_2, background_first_3, background_second_0_0, background_second_0_1, background_second_0_2, background_second_0_3, background_second_1_0, background_second_1_1, background_second_1_2, background_second_1_3, background_second_2_0, background_second_2_1, background_second_2_2, background_second_2_3, background_second_3_0, background_second_3_1, background_second_3_2, background_second_3_3, Matrix.mul_apply]
  all_goals rw [← hK]
  all_goals simp [scalarJet, temporalRadial, angular,
    radialEntries, coord, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.neg,
    ScalarTwoJet.inv, ScalarTwoJet.constant]
  all_goals simp only [← pow_two, ← sub_eq_add_neg]
  all_goals field_simp [hf, hr, hy]
  all_goals ring

/-- Every coordinate component satisfies the linearized Ricci equation. -/
theorem ricci_component (s r y B S Sx Sy Sxx Sxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy) i j +
      3*(scalarJet s r y B S Sx Sy Sxx Sxy).metric i j = 0 := by
  fin_cases i <;> fin_cases j
  · exact ricci_0_0 s r y B S Sx Sy Sxx Sxy hr hy hf
  · exact ricci_0_1 s r y B S Sx Sy Sxx Sxy hr hy hf
  · exact ricci_0_2 s r y B S Sx Sy Sxx Sxy hr hy hf
  · exact ricci_0_3 s r y B S Sx Sy Sxx Sxy hr hy hf
  · exact ricci_1_0 s r y B S Sx Sy Sxx Sxy hr hy hf
  · exact ricci_1_1 s r y B S Sx Sy Sxx Sxy hr hy hf
  · exact ricci_1_2 s r y B S Sx Sy Sxx Sxy hr hy hf
  · exact ricci_1_3 s r y B S Sx Sy Sxx Sxy hr hy hf
  · exact ricci_2_0 s r y B S Sx Sy Sxx Sxy hr hy hf
  · exact ricci_2_1 s r y B S Sx Sy Sxx Sxy hr hy hf
  · exact ricci_2_2 s r y B S Sx Sy Sxx Sxy hr hy hf
  · exact ricci_2_3 s r y B S Sx Sy Sxx Sxy hr hy hf
  · exact ricci_3_0 s r y B S Sx Sy Sxx Sxy hr hy hf
  · exact ricci_3_1 s r y B S Sx Sy Sxx Sxy hr hy hf
  · exact ricci_3_2 s r y B S Sx Sy Sxx Sxy hr hy hf
  · exact ricci_3_3 s r y B S Sx Sy Sxx Sxy hr hy hf

end
end RHTower.D4BMScalarLinearEquation

namespace RHTower.D4BMLinearizedRicci
open GaloisForLFunctions.HTGeometry
open CoordinateMetricTwoJet.Linearization
open scoped BigOperators
noncomputable section

/-- A solution of the linearized Ricci equation has zero actual scalar variation. -/
theorem scalar_zero_of_ricci (r y : ℂ) (K : CoordinateMetricTwoJet 4 ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0)
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
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0)
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
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy) (-3) i j = 0 := by
  apply D4BMLinearizedRicci.cosmological_zero_of_ricci r y _ hr hy hf
  intro k l
  have hz := ricci_component s r y B S Sx Sy Sxx Sxy hr hy hf k l
  linear_combination hz

end
end RHTower.D4BMScalarLinearEquation
