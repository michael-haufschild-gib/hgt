import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMVectorVectorQuadraticRicci
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMVectorLinearizedRicciJet
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarJetQuadraticEinstein

/-!
# The vector–vector quadratic Einstein source of the fundamental Birmingham–Mokhtari vector jet

All ten components of the quadratic Einstein variation `Quadratic.einstein J K` of the fundamental
vector metric jet over the Birmingham–Mokhtari background, in closed form. The vector jet solves the
linearized cosmological equation with constant `-3` and is symmetric, so the Einstein coefficient is
the quadratic Ricci variation minus half the background metric times its background trace
(`vectorJet_quadratic_einstein_eq`), and every Ricci component is a closed form from the assembly
module. This is the complete vector–vector `++` quadratic source tensor `B(h_V, h_V)` of route HB,
with no heartbeat limit raised.
-/

set_option linter.unusedSimpArgs false

namespace RHTower.D4BMVectorLinearEquation
open GaloisForLFunctions.HTGeometry CoordinateMetricTwoJet D4BMScalarLinearEquation
noncomputable section
variable {s r y B A C P Q R U W : ℂ}

/-- The fundamental vector jet's metric block is symmetric. -/
theorem vectorJet_metric_symm (s r y B A C P Q R U W : ℂ) (i j : Fin 4) :
    (vectorJet s r y B A C P Q R U W).metric i j = (vectorJet s r y B A C P Q R U W).metric j i := by
  fin_cases i <;> fin_cases j <;> rfl

/-- The linearized Ricci variation of the vector jet is `-3` times the jet. -/
theorem vectorJet_linearization_ricci (s r y B A C P Q R U W : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (i j : Fin 4) :
    Linearization.ricci (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) i j =
      -3 * (vectorJet s r y B A C P Q R U W).metric i j := by
  have h := ricci_component s r y B A C P Q R U W hr hy hf i j
  linear_combination h

/-- Vector–vector quadratic Einstein source as a trace-adjusted quadratic Ricci variation. -/
theorem vectorJet_quadratic_einstein_eq (s r y B A C P Q R U W : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (i j : Fin 4) :
    Quadratic.einstein (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) i j =
      Quadratic.ricci (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) i j -
      (1 / 2 : ℂ) * (∑ u, ((D4BMBackground.jet r y).metric u u)⁻¹ *
        Quadratic.ricci (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) u u) *
      (D4BMBackground.jet r y).metric i j :=
  (D4BMBackground.jet_isDiagonalJet r y hr hy hf).quadratic_einstein_eq _ (-3)
    (background_ricci_eq r y hr hy hf)
    (vectorJet_linearization_ricci s r y B A C P Q R U W hr hy hf)
    (vectorJet_metric_symm s r y B A C P Q R U W) i j

private theorem background_metric_0_1 (r y : ℂ) : (D4BMBackground.jet r y).metric 0 1 = 0 := rfl
private theorem background_metric_0_2 (r y : ℂ) : (D4BMBackground.jet r y).metric 0 2 = 0 := rfl
private theorem background_metric_0_3 (r y : ℂ) : (D4BMBackground.jet r y).metric 0 3 = 0 := rfl
private theorem background_metric_1_2 (r y : ℂ) : (D4BMBackground.jet r y).metric 1 2 = 0 := rfl
private theorem background_metric_1_3 (r y : ℂ) : (D4BMBackground.jet r y).metric 1 3 = 0 := rfl
private theorem background_metric_2_3 (r y : ℂ) : (D4BMBackground.jet r y).metric 2 3 = 0 := rfl

/-- Vector–vector quadratic Einstein source, component `(0, 0)`. -/
theorem vectorJet_quadratic_einstein_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 0 =
      B ^ (2 : ℕ) * ((-2 : ℂ) * s ^ (2 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ)) * A * Q * y ^ (3 : ℕ) + B ^ (2 : ℕ) * ((-2 : ℂ) * s ^ (2 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ)) * A * R * y ^ (3 : ℕ) + B ^ (2 : ℕ) * ((-5 / 2 : ℂ) * s ^ (2 : ℕ) + (5 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-9 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) + (-3 : ℂ) * s ^ (3 : ℕ) + (4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (3 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1)) * A ^ (2 : ℕ) * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((4 : ℂ) * s ^ (2 : ℕ) + (-4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ)) * C * P * y ^ (3 : ℕ) + B ^ (2 : ℕ) * ((-5 / 2 : ℂ) * s ^ (2 : ℕ) + (5 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-9 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) + (-3 : ℂ) * s ^ (3 : ℕ) + (4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (3 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1)) * C ^ (2 : ℕ) * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-2 : ℂ) * s ^ (2 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ)) * P ^ (2 : ℕ) * y ^ (4 : ℕ) + B ^ (2 : ℕ) * ((-1 : ℂ) * s ^ (2 : ℕ) + (-1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ)) * Q * R * y ^ (4 : ℕ) + B ^ (2 : ℕ) * ((-1 / 2 : ℂ) * s ^ (2 : ℕ) + (3 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ)) * Q ^ (2 : ℕ) * y ^ (4 : ℕ) + B ^ (2 : ℕ) * ((-1 / 2 : ℂ) * s ^ (2 : ℕ) + (3 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ)) * R ^ (2 : ℕ) * y ^ (4 : ℕ) := by
  rw [vectorJet_quadratic_einstein_eq s r y B A C P Q R U W hr hy hf,
    vectorJet_quadratic_ricci_trace hr hy hf, vectorJet_quadratic_ricci_0_0 hr hy hf, D4BMBackground.jet_metric_0_0]
  field_simp
  ring

/-- Vector–vector quadratic Einstein source, component `(0, 1)`. -/
theorem vectorJet_quadratic_einstein_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 1 =
      B ^ (2 : ℕ) * ((-2 : ℂ) * s ^ (2 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-6 : ℂ) * s ^ (3 : ℕ) + (10 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-4 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-2 : ℂ) * s ^ (4 : ℕ) + (2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * A ^ (2 : ℕ) * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-2 : ℂ) * s ^ (2 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-6 : ℂ) * s ^ (3 : ℕ) + (10 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-4 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-2 : ℂ) * s ^ (4 : ℕ) + (2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * C ^ (2 : ℕ) * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-2 : ℂ) * s ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * Q * R * y ^ (4 : ℕ) + B ^ (2 : ℕ) * ((1 : ℂ) * s ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * Q ^ (2 : ℕ) * y ^ (4 : ℕ) + B ^ (2 : ℕ) * ((1 : ℂ) * s ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * R ^ (2 : ℕ) * y ^ (4 : ℕ) := by
  rw [vectorJet_quadratic_einstein_eq s r y B A C P Q R U W hr hy hf,
    vectorJet_quadratic_ricci_trace hr hy hf, vectorJet_quadratic_ricci_0_1 hr hy hf, background_metric_0_1]
  field_simp
  ring

/-- Vector–vector quadratic Einstein source, component `(0, 2)`. -/
theorem vectorJet_quadratic_einstein_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 2 =
      B ^ (2 : ℕ) * ((-2 : ℂ) * s ^ (3 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * A * P * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((3 : ℂ) * s ^ (2 : ℕ) + (-3 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * C * Q * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-3 : ℂ) * s ^ (2 : ℕ) + (3 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-3 : ℂ) * s ^ (3 : ℕ) + (3 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * C * R * y ^ (2 : ℕ) := by
  rw [vectorJet_quadratic_einstein_eq s r y B A C P Q R U W hr hy hf,
    vectorJet_quadratic_ricci_trace hr hy hf, vectorJet_quadratic_ricci_0_2 hr hy hf, background_metric_0_2]
  field_simp
  ring

/-- Vector–vector quadratic Einstein source, component `(0, 3)`. -/
theorem vectorJet_quadratic_einstein_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 3 =
      B ^ (2 : ℕ) * ((-3 : ℂ) * s ^ (2 : ℕ) + (3 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-3 : ℂ) * s ^ (3 : ℕ) + (3 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * A * Q * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((3 : ℂ) * s ^ (2 : ℕ) + (-3 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * A * R * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-2 : ℂ) * s ^ (3 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * A ^ (2 : ℕ) * y + B ^ (2 : ℕ) * ((2 : ℂ) * s ^ (3 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * C * P * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-2 : ℂ) * s ^ (3 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * C ^ (2 : ℕ) * y := by
  rw [vectorJet_quadratic_einstein_eq s r y B A C P Q R U W hr hy hf,
    vectorJet_quadratic_ricci_trace hr hy hf, vectorJet_quadratic_ricci_0_3 hr hy hf, background_metric_0_3]
  field_simp
  ring

/-- Vector–vector quadratic Einstein source, component `(1, 1)`. -/
theorem vectorJet_quadratic_einstein_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 1 1 =
      B ^ (2 : ℕ) * ((2 : ℂ) * s ^ (2 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * A * Q * y ^ (3 : ℕ) + B ^ (2 : ℕ) * ((2 : ℂ) * s ^ (2 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * A * R * y ^ (3 : ℕ) + B ^ (2 : ℕ) * ((-15 / 2 : ℂ) * s ^ (2 : ℕ) + (19 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-35 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (6 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) + (-7 : ℂ) * s ^ (3 : ℕ) + (12 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-5 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-3 / 2 : ℂ) * s ^ (4 : ℕ) + (1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ)) * A ^ (2 : ℕ) * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-4 : ℂ) * s ^ (2 : ℕ) + (4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * C * P * y ^ (3 : ℕ) + B ^ (2 : ℕ) * ((-15 / 2 : ℂ) * s ^ (2 : ℕ) + (19 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-35 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (6 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) + (-7 : ℂ) * s ^ (3 : ℕ) + (12 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-5 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-3 / 2 : ℂ) * s ^ (4 : ℕ) + (1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ)) * C ^ (2 : ℕ) * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((2 : ℂ) * s ^ (2 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * P ^ (2 : ℕ) * y ^ (4 : ℕ) + B ^ (2 : ℕ) * ((-1 : ℂ) * s ^ (2 : ℕ) + (-1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * Q * R * y ^ (4 : ℕ) + B ^ (2 : ℕ) * ((3 / 2 : ℂ) * s ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * Q ^ (2 : ℕ) * y ^ (4 : ℕ) + B ^ (2 : ℕ) * ((3 / 2 : ℂ) * s ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * R ^ (2 : ℕ) * y ^ (4 : ℕ) := by
  rw [vectorJet_quadratic_einstein_eq s r y B A C P Q R U W hr hy hf,
    vectorJet_quadratic_ricci_trace hr hy hf, vectorJet_quadratic_ricci_1_1 hr hy hf, D4BMBackground.jet_metric_1_1]
  field_simp
  ring

/-- Vector–vector quadratic Einstein source, component `(1, 2)`. -/
theorem vectorJet_quadratic_einstein_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 1 2 =
      B ^ (2 : ℕ) * ((-4 : ℂ) * s ^ (2 : ℕ) + (8 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-4 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * A * P * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((3 : ℂ) * s ^ (2 : ℕ) + (-3 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * C * Q * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-7 : ℂ) * s ^ (2 : ℕ) + (11 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-4 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-3 : ℂ) * s ^ (3 : ℕ) + (3 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * C * R * y ^ (2 : ℕ) := by
  rw [vectorJet_quadratic_einstein_eq s r y B A C P Q R U W hr hy hf,
    vectorJet_quadratic_ricci_trace hr hy hf, vectorJet_quadratic_ricci_1_2 hr hy hf, background_metric_1_2]
  field_simp
  ring

/-- Vector–vector quadratic Einstein source, component `(1, 3)`. -/
theorem vectorJet_quadratic_einstein_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 1 3 =
      B ^ (2 : ℕ) * ((-7 : ℂ) * s ^ (2 : ℕ) + (11 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-4 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-3 : ℂ) * s ^ (3 : ℕ) + (3 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * A * Q * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((3 : ℂ) * s ^ (2 : ℕ) + (-3 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * A * R * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-4 : ℂ) * s ^ (2 : ℕ) + (8 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-4 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * A ^ (2 : ℕ) * y + B ^ (2 : ℕ) * ((4 : ℂ) * s ^ (2 : ℕ) + (-8 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (4 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * C * P * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-4 : ℂ) * s ^ (2 : ℕ) + (8 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-4 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * C ^ (2 : ℕ) * y := by
  rw [vectorJet_quadratic_einstein_eq s r y B A C P Q R U W hr hy hf,
    vectorJet_quadratic_ricci_trace hr hy hf, vectorJet_quadratic_ricci_1_3 hr hy hf, background_metric_1_3]
  field_simp
  ring

/-- Vector–vector quadratic Einstein source, component `(2, 2)`. -/
theorem vectorJet_quadratic_einstein_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 2 2 =
      B ^ (2 : ℕ) * ((1 / 2 : ℂ) * s ^ (2 : ℕ) + (-3 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (9 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (1 / 2 : ℂ) * s ^ (4 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * A ^ (2 : ℕ) + B ^ (2 : ℕ) * ((23 / 2 : ℂ) * s ^ (2 : ℕ) + (-25 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (31 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) + (13 : ℂ) * s ^ (3 : ℕ) + (-26 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (13 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (7 / 2 : ℂ) * s ^ (4 : ℕ) + (-7 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (7 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * C ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-1 : ℂ) * s ^ (2 : ℕ) + (1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * Q * R * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((1 / 2 : ℂ) * s ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * Q ^ (2 : ℕ) * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((1 / 2 : ℂ) * s ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * R ^ (2 : ℕ) * y ^ (2 : ℕ) := by
  rw [vectorJet_quadratic_einstein_eq s r y B A C P Q R U W hr hy hf,
    vectorJet_quadratic_ricci_trace hr hy hf, vectorJet_quadratic_ricci_2_2 hr hy hf, D4BMBackground.jet_metric_2_2]
  field_simp
  ring

/-- Vector–vector quadratic Einstein source, component `(2, 3)`. -/
theorem vectorJet_quadratic_einstein_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 2 3 =
      B ^ (2 : ℕ) * ((-11 : ℂ) * s ^ (2 : ℕ) + (22 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-11 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-12 : ℂ) * s ^ (3 : ℕ) + (24 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-12 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-3 : ℂ) * s ^ (4 : ℕ) + (6 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-3 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * A * C := by
  rw [vectorJet_quadratic_einstein_eq s r y B A C P Q R U W hr hy hf,
    vectorJet_quadratic_ricci_trace hr hy hf, vectorJet_quadratic_ricci_2_3 hr hy hf, background_metric_2_3]
  field_simp
  ring

/-- Vector–vector quadratic Einstein source, component `(3, 3)`. -/
theorem vectorJet_quadratic_einstein_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 3 3 =
      B ^ (2 : ℕ) * ((23 / 2 : ℂ) * s ^ (2 : ℕ) + (-25 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (31 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) + (13 : ℂ) * s ^ (3 : ℕ) + (-26 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (13 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (7 / 2 : ℂ) * s ^ (4 : ℕ) + (-7 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (7 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * A ^ (2 : ℕ) + B ^ (2 : ℕ) * ((1 / 2 : ℂ) * s ^ (2 : ℕ) + (-3 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (9 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (1 / 2 : ℂ) * s ^ (4 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * C ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-1 : ℂ) * s ^ (2 : ℕ) + (1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * Q * R * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((1 / 2 : ℂ) * s ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * Q ^ (2 : ℕ) * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((1 / 2 : ℂ) * s ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * R ^ (2 : ℕ) * y ^ (2 : ℕ) := by
  rw [vectorJet_quadratic_einstein_eq s r y B A C P Q R U W hr hy hf,
    vectorJet_quadratic_ricci_trace hr hy hf, vectorJet_quadratic_ricci_3_3 hr hy hf, D4BMBackground.jet_metric_3_3]
  field_simp
  ring

end
end RHTower.D4BMVectorLinearEquation
