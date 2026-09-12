import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarScalarQuadraticRicci

/-!
# The scalar–scalar quadratic Einstein source of the fundamental Birmingham–Mokhtari scalar jet

All ten components of the quadratic Einstein variation `Quadratic.einstein J K` of the fundamental
scalar metric jet over the Birmingham–Mokhtari background, in closed form. The Einstein coefficient
is the quadratic Ricci variation minus half the background metric times its background trace
(`scalarJet_quadratic_einstein_eq`), and every Ricci component is a closed form from the assembly
module. The trace of the quadratic Ricci variation, `scalarJet_quadratic_ricci_trace`, is recorded
on its own. This is the complete scalar–scalar `++` quadratic source tensor `B(h_S, h_S)` of
route HB, with no heartbeat limit raised.
-/

set_option linter.unusedSimpArgs false

namespace RHTower.D4BMBackground
open GaloisForLFunctions.HTGeometry
variable (r y : ℂ)

theorem jet_metric_0_1 : (jet r y).metric 0 1 = 0 := rfl
theorem jet_metric_0_2 : (jet r y).metric 0 2 = 0 := rfl
theorem jet_metric_0_3 : (jet r y).metric 0 3 = 0 := rfl
theorem jet_metric_1_0 : (jet r y).metric 1 0 = 0 := rfl
theorem jet_metric_1_2 : (jet r y).metric 1 2 = 0 := rfl
theorem jet_metric_1_3 : (jet r y).metric 1 3 = 0 := rfl
theorem jet_metric_2_0 : (jet r y).metric 2 0 = 0 := rfl
theorem jet_metric_2_1 : (jet r y).metric 2 1 = 0 := rfl
theorem jet_metric_2_3 : (jet r y).metric 2 3 = 0 := rfl
theorem jet_metric_3_0 : (jet r y).metric 3 0 = 0 := rfl
theorem jet_metric_3_1 : (jet r y).metric 3 1 = 0 := rfl
theorem jet_metric_3_2 : (jet r y).metric 3 2 = 0 := rfl

end RHTower.D4BMBackground

namespace RHTower.D4BMScalarLinearEquation
open GaloisForLFunctions.HTGeometry CoordinateMetricTwoJet
noncomputable section
variable {s r y B S Sx Sy Sxx Sxy : ℂ}

/-- Background trace of the scalar–scalar quadratic Ricci variation. -/
theorem scalarJet_quadratic_ricci_trace (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    (∑ u, (((D4BMBackground.jet r y)).metric u u)⁻¹ * Quadratic.ricci (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) u u) =
      B ^ 2 * (((2 : ℂ) * r ^ 4 + (2 : ℂ) * s * r ^ 2 + (5 / 4 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 2 * r ^ 2 + (5 / 2 : ℂ) * s ^ 3 + (5 / 4 : ℂ) * s ^ 4) / (r ^ 6) * Sy ^ 2 * y ^ 2 +
        ((2 : ℂ) * r ^ 4 + (2 : ℂ) * s * r ^ 2 + (5 / 4 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 2 * r ^ 2 + (5 / 2 : ℂ) * s ^ 3 + (5 / 4 : ℂ) * s ^ 4) / (r ^ 6) * Sx ^ 2 * y ^ 2 +
        ((4 : ℂ) * r ^ 4 + (4 : ℂ) * s * r ^ 2 + (12 : ℂ) * s * r ^ 4 + (-5 : ℂ) * s ^ 2 + (7 : ℂ) * s ^ 2 * r ^ 2 + (-5 : ℂ) * s ^ 2 * r ^ 4 + (-15 : ℂ) * s ^ 3 + (4 : ℂ) * s ^ 3 * r ^ 2 + (-65 / 4 : ℂ) * s ^ 4 + (-3 : ℂ) * s ^ 4 * r ^ 2 + (-15 / 2 : ℂ) * s ^ 5 + (-5 / 4 : ℂ) * s ^ 6) / (r ^ 6) * S ^ 2) := by
  simp only [Fin.sum_univ_four, scalarJet_quadratic_ricci_0_0 hr hy hf, scalarJet_quadratic_ricci_0_1 hr hy hf, scalarJet_quadratic_ricci_0_2 hr hy hf, scalarJet_quadratic_ricci_0_3 hr hy hf, scalarJet_quadratic_ricci_1_1 hr hy hf, scalarJet_quadratic_ricci_1_2 hr hy hf, scalarJet_quadratic_ricci_1_3 hr hy hf, scalarJet_quadratic_ricci_2_2 hr hy hf, scalarJet_quadratic_ricci_2_3 hr hy hf, scalarJet_quadratic_ricci_3_3 hr hy hf, D4BMBackground.jet_metric_0_0, D4BMBackground.jet_metric_0_1, D4BMBackground.jet_metric_0_2, D4BMBackground.jet_metric_0_3, D4BMBackground.jet_metric_1_0, D4BMBackground.jet_metric_1_1, D4BMBackground.jet_metric_1_2, D4BMBackground.jet_metric_1_3, D4BMBackground.jet_metric_2_0, D4BMBackground.jet_metric_2_1, D4BMBackground.jet_metric_2_2, D4BMBackground.jet_metric_2_3, D4BMBackground.jet_metric_3_0, D4BMBackground.jet_metric_3_1, D4BMBackground.jet_metric_3_2, D4BMBackground.jet_metric_3_3]
  field_simp
  ring

/-- Scalar–scalar quadratic Einstein source, component `(0, 0)`. -/
theorem scalarJet_quadratic_einstein_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 =
      B ^ 2 * (((-1 : ℂ) * r ^ 4 + (1 : ℂ) * r ^ 6 + (-1 : ℂ) * s * r ^ 2 + (1 : ℂ) * s * r ^ 4 + (-3 / 8 : ℂ) * s ^ 2 + (-1 / 8 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 2 * r ^ 4 + (-3 / 4 : ℂ) * s ^ 3 + (3 / 4 : ℂ) * s ^ 3 * r ^ 2 + (-3 / 8 : ℂ) * s ^ 4 + (3 / 8 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 6) * Sy ^ 2 * y ^ 2 +
        ((-1 : ℂ) * r ^ 4 + (1 : ℂ) * r ^ 6 + (-1 : ℂ) * s * r ^ 2 + (1 : ℂ) * s * r ^ 4 + (-3 / 8 : ℂ) * s ^ 2 + (-1 / 8 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 2 * r ^ 4 + (-3 / 4 : ℂ) * s ^ 3 + (3 / 4 : ℂ) * s ^ 3 * r ^ 2 + (-3 / 8 : ℂ) * s ^ 4 + (3 / 8 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 6) * Sx ^ 2 * y ^ 2 +
        ((-2 : ℂ) * r ^ 4 + (2 : ℂ) * r ^ 6 + (-3 : ℂ) * s * r ^ 2 + (-3 : ℂ) * s * r ^ 4 + (6 : ℂ) * s * r ^ 6 + (3 / 2 : ℂ) * s ^ 2 + (-11 : ℂ) * s ^ 2 * r ^ 2 + (13 : ℂ) * s ^ 2 * r ^ 4 + (1 / 2 : ℂ) * s ^ 2 * r ^ 6 + (9 / 2 : ℂ) * s ^ 3 + (-14 : ℂ) * s ^ 3 * r ^ 2 + (3 : ℂ) * s ^ 3 * r ^ 4 + (39 / 8 : ℂ) * s ^ 4 + (-45 / 8 : ℂ) * s ^ 4 * r ^ 2 + (3 / 2 : ℂ) * s ^ 4 * r ^ 4 + (9 / 4 : ℂ) * s ^ 5 + (-5 / 4 : ℂ) * s ^ 5 * r ^ 2 + (3 / 8 : ℂ) * s ^ 6 + (3 / 8 : ℂ) * s ^ 6 * r ^ 2) / (r ^ 6) * S ^ 2) := by
  rw [scalarJet_quadratic_einstein_eq s r y B S Sx Sy Sxx Sxy hr hy hf,
    scalarJet_quadratic_ricci_trace hr hy hf, scalarJet_quadratic_ricci_0_0 hr hy hf,
    D4BMBackground.jet_metric_0_0]
  field_simp
  ring

/-- Scalar–scalar quadratic Einstein source, component `(0, 1)`. -/
theorem scalarJet_quadratic_einstein_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 =
      B ^ 2 * (((-2 : ℂ) * s ^ 2 * r ^ 2 + (6 : ℂ) * s ^ 2 * r ^ 4 + (3 / 2 : ℂ) * s ^ 3 + (-7 : ℂ) * s ^ 3 * r ^ 2 + (-1 : ℂ) * s ^ 3 * r ^ 4 + (15 / 4 : ℂ) * s ^ 4 + (-3 : ℂ) * s ^ 4 * r ^ 2 + (3 : ℂ) * s ^ 5 + (-2 : ℂ) * s ^ 5 * r ^ 2 + (3 / 4 : ℂ) * s ^ 6) / (r ^ 5 * (r ^ 2 - 1)) * S ^ 2) := by
  rw [scalarJet_quadratic_einstein_eq s r y B S Sx Sy Sxx Sxy hr hy hf,
    scalarJet_quadratic_ricci_trace hr hy hf, scalarJet_quadratic_ricci_0_1 hr hy hf,
    D4BMBackground.jet_metric_0_1]
  field_simp
  ring

/-- Scalar–scalar quadratic Einstein source, component `(0, 2)`. -/
theorem scalarJet_quadratic_einstein_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2 =
      B ^ 2 * (((2 : ℂ) * s * r ^ 4 + (2 : ℂ) * s ^ 2 * r ^ 2 + (3 / 4 : ℂ) * s ^ 3 + (1 : ℂ) * s ^ 3 * r ^ 2 + (3 / 2 : ℂ) * s ^ 4 + (3 / 4 : ℂ) * s ^ 5) / (r ^ 4) * S * Sx) := by
  rw [scalarJet_quadratic_einstein_eq s r y B S Sx Sy Sxx Sxy hr hy hf,
    scalarJet_quadratic_ricci_trace hr hy hf, scalarJet_quadratic_ricci_0_2 hr hy hf,
    D4BMBackground.jet_metric_0_2]
  field_simp
  ring

/-- Scalar–scalar quadratic Einstein source, component `(0, 3)`. -/
theorem scalarJet_quadratic_einstein_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 3 =
      B ^ 2 * (((2 : ℂ) * s * r ^ 4 + (2 : ℂ) * s ^ 2 * r ^ 2 + (3 / 4 : ℂ) * s ^ 3 + (1 : ℂ) * s ^ 3 * r ^ 2 + (3 / 2 : ℂ) * s ^ 4 + (3 / 4 : ℂ) * s ^ 5) / (r ^ 4) * S * Sy) := by
  rw [scalarJet_quadratic_einstein_eq s r y B S Sx Sy Sxx Sxy hr hy hf,
    scalarJet_quadratic_ricci_trace hr hy hf, scalarJet_quadratic_ricci_0_3 hr hy hf,
    D4BMBackground.jet_metric_0_3]
  field_simp
  ring

/-- Scalar–scalar quadratic Einstein source, component `(1, 1)`. -/
theorem scalarJet_quadratic_einstein_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 =
      B ^ 2 * (((-1 : ℂ) * r ^ 4 + (-1 : ℂ) * s * r ^ 2 + (-3 / 8 : ℂ) * s ^ 2 + (-1 / 2 : ℂ) * s ^ 2 * r ^ 2 + (-3 / 4 : ℂ) * s ^ 3 + (-3 / 8 : ℂ) * s ^ 4) / (r ^ 6 * (r ^ 2 - 1)) * Sy ^ 2 * y ^ 2 +
        ((-1 : ℂ) * r ^ 4 + (-1 : ℂ) * s * r ^ 2 + (-3 / 8 : ℂ) * s ^ 2 + (-1 / 2 : ℂ) * s ^ 2 * r ^ 2 + (-3 / 4 : ℂ) * s ^ 3 + (-3 / 8 : ℂ) * s ^ 4) / (r ^ 6 * (r ^ 2 - 1)) * Sx ^ 2 * y ^ 2 +
        ((2 : ℂ) * r ^ 4 + (-2 : ℂ) * r ^ 6 + (3 : ℂ) * s * r ^ 2 + (3 : ℂ) * s * r ^ 4 + (-6 : ℂ) * s * r ^ 6 + (5 / 2 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 2 * r ^ 4 + (5 / 2 : ℂ) * s ^ 2 * r ^ 6 + (7 : ℂ) * s ^ 3 + (-21 / 2 : ℂ) * s ^ 3 * r ^ 2 + (-3 : ℂ) * s ^ 3 * r ^ 4 + (55 / 8 : ℂ) * s ^ 4 + (-77 / 8 : ℂ) * s ^ 4 * r ^ 2 + (7 / 2 : ℂ) * s ^ 4 * r ^ 4 + (11 / 4 : ℂ) * s ^ 5 + (-7 / 4 : ℂ) * s ^ 5 * r ^ 2 + (3 / 8 : ℂ) * s ^ 6 + (3 / 8 : ℂ) * s ^ 6 * r ^ 2) / (r ^ 6 * (r ^ 2 - 1) ^ 2) * S ^ 2) := by
  rw [scalarJet_quadratic_einstein_eq s r y B S Sx Sy Sxx Sxy hr hy hf,
    scalarJet_quadratic_ricci_trace hr hy hf, scalarJet_quadratic_ricci_1_1 hr hy hf,
    D4BMBackground.jet_metric_1_1]
  field_simp
  ring

/-- Scalar–scalar quadratic Einstein source, component `(1, 2)`. -/
theorem scalarJet_quadratic_einstein_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2 =
      B ^ 2 * (((2 : ℂ) * s * r ^ 2 + (2 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 2 * r ^ 4 + (19 / 4 : ℂ) * s ^ 3 + (-3 : ℂ) * s ^ 3 * r ^ 2 + (7 / 2 : ℂ) * s ^ 4 + (-2 : ℂ) * s ^ 4 * r ^ 2 + (3 / 4 : ℂ) * s ^ 5) / (r ^ 5 * (r ^ 2 - 1)) * S * Sx) := by
  rw [scalarJet_quadratic_einstein_eq s r y B S Sx Sy Sxx Sxy hr hy hf,
    scalarJet_quadratic_ricci_trace hr hy hf, scalarJet_quadratic_ricci_1_2 hr hy hf,
    D4BMBackground.jet_metric_1_2]
  field_simp
  ring

/-- Scalar–scalar quadratic Einstein source, component `(1, 3)`. -/
theorem scalarJet_quadratic_einstein_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 3 =
      B ^ 2 * (((2 : ℂ) * s * r ^ 2 + (2 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 2 * r ^ 4 + (19 / 4 : ℂ) * s ^ 3 + (-3 : ℂ) * s ^ 3 * r ^ 2 + (7 / 2 : ℂ) * s ^ 4 + (-2 : ℂ) * s ^ 4 * r ^ 2 + (3 / 4 : ℂ) * s ^ 5) / (r ^ 5 * (r ^ 2 - 1)) * S * Sy) := by
  rw [scalarJet_quadratic_einstein_eq s r y B S Sx Sy Sxx Sxy hr hy hf,
    scalarJet_quadratic_ricci_trace hr hy hf, scalarJet_quadratic_ricci_1_3 hr hy hf,
    D4BMBackground.jet_metric_1_3]
  field_simp
  ring

/-- Scalar–scalar quadratic Einstein source, component `(2, 2)`. -/
theorem scalarJet_quadratic_einstein_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 2 =
      B ^ 2 * (((-3 / 8 : ℂ) * s ^ 2 + (3 / 2 : ℂ) * s ^ 2 * r ^ 2 + (-3 / 4 : ℂ) * s ^ 3 + (-3 / 8 : ℂ) * s ^ 4) / (r ^ 4) * Sy ^ 2 +
        ((-1 / 8 : ℂ) * s ^ 2 + (1 / 2 : ℂ) * s ^ 2 * r ^ 2 + (-1 / 4 : ℂ) * s ^ 3 + (-1 / 8 : ℂ) * s ^ 4) / (r ^ 4) * Sx ^ 2 +
        ((1 / 2 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 3 + (1 / 2 : ℂ) * s ^ 4) / (r ^ 4) * S * Sxx +
        ((-1 / 2 : ℂ) * s ^ 2 + (2 : ℂ) * s ^ 2 * r ^ 2 + (-1 : ℂ) * s ^ 3 + (-1 / 2 : ℂ) * s ^ 4) / (r ^ 4) * S * Sy * y⁻¹ +
        ((1 : ℂ) * s * r ^ 2 + (5 / 2 : ℂ) * s ^ 2 + (7 / 2 : ℂ) * s ^ 2 * r ^ 2 + (3 / 2 : ℂ) * s ^ 2 * r ^ 4 + (7 : ℂ) * s ^ 3 + (4 : ℂ) * s ^ 3 * r ^ 2 + (55 / 8 : ℂ) * s ^ 4 + (3 / 2 : ℂ) * s ^ 4 * r ^ 2 + (11 / 4 : ℂ) * s ^ 5 + (3 / 8 : ℂ) * s ^ 6) / (r ^ 4) * S ^ 2 * y⁻¹ ^ 2) := by
  rw [scalarJet_quadratic_einstein_eq s r y B S Sx Sy Sxx Sxy hr hy hf,
    scalarJet_quadratic_ricci_trace hr hy hf, scalarJet_quadratic_ricci_2_2 hr hy hf,
    D4BMBackground.jet_metric_2_2]
  field_simp
  ring

/-- Scalar–scalar quadratic Einstein source, component `(2, 3)`. -/
theorem scalarJet_quadratic_einstein_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 3 =
      B ^ 2 * (((1 / 4 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 3 + (1 / 4 : ℂ) * s ^ 4) / (r ^ 4) * Sx * Sy +
        ((1 / 2 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 3 + (1 / 2 : ℂ) * s ^ 4) / (r ^ 4) * S * Sxy +
        ((1 / 2 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 3 + (1 / 2 : ℂ) * s ^ 4) / (r ^ 4) * S * Sx * y⁻¹) := by
  rw [scalarJet_quadratic_einstein_eq s r y B S Sx Sy Sxx Sxy hr hy hf,
    scalarJet_quadratic_ricci_trace hr hy hf, scalarJet_quadratic_ricci_2_3 hr hy hf,
    D4BMBackground.jet_metric_2_3]
  field_simp
  ring

/-- Scalar–scalar quadratic Einstein source, component `(3, 3)`. -/
theorem scalarJet_quadratic_einstein_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 3 =
      B ^ 2 * (((-1 / 8 : ℂ) * s ^ 2 + (1 / 2 : ℂ) * s ^ 2 * r ^ 2 + (-1 / 4 : ℂ) * s ^ 3 + (-1 / 8 : ℂ) * s ^ 4) / (r ^ 4) * Sy ^ 2 +
        ((-3 / 8 : ℂ) * s ^ 2 + (3 / 2 : ℂ) * s ^ 2 * r ^ 2 + (-3 / 4 : ℂ) * s ^ 3 + (-3 / 8 : ℂ) * s ^ 4) / (r ^ 4) * Sx ^ 2 +
        ((-1 / 2 : ℂ) * s ^ 2 + (2 : ℂ) * s ^ 2 * r ^ 2 + (-1 : ℂ) * s ^ 3 + (-1 / 2 : ℂ) * s ^ 4) / (r ^ 4) * S * Sxx +
        ((1 / 2 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 3 + (1 / 2 : ℂ) * s ^ 4) / (r ^ 4) * S * Sy * y⁻¹ +
        ((1 : ℂ) * s * r ^ 2 + (7 / 2 : ℂ) * s ^ 2 + (-1 / 2 : ℂ) * s ^ 2 * r ^ 2 + (3 / 2 : ℂ) * s ^ 2 * r ^ 4 + (21 / 2 : ℂ) * s ^ 3 + (-2 : ℂ) * s ^ 3 * r ^ 2 + (91 / 8 : ℂ) * s ^ 4 + (-1 / 2 : ℂ) * s ^ 4 * r ^ 2 + (21 / 4 : ℂ) * s ^ 5 + (7 / 8 : ℂ) * s ^ 6) / (r ^ 4) * S ^ 2 * y⁻¹ ^ 2) := by
  rw [scalarJet_quadratic_einstein_eq s r y B S Sx Sy Sxx Sxy hr hy hf,
    scalarJet_quadratic_ricci_trace hr hy hf, scalarJet_quadratic_ricci_3_3 hr hy hf,
    D4BMBackground.jet_metric_3_3]
  field_simp
  ring

end
end RHTower.D4BMScalarLinearEquation
