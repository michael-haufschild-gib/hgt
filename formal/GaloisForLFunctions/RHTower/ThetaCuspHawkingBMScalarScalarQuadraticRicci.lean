import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarJetLinearConnectionTable
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarJetQuadraticConnectionTable
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarJetSpatial0ConnectionTable
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarJetSpatial1ConnectionTable
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarJetSpatial2ConnectionTable
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarJetSpatial3ConnectionTable

/-!
# The scalar–scalar quadratic Ricci variation of the fundamental Birmingham–Mokhtari scalar jet

Every component of the quadratic Ricci variation `Quadratic.ricci J K` of the fundamental scalar
metric jet `K = scalarJet s r y B S Sx Sy Sxx Sxy` over the Birmingham–Mokhtari background `J` is
evaluated in closed form: each of the four Riemann traces `Quadratic.curvature J K u i u j` is a
rational function of `(s, r)` times a quadratic monomial in the angular jet `(S, Sx, Sy, Sxx, Sxy)`
times a power of `y`, and the component is their sum. The proofs assemble the Christoffel variation
tables through the index-collapsed Riemann formula over a diagonal background; no summand is
expanded through the jet algebra and no heartbeat limit is raised. This is the scalar–scalar block
of the `++` quadratic source of route HB.
-/

set_option linter.unusedSimpArgs false

namespace RHTower.D4BMScalarLinearEquation
open GaloisForLFunctions.HTGeometry CoordinateMetricTwoJet
noncomputable section
variable {s r y B S Sx Sy Sxx Sxy : ℂ}

theorem scalarJet_quadratic_curvature_0_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 0 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  all_goals field_simp
  all_goals ring

theorem scalarJet_quadratic_curvature_1_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 1 0 =
      B ^ 2 * (((1 / 8 : ℂ) * s ^ 2 + (-5 / 8 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 2 * r ^ 4 + (1 / 4 : ℂ) * s ^ 3 + (-1 / 4 : ℂ) * s ^ 3 * r ^ 2 + (1 / 8 : ℂ) * s ^ 4 + (-1 / 8 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 6) * Sy ^ 2 * y ^ 2 +
        ((1 / 8 : ℂ) * s ^ 2 + (-5 / 8 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 2 * r ^ 4 + (1 / 4 : ℂ) * s ^ 3 + (-1 / 4 : ℂ) * s ^ 3 * r ^ 2 + (1 / 8 : ℂ) * s ^ 4 + (-1 / 8 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 6) * Sx ^ 2 * y ^ 2 +
        ((3 / 2 : ℂ) * s ^ 2 + (-4 : ℂ) * s ^ 2 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 2 * r ^ 4 + (17 / 4 : ℂ) * s ^ 3 + (-21 / 4 : ℂ) * s ^ 3 * r ^ 2 + (-3 / 2 : ℂ) * s ^ 3 * r ^ 4 + (17 / 4 : ℂ) * s ^ 4 + (-3 / 4 : ℂ) * s ^ 4 * r ^ 2 + (-1 : ℂ) * s ^ 4 * r ^ 4 + (7 / 4 : ℂ) * s ^ 5 + (3 / 4 : ℂ) * s ^ 5 * r ^ 2 + (1 / 4 : ℂ) * s ^ 6 + (1 / 4 : ℂ) * s ^ 6 * r ^ 2) / (r ^ 6) * S ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_2_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 0 2 0 =
      B ^ 2 * (((1 / 4 : ℂ) * s * r ^ 2 + (-3 / 4 : ℂ) * s * r ^ 4 + (1 / 8 : ℂ) * s ^ 2 + (-1 / 8 : ℂ) * s ^ 2 * r ^ 2 + (1 / 4 : ℂ) * s ^ 2 * r ^ 4 + (1 / 4 : ℂ) * s ^ 3 + (-1 / 4 : ℂ) * s ^ 3 * r ^ 2 + (1 / 8 : ℂ) * s ^ 4 + (1 / 8 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 6) * Sy ^ 2 * y ^ 2 +
        ((-1 / 4 : ℂ) * s + (3 / 4 : ℂ) * s * r ^ 2 + (-1 / 2 : ℂ) * s ^ 2 + (1 / 4 : ℂ) * s ^ 2 * r ^ 2 + (-1 / 4 : ℂ) * s ^ 4) / (r ^ 4) * Sx ^ 2 * y ^ 2 +
        ((-1 / 2 : ℂ) * s * r ^ 2 + (3 / 2 : ℂ) * s * r ^ 4 + (-1 / 4 : ℂ) * s ^ 2 + (1 / 4 : ℂ) * s ^ 2 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 2 * r ^ 4 + (-1 / 2 : ℂ) * s ^ 3 + (1 / 2 : ℂ) * s ^ 3 * r ^ 2 + (-1 / 4 : ℂ) * s ^ 4 + (-1 / 4 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 6) * S * Sxx * y ^ 2 +
        ((1 / 2 : ℂ) * s * r ^ 2 + (-3 / 2 : ℂ) * s * r ^ 4 + (1 / 4 : ℂ) * s ^ 2 + (-1 / 4 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 2 * r ^ 4 + (1 / 2 : ℂ) * s ^ 3 + (-1 / 2 : ℂ) * s ^ 3 * r ^ 2 + (1 / 4 : ℂ) * s ^ 4 + (1 / 4 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 6) * S * Sy * y ^ 1 +
        ((-1 : ℂ) * s * r ^ 4 + (-1 : ℂ) * s ^ 2 + (2 : ℂ) * s ^ 2 * r ^ 4 + (3 / 2 : ℂ) * s ^ 2 * r ^ 6 + (-11 / 4 : ℂ) * s ^ 3 + (-1 / 4 : ℂ) * s ^ 3 * r ^ 2 + (5 / 4 : ℂ) * s ^ 3 * r ^ 4 + (-21 / 8 : ℂ) * s ^ 4 + (1 / 4 : ℂ) * s ^ 4 * r ^ 2 + (9 / 4 : ℂ) * s ^ 4 * r ^ 4 + (-1 : ℂ) * s ^ 5 + (1 : ℂ) * s ^ 5 * r ^ 2 + (-1 / 8 : ℂ) * s ^ 6 + (1 / 2 : ℂ) * s ^ 6 * r ^ 2) / (r ^ 6) * S ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_3_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 0 3 0 =
      B ^ 2 * (((-1 / 4 : ℂ) * s + (3 / 4 : ℂ) * s * r ^ 2 + (-1 / 2 : ℂ) * s ^ 2 + (1 / 4 : ℂ) * s ^ 2 * r ^ 2 + (-1 / 4 : ℂ) * s ^ 4) / (r ^ 4) * Sy ^ 2 * y ^ 2 +
        ((1 / 4 : ℂ) * s * r ^ 2 + (-3 / 4 : ℂ) * s * r ^ 4 + (1 / 8 : ℂ) * s ^ 2 + (-1 / 8 : ℂ) * s ^ 2 * r ^ 2 + (1 / 4 : ℂ) * s ^ 2 * r ^ 4 + (1 / 4 : ℂ) * s ^ 3 + (-1 / 4 : ℂ) * s ^ 3 * r ^ 2 + (1 / 8 : ℂ) * s ^ 4 + (1 / 8 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 6) * Sx ^ 2 * y ^ 2 +
        ((1 / 2 : ℂ) * s * r ^ 2 + (-3 / 2 : ℂ) * s * r ^ 4 + (1 / 4 : ℂ) * s ^ 2 + (-1 / 4 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 2 * r ^ 4 + (1 / 2 : ℂ) * s ^ 3 + (-1 / 2 : ℂ) * s ^ 3 * r ^ 2 + (1 / 4 : ℂ) * s ^ 4 + (1 / 4 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 6) * S * Sxx * y ^ 2 +
        ((-1 / 2 : ℂ) * s * r ^ 2 + (3 / 2 : ℂ) * s * r ^ 4 + (-1 / 4 : ℂ) * s ^ 2 + (1 / 4 : ℂ) * s ^ 2 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 2 * r ^ 4 + (-1 / 2 : ℂ) * s ^ 3 + (1 / 2 : ℂ) * s ^ 3 * r ^ 2 + (-1 / 4 : ℂ) * s ^ 4 + (-1 / 4 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 6) * S * Sy * y ^ 1 +
        ((-1 : ℂ) * s * r ^ 2 + (2 : ℂ) * s * r ^ 4 + (-3 / 2 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 2 * r ^ 2 + (11 / 2 : ℂ) * s ^ 2 * r ^ 4 + (3 / 2 : ℂ) * s ^ 2 * r ^ 6 + (-9 / 2 : ℂ) * s ^ 3 + (1 : ℂ) * s ^ 3 * r ^ 2 + (5 / 4 : ℂ) * s ^ 3 * r ^ 4 + (-39 / 8 : ℂ) * s ^ 4 + (3 / 2 : ℂ) * s ^ 4 * r ^ 2 + (7 / 4 : ℂ) * s ^ 4 * r ^ 4 + (-9 / 4 : ℂ) * s ^ 5 + (3 / 4 : ℂ) * s ^ 5 * r ^ 2 + (-3 / 8 : ℂ) * s ^ 6 + (1 / 4 : ℂ) * s ^ 6 * r ^ 2) / (r ^ 6) * S ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_0_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 0 1 =
      B ^ 2 * (((-3 : ℂ) * s ^ 2 * r ^ 2 + (3 : ℂ) * s ^ 3 + (-11 / 2 : ℂ) * s ^ 3 * r ^ 2 + (11 / 2 : ℂ) * s ^ 4 + (-3 : ℂ) * s ^ 4 * r ^ 2 + (3 : ℂ) * s ^ 5 + (-1 / 2 : ℂ) * s ^ 5 * r ^ 2 + (1 / 2 : ℂ) * s ^ 6) / (r ^ 5 * (r ^ 2 - 1)) * S ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_1_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 1 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  all_goals field_simp
  all_goals ring

theorem scalarJet_quadratic_curvature_2_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 0 2 1 =
      B ^ 2 * (((-1 / 2 : ℂ) * s * r ^ 4 + (1 / 4 : ℂ) * s ^ 2 * r ^ 2 + (1 / 4 : ℂ) * s ^ 3 + (-1 / 4 : ℂ) * s ^ 3 * r ^ 2 + (1 / 4 : ℂ) * s ^ 4) / (r ^ 5 * (r ^ 2 - 1)) * Sy ^ 2 * y ^ 2 +
        ((1 / 2 : ℂ) * s * r ^ 4 + (-1 / 4 : ℂ) * s ^ 2 * r ^ 2 + (-1 / 4 : ℂ) * s ^ 3 + (1 / 4 : ℂ) * s ^ 3 * r ^ 2 + (-1 / 4 : ℂ) * s ^ 4) / (r ^ 5 * (r ^ 2 - 1)) * Sx ^ 2 * y ^ 2 +
        ((1 : ℂ) * s * r ^ 4 + (-1 / 2 : ℂ) * s ^ 2 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 3 + (1 / 2 : ℂ) * s ^ 3 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 4) / (r ^ 5 * (r ^ 2 - 1)) * S * Sxx * y ^ 2 +
        ((-1 : ℂ) * s * r ^ 4 + (1 / 2 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 3 + (-1 / 2 : ℂ) * s ^ 3 * r ^ 2 + (1 / 2 : ℂ) * s ^ 4) / (r ^ 5 * (r ^ 2 - 1)) * S * Sy * y ^ 1 +
        ((-1 : ℂ) * s * r ^ 4 + (1 : ℂ) * s ^ 2 * r ^ 2 + (3 / 2 : ℂ) * s ^ 2 * r ^ 4 + (-1 / 4 : ℂ) * s ^ 3 + (-1 / 2 : ℂ) * s ^ 3 * r ^ 2 + (-1 : ℂ) * s ^ 3 * r ^ 4 + (3 / 8 : ℂ) * s ^ 4 + (-1 / 2 : ℂ) * s ^ 4 * r ^ 2 + (1 : ℂ) * s ^ 5 + (-1 : ℂ) * s ^ 5 * r ^ 2 + (3 / 8 : ℂ) * s ^ 6) / (r ^ 5 * (r ^ 2 - 1)) * S ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_3_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 0 3 1 =
      B ^ 2 * (((1 / 2 : ℂ) * s * r ^ 4 + (-1 / 4 : ℂ) * s ^ 2 * r ^ 2 + (-1 / 4 : ℂ) * s ^ 3 + (1 / 4 : ℂ) * s ^ 3 * r ^ 2 + (-1 / 4 : ℂ) * s ^ 4) / (r ^ 5 * (r ^ 2 - 1)) * Sy ^ 2 * y ^ 2 +
        ((-1 / 2 : ℂ) * s * r ^ 4 + (1 / 4 : ℂ) * s ^ 2 * r ^ 2 + (1 / 4 : ℂ) * s ^ 3 + (-1 / 4 : ℂ) * s ^ 3 * r ^ 2 + (1 / 4 : ℂ) * s ^ 4) / (r ^ 5 * (r ^ 2 - 1)) * Sx ^ 2 * y ^ 2 +
        ((-1 : ℂ) * s * r ^ 4 + (1 / 2 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 3 + (-1 / 2 : ℂ) * s ^ 3 * r ^ 2 + (1 / 2 : ℂ) * s ^ 4) / (r ^ 5 * (r ^ 2 - 1)) * S * Sxx * y ^ 2 +
        ((1 : ℂ) * s * r ^ 4 + (-1 / 2 : ℂ) * s ^ 2 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 3 + (1 / 2 : ℂ) * s ^ 3 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 4) / (r ^ 5 * (r ^ 2 - 1)) * S * Sy * y ^ 1 +
        ((1 : ℂ) * s * r ^ 4 + (9 / 2 : ℂ) * s ^ 2 * r ^ 4 + (-5 / 4 : ℂ) * s ^ 3 + (-1 : ℂ) * s ^ 3 * r ^ 2 + (-17 / 8 : ℂ) * s ^ 4 + (1 / 2 : ℂ) * s ^ 4 * r ^ 2 + (-1 : ℂ) * s ^ 5 + (-1 / 2 : ℂ) * s ^ 5 * r ^ 2 + (-1 / 8 : ℂ) * s ^ 6) / (r ^ 5 * (r ^ 2 - 1)) * S ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_0_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 0 2 =
      B ^ 2 * (((3 / 2 : ℂ) * s ^ 2 * r ^ 2 + (-3 / 2 : ℂ) * s ^ 2 * r ^ 4 + (-3 / 2 : ℂ) * s ^ 3 + (7 / 2 : ℂ) * s ^ 3 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 3 * r ^ 4 + (-2 : ℂ) * s ^ 4 + (1 : ℂ) * s ^ 4 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 5) / (r ^ 4 * (r ^ 2 - 1)) * S * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_1_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 1 2 =
      B ^ 2 * (((-9 / 4 : ℂ) * s ^ 2 * r ^ 2 + (9 / 4 : ℂ) * s ^ 2 * r ^ 4 + (13 / 8 : ℂ) * s ^ 3 + (-23 / 8 : ℂ) * s ^ 3 * r ^ 2 + (-1 / 4 : ℂ) * s ^ 3 * r ^ 4 + (2 : ℂ) * s ^ 4 + (-1 : ℂ) * s ^ 4 * r ^ 2 + (3 / 8 : ℂ) * s ^ 5 + (1 / 8 : ℂ) * s ^ 5 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * S * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_2_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 0 2 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  all_goals field_simp
  all_goals ring

theorem scalarJet_quadratic_curvature_3_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 0 3 2 =
      B ^ 2 * (((2 : ℂ) * s * r ^ 4 + (5 / 4 : ℂ) * s ^ 2 * r ^ 2 + (7 / 8 : ℂ) * s ^ 3 + (7 / 4 : ℂ) * s ^ 3 * r ^ 2 + (3 / 2 : ℂ) * s ^ 4 + (5 / 8 : ℂ) * s ^ 5) / (r ^ 4) * S * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_0_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 0 3 =
      B ^ 2 * (((3 / 2 : ℂ) * s ^ 2 * r ^ 2 + (-3 / 2 : ℂ) * s ^ 2 * r ^ 4 + (-3 / 2 : ℂ) * s ^ 3 + (7 / 2 : ℂ) * s ^ 3 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 3 * r ^ 4 + (-2 : ℂ) * s ^ 4 + (1 : ℂ) * s ^ 4 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 5) / (r ^ 4 * (r ^ 2 - 1)) * S * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_1_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 1 3 =
      B ^ 2 * (((-9 / 4 : ℂ) * s ^ 2 * r ^ 2 + (9 / 4 : ℂ) * s ^ 2 * r ^ 4 + (13 / 8 : ℂ) * s ^ 3 + (-23 / 8 : ℂ) * s ^ 3 * r ^ 2 + (-1 / 4 : ℂ) * s ^ 3 * r ^ 4 + (2 : ℂ) * s ^ 4 + (-1 : ℂ) * s ^ 4 * r ^ 2 + (3 / 8 : ℂ) * s ^ 5 + (1 / 8 : ℂ) * s ^ 5 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * S * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_2_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 0 2 3 =
      B ^ 2 * (((2 : ℂ) * s * r ^ 4 + (5 / 4 : ℂ) * s ^ 2 * r ^ 2 + (7 / 8 : ℂ) * s ^ 3 + (7 / 4 : ℂ) * s ^ 3 * r ^ 2 + (3 / 2 : ℂ) * s ^ 4 + (5 / 8 : ℂ) * s ^ 5) / (r ^ 4) * S * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_3_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 0 3 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  all_goals field_simp
  all_goals ring

theorem scalarJet_quadratic_curvature_0_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 0 1 =
      B ^ 2 * (((1 / 8 : ℂ) * s ^ 2 + (-1 / 2 : ℂ) * s ^ 2 * r ^ 2 + (1 / 4 : ℂ) * s ^ 3 + (1 / 8 : ℂ) * s ^ 4) / (r ^ 6 * (r ^ 2 - 1)) * Sy ^ 2 * y ^ 2 +
        ((1 / 8 : ℂ) * s ^ 2 + (-1 / 2 : ℂ) * s ^ 2 * r ^ 2 + (1 / 4 : ℂ) * s ^ 3 + (1 / 8 : ℂ) * s ^ 4) / (r ^ 6 * (r ^ 2 - 1)) * Sx ^ 2 * y ^ 2 +
        ((3 / 2 : ℂ) * s ^ 2 + (-5 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 2 * r ^ 4 + (17 / 4 : ℂ) * s ^ 3 + (-33 / 4 : ℂ) * s ^ 3 * r ^ 2 + (3 / 2 : ℂ) * s ^ 3 * r ^ 4 + (17 / 4 : ℂ) * s ^ 4 + (-11 / 4 : ℂ) * s ^ 4 * r ^ 2 + (1 : ℂ) * s ^ 4 * r ^ 4 + (7 / 4 : ℂ) * s ^ 5 + (3 / 4 : ℂ) * s ^ 5 * r ^ 2 + (1 / 4 : ℂ) * s ^ 6 + (1 / 4 : ℂ) * s ^ 6 * r ^ 2) / (r ^ 6 * (r ^ 2 - 1) ^ 2) * S ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_1_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 1 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  all_goals field_simp
  all_goals ring

theorem scalarJet_quadratic_curvature_2_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 1 2 1 =
      B ^ 2 * (((1 / 4 : ℂ) * s * r ^ 2 + (-3 / 4 : ℂ) * s * r ^ 4 + (1 / 8 : ℂ) * s ^ 2 + (-1 / 8 : ℂ) * s ^ 2 * r ^ 2 + (1 / 4 : ℂ) * s ^ 2 * r ^ 4 + (1 / 4 : ℂ) * s ^ 3 + (-1 / 4 : ℂ) * s ^ 3 * r ^ 2 + (1 / 8 : ℂ) * s ^ 4 + (1 / 8 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 6 * (r ^ 2 - 1) ^ 2) * Sy ^ 2 * y ^ 2 +
        ((-1 / 4 : ℂ) * s * r ^ 2 + (3 / 4 : ℂ) * s * r ^ 4 + (-1 / 4 : ℂ) * s ^ 2 + (3 / 4 : ℂ) * s ^ 2 * r ^ 2 + (-3 / 4 : ℂ) * s ^ 2 * r ^ 4 + (-1 / 2 : ℂ) * s ^ 3 + (1 / 2 : ℂ) * s ^ 3 * r ^ 2 + (-1 / 4 : ℂ) * s ^ 4) / (r ^ 6 * (r ^ 2 - 1) ^ 2) * Sx ^ 2 * y ^ 2 +
        ((-1 / 2 : ℂ) * s * r ^ 2 + (3 / 2 : ℂ) * s * r ^ 4 + (-1 / 4 : ℂ) * s ^ 2 + (1 / 4 : ℂ) * s ^ 2 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 2 * r ^ 4 + (-1 / 2 : ℂ) * s ^ 3 + (1 / 2 : ℂ) * s ^ 3 * r ^ 2 + (-1 / 4 : ℂ) * s ^ 4 + (-1 / 4 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 6 * (r ^ 2 - 1) ^ 2) * S * Sxx * y ^ 2 +
        ((1 / 2 : ℂ) * s * r ^ 2 + (-3 / 2 : ℂ) * s * r ^ 4 + (1 / 4 : ℂ) * s ^ 2 + (-1 / 4 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 2 * r ^ 4 + (1 / 2 : ℂ) * s ^ 3 + (-1 / 2 : ℂ) * s ^ 3 * r ^ 2 + (1 / 4 : ℂ) * s ^ 4 + (1 / 4 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 6 * (r ^ 2 - 1) ^ 2) * S * Sy * y ^ 1 +
        ((1 : ℂ) * s * r ^ 2 + (-2 : ℂ) * s * r ^ 4 + (2 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 2 * r ^ 2 + (3 / 2 : ℂ) * s ^ 2 * r ^ 4 + (6 : ℂ) * s ^ 3 + (-13 / 2 : ℂ) * s ^ 3 * r ^ 2 + (-5 / 4 : ℂ) * s ^ 3 * r ^ 4 + (13 / 2 : ℂ) * s ^ 4 + (-59 / 8 : ℂ) * s ^ 4 * r ^ 2 + (3 / 4 : ℂ) * s ^ 4 * r ^ 4 + (3 : ℂ) * s ^ 5 + (-3 : ℂ) * s ^ 5 * r ^ 2 + (1 / 2 : ℂ) * s ^ 6 + (-1 / 8 : ℂ) * s ^ 6 * r ^ 2) / (r ^ 6 * (r ^ 2 - 1) ^ 2) * S ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_3_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 1 3 1 =
      B ^ 2 * (((-1 / 4 : ℂ) * s * r ^ 2 + (3 / 4 : ℂ) * s * r ^ 4 + (-1 / 4 : ℂ) * s ^ 2 + (3 / 4 : ℂ) * s ^ 2 * r ^ 2 + (-3 / 4 : ℂ) * s ^ 2 * r ^ 4 + (-1 / 2 : ℂ) * s ^ 3 + (1 / 2 : ℂ) * s ^ 3 * r ^ 2 + (-1 / 4 : ℂ) * s ^ 4) / (r ^ 6 * (r ^ 2 - 1) ^ 2) * Sy ^ 2 * y ^ 2 +
        ((1 / 4 : ℂ) * s * r ^ 2 + (-3 / 4 : ℂ) * s * r ^ 4 + (1 / 8 : ℂ) * s ^ 2 + (-1 / 8 : ℂ) * s ^ 2 * r ^ 2 + (1 / 4 : ℂ) * s ^ 2 * r ^ 4 + (1 / 4 : ℂ) * s ^ 3 + (-1 / 4 : ℂ) * s ^ 3 * r ^ 2 + (1 / 8 : ℂ) * s ^ 4 + (1 / 8 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 6 * (r ^ 2 - 1) ^ 2) * Sx ^ 2 * y ^ 2 +
        ((1 / 2 : ℂ) * s * r ^ 2 + (-3 / 2 : ℂ) * s * r ^ 4 + (1 / 4 : ℂ) * s ^ 2 + (-1 / 4 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 2 * r ^ 4 + (1 / 2 : ℂ) * s ^ 3 + (-1 / 2 : ℂ) * s ^ 3 * r ^ 2 + (1 / 4 : ℂ) * s ^ 4 + (1 / 4 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 6 * (r ^ 2 - 1) ^ 2) * S * Sxx * y ^ 2 +
        ((-1 / 2 : ℂ) * s * r ^ 2 + (3 / 2 : ℂ) * s * r ^ 4 + (-1 / 4 : ℂ) * s ^ 2 + (1 / 4 : ℂ) * s ^ 2 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 2 * r ^ 4 + (-1 / 2 : ℂ) * s ^ 3 + (1 / 2 : ℂ) * s ^ 3 * r ^ 2 + (-1 / 4 : ℂ) * s ^ 4 + (-1 / 4 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 6 * (r ^ 2 - 1) ^ 2) * S * Sy * y ^ 1 +
        ((1 : ℂ) * s * r ^ 4 + (3 / 2 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 2 * r ^ 2 + (5 : ℂ) * s ^ 2 * r ^ 4 + (17 / 4 : ℂ) * s ^ 3 + (-21 / 4 : ℂ) * s ^ 3 * r ^ 2 + (-5 / 4 : ℂ) * s ^ 3 * r ^ 4 + (17 / 4 : ℂ) * s ^ 4 + (-49 / 8 : ℂ) * s ^ 4 * r ^ 2 + (1 / 4 : ℂ) * s ^ 4 * r ^ 4 + (7 / 4 : ℂ) * s ^ 5 + (-13 / 4 : ℂ) * s ^ 5 * r ^ 2 + (1 / 4 : ℂ) * s ^ 6 + (-3 / 8 : ℂ) * s ^ 6 * r ^ 2) / (r ^ 6 * (r ^ 2 - 1) ^ 2) * S ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_0_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 0 2 =
      B ^ 2 * (((-1 / 2 : ℂ) * s ^ 2 + (11 / 4 : ℂ) * s ^ 2 * r ^ 2 + (-19 / 4 : ℂ) * s ^ 2 * r ^ 4 + (5 / 2 : ℂ) * s ^ 2 * r ^ 6 + (-9 / 8 : ℂ) * s ^ 3 + (25 / 8 : ℂ) * s ^ 3 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 3 * r ^ 4 + (-3 / 4 : ℂ) * s ^ 4 + (-1 / 4 : ℂ) * s ^ 4 * r ^ 4 + (-1 / 8 : ℂ) * s ^ 5 + (-3 / 8 : ℂ) * s ^ 5 * r ^ 2) / (r ^ 5 * (r ^ 2 - 1) ^ 2) * S * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_1_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 1 2 =
      B ^ 2 * (((-3 / 2 : ℂ) * s ^ 3 * r ^ 2 + (3 / 2 : ℂ) * s ^ 4 + (-1 / 2 : ℂ) * s ^ 4 * r ^ 2 + (1 / 2 : ℂ) * s ^ 5) / (r ^ 3 * (r ^ 2 - 1) ^ 2) * S * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_2_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 1 2 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  all_goals field_simp
  all_goals ring

theorem scalarJet_quadratic_curvature_3_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 1 3 2 =
      B ^ 2 * (((2 : ℂ) * s * r ^ 2 + (3 / 2 : ℂ) * s ^ 2 + (5 / 4 : ℂ) * s ^ 2 * r ^ 2 + (-3 / 2 : ℂ) * s ^ 2 * r ^ 4 + (29 / 8 : ℂ) * s ^ 3 + (-1 : ℂ) * s ^ 3 * r ^ 2 + (11 / 4 : ℂ) * s ^ 4 + (-5 / 4 : ℂ) * s ^ 4 * r ^ 2 + (5 / 8 : ℂ) * s ^ 5) / (r ^ 5 * (r ^ 2 - 1)) * S * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_0_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 0 3 =
      B ^ 2 * (((-1 / 2 : ℂ) * s ^ 2 + (11 / 4 : ℂ) * s ^ 2 * r ^ 2 + (-19 / 4 : ℂ) * s ^ 2 * r ^ 4 + (5 / 2 : ℂ) * s ^ 2 * r ^ 6 + (-9 / 8 : ℂ) * s ^ 3 + (25 / 8 : ℂ) * s ^ 3 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 3 * r ^ 4 + (-3 / 4 : ℂ) * s ^ 4 + (-1 / 4 : ℂ) * s ^ 4 * r ^ 4 + (-1 / 8 : ℂ) * s ^ 5 + (-3 / 8 : ℂ) * s ^ 5 * r ^ 2) / (r ^ 5 * (r ^ 2 - 1) ^ 2) * S * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_1_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 1 3 =
      B ^ 2 * (((-3 / 2 : ℂ) * s ^ 3 * r ^ 2 + (3 / 2 : ℂ) * s ^ 4 + (-1 / 2 : ℂ) * s ^ 4 * r ^ 2 + (1 / 2 : ℂ) * s ^ 5) / (r ^ 3 * (r ^ 2 - 1) ^ 2) * S * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_2_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 1 2 3 =
      B ^ 2 * (((2 : ℂ) * s * r ^ 2 + (3 / 2 : ℂ) * s ^ 2 + (5 / 4 : ℂ) * s ^ 2 * r ^ 2 + (-3 / 2 : ℂ) * s ^ 2 * r ^ 4 + (29 / 8 : ℂ) * s ^ 3 + (-1 : ℂ) * s ^ 3 * r ^ 2 + (11 / 4 : ℂ) * s ^ 4 + (-5 / 4 : ℂ) * s ^ 4 * r ^ 2 + (5 / 8 : ℂ) * s ^ 5) / (r ^ 5 * (r ^ 2 - 1)) * S * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_3_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 1 3 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  all_goals field_simp
  all_goals ring

theorem scalarJet_quadratic_curvature_0_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2 0 2 =
      B ^ 2 * (((-1 / 4 : ℂ) * s * r ^ 2 + (3 / 4 : ℂ) * s * r ^ 4 + (-1 / 8 : ℂ) * s ^ 2 + (1 / 8 : ℂ) * s ^ 2 * r ^ 2 + (-1 / 4 : ℂ) * s ^ 2 * r ^ 4 + (-1 / 4 : ℂ) * s ^ 3 + (1 / 4 : ℂ) * s ^ 3 * r ^ 2 + (-1 / 8 : ℂ) * s ^ 4 + (-1 / 8 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * Sy ^ 2 +
        ((1 / 4 : ℂ) * s + (-3 / 4 : ℂ) * s * r ^ 2 + (1 / 2 : ℂ) * s ^ 2 + (-1 / 4 : ℂ) * s ^ 2 * r ^ 2 + (1 / 4 : ℂ) * s ^ 4) / (r ^ 2 * (r ^ 2 - 1)) * Sx ^ 2 +
        ((1 / 4 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 3 + (1 / 4 : ℂ) * s ^ 4) / (r ^ 4) * S * Sxx +
        ((-1 / 4 : ℂ) * s ^ 2 + (1 : ℂ) * s ^ 2 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 3 + (-1 / 4 : ℂ) * s ^ 4) / (r ^ 4) * S * Sy * y⁻¹ +
        ((-1 : ℂ) * s * r ^ 2 + (1 : ℂ) * s * r ^ 4 + (-1 / 2 : ℂ) * s ^ 2 * r ^ 2 + (-3 / 2 : ℂ) * s ^ 2 * r ^ 6 + (1 / 4 : ℂ) * s ^ 3 + (5 / 4 : ℂ) * s ^ 3 * r ^ 2 + (7 / 4 : ℂ) * s ^ 3 * r ^ 4 + (5 / 8 : ℂ) * s ^ 4 + (1 / 4 : ℂ) * s ^ 4 * r ^ 2 + (-5 / 4 : ℂ) * s ^ 4 * r ^ 4 + (1 / 2 : ℂ) * s ^ 5 + (-1 : ℂ) * s ^ 5 * r ^ 2 + (1 / 8 : ℂ) * s ^ 6 + (-1 / 2 : ℂ) * s ^ 6 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * S ^ 2 * y⁻¹ ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_1_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2 1 2 =
      B ^ 2 * (((1 / 4 : ℂ) * s * r ^ 2 + (-3 / 4 : ℂ) * s * r ^ 4 + (1 / 8 : ℂ) * s ^ 2 + (-1 / 8 : ℂ) * s ^ 2 * r ^ 2 + (1 / 4 : ℂ) * s ^ 2 * r ^ 4 + (1 / 4 : ℂ) * s ^ 3 + (-1 / 4 : ℂ) * s ^ 3 * r ^ 2 + (1 / 8 : ℂ) * s ^ 4 + (1 / 8 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * Sy ^ 2 +
        ((-1 / 4 : ℂ) * s * r ^ 2 + (3 / 4 : ℂ) * s * r ^ 4 + (-1 / 4 : ℂ) * s ^ 2 + (3 / 4 : ℂ) * s ^ 2 * r ^ 2 + (-3 / 4 : ℂ) * s ^ 2 * r ^ 4 + (-1 / 2 : ℂ) * s ^ 3 + (1 / 2 : ℂ) * s ^ 3 * r ^ 2 + (-1 / 4 : ℂ) * s ^ 4) / (r ^ 4 * (r ^ 2 - 1)) * Sx ^ 2 +
        ((1 / 4 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 3 + (1 / 4 : ℂ) * s ^ 4) / (r ^ 4) * S * Sxx +
        ((-1 / 4 : ℂ) * s ^ 2 + (1 : ℂ) * s ^ 2 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 3 + (-1 / 4 : ℂ) * s ^ 4) / (r ^ 4) * S * Sy * y⁻¹ +
        ((-1 : ℂ) * s * r ^ 2 + (1 : ℂ) * s * r ^ 4 + (2 : ℂ) * s ^ 2 + (-7 : ℂ) * s ^ 2 * r ^ 2 + (7 : ℂ) * s ^ 2 * r ^ 4 + (6 : ℂ) * s ^ 3 + (-11 : ℂ) * s ^ 3 * r ^ 2 + (7 / 4 : ℂ) * s ^ 3 * r ^ 4 + (13 / 2 : ℂ) * s ^ 4 + (-59 / 8 : ℂ) * s ^ 4 * r ^ 2 + (5 / 4 : ℂ) * s ^ 4 * r ^ 4 + (3 : ℂ) * s ^ 5 + (-5 / 2 : ℂ) * s ^ 5 * r ^ 2 + (1 / 2 : ℂ) * s ^ 6 + (-1 / 8 : ℂ) * s ^ 6 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * S ^ 2 * y⁻¹ ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_2_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 2 2 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  all_goals field_simp
  all_goals ring

theorem scalarJet_quadratic_curvature_3_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 2 3 2 =
      B ^ 2 * (((1 : ℂ) * r ^ 4 + (1 : ℂ) * s * r ^ 2 + (1 / 4 : ℂ) * s ^ 2 + (1 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 3 + (1 / 4 : ℂ) * s ^ 4) / (r ^ 4) * Sy ^ 2 +
        ((1 : ℂ) * r ^ 4 + (1 : ℂ) * s * r ^ 2 + (1 / 4 : ℂ) * s ^ 2 + (1 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 3 + (1 / 4 : ℂ) * s ^ 4) / (r ^ 4) * Sx ^ 2 +
        ((2 : ℂ) * r ^ 4 + (1 : ℂ) * s * r ^ 2 + (6 : ℂ) * s * r ^ 4 + (2 : ℂ) * s ^ 2 + (3 / 2 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 2 * r ^ 4 + (23 / 4 : ℂ) * s ^ 3 + (5 / 2 : ℂ) * s ^ 3 * r ^ 2 + (47 / 8 : ℂ) * s ^ 4 + (5 / 2 : ℂ) * s ^ 5 + (3 / 8 : ℂ) * s ^ 6) / (r ^ 4) * S ^ 2 * y⁻¹ ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_0_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2 0 3 =
      B ^ 2 * (((1 / 2 : ℂ) * s * r ^ 2 + (-3 / 2 : ℂ) * s * r ^ 4 + (1 / 8 : ℂ) * s ^ 2 + (3 / 8 : ℂ) * s ^ 2 * r ^ 2 + (1 / 4 : ℂ) * s ^ 3 + (-1 / 4 : ℂ) * s ^ 3 * r ^ 2 + (1 / 8 : ℂ) * s ^ 4 + (3 / 8 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * Sx * Sy +
        ((1 / 4 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 3 + (1 / 4 : ℂ) * s ^ 4) / (r ^ 4) * S * Sxy +
        ((1 / 4 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 3 + (1 / 4 : ℂ) * s ^ 4) / (r ^ 4) * S * Sx * y⁻¹) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_1_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2 1 3 =
      B ^ 2 * (((-1 / 2 : ℂ) * s * r ^ 2 + (3 / 2 : ℂ) * s * r ^ 4 + (-3 / 8 : ℂ) * s ^ 2 + (7 / 8 : ℂ) * s ^ 2 * r ^ 2 + (-1 : ℂ) * s ^ 2 * r ^ 4 + (-3 / 4 : ℂ) * s ^ 3 + (3 / 4 : ℂ) * s ^ 3 * r ^ 2 + (-3 / 8 : ℂ) * s ^ 4 + (-1 / 8 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * Sx * Sy +
        ((1 / 4 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 3 + (1 / 4 : ℂ) * s ^ 4) / (r ^ 4) * S * Sxy +
        ((1 / 4 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 3 + (1 / 4 : ℂ) * s ^ 4) / (r ^ 4) * S * Sx * y⁻¹) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_2_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 2 2 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  all_goals field_simp
  all_goals ring

theorem scalarJet_quadratic_curvature_3_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 2 3 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  all_goals field_simp
  all_goals ring

theorem scalarJet_quadratic_curvature_0_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 3 0 3 =
      B ^ 2 * (((1 / 4 : ℂ) * s + (-3 / 4 : ℂ) * s * r ^ 2 + (1 / 2 : ℂ) * s ^ 2 + (-1 / 4 : ℂ) * s ^ 2 * r ^ 2 + (1 / 4 : ℂ) * s ^ 4) / (r ^ 2 * (r ^ 2 - 1)) * Sy ^ 2 +
        ((-1 / 4 : ℂ) * s * r ^ 2 + (3 / 4 : ℂ) * s * r ^ 4 + (-1 / 8 : ℂ) * s ^ 2 + (1 / 8 : ℂ) * s ^ 2 * r ^ 2 + (-1 / 4 : ℂ) * s ^ 2 * r ^ 4 + (-1 / 4 : ℂ) * s ^ 3 + (1 / 4 : ℂ) * s ^ 3 * r ^ 2 + (-1 / 8 : ℂ) * s ^ 4 + (-1 / 8 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * Sx ^ 2 +
        ((-1 / 4 : ℂ) * s ^ 2 + (1 : ℂ) * s ^ 2 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 3 + (-1 / 4 : ℂ) * s ^ 4) / (r ^ 4) * S * Sxx +
        ((1 / 4 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 3 + (1 / 4 : ℂ) * s ^ 4) / (r ^ 4) * S * Sy * y⁻¹ +
        ((-1 : ℂ) * s * r ^ 2 + (1 : ℂ) * s * r ^ 4 + (-1 / 2 : ℂ) * s ^ 2 + (2 : ℂ) * s ^ 2 * r ^ 2 + (-2 : ℂ) * s ^ 2 * r ^ 4 + (-3 / 2 : ℂ) * s ^ 2 * r ^ 6 + (-3 / 2 : ℂ) * s ^ 3 + (6 : ℂ) * s ^ 3 * r ^ 2 + (-5 / 4 : ℂ) * s ^ 3 * r ^ 4 + (-13 / 8 : ℂ) * s ^ 4 + (7 / 2 : ℂ) * s ^ 4 * r ^ 2 + (-9 / 4 : ℂ) * s ^ 4 * r ^ 4 + (-3 / 4 : ℂ) * s ^ 5 + (1 / 4 : ℂ) * s ^ 5 * r ^ 2 + (-1 / 8 : ℂ) * s ^ 6 + (-1 / 4 : ℂ) * s ^ 6 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * S ^ 2 * y⁻¹ ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_1_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 3 1 3 =
      B ^ 2 * (((-1 / 4 : ℂ) * s * r ^ 2 + (3 / 4 : ℂ) * s * r ^ 4 + (-1 / 4 : ℂ) * s ^ 2 + (3 / 4 : ℂ) * s ^ 2 * r ^ 2 + (-3 / 4 : ℂ) * s ^ 2 * r ^ 4 + (-1 / 2 : ℂ) * s ^ 3 + (1 / 2 : ℂ) * s ^ 3 * r ^ 2 + (-1 / 4 : ℂ) * s ^ 4) / (r ^ 4 * (r ^ 2 - 1)) * Sy ^ 2 +
        ((1 / 4 : ℂ) * s * r ^ 2 + (-3 / 4 : ℂ) * s * r ^ 4 + (1 / 8 : ℂ) * s ^ 2 + (-1 / 8 : ℂ) * s ^ 2 * r ^ 2 + (1 / 4 : ℂ) * s ^ 2 * r ^ 4 + (1 / 4 : ℂ) * s ^ 3 + (-1 / 4 : ℂ) * s ^ 3 * r ^ 2 + (1 / 8 : ℂ) * s ^ 4 + (1 / 8 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * Sx ^ 2 +
        ((-1 / 4 : ℂ) * s ^ 2 + (1 : ℂ) * s ^ 2 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 3 + (-1 / 4 : ℂ) * s ^ 4) / (r ^ 4) * S * Sxx +
        ((1 / 4 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 3 + (1 / 4 : ℂ) * s ^ 4) / (r ^ 4) * S * Sy * y⁻¹ +
        ((-1 : ℂ) * s * r ^ 2 + (1 : ℂ) * s * r ^ 4 + (3 / 2 : ℂ) * s ^ 2 + (-9 / 2 : ℂ) * s ^ 2 * r ^ 2 + (5 : ℂ) * s ^ 2 * r ^ 4 + (17 / 4 : ℂ) * s ^ 3 + (-25 / 4 : ℂ) * s ^ 3 * r ^ 2 + (-5 / 4 : ℂ) * s ^ 3 * r ^ 4 + (17 / 4 : ℂ) * s ^ 4 + (-33 / 8 : ℂ) * s ^ 4 * r ^ 2 + (1 / 4 : ℂ) * s ^ 4 * r ^ 4 + (7 / 4 : ℂ) * s ^ 5 + (-5 / 4 : ℂ) * s ^ 5 * r ^ 2 + (1 / 4 : ℂ) * s ^ 6 + (1 / 8 : ℂ) * s ^ 6 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * S ^ 2 * y⁻¹ ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_2_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 3 2 3 =
      B ^ 2 * (((1 : ℂ) * r ^ 4 + (1 : ℂ) * s * r ^ 2 + (1 / 4 : ℂ) * s ^ 2 + (1 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 3 + (1 / 4 : ℂ) * s ^ 4) / (r ^ 4) * Sy ^ 2 +
        ((1 : ℂ) * r ^ 4 + (1 : ℂ) * s * r ^ 2 + (1 / 4 : ℂ) * s ^ 2 + (1 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 3 + (1 / 4 : ℂ) * s ^ 4) / (r ^ 4) * Sx ^ 2 +
        ((2 : ℂ) * r ^ 4 + (1 : ℂ) * s * r ^ 2 + (6 : ℂ) * s * r ^ 4 + (2 : ℂ) * s ^ 2 + (3 / 2 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 2 * r ^ 4 + (23 / 4 : ℂ) * s ^ 3 + (5 / 2 : ℂ) * s ^ 3 * r ^ 2 + (47 / 8 : ℂ) * s ^ 4 + (5 / 2 : ℂ) * s ^ 5 + (3 / 8 : ℂ) * s ^ 6) / (r ^ 4) * S ^ 2 * y⁻¹ ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_3_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 3 3 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  all_goals field_simp
  all_goals ring

/-- Scalar–scalar quadratic Ricci variation, component `(0, 0)`. -/
theorem scalarJet_quadratic_ricci_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 =
      B ^ 2 * (((1 / 4 : ℂ) * s ^ 2 + (-5 / 4 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 2 * r ^ 4 + (1 / 2 : ℂ) * s ^ 3 + (-1 / 2 : ℂ) * s ^ 3 * r ^ 2 + (1 / 4 : ℂ) * s ^ 4 + (-1 / 4 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 6) * Sy ^ 2 * y ^ 2 +
        ((1 / 4 : ℂ) * s ^ 2 + (-5 / 4 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 2 * r ^ 4 + (1 / 2 : ℂ) * s ^ 3 + (-1 / 2 : ℂ) * s ^ 3 * r ^ 2 + (1 / 4 : ℂ) * s ^ 4 + (-1 / 4 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 6) * Sx ^ 2 * y ^ 2 +
        ((-1 : ℂ) * s * r ^ 2 + (1 : ℂ) * s * r ^ 4 + (-1 : ℂ) * s ^ 2 + (-5 : ℂ) * s ^ 2 * r ^ 2 + (7 : ℂ) * s ^ 2 * r ^ 4 + (3 : ℂ) * s ^ 2 * r ^ 6 + (-3 : ℂ) * s ^ 3 + (-9 / 2 : ℂ) * s ^ 3 * r ^ 2 + (1 : ℂ) * s ^ 3 * r ^ 4 + (-13 / 4 : ℂ) * s ^ 4 + (1 : ℂ) * s ^ 4 * r ^ 2 + (3 : ℂ) * s ^ 4 * r ^ 4 + (-3 / 2 : ℂ) * s ^ 5 + (5 / 2 : ℂ) * s ^ 5 * r ^ 2 + (-1 / 4 : ℂ) * s ^ 6 + (1 : ℂ) * s ^ 6 * r ^ 2) / (r ^ 6) * S ^ 2) := by
  simp only [Quadratic.ricci, Fin.sum_univ_four, scalarJet_quadratic_curvature_0_0_0 hr hy hf, scalarJet_quadratic_curvature_1_0_0 hr hy hf, scalarJet_quadratic_curvature_2_0_0 hr hy hf, scalarJet_quadratic_curvature_3_0_0 hr hy hf]
  field_simp
  ring

/-- Scalar–scalar quadratic Ricci variation, component `(0, 1)`. -/
theorem scalarJet_quadratic_ricci_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 =
      B ^ 2 * (((-2 : ℂ) * s ^ 2 * r ^ 2 + (6 : ℂ) * s ^ 2 * r ^ 4 + (3 / 2 : ℂ) * s ^ 3 + (-7 : ℂ) * s ^ 3 * r ^ 2 + (-1 : ℂ) * s ^ 3 * r ^ 4 + (15 / 4 : ℂ) * s ^ 4 + (-3 : ℂ) * s ^ 4 * r ^ 2 + (3 : ℂ) * s ^ 5 + (-2 : ℂ) * s ^ 5 * r ^ 2 + (3 / 4 : ℂ) * s ^ 6) / (r ^ 5 * (r ^ 2 - 1)) * S ^ 2) := by
  simp only [Quadratic.ricci, Fin.sum_univ_four, scalarJet_quadratic_curvature_0_0_1 hr hy hf, scalarJet_quadratic_curvature_1_0_1 hr hy hf, scalarJet_quadratic_curvature_2_0_1 hr hy hf, scalarJet_quadratic_curvature_3_0_1 hr hy hf]
  field_simp
  ring

/-- Scalar–scalar quadratic Ricci variation, component `(0, 2)`. -/
theorem scalarJet_quadratic_ricci_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2 =
      B ^ 2 * (((2 : ℂ) * s * r ^ 4 + (2 : ℂ) * s ^ 2 * r ^ 2 + (3 / 4 : ℂ) * s ^ 3 + (1 : ℂ) * s ^ 3 * r ^ 2 + (3 / 2 : ℂ) * s ^ 4 + (3 / 4 : ℂ) * s ^ 5) / (r ^ 4) * S * Sx) := by
  simp only [Quadratic.ricci, Fin.sum_univ_four, scalarJet_quadratic_curvature_0_0_2 hr hy hf, scalarJet_quadratic_curvature_1_0_2 hr hy hf, scalarJet_quadratic_curvature_2_0_2 hr hy hf, scalarJet_quadratic_curvature_3_0_2 hr hy hf]
  field_simp
  ring

/-- Scalar–scalar quadratic Ricci variation, component `(0, 3)`. -/
theorem scalarJet_quadratic_ricci_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 3 =
      B ^ 2 * (((2 : ℂ) * s * r ^ 4 + (2 : ℂ) * s ^ 2 * r ^ 2 + (3 / 4 : ℂ) * s ^ 3 + (1 : ℂ) * s ^ 3 * r ^ 2 + (3 / 2 : ℂ) * s ^ 4 + (3 / 4 : ℂ) * s ^ 5) / (r ^ 4) * S * Sy) := by
  simp only [Quadratic.ricci, Fin.sum_univ_four, scalarJet_quadratic_curvature_0_0_3 hr hy hf, scalarJet_quadratic_curvature_1_0_3 hr hy hf, scalarJet_quadratic_curvature_2_0_3 hr hy hf, scalarJet_quadratic_curvature_3_0_3 hr hy hf]
  field_simp
  ring

/-- Scalar–scalar quadratic Ricci variation, component `(1, 1)`. -/
theorem scalarJet_quadratic_ricci_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 =
      B ^ 2 * (((1 / 4 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 3 + (1 / 4 : ℂ) * s ^ 4) / (r ^ 6 * (r ^ 2 - 1)) * Sy ^ 2 * y ^ 2 +
        ((1 / 4 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 3 + (1 / 4 : ℂ) * s ^ 4) / (r ^ 6 * (r ^ 2 - 1)) * Sx ^ 2 * y ^ 2 +
        ((1 : ℂ) * s * r ^ 2 + (-1 : ℂ) * s * r ^ 4 + (5 : ℂ) * s ^ 2 + (-8 : ℂ) * s ^ 2 * r ^ 2 + (7 : ℂ) * s ^ 2 * r ^ 4 + (29 / 2 : ℂ) * s ^ 3 + (-20 : ℂ) * s ^ 3 * r ^ 2 + (-1 : ℂ) * s ^ 3 * r ^ 4 + (15 : ℂ) * s ^ 4 + (-65 / 4 : ℂ) * s ^ 4 * r ^ 2 + (2 : ℂ) * s ^ 4 * r ^ 4 + (13 / 2 : ℂ) * s ^ 5 + (-11 / 2 : ℂ) * s ^ 5 * r ^ 2 + (1 : ℂ) * s ^ 6 + (-1 / 4 : ℂ) * s ^ 6 * r ^ 2) / (r ^ 6 * (r ^ 2 - 1) ^ 2) * S ^ 2) := by
  simp only [Quadratic.ricci, Fin.sum_univ_four, scalarJet_quadratic_curvature_0_1_1 hr hy hf, scalarJet_quadratic_curvature_1_1_1 hr hy hf, scalarJet_quadratic_curvature_2_1_1 hr hy hf, scalarJet_quadratic_curvature_3_1_1 hr hy hf]
  field_simp
  ring

/-- Scalar–scalar quadratic Ricci variation, component `(1, 2)`. -/
theorem scalarJet_quadratic_ricci_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2 =
      B ^ 2 * (((2 : ℂ) * s * r ^ 2 + (2 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 2 * r ^ 4 + (19 / 4 : ℂ) * s ^ 3 + (-3 : ℂ) * s ^ 3 * r ^ 2 + (7 / 2 : ℂ) * s ^ 4 + (-2 : ℂ) * s ^ 4 * r ^ 2 + (3 / 4 : ℂ) * s ^ 5) / (r ^ 5 * (r ^ 2 - 1)) * S * Sx) := by
  simp only [Quadratic.ricci, Fin.sum_univ_four, scalarJet_quadratic_curvature_0_1_2 hr hy hf, scalarJet_quadratic_curvature_1_1_2 hr hy hf, scalarJet_quadratic_curvature_2_1_2 hr hy hf, scalarJet_quadratic_curvature_3_1_2 hr hy hf]
  field_simp
  ring

/-- Scalar–scalar quadratic Ricci variation, component `(1, 3)`. -/
theorem scalarJet_quadratic_ricci_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 3 =
      B ^ 2 * (((2 : ℂ) * s * r ^ 2 + (2 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 2 * r ^ 4 + (19 / 4 : ℂ) * s ^ 3 + (-3 : ℂ) * s ^ 3 * r ^ 2 + (7 / 2 : ℂ) * s ^ 4 + (-2 : ℂ) * s ^ 4 * r ^ 2 + (3 / 4 : ℂ) * s ^ 5) / (r ^ 5 * (r ^ 2 - 1)) * S * Sy) := by
  simp only [Quadratic.ricci, Fin.sum_univ_four, scalarJet_quadratic_curvature_0_1_3 hr hy hf, scalarJet_quadratic_curvature_1_1_3 hr hy hf, scalarJet_quadratic_curvature_2_1_3 hr hy hf, scalarJet_quadratic_curvature_3_1_3 hr hy hf]
  field_simp
  ring

/-- Scalar–scalar quadratic Ricci variation, component `(2, 2)`. -/
theorem scalarJet_quadratic_ricci_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 2 =
      B ^ 2 * (((1 : ℂ) * r ^ 4 + (1 : ℂ) * s * r ^ 2 + (1 / 4 : ℂ) * s ^ 2 + (1 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 3 + (1 / 4 : ℂ) * s ^ 4) / (r ^ 4) * Sy ^ 2 +
        ((1 : ℂ) * r ^ 4 + (1 : ℂ) * s * r ^ 2 + (1 / 2 : ℂ) * s ^ 2 + (1 : ℂ) * s ^ 3 + (1 / 2 : ℂ) * s ^ 4) / (r ^ 4) * Sx ^ 2 +
        ((1 / 2 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 3 + (1 / 2 : ℂ) * s ^ 4) / (r ^ 4) * S * Sxx +
        ((-1 / 2 : ℂ) * s ^ 2 + (2 : ℂ) * s ^ 2 * r ^ 2 + (-1 : ℂ) * s ^ 3 + (-1 / 2 : ℂ) * s ^ 4) / (r ^ 4) * S * Sy * y⁻¹ +
        ((2 : ℂ) * r ^ 4 + (3 : ℂ) * s * r ^ 2 + (6 : ℂ) * s * r ^ 4 + (7 : ℂ) * s ^ 2 * r ^ 2 + (-1 : ℂ) * s ^ 2 * r ^ 4 + (-1 / 2 : ℂ) * s ^ 3 + (6 : ℂ) * s ^ 3 * r ^ 2 + (-5 / 4 : ℂ) * s ^ 4 + (-1 : ℂ) * s ^ 5 + (-1 / 4 : ℂ) * s ^ 6) / (r ^ 4) * S ^ 2 * y⁻¹ ^ 2) := by
  simp only [Quadratic.ricci, Fin.sum_univ_four, scalarJet_quadratic_curvature_0_2_2 hr hy hf, scalarJet_quadratic_curvature_1_2_2 hr hy hf, scalarJet_quadratic_curvature_2_2_2 hr hy hf, scalarJet_quadratic_curvature_3_2_2 hr hy hf]
  field_simp
  ring

/-- Scalar–scalar quadratic Ricci variation, component `(2, 3)`. -/
theorem scalarJet_quadratic_ricci_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 3 =
      B ^ 2 * (((1 / 4 : ℂ) * s ^ 2 + (-1 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 3 + (1 / 4 : ℂ) * s ^ 4) / (r ^ 4) * Sx * Sy +
        ((1 / 2 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 3 + (1 / 2 : ℂ) * s ^ 4) / (r ^ 4) * S * Sxy +
        ((1 / 2 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 3 + (1 / 2 : ℂ) * s ^ 4) / (r ^ 4) * S * Sx * y⁻¹) := by
  simp only [Quadratic.ricci, Fin.sum_univ_four, scalarJet_quadratic_curvature_0_2_3 hr hy hf, scalarJet_quadratic_curvature_1_2_3 hr hy hf, scalarJet_quadratic_curvature_2_2_3 hr hy hf, scalarJet_quadratic_curvature_3_2_3 hr hy hf]
  field_simp
  ring

/-- Scalar–scalar quadratic Ricci variation, component `(3, 3)`. -/
theorem scalarJet_quadratic_ricci_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 3 =
      B ^ 2 * (((1 : ℂ) * r ^ 4 + (1 : ℂ) * s * r ^ 2 + (1 / 2 : ℂ) * s ^ 2 + (1 : ℂ) * s ^ 3 + (1 / 2 : ℂ) * s ^ 4) / (r ^ 4) * Sy ^ 2 +
        ((1 : ℂ) * r ^ 4 + (1 : ℂ) * s * r ^ 2 + (1 / 4 : ℂ) * s ^ 2 + (1 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 3 + (1 / 4 : ℂ) * s ^ 4) / (r ^ 4) * Sx ^ 2 +
        ((-1 / 2 : ℂ) * s ^ 2 + (2 : ℂ) * s ^ 2 * r ^ 2 + (-1 : ℂ) * s ^ 3 + (-1 / 2 : ℂ) * s ^ 4) / (r ^ 4) * S * Sxx +
        ((1 / 2 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 3 + (1 / 2 : ℂ) * s ^ 4) / (r ^ 4) * S * Sy * y⁻¹ +
        ((2 : ℂ) * r ^ 4 + (3 : ℂ) * s * r ^ 2 + (6 : ℂ) * s * r ^ 4 + (1 : ℂ) * s ^ 2 + (3 : ℂ) * s ^ 2 * r ^ 2 + (-1 : ℂ) * s ^ 2 * r ^ 4 + (3 : ℂ) * s ^ 3 + (13 / 4 : ℂ) * s ^ 4 + (-2 : ℂ) * s ^ 4 * r ^ 2 + (3 / 2 : ℂ) * s ^ 5 + (1 / 4 : ℂ) * s ^ 6) / (r ^ 4) * S ^ 2 * y⁻¹ ^ 2) := by
  simp only [Quadratic.ricci, Fin.sum_univ_four, scalarJet_quadratic_curvature_0_3_3 hr hy hf, scalarJet_quadratic_curvature_1_3_3 hr hy hf, scalarJet_quadratic_curvature_2_3_3 hr hy hf, scalarJet_quadratic_curvature_3_3_3 hr hy hf]
  field_simp
  ring

end
end RHTower.D4BMScalarLinearEquation
