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

theorem scalarJet_quadratic_curvature_0_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 0 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  all_goals field_simp
  all_goals ring

theorem scalarJet_quadratic_curvature_1_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 1 0 =
      B ^ (2 : ℕ) * (((1 / 8 : ℂ) * s ^ (2 : ℕ) + (-5 / 8 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (1 / 4 : ℂ) * s ^ (3 : ℕ) + (-1 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (1 / 8 : ℂ) * s ^ (4 : ℕ) + (-1 / 8 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ)) * Sy ^ (2 : ℕ) * y ^ (2 : ℕ) +
        ((1 / 8 : ℂ) * s ^ (2 : ℕ) + (-5 / 8 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (1 / 4 : ℂ) * s ^ (3 : ℕ) + (-1 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (1 / 8 : ℂ) * s ^ (4 : ℕ) + (-1 / 8 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ)) * Sx ^ (2 : ℕ) * y ^ (2 : ℕ) +
        ((3 / 2 : ℂ) * s ^ (2 : ℕ) + (-4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (17 / 4 : ℂ) * s ^ (3 : ℕ) + (-21 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-3 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (17 / 4 : ℂ) * s ^ (4 : ℕ) + (-3 / 4 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) + (7 / 4 : ℂ) * s ^ (5 : ℕ) + (3 / 4 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (6 : ℕ) + (1 / 4 : ℂ) * s ^ (6 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ)) * S ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_2_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 0 2 0 =
      B ^ (2 : ℕ) * (((1 / 4 : ℂ) * s * r ^ (2 : ℕ) + (-3 / 4 : ℂ) * s * r ^ (4 : ℕ) + (1 / 8 : ℂ) * s ^ (2 : ℕ) + (-1 / 8 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (1 / 4 : ℂ) * s ^ (3 : ℕ) + (-1 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (1 / 8 : ℂ) * s ^ (4 : ℕ) + (1 / 8 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ)) * Sy ^ (2 : ℕ) * y ^ (2 : ℕ) +
        ((-1 / 4 : ℂ) * s + (3 / 4 : ℂ) * s * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 / 4 : ℂ) * s ^ (4 : ℕ)) / (r ^ (4 : ℕ)) * Sx ^ (2 : ℕ) * y ^ (2 : ℕ) +
        ((-1 / 2 : ℂ) * s * r ^ (2 : ℕ) + (3 / 2 : ℂ) * s * r ^ (4 : ℕ) + (-1 / 4 : ℂ) * s ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 / 4 : ℂ) * s ^ (4 : ℕ) + (-1 / 4 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ)) * S * Sxx * y ^ (2 : ℕ) +
        ((1 / 2 : ℂ) * s * r ^ (2 : ℕ) + (-3 / 2 : ℂ) * s * r ^ (4 : ℕ) + (1 / 4 : ℂ) * s ^ (2 : ℕ) + (-1 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ)) * S * Sy * y ^ (1 : ℕ) +
        ((-1 : ℂ) * s * r ^ (4 : ℕ) + (-1 : ℂ) * s ^ (2 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (3 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) + (-11 / 4 : ℂ) * s ^ (3 : ℕ) + (-1 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (5 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-21 / 8 : ℂ) * s ^ (4 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (9 / 4 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) + (-1 : ℂ) * s ^ (5 : ℕ) + (1 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (-1 / 8 : ℂ) * s ^ (6 : ℕ) + (1 / 2 : ℂ) * s ^ (6 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ)) * S ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_3_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 0 3 0 =
      B ^ (2 : ℕ) * (((-1 / 4 : ℂ) * s + (3 / 4 : ℂ) * s * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 / 4 : ℂ) * s ^ (4 : ℕ)) / (r ^ (4 : ℕ)) * Sy ^ (2 : ℕ) * y ^ (2 : ℕ) +
        ((1 / 4 : ℂ) * s * r ^ (2 : ℕ) + (-3 / 4 : ℂ) * s * r ^ (4 : ℕ) + (1 / 8 : ℂ) * s ^ (2 : ℕ) + (-1 / 8 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (1 / 4 : ℂ) * s ^ (3 : ℕ) + (-1 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (1 / 8 : ℂ) * s ^ (4 : ℕ) + (1 / 8 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ)) * Sx ^ (2 : ℕ) * y ^ (2 : ℕ) +
        ((1 / 2 : ℂ) * s * r ^ (2 : ℕ) + (-3 / 2 : ℂ) * s * r ^ (4 : ℕ) + (1 / 4 : ℂ) * s ^ (2 : ℕ) + (-1 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ)) * S * Sxx * y ^ (2 : ℕ) +
        ((-1 / 2 : ℂ) * s * r ^ (2 : ℕ) + (3 / 2 : ℂ) * s * r ^ (4 : ℕ) + (-1 / 4 : ℂ) * s ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 / 4 : ℂ) * s ^ (4 : ℕ) + (-1 / 4 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ)) * S * Sy * y ^ (1 : ℕ) +
        ((-1 : ℂ) * s * r ^ (2 : ℕ) + (2 : ℂ) * s * r ^ (4 : ℕ) + (-3 / 2 : ℂ) * s ^ (2 : ℕ) + (-1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (11 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (3 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) + (-9 / 2 : ℂ) * s ^ (3 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (5 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-39 / 8 : ℂ) * s ^ (4 : ℕ) + (3 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (7 / 4 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) + (-9 / 4 : ℂ) * s ^ (5 : ℕ) + (3 / 4 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (-3 / 8 : ℂ) * s ^ (6 : ℕ) + (1 / 4 : ℂ) * s ^ (6 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ)) * S ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_0_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 0 1 =
      B ^ (2 : ℕ) * (((-3 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (3 : ℂ) * s ^ (3 : ℕ) + (-11 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (11 / 2 : ℂ) * s ^ (4 : ℕ) + (-3 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (3 : ℂ) * s ^ (5 : ℕ) + (-1 / 2 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (6 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * S ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_1_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 1 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  all_goals field_simp
  all_goals ring

theorem scalarJet_quadratic_curvature_2_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 0 2 1 =
      B ^ (2 : ℕ) * (((-1 / 2 : ℂ) * s * r ^ (4 : ℕ) + (1 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (3 : ℕ) + (-1 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * Sy ^ (2 : ℕ) * y ^ (2 : ℕ) +
        ((1 / 2 : ℂ) * s * r ^ (4 : ℕ) + (-1 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 / 4 : ℂ) * s ^ (3 : ℕ) + (1 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 / 4 : ℂ) * s ^ (4 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * Sx ^ (2 : ℕ) * y ^ (2 : ℕ) +
        ((1 : ℂ) * s * r ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * S * Sxx * y ^ (2 : ℕ) +
        ((-1 : ℂ) * s * r ^ (4 : ℕ) + (1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (4 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * S * Sy * y ^ (1 : ℕ) +
        ((-1 : ℂ) * s * r ^ (4 : ℕ) + (1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (3 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-1 / 4 : ℂ) * s ^ (3 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (3 / 8 : ℂ) * s ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (1 : ℂ) * s ^ (5 : ℕ) + (-1 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (3 / 8 : ℂ) * s ^ (6 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * S ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_3_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 0 3 1 =
      B ^ (2 : ℕ) * (((1 / 2 : ℂ) * s * r ^ (4 : ℕ) + (-1 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 / 4 : ℂ) * s ^ (3 : ℕ) + (1 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 / 4 : ℂ) * s ^ (4 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * Sy ^ (2 : ℕ) * y ^ (2 : ℕ) +
        ((-1 / 2 : ℂ) * s * r ^ (4 : ℕ) + (1 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (3 : ℕ) + (-1 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * Sx ^ (2 : ℕ) * y ^ (2 : ℕ) +
        ((-1 : ℂ) * s * r ^ (4 : ℕ) + (1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (4 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * S * Sxx * y ^ (2 : ℕ) +
        ((1 : ℂ) * s * r ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * S * Sy * y ^ (1 : ℕ) +
        ((1 : ℂ) * s * r ^ (4 : ℕ) + (9 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-5 / 4 : ℂ) * s ^ (3 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-17 / 8 : ℂ) * s ^ (4 : ℕ) + (1 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (5 : ℕ) + (-1 / 2 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (-1 / 8 : ℂ) * s ^ (6 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * S ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_0_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 0 2 =
      B ^ (2 : ℕ) * (((3 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-3 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-3 / 2 : ℂ) * s ^ (3 : ℕ) + (7 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-2 : ℂ) * s ^ (4 : ℕ) + (1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (5 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * S * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_1_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 1 2 =
      B ^ (2 : ℕ) * (((-9 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (9 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (13 / 8 : ℂ) * s ^ (3 : ℕ) + (-23 / 8 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (2 : ℂ) * s ^ (4 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (3 / 8 : ℂ) * s ^ (5 : ℕ) + (1 / 8 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * S * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_2_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 0 2 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  all_goals field_simp
  all_goals ring

theorem scalarJet_quadratic_curvature_3_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 0 3 2 =
      B ^ (2 : ℕ) * (((2 : ℂ) * s * r ^ (4 : ℕ) + (5 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (7 / 8 : ℂ) * s ^ (3 : ℕ) + (7 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (3 / 2 : ℂ) * s ^ (4 : ℕ) + (5 / 8 : ℂ) * s ^ (5 : ℕ)) / (r ^ (4 : ℕ)) * S * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_0_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 0 3 =
      B ^ (2 : ℕ) * (((3 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-3 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-3 / 2 : ℂ) * s ^ (3 : ℕ) + (7 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-2 : ℂ) * s ^ (4 : ℕ) + (1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (5 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * S * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_1_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 1 3 =
      B ^ (2 : ℕ) * (((-9 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (9 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (13 / 8 : ℂ) * s ^ (3 : ℕ) + (-23 / 8 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (2 : ℂ) * s ^ (4 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (3 / 8 : ℂ) * s ^ (5 : ℕ) + (1 / 8 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * S * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_2_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 0 2 3 =
      B ^ (2 : ℕ) * (((2 : ℂ) * s * r ^ (4 : ℕ) + (5 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (7 / 8 : ℂ) * s ^ (3 : ℕ) + (7 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (3 / 2 : ℂ) * s ^ (4 : ℕ) + (5 / 8 : ℂ) * s ^ (5 : ℕ)) / (r ^ (4 : ℕ)) * S * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_3_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 0 3 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  all_goals field_simp
  all_goals ring

theorem scalarJet_quadratic_curvature_0_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 0 1 =
      B ^ (2 : ℕ) * (((1 / 8 : ℂ) * s ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (3 : ℕ) + (1 / 8 : ℂ) * s ^ (4 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1)) * Sy ^ (2 : ℕ) * y ^ (2 : ℕ) +
        ((1 / 8 : ℂ) * s ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (3 : ℕ) + (1 / 8 : ℂ) * s ^ (4 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1)) * Sx ^ (2 : ℕ) * y ^ (2 : ℕ) +
        ((3 / 2 : ℂ) * s ^ (2 : ℕ) + (-5 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (17 / 4 : ℂ) * s ^ (3 : ℕ) + (-33 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (3 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (17 / 4 : ℂ) * s ^ (4 : ℕ) + (-11 / 4 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (1 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) + (7 / 4 : ℂ) * s ^ (5 : ℕ) + (3 / 4 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (6 : ℕ) + (1 / 4 : ℂ) * s ^ (6 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * S ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_1_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 1 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  all_goals field_simp
  all_goals ring

theorem scalarJet_quadratic_curvature_2_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 1 2 1 =
      B ^ (2 : ℕ) * (((1 / 4 : ℂ) * s * r ^ (2 : ℕ) + (-3 / 4 : ℂ) * s * r ^ (4 : ℕ) + (1 / 8 : ℂ) * s ^ (2 : ℕ) + (-1 / 8 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (1 / 4 : ℂ) * s ^ (3 : ℕ) + (-1 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (1 / 8 : ℂ) * s ^ (4 : ℕ) + (1 / 8 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * Sy ^ (2 : ℕ) * y ^ (2 : ℕ) +
        ((-1 / 4 : ℂ) * s * r ^ (2 : ℕ) + (3 / 4 : ℂ) * s * r ^ (4 : ℕ) + (-1 / 4 : ℂ) * s ^ (2 : ℕ) + (3 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-3 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 / 4 : ℂ) * s ^ (4 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * Sx ^ (2 : ℕ) * y ^ (2 : ℕ) +
        ((-1 / 2 : ℂ) * s * r ^ (2 : ℕ) + (3 / 2 : ℂ) * s * r ^ (4 : ℕ) + (-1 / 4 : ℂ) * s ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 / 4 : ℂ) * s ^ (4 : ℕ) + (-1 / 4 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * S * Sxx * y ^ (2 : ℕ) +
        ((1 / 2 : ℂ) * s * r ^ (2 : ℕ) + (-3 / 2 : ℂ) * s * r ^ (4 : ℕ) + (1 / 4 : ℂ) * s ^ (2 : ℕ) + (-1 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * S * Sy * y ^ (1 : ℕ) +
        ((1 : ℂ) * s * r ^ (2 : ℕ) + (-2 : ℂ) * s * r ^ (4 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) + (-1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (3 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (6 : ℂ) * s ^ (3 : ℕ) + (-13 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-5 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (13 / 2 : ℂ) * s ^ (4 : ℕ) + (-59 / 8 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (3 / 4 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) + (3 : ℂ) * s ^ (5 : ℕ) + (-3 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (6 : ℕ) + (-1 / 8 : ℂ) * s ^ (6 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * S ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_3_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 1 3 1 =
      B ^ (2 : ℕ) * (((-1 / 4 : ℂ) * s * r ^ (2 : ℕ) + (3 / 4 : ℂ) * s * r ^ (4 : ℕ) + (-1 / 4 : ℂ) * s ^ (2 : ℕ) + (3 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-3 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 / 4 : ℂ) * s ^ (4 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * Sy ^ (2 : ℕ) * y ^ (2 : ℕ) +
        ((1 / 4 : ℂ) * s * r ^ (2 : ℕ) + (-3 / 4 : ℂ) * s * r ^ (4 : ℕ) + (1 / 8 : ℂ) * s ^ (2 : ℕ) + (-1 / 8 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (1 / 4 : ℂ) * s ^ (3 : ℕ) + (-1 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (1 / 8 : ℂ) * s ^ (4 : ℕ) + (1 / 8 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * Sx ^ (2 : ℕ) * y ^ (2 : ℕ) +
        ((1 / 2 : ℂ) * s * r ^ (2 : ℕ) + (-3 / 2 : ℂ) * s * r ^ (4 : ℕ) + (1 / 4 : ℂ) * s ^ (2 : ℕ) + (-1 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * S * Sxx * y ^ (2 : ℕ) +
        ((-1 / 2 : ℂ) * s * r ^ (2 : ℕ) + (3 / 2 : ℂ) * s * r ^ (4 : ℕ) + (-1 / 4 : ℂ) * s ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 / 4 : ℂ) * s ^ (4 : ℕ) + (-1 / 4 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * S * Sy * y ^ (1 : ℕ) +
        ((1 : ℂ) * s * r ^ (4 : ℕ) + (3 / 2 : ℂ) * s ^ (2 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (5 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (17 / 4 : ℂ) * s ^ (3 : ℕ) + (-21 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-5 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (17 / 4 : ℂ) * s ^ (4 : ℕ) + (-49 / 8 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) + (7 / 4 : ℂ) * s ^ (5 : ℕ) + (-13 / 4 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (6 : ℕ) + (-3 / 8 : ℂ) * s ^ (6 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * S ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_0_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 0 2 =
      B ^ (2 : ℕ) * (((-1 / 2 : ℂ) * s ^ (2 : ℕ) + (11 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-19 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (5 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) + (-9 / 8 : ℂ) * s ^ (3 : ℕ) + (25 / 8 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-3 / 4 : ℂ) * s ^ (4 : ℕ) + (-1 / 4 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) + (-1 / 8 : ℂ) * s ^ (5 : ℕ) + (-3 / 8 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * S * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_1_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 1 2 =
      B ^ (2 : ℕ) * (((-3 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (3 / 2 : ℂ) * s ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (5 : ℕ)) / (r ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * S * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_2_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 1 2 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  all_goals field_simp
  all_goals ring

theorem scalarJet_quadratic_curvature_3_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 1 3 2 =
      B ^ (2 : ℕ) * (((2 : ℂ) * s * r ^ (2 : ℕ) + (3 / 2 : ℂ) * s ^ (2 : ℕ) + (5 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-3 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (29 / 8 : ℂ) * s ^ (3 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (11 / 4 : ℂ) * s ^ (4 : ℕ) + (-5 / 4 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (5 / 8 : ℂ) * s ^ (5 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * S * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_0_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 0 3 =
      B ^ (2 : ℕ) * (((-1 / 2 : ℂ) * s ^ (2 : ℕ) + (11 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-19 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (5 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) + (-9 / 8 : ℂ) * s ^ (3 : ℕ) + (25 / 8 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-3 / 4 : ℂ) * s ^ (4 : ℕ) + (-1 / 4 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) + (-1 / 8 : ℂ) * s ^ (5 : ℕ) + (-3 / 8 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * S * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_1_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 1 3 =
      B ^ (2 : ℕ) * (((-3 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (3 / 2 : ℂ) * s ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (5 : ℕ)) / (r ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * S * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_2_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 1 2 3 =
      B ^ (2 : ℕ) * (((2 : ℂ) * s * r ^ (2 : ℕ) + (3 / 2 : ℂ) * s ^ (2 : ℕ) + (5 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-3 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (29 / 8 : ℂ) * s ^ (3 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (11 / 4 : ℂ) * s ^ (4 : ℕ) + (-5 / 4 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (5 / 8 : ℂ) * s ^ (5 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * S * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_3_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 1 3 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  all_goals field_simp
  all_goals ring

theorem scalarJet_quadratic_curvature_0_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2 0 2 =
      B ^ (2 : ℕ) * (((-1 / 4 : ℂ) * s * r ^ (2 : ℕ) + (3 / 4 : ℂ) * s * r ^ (4 : ℕ) + (-1 / 8 : ℂ) * s ^ (2 : ℕ) + (1 / 8 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-1 / 4 : ℂ) * s ^ (3 : ℕ) + (1 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 / 8 : ℂ) * s ^ (4 : ℕ) + (-1 / 8 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * Sy ^ (2 : ℕ) +
        ((1 / 4 : ℂ) * s + (-3 / 4 : ℂ) * s * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (2 : ℕ) + (-1 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ)) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * Sx ^ (2 : ℕ) +
        ((1 / 4 : ℂ) * s ^ (2 : ℕ) + (-1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ)) / (r ^ (4 : ℕ)) * S * Sxx +
        ((-1 / 4 : ℂ) * s ^ (2 : ℕ) + (1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) + (-1 / 4 : ℂ) * s ^ (4 : ℕ)) / (r ^ (4 : ℕ)) * S * Sy * y⁻¹ +
        ((-1 : ℂ) * s * r ^ (2 : ℕ) + (1 : ℂ) * s * r ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-3 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) + (1 / 4 : ℂ) * s ^ (3 : ℕ) + (5 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (7 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (5 / 8 : ℂ) * s ^ (4 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-5 / 4 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) + (1 / 2 : ℂ) * s ^ (5 : ℕ) + (-1 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (1 / 8 : ℂ) * s ^ (6 : ℕ) + (-1 / 2 : ℂ) * s ^ (6 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * S ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_1_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2 1 2 =
      B ^ (2 : ℕ) * (((1 / 4 : ℂ) * s * r ^ (2 : ℕ) + (-3 / 4 : ℂ) * s * r ^ (4 : ℕ) + (1 / 8 : ℂ) * s ^ (2 : ℕ) + (-1 / 8 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (1 / 4 : ℂ) * s ^ (3 : ℕ) + (-1 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (1 / 8 : ℂ) * s ^ (4 : ℕ) + (1 / 8 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * Sy ^ (2 : ℕ) +
        ((-1 / 4 : ℂ) * s * r ^ (2 : ℕ) + (3 / 4 : ℂ) * s * r ^ (4 : ℕ) + (-1 / 4 : ℂ) * s ^ (2 : ℕ) + (3 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-3 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 / 4 : ℂ) * s ^ (4 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * Sx ^ (2 : ℕ) +
        ((1 / 4 : ℂ) * s ^ (2 : ℕ) + (-1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ)) / (r ^ (4 : ℕ)) * S * Sxx +
        ((-1 / 4 : ℂ) * s ^ (2 : ℕ) + (1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) + (-1 / 4 : ℂ) * s ^ (4 : ℕ)) / (r ^ (4 : ℕ)) * S * Sy * y⁻¹ +
        ((-1 : ℂ) * s * r ^ (2 : ℕ) + (1 : ℂ) * s * r ^ (4 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) + (-7 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (7 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (6 : ℂ) * s ^ (3 : ℕ) + (-11 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (7 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (13 / 2 : ℂ) * s ^ (4 : ℕ) + (-59 / 8 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (5 / 4 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) + (3 : ℂ) * s ^ (5 : ℕ) + (-5 / 2 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (6 : ℕ) + (-1 / 8 : ℂ) * s ^ (6 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * S ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_2_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 2 2 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  all_goals field_simp
  all_goals ring

theorem scalarJet_quadratic_curvature_3_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 2 3 2 =
      B ^ (2 : ℕ) * (((1 : ℂ) * r ^ (4 : ℕ) + (1 : ℂ) * s * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (2 : ℕ) + (1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ)) / (r ^ (4 : ℕ)) * Sy ^ (2 : ℕ) +
        ((1 : ℂ) * r ^ (4 : ℕ) + (1 : ℂ) * s * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (2 : ℕ) + (1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ)) / (r ^ (4 : ℕ)) * Sx ^ (2 : ℕ) +
        ((2 : ℂ) * r ^ (4 : ℕ) + (1 : ℂ) * s * r ^ (2 : ℕ) + (6 : ℂ) * s * r ^ (4 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) + (3 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (23 / 4 : ℂ) * s ^ (3 : ℕ) + (5 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (47 / 8 : ℂ) * s ^ (4 : ℕ) + (5 / 2 : ℂ) * s ^ (5 : ℕ) + (3 / 8 : ℂ) * s ^ (6 : ℕ)) / (r ^ (4 : ℕ)) * S ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_0_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2 0 3 =
      B ^ (2 : ℕ) * (((1 / 2 : ℂ) * s * r ^ (2 : ℕ) + (-3 / 2 : ℂ) * s * r ^ (4 : ℕ) + (1 / 8 : ℂ) * s ^ (2 : ℕ) + (3 / 8 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (3 : ℕ) + (-1 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (1 / 8 : ℂ) * s ^ (4 : ℕ) + (3 / 8 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * Sx * Sy +
        ((1 / 4 : ℂ) * s ^ (2 : ℕ) + (-1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ)) / (r ^ (4 : ℕ)) * S * Sxy +
        ((1 / 4 : ℂ) * s ^ (2 : ℕ) + (-1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ)) / (r ^ (4 : ℕ)) * S * Sx * y⁻¹) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_1_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2 1 3 =
      B ^ (2 : ℕ) * (((-1 / 2 : ℂ) * s * r ^ (2 : ℕ) + (3 / 2 : ℂ) * s * r ^ (4 : ℕ) + (-3 / 8 : ℂ) * s ^ (2 : ℕ) + (7 / 8 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-3 / 4 : ℂ) * s ^ (3 : ℕ) + (3 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-3 / 8 : ℂ) * s ^ (4 : ℕ) + (-1 / 8 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * Sx * Sy +
        ((1 / 4 : ℂ) * s ^ (2 : ℕ) + (-1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ)) / (r ^ (4 : ℕ)) * S * Sxy +
        ((1 / 4 : ℂ) * s ^ (2 : ℕ) + (-1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ)) / (r ^ (4 : ℕ)) * S * Sx * y⁻¹) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_2_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 2 2 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  all_goals field_simp
  all_goals ring

theorem scalarJet_quadratic_curvature_3_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 2 3 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  all_goals field_simp
  all_goals ring

theorem scalarJet_quadratic_curvature_0_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 3 0 3 =
      B ^ (2 : ℕ) * (((1 / 4 : ℂ) * s + (-3 / 4 : ℂ) * s * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (2 : ℕ) + (-1 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ)) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * Sy ^ (2 : ℕ) +
        ((-1 / 4 : ℂ) * s * r ^ (2 : ℕ) + (3 / 4 : ℂ) * s * r ^ (4 : ℕ) + (-1 / 8 : ℂ) * s ^ (2 : ℕ) + (1 / 8 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-1 / 4 : ℂ) * s ^ (3 : ℕ) + (1 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 / 8 : ℂ) * s ^ (4 : ℕ) + (-1 / 8 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * Sx ^ (2 : ℕ) +
        ((-1 / 4 : ℂ) * s ^ (2 : ℕ) + (1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) + (-1 / 4 : ℂ) * s ^ (4 : ℕ)) / (r ^ (4 : ℕ)) * S * Sxx +
        ((1 / 4 : ℂ) * s ^ (2 : ℕ) + (-1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ)) / (r ^ (4 : ℕ)) * S * Sy * y⁻¹ +
        ((-1 : ℂ) * s * r ^ (2 : ℕ) + (1 : ℂ) * s * r ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (2 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-3 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) + (-3 / 2 : ℂ) * s ^ (3 : ℕ) + (6 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-5 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-13 / 8 : ℂ) * s ^ (4 : ℕ) + (7 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-9 / 4 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) + (-3 / 4 : ℂ) * s ^ (5 : ℕ) + (1 / 4 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (-1 / 8 : ℂ) * s ^ (6 : ℕ) + (-1 / 4 : ℂ) * s ^ (6 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * S ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_1_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 3 1 3 =
      B ^ (2 : ℕ) * (((-1 / 4 : ℂ) * s * r ^ (2 : ℕ) + (3 / 4 : ℂ) * s * r ^ (4 : ℕ) + (-1 / 4 : ℂ) * s ^ (2 : ℕ) + (3 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-3 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 / 4 : ℂ) * s ^ (4 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * Sy ^ (2 : ℕ) +
        ((1 / 4 : ℂ) * s * r ^ (2 : ℕ) + (-3 / 4 : ℂ) * s * r ^ (4 : ℕ) + (1 / 8 : ℂ) * s ^ (2 : ℕ) + (-1 / 8 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (1 / 4 : ℂ) * s ^ (3 : ℕ) + (-1 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (1 / 8 : ℂ) * s ^ (4 : ℕ) + (1 / 8 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * Sx ^ (2 : ℕ) +
        ((-1 / 4 : ℂ) * s ^ (2 : ℕ) + (1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) + (-1 / 4 : ℂ) * s ^ (4 : ℕ)) / (r ^ (4 : ℕ)) * S * Sxx +
        ((1 / 4 : ℂ) * s ^ (2 : ℕ) + (-1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ)) / (r ^ (4 : ℕ)) * S * Sy * y⁻¹ +
        ((-1 : ℂ) * s * r ^ (2 : ℕ) + (1 : ℂ) * s * r ^ (4 : ℕ) + (3 / 2 : ℂ) * s ^ (2 : ℕ) + (-9 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (5 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (17 / 4 : ℂ) * s ^ (3 : ℕ) + (-25 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-5 / 4 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (17 / 4 : ℂ) * s ^ (4 : ℕ) + (-33 / 8 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) + (7 / 4 : ℂ) * s ^ (5 : ℕ) + (-5 / 4 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (6 : ℕ) + (1 / 8 : ℂ) * s ^ (6 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * S ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_2_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 3 2 3 =
      B ^ (2 : ℕ) * (((1 : ℂ) * r ^ (4 : ℕ) + (1 : ℂ) * s * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (2 : ℕ) + (1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ)) / (r ^ (4 : ℕ)) * Sy ^ (2 : ℕ) +
        ((1 : ℂ) * r ^ (4 : ℕ) + (1 : ℂ) * s * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (2 : ℕ) + (1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ)) / (r ^ (4 : ℕ)) * Sx ^ (2 : ℕ) +
        ((2 : ℂ) * r ^ (4 : ℕ) + (1 : ℂ) * s * r ^ (2 : ℕ) + (6 : ℂ) * s * r ^ (4 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) + (3 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (23 / 4 : ℂ) * s ^ (3 : ℕ) + (5 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (47 / 8 : ℂ) * s ^ (4 : ℕ) + (5 / 2 : ℂ) * s ^ (5 : ℕ) + (3 / 8 : ℂ) * s ^ (6 : ℕ)) / (r ^ (4 : ℕ)) * S ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  field_simp
  ring

theorem scalarJet_quadratic_curvature_3_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 3 3 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmJetEntry]
  all_goals field_simp
  all_goals ring

/-- Scalar–scalar quadratic Ricci variation, component `(0, 0)`. -/
theorem scalarJet_quadratic_ricci_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 =
      B ^ (2 : ℕ) * (((1 / 4 : ℂ) * s ^ (2 : ℕ) + (-5 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ) + (-1 / 4 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ)) * Sy ^ (2 : ℕ) * y ^ (2 : ℕ) +
        ((1 / 4 : ℂ) * s ^ (2 : ℕ) + (-5 / 4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ) + (-1 / 4 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ)) * Sx ^ (2 : ℕ) * y ^ (2 : ℕ) +
        ((-1 : ℂ) * s * r ^ (2 : ℕ) + (1 : ℂ) * s * r ^ (4 : ℕ) + (-1 : ℂ) * s ^ (2 : ℕ) + (-5 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (7 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (3 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) + (-3 : ℂ) * s ^ (3 : ℕ) + (-9 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-13 / 4 : ℂ) * s ^ (4 : ℕ) + (1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (3 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) + (-3 / 2 : ℂ) * s ^ (5 : ℕ) + (5 / 2 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (-1 / 4 : ℂ) * s ^ (6 : ℕ) + (1 : ℂ) * s ^ (6 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ)) * S ^ (2 : ℕ)) := by
  simp only [Quadratic.ricci, Fin.sum_univ_four, scalarJet_quadratic_curvature_0_0_0 hr hy hf, scalarJet_quadratic_curvature_1_0_0 hr hy hf, scalarJet_quadratic_curvature_2_0_0 hr hy hf, scalarJet_quadratic_curvature_3_0_0 hr hy hf]
  field_simp
  ring

/-- Scalar–scalar quadratic Ricci variation, component `(0, 1)`. -/
theorem scalarJet_quadratic_ricci_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 =
      B ^ (2 : ℕ) * (((-2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (6 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (3 / 2 : ℂ) * s ^ (3 : ℕ) + (-7 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (15 / 4 : ℂ) * s ^ (4 : ℕ) + (-3 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (3 : ℂ) * s ^ (5 : ℕ) + (-2 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (3 / 4 : ℂ) * s ^ (6 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * S ^ (2 : ℕ)) := by
  simp only [Quadratic.ricci, Fin.sum_univ_four, scalarJet_quadratic_curvature_0_0_1 hr hy hf, scalarJet_quadratic_curvature_1_0_1 hr hy hf, scalarJet_quadratic_curvature_2_0_1 hr hy hf, scalarJet_quadratic_curvature_3_0_1 hr hy hf]
  field_simp
  ring

/-- Scalar–scalar quadratic Ricci variation, component `(0, 2)`. -/
theorem scalarJet_quadratic_ricci_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2 =
      B ^ (2 : ℕ) * (((2 : ℂ) * s * r ^ (4 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (3 / 4 : ℂ) * s ^ (3 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (3 / 2 : ℂ) * s ^ (4 : ℕ) + (3 / 4 : ℂ) * s ^ (5 : ℕ)) / (r ^ (4 : ℕ)) * S * Sx) := by
  simp only [Quadratic.ricci, Fin.sum_univ_four, scalarJet_quadratic_curvature_0_0_2 hr hy hf, scalarJet_quadratic_curvature_1_0_2 hr hy hf, scalarJet_quadratic_curvature_2_0_2 hr hy hf, scalarJet_quadratic_curvature_3_0_2 hr hy hf]
  field_simp
  ring

/-- Scalar–scalar quadratic Ricci variation, component `(0, 3)`. -/
theorem scalarJet_quadratic_ricci_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 3 =
      B ^ (2 : ℕ) * (((2 : ℂ) * s * r ^ (4 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (3 / 4 : ℂ) * s ^ (3 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (3 / 2 : ℂ) * s ^ (4 : ℕ) + (3 / 4 : ℂ) * s ^ (5 : ℕ)) / (r ^ (4 : ℕ)) * S * Sy) := by
  simp only [Quadratic.ricci, Fin.sum_univ_four, scalarJet_quadratic_curvature_0_0_3 hr hy hf, scalarJet_quadratic_curvature_1_0_3 hr hy hf, scalarJet_quadratic_curvature_2_0_3 hr hy hf, scalarJet_quadratic_curvature_3_0_3 hr hy hf]
  field_simp
  ring

/-- Scalar–scalar quadratic Ricci variation, component `(1, 1)`. -/
theorem scalarJet_quadratic_ricci_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 =
      B ^ (2 : ℕ) * (((1 / 4 : ℂ) * s ^ (2 : ℕ) + (-1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1)) * Sy ^ (2 : ℕ) * y ^ (2 : ℕ) +
        ((1 / 4 : ℂ) * s ^ (2 : ℕ) + (-1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1)) * Sx ^ (2 : ℕ) * y ^ (2 : ℕ) +
        ((1 : ℂ) * s * r ^ (2 : ℕ) + (-1 : ℂ) * s * r ^ (4 : ℕ) + (5 : ℂ) * s ^ (2 : ℕ) + (-8 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (7 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (29 / 2 : ℂ) * s ^ (3 : ℕ) + (-20 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (15 : ℂ) * s ^ (4 : ℕ) + (-65 / 4 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (2 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) + (13 / 2 : ℂ) * s ^ (5 : ℕ) + (-11 / 2 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (1 : ℂ) * s ^ (6 : ℕ) + (-1 / 4 : ℂ) * s ^ (6 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * S ^ (2 : ℕ)) := by
  simp only [Quadratic.ricci, Fin.sum_univ_four, scalarJet_quadratic_curvature_0_1_1 hr hy hf, scalarJet_quadratic_curvature_1_1_1 hr hy hf, scalarJet_quadratic_curvature_2_1_1 hr hy hf, scalarJet_quadratic_curvature_3_1_1 hr hy hf]
  field_simp
  ring

/-- Scalar–scalar quadratic Ricci variation, component `(1, 2)`. -/
theorem scalarJet_quadratic_ricci_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2 =
      B ^ (2 : ℕ) * (((2 : ℂ) * s * r ^ (2 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) + (-1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (19 / 4 : ℂ) * s ^ (3 : ℕ) + (-3 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (7 / 2 : ℂ) * s ^ (4 : ℕ) + (-2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (3 / 4 : ℂ) * s ^ (5 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * S * Sx) := by
  simp only [Quadratic.ricci, Fin.sum_univ_four, scalarJet_quadratic_curvature_0_1_2 hr hy hf, scalarJet_quadratic_curvature_1_1_2 hr hy hf, scalarJet_quadratic_curvature_2_1_2 hr hy hf, scalarJet_quadratic_curvature_3_1_2 hr hy hf]
  field_simp
  ring

/-- Scalar–scalar quadratic Ricci variation, component `(1, 3)`. -/
theorem scalarJet_quadratic_ricci_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 3 =
      B ^ (2 : ℕ) * (((2 : ℂ) * s * r ^ (2 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) + (-1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (19 / 4 : ℂ) * s ^ (3 : ℕ) + (-3 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (7 / 2 : ℂ) * s ^ (4 : ℕ) + (-2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (3 / 4 : ℂ) * s ^ (5 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * S * Sy) := by
  simp only [Quadratic.ricci, Fin.sum_univ_four, scalarJet_quadratic_curvature_0_1_3 hr hy hf, scalarJet_quadratic_curvature_1_1_3 hr hy hf, scalarJet_quadratic_curvature_2_1_3 hr hy hf, scalarJet_quadratic_curvature_3_1_3 hr hy hf]
  field_simp
  ring

/-- Scalar–scalar quadratic Ricci variation, component `(2, 2)`. -/
theorem scalarJet_quadratic_ricci_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 2 =
      B ^ (2 : ℕ) * (((1 : ℂ) * r ^ (4 : ℕ) + (1 : ℂ) * s * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (2 : ℕ) + (1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ)) / (r ^ (4 : ℕ)) * Sy ^ (2 : ℕ) +
        ((1 : ℂ) * r ^ (4 : ℕ) + (1 : ℂ) * s * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (2 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) + (1 / 2 : ℂ) * s ^ (4 : ℕ)) / (r ^ (4 : ℕ)) * Sx ^ (2 : ℕ) +
        ((1 / 2 : ℂ) * s ^ (2 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) + (1 / 2 : ℂ) * s ^ (4 : ℕ)) / (r ^ (4 : ℕ)) * S * Sxx +
        ((-1 / 2 : ℂ) * s ^ (2 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ)) / (r ^ (4 : ℕ)) * S * Sy * y⁻¹ +
        ((2 : ℂ) * r ^ (4 : ℕ) + (3 : ℂ) * s * r ^ (2 : ℕ) + (6 : ℂ) * s * r ^ (4 : ℕ) + (7 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) + (6 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-5 / 4 : ℂ) * s ^ (4 : ℕ) + (-1 : ℂ) * s ^ (5 : ℕ) + (-1 / 4 : ℂ) * s ^ (6 : ℕ)) / (r ^ (4 : ℕ)) * S ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ)) := by
  simp only [Quadratic.ricci, Fin.sum_univ_four, scalarJet_quadratic_curvature_0_2_2 hr hy hf, scalarJet_quadratic_curvature_1_2_2 hr hy hf, scalarJet_quadratic_curvature_2_2_2 hr hy hf, scalarJet_quadratic_curvature_3_2_2 hr hy hf]
  field_simp
  ring

/-- Scalar–scalar quadratic Ricci variation, component `(2, 3)`. -/
theorem scalarJet_quadratic_ricci_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 3 =
      B ^ (2 : ℕ) * (((1 / 4 : ℂ) * s ^ (2 : ℕ) + (-1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ)) / (r ^ (4 : ℕ)) * Sx * Sy +
        ((1 / 2 : ℂ) * s ^ (2 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) + (1 / 2 : ℂ) * s ^ (4 : ℕ)) / (r ^ (4 : ℕ)) * S * Sxy +
        ((1 / 2 : ℂ) * s ^ (2 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) + (1 / 2 : ℂ) * s ^ (4 : ℕ)) / (r ^ (4 : ℕ)) * S * Sx * y⁻¹) := by
  simp only [Quadratic.ricci, Fin.sum_univ_four, scalarJet_quadratic_curvature_0_2_3 hr hy hf, scalarJet_quadratic_curvature_1_2_3 hr hy hf, scalarJet_quadratic_curvature_2_2_3 hr hy hf, scalarJet_quadratic_curvature_3_2_3 hr hy hf]
  field_simp
  ring

/-- Scalar–scalar quadratic Ricci variation, component `(3, 3)`. -/
theorem scalarJet_quadratic_ricci_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 3 =
      B ^ (2 : ℕ) * (((1 : ℂ) * r ^ (4 : ℕ) + (1 : ℂ) * s * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (2 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) + (1 / 2 : ℂ) * s ^ (4 : ℕ)) / (r ^ (4 : ℕ)) * Sy ^ (2 : ℕ) +
        ((1 : ℂ) * r ^ (4 : ℕ) + (1 : ℂ) * s * r ^ (2 : ℕ) + (1 / 4 : ℂ) * s ^ (2 : ℕ) + (1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) + (1 / 4 : ℂ) * s ^ (4 : ℕ)) / (r ^ (4 : ℕ)) * Sx ^ (2 : ℕ) +
        ((-1 / 2 : ℂ) * s ^ (2 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ)) / (r ^ (4 : ℕ)) * S * Sxx +
        ((1 / 2 : ℂ) * s ^ (2 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) + (1 / 2 : ℂ) * s ^ (4 : ℕ)) / (r ^ (4 : ℕ)) * S * Sy * y⁻¹ +
        ((2 : ℂ) * r ^ (4 : ℕ) + (3 : ℂ) * s * r ^ (2 : ℕ) + (6 : ℂ) * s * r ^ (4 : ℕ) + (1 : ℂ) * s ^ (2 : ℕ) + (3 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (3 : ℂ) * s ^ (3 : ℕ) + (13 / 4 : ℂ) * s ^ (4 : ℕ) + (-2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (3 / 2 : ℂ) * s ^ (5 : ℕ) + (1 / 4 : ℂ) * s ^ (6 : ℕ)) / (r ^ (4 : ℕ)) * S ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ)) := by
  simp only [Quadratic.ricci, Fin.sum_univ_four, scalarJet_quadratic_curvature_0_3_3 hr hy hf, scalarJet_quadratic_curvature_1_3_3 hr hy hf, scalarJet_quadratic_curvature_2_3_3 hr hy hf, scalarJet_quadratic_curvature_3_3_3 hr hy hf]
  field_simp
  ring

end
end RHTower.D4BMScalarLinearEquation
