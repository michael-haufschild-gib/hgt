import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMBackgroundDiagonalJet
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMScalarLinearizedRicciJet

/-!
# The scalar–scalar quadratic Einstein source is a trace-adjusted quadratic Ricci variation

Over the Birmingham–Mokhtari background, which is Einstein with constant `-3`, the fundamental
scalar metric jet solves the linearized equation with the same constant and is symmetric. Both
inverse–Ricci cross terms of the quadratic scalar variation then cancel, the linearized scalar
variation vanishes, and the scalar–scalar quadratic Einstein coefficient is the quadratic Ricci
variation minus half the background metric times its background trace. No component of the
quadratic Ricci variation is evaluated here.
-/

namespace RHTower.D4BMScalarLinearEquation
open GaloisForLFunctions.HTGeometry
open scoped BigOperators
noncomputable section

/-- The fundamental scalar jet's metric block is symmetric. -/
theorem scalarJet_metric_symm (s r y B S Sx Sy Sxx Sxy : ℂ) (i j : Fin 4) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).metric i j =
      (scalarJet s r y B S Sx Sy Sxx Sxy).metric j i := by
  fin_cases i <;> fin_cases j <;> rfl

/-- The linearized Ricci variation of the scalar jet is `-3` times the jet (the linearized
cosmological Einstein equation on the background). -/
theorem scalarJet_linearization_ricci (s r y B S Sx Sy Sxx Sxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.ricci (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy) i j =
      -3 * (scalarJet s r y B S Sx Sy Sxx Sxy).metric i j := by
  have h := ricci_component s r y B S Sx Sy Sxx Sxy hr hy hf i j
  linear_combination h

/-- The background jet is Einstein with constant `-3`, stated on its own metric block. -/
theorem background_ricci_eq (r y : ℂ) (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0)
    (i j : Fin 4) :
    (D4BMBackground.jet r y).ricci i j = -3 * (D4BMBackground.jet r y).metric i j :=
  D4BMBackground.jet_ricci r y hr hy hf i j

/-- Scalar–scalar quadratic Einstein source as a trace-adjusted quadratic Ricci variation. -/
theorem scalarJet_quadratic_einstein_eq (s r y B S Sx Sy Sxx Sxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) (i j : Fin 4) :
    CoordinateMetricTwoJet.Quadratic.einstein (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy) i j =
      CoordinateMetricTwoJet.Quadratic.ricci (D4BMBackground.jet r y)
        (scalarJet s r y B S Sx Sy Sxx Sxy) i j -
      (1 / 2 : ℂ) * (∑ u, ((D4BMBackground.jet r y).metric u u)⁻¹ *
        CoordinateMetricTwoJet.Quadratic.ricci (D4BMBackground.jet r y)
          (scalarJet s r y B S Sx Sy Sxx Sxy) u u) * (D4BMBackground.jet r y).metric i j :=
  (D4BMBackground.jet_isDiagonalJet r y hr hy hf).quadratic_einstein_eq _ (-3)
    (background_ricci_eq r y hr hy hf)
    (scalarJet_linearization_ricci s r y B S Sx Sy Sxx Sxy hr hy hf)
    (scalarJet_metric_symm s r y B S Sx Sy Sxx Sxy) i j

/-- The quadratic scalar variation of the scalar jet is the background trace of its quadratic
Ricci variation. -/
theorem scalarJet_quadratic_scalar_eq (s r y B S Sx Sy Sxx Sxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    CoordinateMetricTwoJet.Quadratic.scalar (D4BMBackground.jet r y)
      (scalarJet s r y B S Sx Sy Sxx Sxy) =
      ∑ u, ((D4BMBackground.jet r y).metric u u)⁻¹ *
        CoordinateMetricTwoJet.Quadratic.ricci (D4BMBackground.jet r y)
          (scalarJet s r y B S Sx Sy Sxx Sxy) u u :=
  (D4BMBackground.jet_isDiagonalJet r y hr hy hf).quadratic_scalar_eq _ (-3)
    (background_ricci_eq r y hr hy hf)
    (scalarJet_linearization_ricci s r y B S Sx Sy Sxx Sxy hr hy hf)
    (scalarJet_metric_symm s r y B S Sx Sy Sxx Sxy)

end
end RHTower.D4BMScalarLinearEquation
