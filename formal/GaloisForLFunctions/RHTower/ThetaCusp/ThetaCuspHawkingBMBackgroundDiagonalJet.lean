import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMBackgroundMetricTwoJet
import GaloisForLFunctions.HTGeometry.CoordinateEinsteinDiagonalCollapse

/-!
# The Birmingham–Mokhtari background is a diagonal two-jet

Its metric and every derivative matrix are diagonal, and the diagonal metric entries are nonzero
on the exterior, so the index-collapsed forms of the linearized Einstein coefficients apply to
every perturbation jet over it.
-/

namespace RHTower.D4BMBackground
open GaloisForLFunctions.HTGeometry

theorem jet_isDiagonalJet (r y : ℂ) (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    CoordinateMetricTwoJet.IsDiagonalJet (jet r y) where
  metric_ne i j hij := by simp [jet, metric, Matrix.diagonal_apply_ne _ hij]
  first_ne k i j hij := by simp [jet, Matrix.diagonal_apply_ne _ hij]
  second_ne k l i j hij := by simp [jet, Matrix.diagonal_apply_ne _ hij]
  metric_diag_ne_zero i := by
    have hf' : 1 - r ^ (2 : ℕ) ≠ 0 := by
      intro h; apply hf; linear_combination -h
    fin_cases i <;> simp [jet, metric, hr, hy, hf, hf']

/-- Linearized inverse metric of any perturbation over the BM background. -/
theorem linearization_inverse_apply (r y : ℂ) (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0)
    (K : CoordinateMetricTwoJet 4 ℂ) (u m : Fin 4) :
    CoordinateMetricTwoJet.Linearization.inverse (jet r y) K u m =
      -(K.metric u m / ((jet r y).metric u u * (jet r y).metric m m)) :=
  (jet_isDiagonalJet r y hr hy hf).linearization_inverse_apply K u m

/-- Linearized Christoffel symbols of any perturbation over the BM background. -/
theorem linearization_connection_eq (r y : ℂ) (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0)
    (K : CoordinateMetricTwoJet 4 ℂ) (u i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.connection (jet r y) K u i j =
      (1 / 2 : ℂ) * (-(K.metric u j * (jet r y).first i j j /
          ((jet r y).metric u u * (jet r y).metric j j)) -
        K.metric u i * (jet r y).first j i i / ((jet r y).metric u u * (jet r y).metric i i) +
        (if i = j then ∑ m, K.metric u m * (jet r y).first m i i /
          ((jet r y).metric u u * (jet r y).metric m m) else 0) +
        (K.first i u j + K.first j u i - K.first u i j) / (jet r y).metric u u) :=
  (jet_isDiagonalJet r y hr hy hf).linearization_connection_eq K u i j

end RHTower.D4BMBackground
