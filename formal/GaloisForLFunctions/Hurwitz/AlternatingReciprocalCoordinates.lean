import GaloisForLFunctions.KodairaParshinAbc.Periods.ReciprocalCoordinates
import GaloisForLFunctions.RHTower.AlternatingInverseCoefficientBoundary

/-!
# Reciprocal coordinates for the alternating Dirichlet series

The formal series with coefficients `(-1)^(n-1) n^(-s)` is tangent to the
identity at every complex parameter. The reciprocal mirror-coordinate law
therefore applies to its existing compositional inverse without any
univalence, convergence, or zero-free-region input.
-/

noncomputable section

namespace GaloisForLFunctions.Hurwitz

open KodairaParshinAbc.Periods _root_.RHTower.AlternatingInverseCoefficient

theorem alternating_tangentSeries (s : ℂ) :
    tangentPowerSeriesOfCoefficients (fun n => coefficient s (n + 2)) = formalSeries s := by
  apply PowerSeries.ext
  intro n
  obtain (_ | _ | n) := n
  · simp [formalSeries, coefficient]
  · simp
  · simp only [tangentPowerSeriesOfCoefficients_coeff_add_two, formalSeries, PowerSeries.coeff_mk]

/-- The two independently constructed formal inverses coincide at every parameter. -/
theorem alternating_inverseCoordinate (s : ℂ) :
    inverseCoordinate (fun n => coefficient s (n + 2)) = formalInverse s := by
  have h := inverse_subst_coordinate (fun n => coefficient s (n + 2))
  rw [alternating_tangentSeries] at h
  exact (powerSeries_subst_rightInverse_unique
    (formalSeries_constantCoeff s) (by simp [formalInverse])
    h (formalSeries_subst_inverse s)).symm

/-- Logarithmic responses of the actual alternating source and its inverse are reciprocal. -/
theorem alternating_reciprocal_logarithmicResponses (s : ℂ) :
    (logarithmicResponse (formalSeries s)).subst (formalInverse s) *
      logarithmicResponse (formalInverse s) = 1 := by
  have h := reciprocal_logarithmicResponses (fun n => coefficient s (n + 2))
  rwa [alternating_tangentSeries, alternating_inverseCoordinate] at h

/-- Euler differentiation lowers the Dirichlet parameter by one. -/
theorem alternating_coefficient_shift (s : ℂ) (n : ℕ) :
    coefficient (s - 1) (n + 1) = (n + 1 : ℂ) * coefficient s (n + 1) := by
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [coefficient, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, Nat.cast_add,
    Nat.cast_one]
  rw [show -(s - 1) = -s + 1 by ring, Complex.cpow_add _ _ hn, Complex.cpow_one]
  ring

/-- The actual derivative is the unit part of the adjacent Dirichlet series. -/
theorem alternating_derivative (s : ℂ) :
    PowerSeries.derivative ℂ (formalSeries s) = unitPart (formalSeries (s - 1)) := by
  apply PowerSeries.ext
  intro n
  simp only [PowerSeries.coeff_derivative, unitPart, PowerSeries.coeff_mk, formalSeries]
  rw [alternating_coefficient_shift]
  ring

/-- The reciprocal-coordinate response is a ratio of adjacent Dirichlet-parameter series. -/
theorem alternating_response_parameterShift (s : ℂ) :
    logarithmicResponse (formalSeries s) =
      unitPart (formalSeries (s - 1)) * PowerSeries.invOfUnit (unitPart (formalSeries s)) 1 := by
  rw [logarithmicResponse, alternating_derivative]

end GaloisForLFunctions.Hurwitz
