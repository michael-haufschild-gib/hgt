import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WittIntegralityIsNotPurity
import GaloisForLFunctions.KodairaParshinAbc.Periods.ReciprocalCoordinates

/-!
# Point-count series as reciprocal coordinate derivatives

For a curve datum with zeta series `Z(q)`, set `Q=q Z(q)`. Its normalized
logarithmic derivative is `1+Σ N_n q^n`, and the inverse coordinate has the
reciprocal response. Thus the coordinate mechanism of arXiv:2611.13126
also packages Lefschetz point counts. It holds for the explicit impure
golden datum as well, so reciprocity by itself does not imply purity.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open PowerSeries KodairaParshinAbc.Periods

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- The zeta series regarded as the unit part of a formal coordinate. -/
def pointCountCoordinate : PowerSeries ℂ := PowerSeries.X * D.zetaSeries

/-- Its canonical compositional inverse. -/
def inversePointCountCoordinate : PowerSeries ℂ :=
  inverseCoordinate (fun n => PowerSeries.coeff (n + 1) D.zetaSeries)

theorem pointCountCoordinate_eq_tangent :
    D.pointCountCoordinate =
      tangentPowerSeriesOfCoefficients (fun n => PowerSeries.coeff (n + 1) D.zetaSeries) := by
  apply PowerSeries.ext
  intro n
  obtain (_ | _ | n) := n
  · simp [pointCountCoordinate]
  · simp [pointCountCoordinate, D.constantCoeff_zetaSeries]
  · simp only [pointCountCoordinate, coeff_succ_X_mul,
      tangentPowerSeriesOfCoefficients_coeff_add_two]

theorem pointCountCoordinate_unitPart : unitPart D.pointCountCoordinate = D.zetaSeries := by
  apply PowerSeries.ext
  intro n
  simp only [unitPart, coeff_mk, pointCountCoordinate, coeff_succ_X_mul]

/-- The coordinate response is the entire point-count generating series, with constant one. -/
theorem pointCountCoordinate_response :
    logarithmicResponse D.pointCountCoordinate = 1 + D.ghostSeries := by
  have hu := PowerSeries.mul_invOfUnit D.zetaSeries 1 D.constantCoeff_zetaSeries
  have hG := D.zetaSeries_hasGhost
  change PowerSeries.X * PowerSeries.derivative ℂ D.zetaSeries =
    D.zetaSeries * D.ghostSeries at hG
  rw [logarithmicResponse, D.pointCountCoordinate_unitPart, pointCountCoordinate,
    Derivation.leibniz, smul_eq_mul, smul_eq_mul, derivative_X, mul_one, hG]
  calc
    _ = (1 + D.ghostSeries) * (D.zetaSeries * invOfUnit D.zetaSeries 1) := by ring
    _ = 1 + D.ghostSeries := by rw [hu, mul_one]

/-- Every curve datum satisfies reciprocal point-count coordinate duality. -/
theorem pointCount_reciprocalResponses :
    (1 + D.ghostSeries).subst D.inversePointCountCoordinate *
      logarithmicResponse D.inversePointCountCoordinate = 1 := by
  have h := reciprocal_logarithmicResponses
    (fun n => PowerSeries.coeff (n + 1) D.zetaSeries)
  rw [← D.pointCountCoordinate_eq_tangent, D.pointCountCoordinate_response] at h
  exact h

end CurveDatum

/-- Reciprocal coordinate duality is compatible with the corpus's explicit failure of purity. -/
theorem golden_reciprocity_without_purity :
    (1 + goldenDatum.ghostSeries).subst goldenDatum.inversePointCountCoordinate *
        logarithmicResponse goldenDatum.inversePointCountCoordinate = 1 ∧
      ¬ ∀ i, ‖goldenDatum.β i‖ = 1 :=
  ⟨goldenDatum.pointCount_reciprocalResponses, goldenDatum_not_unitary⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
