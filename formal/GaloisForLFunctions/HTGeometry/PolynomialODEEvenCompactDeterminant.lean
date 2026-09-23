import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactUnitRaw
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapDeterminantIdentity
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactRelativeDeterminant
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactUnitReserve
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactRelativeHorner
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactHornerLanding

/-! # Exact determinant incidence of the positive compact polynomial certificate -/
namespace HTGeometry
noncomputable section

/-- Every determinant term lands in the positive polynomial on the physical drift domain. -/
theorem evenCompactUnitDet_eq_polynomial {r : ℝ} (hr : 0 ≤ r) (t v : ℝ) :
    evenCompactUnitDet r t v = evenCompactUnitPolynomial r t v := by
  have hs := Real.sq_sqrt hr
  calc
    evenCompactUnitDet r t v = evenCompactUnitDet ((Real.sqrt r)^2) t v := by rw [hs]
    _ = evenCompactRawDet (Real.sqrt r)
        (evenCompactUnitGap ((Real.sqrt r)^2) t) (Real.sqrt r*(1+v/4)) :=
      evenCompactUnitDet_square_eq_raw (Real.sqrt r) t v
    _ = evenCompactRawPolynomial (Real.sqrt r)
        (evenCompactUnitGap ((Real.sqrt r)^2) t) (Real.sqrt r*(1+v/4)) :=
      evenCompactRawDet_eq_polynomial _ _ _
    _ = evenCompactRelativeDet ((Real.sqrt r)^2)
        (evenCompactUnitGap ((Real.sqrt r)^2) t) v :=
      evenCompactRawPolynomial_relative_eq _ _ _
    _ = evenCompactHorner0 ((Real.sqrt r)^2) t v :=
      evenCompactRelativeDet_gap_eq_horner _ _ _
    _ = evenCompactUnitPolynomial ((Real.sqrt r)^2) t v :=
      evenCompactHorner0_eq_unitPolynomial _ _ _
    _ = evenCompactUnitPolynomial r t v := by rw [hs]

/-- The coupled even determinant model has a fixed positive reserve on the full unit cube. -/
theorem evenCompactUnitDet_lower {r t v : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    (1/1000 : ℝ) ≤ evenCompactUnitDet r t v := by
  rw [evenCompactUnitDet_eq_polynomial hr0]
  exact evenCompactUnitPolynomial_lower hr0 hr1 ht0 ht1 hv0 hv1

end
end HTGeometry
