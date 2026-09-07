import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapReversedDet

/-! # Exact cofactor decomposition before source-coefficient normalization -/
namespace HTGeometry
noncomputable section
open GaloisForLFunctions.HTGeometry
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

/-- The complete leading three-by-three determinant in signed source coordinates. -/
def evenCompactGapHeadPolynomial (u w : ℝ) : Polynomial ℝ :=
  (evenCompactGapSourceZeroPolynomial u)^2 * evenCompactGapReflectedFourPolynomial u w *
      evenCompactGapReflectedEightPolynomial u w -
    (evenCompactGapSourceZeroPolynomial u)^2 * (evenCompactGapReflectedSixPolynomial u w)^2 -
    (evenCompactGapReflectedTwoPolynomial u w)^2 * evenCompactGapReflectedEightPolynomial u w +
    2 * evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedFourPolynomial u w *
      evenCompactGapReflectedSixPolynomial u w -
    (evenCompactGapReflectedFourPolynomial u w)^3

/-- Leading cofactor times the complete corrected final source entry. -/
def evenCompactGapCofactorTerm0 (u w : ℝ) : Polynomial ℝ :=
  evenCompactGapHeadPolynomial u w *
    (evenCompactGapReflectedTwelvePolynomial u w + evenCompactGapCorrectionPolynomial u)

/-- First adjugate contribution. -/
def evenCompactGapCofactorTerm1 (u w : ℝ) : Polynomial ℝ :=
  (evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w -
    (evenCompactGapReflectedSixPolynomial u w)^2) *
    (evenCompactGapReflectedSixPolynomial u w)^2

/-- Second adjugate contribution, retaining its signed cofactor. -/
def evenCompactGapCofactorTerm2 (u w : ℝ) : Polynomial ℝ :=
  2 * (evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w -
    evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w) *
    evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w

/-- Third adjugate contribution. -/
def evenCompactGapCofactorTerm3 (u w : ℝ) : Polynomial ℝ :=
  2 * (evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedSixPolynomial u w -
    (evenCompactGapReflectedFourPolynomial u w)^2) *
    evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedTenPolynomial u w

/-- Fourth adjugate contribution. -/
def evenCompactGapCofactorTerm4 (u w : ℝ) : Polynomial ℝ :=
  ((evenCompactGapSourceZeroPolynomial u)^2 * evenCompactGapReflectedEightPolynomial u w -
    (evenCompactGapReflectedFourPolynomial u w)^2) *
    (evenCompactGapReflectedEightPolynomial u w)^2

/-- Fifth adjugate contribution, retaining its signed cofactor. -/
def evenCompactGapCofactorTerm5 (u w : ℝ) : Polynomial ℝ :=
  2 * (evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedFourPolynomial u w -
    (evenCompactGapSourceZeroPolynomial u)^2 * evenCompactGapReflectedSixPolynomial u w) *
    evenCompactGapReflectedEightPolynomial u w * evenCompactGapReflectedTenPolynomial u w

/-- Sixth adjugate contribution. -/
def evenCompactGapCofactorTerm6 (u w : ℝ) : Polynomial ℝ :=
  ((evenCompactGapSourceZeroPolynomial u)^2 * evenCompactGapReflectedFourPolynomial u w -
    (evenCompactGapReflectedTwoPolynomial u w)^2) *
    (evenCompactGapReflectedTenPolynomial u w)^2

attribute [local irreducible] evenCompactGapSourceZeroPolynomial
  evenCompactGapReflectedTwoPolynomial evenCompactGapReflectedFourPolynomial
  evenCompactGapReflectedSixPolynomial evenCompactGapReflectedEightPolynomial
  evenCompactGapReflectedTenPolynomial evenCompactGapReflectedTwelvePolynomial

/-- Exact cofactor splitting of the full determinant, without sign assumptions. -/
theorem evenCompactGapDetPolynomial_cofactor_eq (u w : ℝ) :
    evenCompactGapDetPolynomial u w =
      (evenCompactGapCofactorTerm0 u w -
        (evenCompactGapCofactorTerm1 u w + evenCompactGapCofactorTerm2 u w +
          evenCompactGapCofactorTerm3 u w + evenCompactGapCofactorTerm4 u w +
          evenCompactGapCofactorTerm5 u w + evenCompactGapCofactorTerm6 u w)) *
        Polynomial.C (((100 : ℝ)^12)⁻¹) := by
  dsimp only [evenCompactGapDetPolynomial, hankelFourDet, evenCompactGapHeadPolynomial,
    evenCompactGapCofactorTerm0, evenCompactGapCofactorTerm1, evenCompactGapCofactorTerm2,
    evenCompactGapCofactorTerm3, evenCompactGapCofactorTerm4, evenCompactGapCofactorTerm5,
    evenCompactGapCofactorTerm6, evenCompactGapCorrectionPolynomial]
  ring1

end
end HTGeometry
