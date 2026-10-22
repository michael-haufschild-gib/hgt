import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapGrade0
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapGrade1
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapGrade2
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapGrade3
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapGrade4
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapGrade5
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapGrade6
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapGrade7
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapGrade8
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapGrade9
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapGrade10
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapGrade11
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapGrade12
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapGrade13
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapGrade14
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapGrade15
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapGrade16
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapGrade17
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapGrade18
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapGrade19
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapGrade20
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactModel

/-! # Full corrected determinant in the original modular coordinates -/
namespace HTGeometry
noncomputable section
set_option maxRecDepth 100000
set_option pp.deepTerms false
set_option pp.maxSteps 1000

open GaloisForLFunctions.HTGeometry

/-- Full signed source determinant with the stronger correction, in fixed units. -/
def evenCompactRawDet (u a w : ℝ) : ℝ :=
  hankelFourDet ((oddCompactSourceZero u a)^(2 : ℕ)) (-oddCompactReflectedScalar2 u a w)
    (oddCompactReflectedScalar4 u a w) (-oddCompactReflectedScalar6 u a w)
    (oddCompactReflectedScalar8 u a w) (-oddCompactReflectedScalar10 u a w)
    (evenCompactReflectedScalar12 u a w+1000000000000*oddCompactSourceZero u a*
      (3*oddCompactSourceZero u a-6/19))/(100 : ℝ)^(12 : ℕ)

/-- Gap grading of every coefficient of the corrected raw determinant. -/
def evenCompactRawPolynomial (u a w : ℝ) : ℝ :=
  ((((evenCompactRawGapGrade0 u w +
    (a^(1 : ℕ)*evenCompactRawGapGrade1 u w) : ℝ) +
    ((a^(2 : ℕ)*evenCompactRawGapGrade2 u w) +
    ((a^(3 : ℕ)*evenCompactRawGapGrade3 u w) +
    (a^(4 : ℕ)*evenCompactRawGapGrade4 u w) : ℝ) : ℝ) : ℝ) +
    (((a^(5 : ℕ)*evenCompactRawGapGrade5 u w) +
    (a^(6 : ℕ)*evenCompactRawGapGrade6 u w) : ℝ) +
    ((a^(7 : ℕ)*evenCompactRawGapGrade7 u w) +
    ((a^(8 : ℕ)*evenCompactRawGapGrade8 u w) +
    (a^(9 : ℕ)*evenCompactRawGapGrade9 u w) : ℝ) : ℝ) : ℝ) : ℝ) +
    ((((a^(10 : ℕ)*evenCompactRawGapGrade10 u w) +
    (a^(11 : ℕ)*evenCompactRawGapGrade11 u w) : ℝ) +
    ((a^(12 : ℕ)*evenCompactRawGapGrade12 u w) +
    ((a^(13 : ℕ)*evenCompactRawGapGrade13 u w) +
    (a^(14 : ℕ)*evenCompactRawGapGrade14 u w) : ℝ) : ℝ) : ℝ) +
    (((a^(15 : ℕ)*evenCompactRawGapGrade15 u w) +
    ((a^(16 : ℕ)*evenCompactRawGapGrade16 u w) +
    (a^(17 : ℕ)*evenCompactRawGapGrade17 u w) : ℝ) : ℝ) +
    ((a^(18 : ℕ)*evenCompactRawGapGrade18 u w) +
    ((a^(19 : ℕ)*evenCompactRawGapGrade19 u w) +
    (a^(20 : ℕ)*evenCompactRawGapGrade20 u w) : ℝ) : ℝ) : ℝ) : ℝ) : ℝ)

end
end HTGeometry
