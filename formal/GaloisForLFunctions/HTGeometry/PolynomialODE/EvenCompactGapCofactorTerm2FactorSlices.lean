import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorTopNormalizer

/-! # Certified coefficients of both factors of adjugate contribution 2 -/
namespace HTGeometry

noncomputable section
set_option maxRecDepth 20000

def evenCompactGapCofactorTerm2LeftFactorCoeff0Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 0) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 0)
def evenCompactGapCofactorTerm2LeftFactorCoeff1Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 1) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 1)
def evenCompactGapCofactorTerm2LeftFactorCoeff2Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 2) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 2)
def evenCompactGapCofactorTerm2LeftFactorCoeff3Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 3) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 3)
def evenCompactGapCofactorTerm2LeftFactorCoeff4Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 4) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 4)
def evenCompactGapCofactorTerm2LeftFactorCoeff5Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 5) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 5)
def evenCompactGapCofactorTerm2LeftFactorCoeff6Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 6) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 6)
def evenCompactGapCofactorTerm2LeftFactorCoeff7Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 7) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 7)
def evenCompactGapCofactorTerm2LeftFactorCoeff8Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 8) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 8)
def evenCompactGapCofactorTerm2LeftFactorCoeff9Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 9) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 9)
def evenCompactGapCofactorTerm2LeftFactorCoeff10Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 10) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 10)
def evenCompactGapCofactorTerm2LeftFactorCoeff11Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 11) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedSixPolynomial u w - evenCompactGapReflectedTwoPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 11)

def evenCompactGapCofactorTerm2RightFactorCoeff0Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 0) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 0)
def evenCompactGapCofactorTerm2RightFactorCoeff1Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 1) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 1)
def evenCompactGapCofactorTerm2RightFactorCoeff2Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 2) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 2)
def evenCompactGapCofactorTerm2RightFactorCoeff3Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 3) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 3)
def evenCompactGapCofactorTerm2RightFactorCoeff4Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 4) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 4)
def evenCompactGapCofactorTerm2RightFactorCoeff5Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 5) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 5)
def evenCompactGapCofactorTerm2RightFactorCoeff6Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 6) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 6)
def evenCompactGapCofactorTerm2RightFactorCoeff7Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 7) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 7)
def evenCompactGapCofactorTerm2RightFactorCoeff8Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 8) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 8)
def evenCompactGapCofactorTerm2RightFactorCoeff9Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 9) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 9)
def evenCompactGapCofactorTerm2RightFactorCoeff10Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 10) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 10)
def evenCompactGapCofactorTerm2RightFactorCoeff11Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 11) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedSixPolynomial u w * evenCompactGapReflectedEightPolynomial u w).coeff 11)

end

end HTGeometry
