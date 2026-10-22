import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorTopNormalizer

/-! # Certified coefficients of both factors of adjugate contribution 1 -/
namespace HTGeometry

noncomputable section
set_option maxRecDepth 20000

def evenCompactGapCofactorTerm1LeftFactorCoeff0Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 0) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 0)
def evenCompactGapCofactorTerm1LeftFactorCoeff1Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 1) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 1)
def evenCompactGapCofactorTerm1LeftFactorCoeff2Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 2) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 2)
def evenCompactGapCofactorTerm1LeftFactorCoeff3Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 3) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 3)
def evenCompactGapCofactorTerm1LeftFactorCoeff4Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 4) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 4)
def evenCompactGapCofactorTerm1LeftFactorCoeff5Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 5) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 5)
def evenCompactGapCofactorTerm1LeftFactorCoeff6Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 6) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 6)
def evenCompactGapCofactorTerm1LeftFactorCoeff7Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 7) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 7)
def evenCompactGapCofactorTerm1LeftFactorCoeff8Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 8) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 8)
def evenCompactGapCofactorTerm1LeftFactorCoeff9Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 9) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 9)
def evenCompactGapCofactorTerm1LeftFactorCoeff10Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 10) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 10)
def evenCompactGapCofactorTerm1LeftFactorCoeff11Certificate (u w : ℝ) : CompactGapNormalForm
    ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 11) :=
  compactGapCofactorTopCertified% ((evenCompactGapReflectedFourPolynomial u w * evenCompactGapReflectedEightPolynomial u w - (evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 11)

def evenCompactGapCofactorTerm1RightFactorCoeff0Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 0) :=
  compactGapCofactorTopCertified% (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 0)
def evenCompactGapCofactorTerm1RightFactorCoeff1Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 1) :=
  compactGapCofactorTopCertified% (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 1)
def evenCompactGapCofactorTerm1RightFactorCoeff2Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 2) :=
  compactGapCofactorTopCertified% (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 2)
def evenCompactGapCofactorTerm1RightFactorCoeff3Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 3) :=
  compactGapCofactorTopCertified% (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 3)
def evenCompactGapCofactorTerm1RightFactorCoeff4Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 4) :=
  compactGapCofactorTopCertified% (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 4)
def evenCompactGapCofactorTerm1RightFactorCoeff5Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 5) :=
  compactGapCofactorTopCertified% (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 5)
def evenCompactGapCofactorTerm1RightFactorCoeff6Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 6) :=
  compactGapCofactorTopCertified% (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 6)
def evenCompactGapCofactorTerm1RightFactorCoeff7Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 7) :=
  compactGapCofactorTopCertified% (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 7)
def evenCompactGapCofactorTerm1RightFactorCoeff8Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 8) :=
  compactGapCofactorTopCertified% (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 8)
def evenCompactGapCofactorTerm1RightFactorCoeff9Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 9) :=
  compactGapCofactorTopCertified% (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 9)
def evenCompactGapCofactorTerm1RightFactorCoeff10Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 10) :=
  compactGapCofactorTopCertified% (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 10)
def evenCompactGapCofactorTerm1RightFactorCoeff11Certificate (u w : ℝ) : CompactGapNormalForm
    (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 11) :=
  compactGapCofactorTopCertified% (((evenCompactGapReflectedSixPolynomial u w)^(2 : ℕ)).coeff 11)

end

end HTGeometry
