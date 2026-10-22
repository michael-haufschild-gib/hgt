import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapReversedDet

/-!
# Hankel groups of the reversed determinant

The reversed four-by-four Hankel determinant is the sum of eleven groups of
its expansion. Each group carries the same weight `100^(-12)`, and the groups add
up to the determinant by a ring identity in the seven reflected entries.
-/

namespace HTGeometry
noncomputable section
open GaloisForLFunctions.HTGeometry
set_option maxRecDepth 10000

/-- The reflected squared zeroth source entry. -/
def evenCompactGapReversedEntryA (u : ℝ) : Polynomial ℝ :=
  (Polynomial.reflect 1 (evenCompactGapSourceZeroPolynomial u))^(2 : ℕ)

/-- The reflected second source entry. -/
def evenCompactGapReversedEntryB (u w : ℝ) : Polynomial ℝ :=
  -Polynomial.reflect 3 (evenCompactGapReflectedTwoPolynomial u w)

/-- The reflected fourth source entry. -/
def evenCompactGapReversedEntryC (u w : ℝ) : Polynomial ℝ :=
  Polynomial.reflect 4 (evenCompactGapReflectedFourPolynomial u w)

/-- The reflected sixth source entry. -/
def evenCompactGapReversedEntryD (u w : ℝ) : Polynomial ℝ :=
  -Polynomial.reflect 5 (evenCompactGapReflectedSixPolynomial u w)

/-- The reflected eighth source entry. -/
def evenCompactGapReversedEntryE (u w : ℝ) : Polynomial ℝ :=
  Polynomial.reflect 6 (evenCompactGapReflectedEightPolynomial u w)

/-- The reflected tenth source entry. -/
def evenCompactGapReversedEntryF (u w : ℝ) : Polynomial ℝ :=
  -Polynomial.reflect 7 (evenCompactGapReflectedTenPolynomial u w)

/-- The reflected twelfth source entry with the fixed correction. -/
def evenCompactGapReversedEntryG (u w : ℝ) : Polynomial ℝ :=
  Polynomial.reflect 8 (evenCompactGapReflectedTwelvePolynomial u w)+
    Polynomial.reflect 8 (evenCompactGapCorrectionPolynomial u)

/-- The reversed determinant restricted to the leading three-minor term. -/
def evenCompactGapReversedDetGroup0 (u w : ℝ) : Polynomial ℝ :=
  evenCompactGapReversedEntryA u*evenCompactGapReversedEntryC u w*evenCompactGapReversedEntryE u w*evenCompactGapReversedEntryG u w * Polynomial.C (((100 : ℝ)^(12 : ℕ))⁻¹)

/-- The reversed determinant restricted to the squared sixth-entry term. -/
def evenCompactGapReversedDetGroup1 (u w : ℝ) : Polynomial ℝ :=
  -(evenCompactGapReversedEntryA u*evenCompactGapReversedEntryD u w^(2 : ℕ)*evenCompactGapReversedEntryG u w) * Polynomial.C (((100 : ℝ)^(12 : ℕ))⁻¹)

/-- The reversed determinant restricted to the squared second-entry term. -/
def evenCompactGapReversedDetGroup2 (u w : ℝ) : Polynomial ℝ :=
  -(evenCompactGapReversedEntryB u w^(2 : ℕ)*evenCompactGapReversedEntryE u w*evenCompactGapReversedEntryG u w) * Polynomial.C (((100 : ℝ)^(12 : ℕ))⁻¹)

/-- The reversed determinant restricted to the mixed second-fourth-sixth term. -/
def evenCompactGapReversedDetGroup3 (u w : ℝ) : Polynomial ℝ :=
  2*evenCompactGapReversedEntryB u w*evenCompactGapReversedEntryC u w*evenCompactGapReversedEntryD u w*evenCompactGapReversedEntryG u w * Polynomial.C (((100 : ℝ)^(12 : ℕ))⁻¹)

/-- The reversed determinant restricted to the cubed fourth-entry term. -/
def evenCompactGapReversedDetGroup4 (u w : ℝ) : Polynomial ℝ :=
  -(evenCompactGapReversedEntryC u w^(3 : ℕ)*evenCompactGapReversedEntryG u w) * Polynomial.C (((100 : ℝ)^(12 : ℕ))⁻¹)

/-- The reversed determinant restricted to the first adjugate term. -/
def evenCompactGapReversedDetGroup5 (u w : ℝ) : Polynomial ℝ :=
  -((evenCompactGapReversedEntryC u w*evenCompactGapReversedEntryE u w - evenCompactGapReversedEntryD u w^(2 : ℕ))*evenCompactGapReversedEntryD u w^(2 : ℕ)) * Polynomial.C (((100 : ℝ)^(12 : ℕ))⁻¹)

/-- The reversed determinant restricted to the second adjugate term. -/
def evenCompactGapReversedDetGroup6 (u w : ℝ) : Polynomial ℝ :=
  -(2*(evenCompactGapReversedEntryC u w*evenCompactGapReversedEntryD u w - evenCompactGapReversedEntryB u w*evenCompactGapReversedEntryE u w)*evenCompactGapReversedEntryD u w*evenCompactGapReversedEntryE u w) * Polynomial.C (((100 : ℝ)^(12 : ℕ))⁻¹)

/-- The reversed determinant restricted to the third adjugate term. -/
def evenCompactGapReversedDetGroup7 (u w : ℝ) : Polynomial ℝ :=
  -(2*(evenCompactGapReversedEntryB u w*evenCompactGapReversedEntryD u w - evenCompactGapReversedEntryC u w^(2 : ℕ))*evenCompactGapReversedEntryD u w*evenCompactGapReversedEntryF u w) * Polynomial.C (((100 : ℝ)^(12 : ℕ))⁻¹)

/-- The reversed determinant restricted to the fourth adjugate term. -/
def evenCompactGapReversedDetGroup8 (u w : ℝ) : Polynomial ℝ :=
  -((evenCompactGapReversedEntryA u*evenCompactGapReversedEntryE u w - evenCompactGapReversedEntryC u w^(2 : ℕ))*evenCompactGapReversedEntryE u w^(2 : ℕ)) * Polynomial.C (((100 : ℝ)^(12 : ℕ))⁻¹)

/-- The reversed determinant restricted to the fifth adjugate term. -/
def evenCompactGapReversedDetGroup9 (u w : ℝ) : Polynomial ℝ :=
  -(2*(evenCompactGapReversedEntryB u w*evenCompactGapReversedEntryC u w - evenCompactGapReversedEntryA u*evenCompactGapReversedEntryD u w)*evenCompactGapReversedEntryE u w*evenCompactGapReversedEntryF u w) * Polynomial.C (((100 : ℝ)^(12 : ℕ))⁻¹)

/-- The reversed determinant restricted to the sixth adjugate term. -/
def evenCompactGapReversedDetGroup10 (u w : ℝ) : Polynomial ℝ :=
  -((evenCompactGapReversedEntryA u*evenCompactGapReversedEntryC u w - evenCompactGapReversedEntryB u w^(2 : ℕ))*evenCompactGapReversedEntryF u w^(2 : ℕ)) * Polynomial.C (((100 : ℝ)^(12 : ℕ))⁻¹)

/-- The eleven Hankel groups add up to the reversed determinant. -/
theorem evenCompactGapReversedDetPolynomial_groups (u w : ℝ) :
    evenCompactGapReversedDetPolynomial u w =
      evenCompactGapReversedDetGroup0 u w +
      evenCompactGapReversedDetGroup1 u w +
      evenCompactGapReversedDetGroup2 u w +
      evenCompactGapReversedDetGroup3 u w +
      evenCompactGapReversedDetGroup4 u w +
      evenCompactGapReversedDetGroup5 u w +
      evenCompactGapReversedDetGroup6 u w +
      evenCompactGapReversedDetGroup7 u w +
      evenCompactGapReversedDetGroup8 u w +
      evenCompactGapReversedDetGroup9 u w +
      evenCompactGapReversedDetGroup10 u w := by
  unfold evenCompactGapReversedDetPolynomial hankelFourDet
    evenCompactGapReversedDetGroup0 evenCompactGapReversedDetGroup1 evenCompactGapReversedDetGroup2 evenCompactGapReversedDetGroup3 evenCompactGapReversedDetGroup4 evenCompactGapReversedDetGroup5 evenCompactGapReversedDetGroup6 evenCompactGapReversedDetGroup7 evenCompactGapReversedDetGroup8 evenCompactGapReversedDetGroup9 evenCompactGapReversedDetGroup10 evenCompactGapReversedEntryA evenCompactGapReversedEntryB evenCompactGapReversedEntryC evenCompactGapReversedEntryD evenCompactGapReversedEntryE evenCompactGapReversedEntryF evenCompactGapReversedEntryG
  ring

end
end HTGeometry
