import GaloisForLFunctions.RHTower.PolynomialFockCriticalPrimeSampling
import GaloisForLFunctions.RHTower.PositiveXiDeterminantExclusion

/-!
# Literal polynomial-Fock critical-prime determinant exclusion

The literal critical-prime sampling incidence is positive. Consequently, whenever a
Hilbert--Schmidt kernel represents that operator on the moment-Fock coefficient model, its
Hilbert--Carleman determinant cannot equal centered Xi through any zero-free gauge.
-/

open Complex
open HilbertSchmidt

namespace RHTower

noncomputable section

/-- The actual polynomial critical-prime incidence cannot be an exact Xi determinant carrier.
This exclusion uses its proved positivity and the unconditional two-sided Xi divisor, and therefore
does not assume the still-stronger exact polynomial-Fock Schatten threshold law. -/
theorem polynomialCriticalPrimeSamplingIncidence_not_exactXiDeterminant
    (m : ℝ) (hm : 4 ≤ m)
    {K : ℕ × ℕ → ℂ} (hK : IsHS K)
    (hoperator : toOperator hK = polynomialCriticalPrimeSamplingIncidence m hm)
    (H : ℂ → ℂ) (hH : ∀ z, H z ≠ 0) :
    ¬ (∀ z, XiC z = H z *
      GaloisForLFunctions.HTGeometry.entireDet2 K z) := by
  have hpos : (toOperator hK).IsPositive := by
    rw [hoperator]
    exact polynomialCriticalPrimeSamplingIncidence_isPositive m hm
  exact positiveOperator_not_exactXiDeterminant hK hpos H hH

/-- No finite-degree polynomial critical-prime incidence admits an exact Xi spectral determinant
of any regularization order.  The statement uses only the defining nonzero-zero law shared by all
regularized determinant orders. -/
theorem polynomialCriticalPrimeSamplingIncidence_not_exists_exactXiSpectralZeroFunction :
    ¬ ∃ (m : ℝ) (hm : 4 ≤ m) (D H : ℂ → ℂ),
      HasReciprocalEigenvalueZeroSet
        (polynomialCriticalPrimeSamplingIncidence m hm) D ∧
      (∀ z, H z ≠ 0) ∧
      (∀ z, XiC z = H z * D z) := by
  rintro ⟨m, hm, D, H, hzeros, hH, hXi⟩
  exact positiveOperator_not_exactXiSpectralZeroFunction
    (polynomialCriticalPrimeSamplingIncidence_isPositive m hm)
    ⟨D, H, hzeros, hH, hXi⟩

end

end RHTower
