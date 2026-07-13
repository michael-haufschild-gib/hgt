import GaloisForLFunctions.HTGeometry.MvPolynomialCoefficientRegular
import Mathlib.RingTheory.Localization.AtPrime.Basic

namespace GaloisForLFunctions.HTGeometry

open scoped nonZeroDivisors

noncomputable section

/-- A row polynomial becomes a non-zero-divisor after localization at any coefficient prime that
does not contain one of its coefficients. -/
theorem primeLocalized_finMvPolynomial_mem_nonZeroDivisors_of_coeff_not_mem
    {A : Type*} [CommRing A] (p : Ideal A) [p.IsPrime]
    (n : ℕ) (P : MvPolynomial (Fin n) A) (m : Fin n →₀ ℕ)
    (hm : P.coeff m ∉ p) :
    MvPolynomial.map (algebraMap A (Localization.AtPrime p)) P ∈
      nonZeroDivisors (MvPolynomial (Fin n) (Localization.AtPrime p)) := by
  apply finMvPolynomial_mem_nonZeroDivisors_of_coeff_mem n _ m
  rw [MvPolynomial.coeff_map]
  rw [← isRegular_iff_mem_nonZeroDivisors]
  exact IsUnit.isRegular (IsLocalization.map_units (M := p.primeCompl)
    (Localization.AtPrime p) ⟨P.coeff m, hm⟩)

end
end GaloisForLFunctions.HTGeometry
