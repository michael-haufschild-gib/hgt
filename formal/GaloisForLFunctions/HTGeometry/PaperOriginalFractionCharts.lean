import GaloisForLFunctions.HTGeometry.PaperFiberClockGeometry
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.Degree
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.LocalizationIntersection
import GaloisForLFunctions.HTGeometry.FreeCoordinateField
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Two rational charts recover the original polynomial algebra

The exact source polynomial is prime because its zero fibre is affine space.
Its proved degree excludes divisibility of any coordinate variable. The source
two-denominator theorem therefore identifies the intersection of the `f` chart
and any coordinate chart inside the native rational function field.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate

noncomputable section

/-- The distinguished polynomial is prime in the actual four-variable ring. -/
theorem paperOriginalPolynomial_prime : Prime f := by
  have hf : f ≠ 0 := by
    intro h
    have hd := f_totalDegree
    simp [h] at hd
  apply (Ideal.span_singleton_prime hf).mp
  simpa [fiberIdeal] using paperFiberIdeal_isPrime 0

/-- The distinguished prime polynomial is relatively prime to each original coordinate. -/
theorem paperOriginalPolynomial_isRelPrime_coordinate (i : Fin 4) :
    IsRelPrime f (MvPolynomial.X i : R 4) := by
  apply paperOriginalPolynomial_prime.irreducible.isRelPrime_iff_not_dvd.mpr
  intro h
  have hd := MvPolynomial.totalDegree_le_of_dvd_of_isDomain h (MvPolynomial.X_ne_zero i)
  rw [f_totalDegree, MvPolynomial.totalDegree_X] at hd
  omega

/-- Rational functions whose denominator is a power of the distinguished polynomial. -/
def paperOriginalPolynomialChart :
    Subalgebra (R 4) (FreeCoordinateRationalField ℂ (Fin 4)) :=
  awayInFractionField _ f paperOriginalPolynomial_prime.ne_zero

/-- Rational functions whose denominator is a power of one original coordinate. -/
def paperOriginalCoordinateChart (i : Fin 4) :
    Subalgebra (R 4) (FreeCoordinateRationalField ℂ (Fin 4)) :=
  awayInFractionField _ (MvPolynomial.X i) (MvPolynomial.X_ne_zero i)

/-- The two actual rational charts intersect exactly in the original polynomial algebra. -/
theorem paperOriginalFractionCharts_intersection (i : Fin 4) :
    paperOriginalPolynomialChart ⊓ paperOriginalCoordinateChart i = ⊥ :=
  awayInFractionField_inf_eq_bot _ paperOriginalPolynomial_prime.ne_zero
    (MvPolynomial.X_ne_zero i) (paperOriginalPolynomial_isRelPrime_coordinate i)

/-- Independent denominator certificates force an actual polynomial representative. -/
theorem paperOriginalFractionCharts_mem_iff (i : Fin 4)
    (q : FreeCoordinateRationalField ℂ (Fin 4)) :
    (q ∈ paperOriginalPolynomialChart ∧ q ∈ paperOriginalCoordinateChart i) ↔
      ∃ p : R 4, algebraMap (R 4) (FreeCoordinateRationalField ℂ (Fin 4)) p = q := by
  change q ∈ paperOriginalPolynomialChart ⊓ paperOriginalCoordinateChart i ↔ _
  rw [paperOriginalFractionCharts_intersection]
  exact Algebra.mem_bot

end

end GaloisForLFunctions.HTGeometry
