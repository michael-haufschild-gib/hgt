import GaloisForLFunctions.HTGeometry.PolynomialPlaceResidue
import Mathlib.NumberTheory.RamificationInertia.Valuation

/-!
# Rational places and polynomial multiplicities

The normalized adic valuation at `X-a` is the negative root multiplicity
of a polynomial. Nonzero constants have value one at every height-one
place of a constant-field algebra. Together these identify the local
orders and constant characters in Kummer ramification calculations.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable {K : Type*} [Field K]

/-- At a rational base place, the adic valuation is the negative root multiplicity. -/
theorem polynomial_linearPlace_valuation (a : K) (f : K[X]) (hf : f ≠ 0) :
    (GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C a)).valuation (FractionRing K[X])
      (algebraMap K[X] (FractionRing K[X]) f) =
      WithZero.exp (-(f.rootMultiplicity a : ℤ)) := by
  classical
  rw [HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hf,
    rootMultiplicity_eq_multiplicity, if_neg hf]
  have hm : multiplicity (Ideal.span {X - C a}) (Ideal.span {f}) =
      multiplicity (X - C a) f :=
    multiplicity_eq_of_emultiplicity_eq Ideal.emultiplicity_eq_emultiplicity_span
  change WithZero.exp (-(multiplicity (Ideal.span {X - C a}) (Ideal.span {f}) : ℤ)) = _
  rw [hm]

/-- Nonzero constants have valuation one at every place of a constant-field algebra. -/
theorem heightOne_valuation_constant {B L : Type*} [CommRing B] [IsDedekindDomain B]
    [Algebra K B] [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L]
    [IsScalarTower K B L] (w : HeightOneSpectrum B) (a : K) (ha : a ≠ 0) :
    w.valuation L (algebraMap K L a) = 1 := by
  rw [IsScalarTower.algebraMap_apply K B L]
  apply (HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr
  intro hm
  have hu : IsUnit (algebraMap K B a) :=
    (isUnit_iff_ne_zero.mpr ha).map (algebraMap K B)
  exact w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem w.asIdeal hm hu)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
