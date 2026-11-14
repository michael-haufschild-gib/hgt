import GaloisForLFunctions.HTGeometry.PolynomialPlaceResidue
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.RingTheory.AdjoinRoot

/-!
# Finite places and polynomial multiplicities

The normalized adic valuation at an irreducible polynomial is its
negative multiplicity; at `X-a` this is root multiplicity. Residue fields
of finite places over finite constants are finite. Nonzero constants have value one at every height-one
place of a constant-field algebra. Together these identify the local
orders and constant characters in Kummer ramification calculations.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable {K : Type*} [Field K]

/-- Polynomial multiplicity computes the normalized valuation at an arbitrary finite place. -/
theorem polynomial_irreduciblePlace_valuation {π : K[X]} (hπ : Irreducible π)
    (f : K[X]) (hf : f ≠ 0) :
    (GaloisForLFunctions.HTGeometry.polyPlace hπ).valuation (FractionRing K[X])
      (algebraMap K[X] (FractionRing K[X]) f) =
      WithZero.exp (-(multiplicity π f : ℤ)) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hf]
  have hm : multiplicity (Ideal.span {π}) (Ideal.span {f}) = multiplicity π f :=
    multiplicity_eq_of_emultiplicity_eq Ideal.emultiplicity_eq_emultiplicity_span
  change WithZero.exp (-(multiplicity (Ideal.span {π}) (Ideal.span {f}) : ℤ)) = _
  rw [hm]

/-- Every irreducible polynomial over a finite field has finite ideal residue field. -/
theorem polynomial_irreduciblePlace_finite_residue [Finite K]
    {π : K[X]} (hπ : Irreducible π) :
    Finite (GaloisForLFunctions.HTGeometry.polyPlace hπ).asIdeal.ResidueField := by
  let v := GaloisForLFunctions.HTGeometry.polyPlace hπ
  letI : (Ideal.span {π}).IsMaximal := v.isPrime.isMaximal v.ne_bot
  letI : Module.Finite K (AdjoinRoot π) := (AdjoinRoot.powerBasis hπ.ne_zero).finite
  letI : Finite (AdjoinRoot π) := Module.finite_of_finite K
  exact Finite.of_equiv (AdjoinRoot π)
    (GaloisForLFunctions.HTGeometry.quotientEquivIdealResidueField (Ideal.span {π})).toEquiv

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
