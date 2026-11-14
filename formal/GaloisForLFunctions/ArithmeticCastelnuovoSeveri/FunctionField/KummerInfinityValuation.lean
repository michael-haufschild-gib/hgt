import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerInfinityCoordinate
import GaloisForLFunctions.HTGeometry.PolynomialPlaceResidue

/-!
# The pole of the Kummer branch function

In the reciprocal coordinate, the base origin gives the exact valuation
`v(c t⁻¹(1-t⁻(b+1))^R)=exp(1+(b+1)R)`. The unequal valuations of
`1` and `t⁻(b+1)` prevent cancellation. This computes the actual pole
order needed by ramification, independently of any genus formula.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable {K : Type*} [Field K]

/-- The origin in the inverted coordinate is the base place at infinity. -/
def kummerInfinityBasePlace : HeightOneSpectrum K[X] :=
  GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X (R := K))

/-- The inverted coordinate is a uniformizer at the base origin. -/
theorem kummerInfinityBasePlace_coordinate :
    (kummerInfinityBasePlace (K := K)).valuation (FractionRing K[X])
      (algebraMap K[X] (FractionRing K[X]) X) = WithZero.exp (-1 : ℤ) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton _ X_ne_zero rfl

/-- The inverse coordinate has a simple pole. -/
theorem kummerInfinityBasePlace_inverseCoordinate :
    (kummerInfinityBasePlace (K := K)).valuation (FractionRing K[X])
      (algebraMap K[X] (FractionRing K[X]) X)⁻¹ = WithZero.exp (1 : ℤ) := by
  rw [map_inv₀, kummerInfinityBasePlace_coordinate, ← WithZero.exp_neg, neg_neg]

/-- Coordinate inversion fixes constants. -/
theorem kummerCoordinateInversion_C (a : K) :
    kummerCoordinateInversion K (algebraMap K[X] (FractionRing K[X]) (C a)) =
      algebraMap K[X] (FractionRing K[X]) (C a) := by
  change kummerCoordinateInversion K (algebraMap K (FractionRing K[X]) a) =
    algebraMap K (FractionRing K[X]) a
  exact (kummerCoordinateInversion K).commutes a

/-- At infinity the branch function has pole order `1+(b+1)R`. -/
theorem kummerInfinityBasePlace_branch (c : Kˣ) (b R : ℕ) :
    (kummerInfinityBasePlace (K := K)).valuation (FractionRing K[X])
      (kummerCoordinateInversion K
        (algebraMap K[X] (FractionRing K[X]) (kummerBranch c b R))) =
      WithZero.exp ((1 + (b + 1) * R : ℕ) : ℤ) := by
  let v := (kummerInfinityBasePlace (K := K)).valuation (FractionRing K[X])
  let t := algebraMap K[X] (FractionRing K[X]) X
  have hc : v (algebraMap K[X] (FractionRing K[X]) (C (c : K))) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem _).mpr
      (GaloisForLFunctions.HTGeometry.C_notMem_span_X (Units.ne_zero c))
  have ht : v t⁻¹ = WithZero.exp (1 : ℤ) := kummerInfinityBasePlace_inverseCoordinate
  have htp : v (t⁻¹ ^ (b + 1)) = WithZero.exp (b + 1 : ℤ) := by
    rw [map_pow, ht, ← WithZero.exp_nsmul, nsmul_eq_mul]
    simp only [Nat.cast_add, Nat.cast_one, mul_one]
  have hs : v (1 - t⁻¹ ^ (b + 1)) = WithZero.exp (b + 1 : ℤ) := by
    rw [v.map_sub_eq_of_lt_right, htp]
    rw [map_one, htp, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    positivity
  change v (kummerCoordinateInversion K
    (algebraMap K[X] (FractionRing K[X]) (kummerBranch c b R))) = _
  have he : kummerCoordinateInversion K
      (algebraMap K[X] (FractionRing K[X]) (kummerBranch c b R)) =
      algebraMap K[X] (FractionRing K[X]) (C (c : K)) * t⁻¹ *
        (1 - t⁻¹ ^ (b + 1)) ^ R := by
    simp only [kummerBranch, map_mul, map_sub, map_pow, map_one,
      kummerCoordinateInversion_C, kummerCoordinateInversion_X]
    rfl
  rw [he, map_mul, map_mul, map_pow, hc, ht, hs, one_mul,
    ← WithZero.exp_nsmul, ← WithZero.exp_add]
  congr 1
  simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  ring

/-- The logarithmic valuation records the exact pole degree. -/
theorem kummerInfinityBasePlace_branch_log (c : Kˣ) (b R : ℕ) :
    ((kummerInfinityBasePlace (K := K)).valuation (FractionRing K[X])
      (kummerCoordinateInversion K
        (algebraMap K[X] (FractionRing K[X]) (kummerBranch c b R)))).log =
      ((1 + (b + 1) * R : ℕ) : ℤ) := by
  rw [kummerInfinityBasePlace_branch, WithZero.log_exp]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
