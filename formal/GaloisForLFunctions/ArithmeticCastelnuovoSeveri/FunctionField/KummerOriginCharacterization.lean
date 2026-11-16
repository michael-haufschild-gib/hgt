import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerOriginFunctionOrders
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.ValuationPrincipalDivisors
import Mathlib.RingTheory.KrullDimension.Basic

/-!
# The unique finite zero of the Kummer coordinate

A normalization prime contains the base coordinate precisely when it
lies over the polynomial origin. Total ramification makes that prime
unique. Thus the coordinate has valuation one at every other finite place.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)
local notation "K" => SquareConstantField p s
local notation "L" => SquareKummerField p s c b R
local notation "B" => SquareKummerNormalization p s c b R

/-- A finite normalization prime contains the coordinate exactly when it is the unique origin prime. -/
theorem squareKummerOriginPlace_eq_iff_coordinate_mem (w : HeightOneSpectrum B) :
    w = squareKummerOriginPlace p s c b R ↔ algebraMap K[X] B X ∈ w.asIdeal := by
  constructor
  · rintro rfl
    exact (Ideal.mem_of_liesOver (squareKummerOriginIdeal p s c b R)
      (Ideal.span {(X : K[X])}) X).mp (Ideal.mem_span_singleton_self _)
  · intro hx
    have hover : w.asIdeal.LiesOver (Ideal.span {(X : K[X])}) :=
      (Ideal.liesOver_span_iff w.isPrime.ne_top (irreducible_X (R := K)).prime).mpr hx
    apply HeightOneSpectrum.ext
    exact (squareKummer_origin_unique p s c b R).choose_spec.2 w.asIdeal ⟨w.isPrime, hover⟩

/-- The original coordinate has valuation one at every finite place other than the origin. -/
theorem squareKummer_coordinate_valuation_one_of_ne_origin (w : HeightOneSpectrum B)
    (hw : w ≠ squareKummerOriginPlace p s c b R) :
    w.valuation L (algebraMap K[X] L X) = 1 := by
  rw [IsScalarTower.algebraMap_apply K[X] B L]
  apply (HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr
  intro hx
  exact hw ((squareKummerOriginPlace_eq_iff_coordinate_mem p s c b R w).mpr hx)

/-- A strictly positive zero order of the base coordinate identifies the actual origin place. -/
theorem squareKummerOriginPlace_eq_of_coordinate_lt_one (w : HeightOneSpectrum B)
    (hw : w.valuation L (algebraMap K[X] L X) < 1) :
    w = squareKummerOriginPlace p s c b R := by
  by_contra hne
  rw [squareKummer_coordinate_valuation_one_of_ne_origin p s c b R w hne] at hw
  exact lt_irrefl _ hw

open Classical in
/-- The complete finite valuation formula for the original Kummer coordinate. -/
theorem squareKummer_coordinate_valuation (w : HeightOneSpectrum B) :
    w.valuation L (algebraMap K[X] L X) =
      if w = squareKummerOriginPlace p s c b R then
        WithZero.exp (-((p ^ (s + 1) + 1 : ℕ) : ℤ)) else 1 := by
  classical
  by_cases hw : w = squareKummerOriginPlace p s c b R
  · subst w
    rw [if_pos rfl]
    exact squareKummerOriginValuation_coordinate p s c b R
  · rw [if_neg hw]
    exact squareKummer_coordinate_valuation_one_of_ne_origin p s c b R w hw

/-- The complete finite principal valuation divisor of the coordinate is concentrated at the origin. -/
theorem squareKummerCoordinate_finiteValuationDivisor :
    finiteValuationDivisor B L (algebraMap K[X] L X) =
      Finsupp.single (squareKummerOriginPlace p s c b R) (-((p ^ (s + 1) + 1 : ℕ) : ℤ)) := by
  classical
  ext w
  rw [finiteValuationDivisor_apply]
  by_cases hw : w = squareKummerOriginPlace p s c b R
  · subst w
    rw [Finsupp.single_eq_same]
    change WithZero.log (squareKummerOriginValuation p s c b R _) = _
    rw [squareKummerOriginValuation_coordinate, WithZero.log_exp]
  · rw [Finsupp.single_eq_of_ne hw,
      squareKummer_coordinate_valuation_one_of_ne_origin p s c b R w hw, WithZero.log_one]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
