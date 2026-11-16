import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerExtensionNormalizationPoints
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.PolynomialOrderClosedPointDegrees

/-!
# Kummer extension counts from actual closed primes

The fixed three-point normalization is a finite free polynomial order.
Its closed primes contribute their residue degrees over precisely the
divisible extension degrees. The unique rational place at infinity
contributes one in every positive degree.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain PolynomialOrderClosedPoints
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
local notation "K" => SquareConstantField p (kummerSquareIndex d n)
local notation "A" => PrimePowerKummerThreePointAffineNormalization p d n r

/-- The normalization contains the polynomial ring and is therefore infinite. -/
instance primePowerKummerThreePointAffineNormalization_infinite : Infinite A :=
  Infinite.of_injective (algebraMap K[X] A) (FaithfulSMul.algebraMap_injective K[X] A)

/-- Every extension count is the literal degree sum over closed primes, with rational infinity added. -/
theorem primePowerKummerExtensionPointCount_eq_closed_degree_sum (e : ℕ) [NeZero e] :
    primePowerKummerExtensionPointCount p d n r e = 1 +
      ∑ v ∈ placesDegreeLe K A p e, if placeDegree K A v ∣ e then placeDegree K A v else 0 := by
  rw [primePowerKummerExtensionPointCount_eq_algHom,
    card_algHom_extension_eq_closed_degree_sum K A p e, Nat.add_comm]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
