import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerCoordinateCartier

/-!
# Exact lower monomial differentials in every function

For any function `t`, the form `t^i dt` has the expected polynomial
primitive whenever `i+1<p`. Thus coefficient extraction annihilates
these lower powers without any assumption that `t` is a coordinate.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)
local notation "K" => SquareConstantField p s
local notation "L" => SquareKummerField p s c b R

/-- Every lower monomial differential in any function has its usual divided-power primitive. -/
theorem squareKummer_lower_monomial_primitive (t : L) (i : ℕ) (hi : i < p - 1) :
    KaehlerDifferential.D K L
      (algebraMap K L (((i + 1 : ℕ) : K)⁻¹) * t ^ (i + 1)) =
        t ^ i • KaehlerDifferential.D K L t := by
  let D := KaehlerDifferential.D K L
  have hn : ((i + 1 : ℕ) : L) ≠ 0 := by
    rw [CharP.cast_eq_zero_iff L p]
    intro hd
    have hp := Nat.le_of_dvd (Nat.succ_pos i) hd
    omega
  rw [D.leibniz, D.map_algebraMap, smul_zero, add_zero, D.leibniz_pow,
    Nat.add_sub_cancel, ← Nat.cast_smul_eq_nsmul L, smul_smul,
    map_inv₀, map_natCast, inv_mul_cancel₀ hn, one_smul]

/-- Coefficient extraction annihilates lower monomial differentials in every function. -/
theorem squareKummerCoordinateCartier_lower_monomial (t : L) (i : ℕ) (hi : i < p - 1) :
    squareKummerCoordinateCartier p s c b R
      (t ^ i • KaehlerDifferential.D K L t) = 0 := by
  rw [← squareKummer_lower_monomial_primitive p s c b R t i hi,
    squareKummerCoordinateCartier_D]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
