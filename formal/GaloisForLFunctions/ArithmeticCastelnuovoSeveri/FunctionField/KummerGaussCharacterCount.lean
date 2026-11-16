import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FiniteFieldPowerCharacterCounts
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointCyclic
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRegularDifferentialDimension

/-!
# Gauss characters and the intrinsic Kummer genus

In the full cyclic character group, raising a character to `(q-1)R`
has kernel of size `(q-1)gcd(N,R)`. The remaining characters number
`(q-1)(N-gcd(N,R))`, exactly twice the dimension of the actual global
regular differential space. The same count holds in every finite
extension of the stated constant field, with the covering degree fixed.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
local notation "s" => kummerSquareIndex d n
local notation "K" => SquareConstantField p s
local notation "N" => p ^ (s + 1) + 1
local notation "m" => p ^ (d + 1) - 1
local notation "R" => kummerExponent (p ^ (d + 1)) r
local notation "M" => primePowerKummerCyclicDegree p d n
variable (E : Type*) [Field E] [Finite E]
    [Algebra (SquareConstantField p (kummerSquareIndex d n)) E]
local notation "H" => unitEndomorphismCharacters («R» := ℂ) (powMonoidHom M : Eˣ →* Eˣ)

private theorem cyclic_degree_dvd_extension : M ∣ Nat.card E - 1 :=
  (primePowerKummerCyclicDegree_dvd p d n).trans (finiteField_unit_card_dvd_extension K E)

/-- Exactly `(q-1)gcd(N,R)` full cyclic characters have trivial powered Gauss character. -/
theorem primePowerKummer_trivial_gauss_character_card :
    Nat.card {χ : H | χ.val ^ (m * R) = 1} = m * Nat.gcd N R := by
  rw [finiteField_power_character_kernel_card,
    Nat.gcd_eq_right (cyclic_degree_dvd_extension p d n E)]
  change Nat.gcd (N * m) (m * R) = m * Nat.gcd N R
  rw [Nat.mul_comm N m, Nat.gcd_mul_left]

/-- The full cyclic characters with nontrivial Gauss character are counted by the ramification defect. -/
theorem primePowerKummer_active_gauss_character_card :
    Nat.card {χ : H | χ.val ^ (m * R) ≠ 1} = m * (N - Nat.gcd N R) := by
  rw [finiteField_power_character_active_card,
    Nat.gcd_eq_right (cyclic_degree_dvd_extension p d n E)]
  change N * m - Nat.gcd (N * m) (m * R) = m * (N - Nat.gcd N R)
  rw [Nat.mul_comm N m, Nat.gcd_mul_left, Nat.mul_sub_left_distrib]

/-- The active Gauss characters number exactly twice the intrinsic regular differential dimension. -/
theorem primePowerKummer_active_gauss_character_card_eq_twice_genus (c : Kˣ) :
    Nat.card {χ : H | χ.val ^ (m * R) ≠ 1} =
      2 * Module.finrank K
        (globalRegularDifferentials K (SquareKummerField p s c (p ^ (d + 1) - 2) R)) := by
  rw [primePowerKummer_active_gauss_character_card p d n r E,
    squareKummer_regularDifferential_finrank_twice p s c d r]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
