import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.CharacterFiberCount
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerNormFibers
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Character counts for nonzero Kummer fibers

A nonzero power fiber lies entirely in the unit group. Its cardinality
is the sum of all complex multiplicative characters killed by the
covering exponent. No divisibility restriction on the field size is
needed; the character group has the corresponding gcd cardinality.
-/

noncomputable section
open scoped Classical
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable {K : Type*} [Field K] [Finite K]

local instance : Fintype (MulChar K ℂ) := Fintype.ofFinite _

/-- Every nonzero Kummer fiber is counted exactly by the characters annihilating the power-map image. -/
theorem finiteField_nonzero_power_fiber_character_sum (n : ℕ) (a : K) (ha : a ≠ 0) :
    (Nat.card {z : K | z ^ (n + 1) = a} : ℂ) =
      ∑ χ : unitEndomorphismCharacters (R := ℂ) (powMonoidHom (n + 1) : Kˣ →* Kˣ),
        χ.val a := by
  rw [Nat.card_congr (nonzeroPowerFiberEquivUnits n a ha)]
  exact unitEndomorphism_fiber_card_eq_character_sum
    (powMonoidHom (n + 1) : Kˣ →* Kˣ) (Units.mk0 a ha)

/-- The characters contributing to a power fiber are counted by the gcd of its exponent and the field's unit count. -/
theorem finiteField_power_characters_card (n : ℕ) :
    Nat.card (unitEndomorphismCharacters (R := ℂ) (powMonoidHom n : Kˣ →* Kˣ)) =
      Nat.gcd (Nat.card K - 1) n := by
  rw [powerEndomorphismCharacters_card, Nat.card_units]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
