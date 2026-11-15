import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerIntrinsicRationalCount
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.IntrinsicPlaceActions
import Mathlib.GroupTheory.Sylow

/-!
# Rational fixed places of Sylow p-subgroups

The exact intrinsic point count is one modulo the characteristic.
The p-group orbit congruence therefore gives a rational place fixed by
every element of each Sylow p-subgroup of the actual
constant-field automorphism group. No finiteness assumption on that
automorphism group is needed.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
local notation "s" => kummerSquareIndex d n
local notation "Q" => p ^ (s + 1)
local notation "K" => SquareConstantField p s
local notation "L" => NormalizedKummerField p s d r
local notation "X" => NormalizedKummerRationalPlaces p d n r

/-- The actual rational-place count is one modulo the characteristic. -/
theorem normalizedKummerRationalPlaces_card_mod_characteristic : Nat.card X % p = 1 := by
  let m := p ^ (d + 1) - 1
  let D := Q + 1 - Nat.gcd (Q + 1) (kummerExponent (p ^ (d + 1)) (r + 1))
  have hQ : Q % p = 0 := by
    rw [pow_succ' p s, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
  have hQ2 : Q ^ 2 % p = 0 := by
    rw [pow_two, Nat.mul_mod, hQ, Nat.zero_mul, Nat.zero_mod]
  have hterm : (m * Q * D) % p = 0 := by
    rw [Nat.mul_mod (m * Q) D p, Nat.mul_mod m Q p,
      hQ, Nat.mul_zero, Nat.zero_mod, Nat.zero_mul, Nat.zero_mod]
  rw [normalizedKummerRationalPlaces_card]
  change (Q ^ 2 + 1 + m * Q * D) % p = 1
  simp only [Nat.add_mod, hQ2, hterm,
    Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt, Nat.zero_add, Nat.add_zero]

/-- Every p-group action on the actual rational places has a common fixed place. -/
theorem normalizedKummer_pGroup_fixedPoint
    (G : Type*) [Group G] [MulAction G X] (hG : IsPGroup p G) :
    ∃ W : X, ∀ g : G, g • W = W := by
  have hcard : ¬ p ∣ Nat.card X := by
    intro h
    have hz := Nat.mod_eq_zero_of_dvd h
    rw [normalizedKummerRationalPlaces_card_mod_characteristic p d n r] at hz
    exact Nat.one_ne_zero hz
  obtain ⟨W, hW⟩ := hG.nonempty_fixed_point_of_prime_not_dvd_card X hcard
  exact ⟨W, MulAction.mem_fixedPoints.mp hW⟩

/-- Each Sylow p-subgroup of the actual automorphism group fixes an intrinsic rational place. -/
theorem normalizedKummer_sylow_fixed_rationalPlace (S : Sylow p (L ≃ₐ[K] L)) :
    ∃ W : X, ∀ σ : S, rationalConstantFieldPlaceEquiv (σ : L ≃ₐ[K] L) W = W := by
  obtain ⟨W, hW⟩ := normalizedKummer_pGroup_fixedPoint p d n r S S.isPGroup'
  exact ⟨W, hW⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
