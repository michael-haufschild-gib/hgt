import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerTracePointFamilies
import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.FiniteField.FrobeniusFixedCardinality
import Mathlib.Data.Nat.GCD.Basic

/-!
# Auxiliary finite fields in Kummer point counts

Inside the square field of order `p^(2m)`, the `p^k`-fixed subfield has
`p^gcd(2m,k)` elements. The middle Frobenius acts as an involution on it,
whose fixed field has `p^gcd(m,k)` elements. Roots of unity in the middle
field supply exactly the gcd-predicted number of scalar parameters.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

variable (p : ℕ) [Fact p.Prime]

/-- The exact prime-field degree of the chosen square finite field. -/
theorem squareConstantField_finrank (s : ℕ) :
    Module.finrank (ZMod p) (SquareConstantField p s) = 2 * (s + 1) := by
  simpa only [Module.finrank_self, one_mul] using
    FiniteField.finrank_zmod_extension (ZMod p) p (2 * (s + 1))

/-- The auxiliary Frobenius fixed field inside the specified constant field. -/
abbrev KummerAuxiliaryField (s k : ℕ) := frobeniusFixedSubfield p (SquareConstantField p s) k

/-- Its cardinality depends only on the gcd of the two exponents. -/
theorem kummerAuxiliaryField_card (s k : ℕ) :
    Nat.card (KummerAuxiliaryField p s k) = p ^ Nat.gcd (2 * (s + 1)) k := by
  rw [KummerAuxiliaryField, frobeniusFixedSubfield_card, squareConstantField_finrank]

/-- The middle Frobenius restricts to the auxiliary field. -/
def kummerAuxiliaryFrobenius (s k : ℕ) : KummerAuxiliaryField p s k →+* KummerAuxiliaryField p s k where
  toFun x := ⟨x.val ^ p ^ (s + 1), by
    change (x.val ^ p ^ (s + 1)) ^ p ^ k = x.val ^ p ^ (s + 1)
    rw [← pow_mul, Nat.mul_comm (p ^ (s + 1)) (p ^ k), pow_mul,
      (show x.val ^ p ^ k = x.val from x.property)]⟩
  map_one' := Subtype.ext (one_pow _)
  map_mul' x y := Subtype.ext (mul_pow x.val y.val _)
  map_zero' := Subtype.ext (zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))
  map_add' x y := Subtype.ext (add_pow_char_pow x.val y.val p (s + 1))

/-- The restricted Frobenius is an involution. -/
theorem kummerAuxiliaryFrobenius_involutive (s k : ℕ) :
    Function.Involutive (kummerAuxiliaryFrobenius p s k) :=
  fun x => Subtype.ext (squareConstantField_frobenius_sq p s x.val)

/-- Fixed elements of the restricted Frobenius are the intersection of the two ambient fixed fields. -/
def kummerAuxiliaryFixedEquiv (s k : ℕ) :
    (kummerAuxiliaryFrobenius p s k).eqLocusField (RingHom.id _) ≃
      ↥(frobeniusFixedSubfield p (SquareConstantField p s) (s + 1) ⊓ KummerAuxiliaryField p s k) where
  toFun x := ⟨x.val.val, ⟨congrArg Subtype.val x.property, x.val.property⟩⟩
  invFun x := ⟨⟨x.val, x.property.2⟩, Subtype.ext x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The fixed field of the restricted involution has `p^gcd(m,k)` elements. -/
theorem kummerAuxiliaryFixed_card (s k : ℕ) :
    Nat.card ((kummerAuxiliaryFrobenius p s k).eqLocusField (RingHom.id _)) =
      p ^ Nat.gcd (s + 1) k := by
  rw [Nat.card_congr (kummerAuxiliaryFixedEquiv p s k)]
  change Nat.card ↥(frobeniusFixedSubfield p (SquareConstantField p s) (s + 1) ⊓
    frobeniusFixedSubfield p (SquareConstantField p s) k) = _
  rw [frobeniusFixedSubfield_inf_card, squareConstantField_finrank,
    Nat.gcd_eq_right ((Nat.gcd_dvd_left (s + 1) k).trans (dvd_mul_left _ _))]

/-- Equal gcd degrees force the restricted Frobenius to be the identity. -/
theorem kummerAuxiliaryFrobenius_eq_id (s k : ℕ)
    (h : Nat.gcd (2 * (s + 1)) k = Nat.gcd (s + 1) k) :
    kummerAuxiliaryFrobenius p s k = RingHom.id _ := by
  ext x
  have hx : x.val ^ p ^ Nat.gcd (2 * (s + 1)) k = x.val :=
    (frobenius_fixed_gcd_iff p _ k x.val).mpr
      ⟨by simpa only [squareConstantField_finrank] using
          finiteField_frobenius_full_period p (SquareConstantField p s) x.val,
        x.property⟩
  rw [h] at hx
  exact frobenius_fixed_of_dvd p (Nat.gcd_dvd_left (s + 1) k) hx

/-- Unequal gcd degrees force a nonfixed element of the restricted involution. -/
theorem kummerAuxiliaryFrobenius_nontrivial (s k : ℕ)
    (h : Nat.gcd (2 * (s + 1)) k ≠ Nat.gcd (s + 1) k) :
    ∃ x : KummerAuxiliaryField p s k, kummerAuxiliaryFrobenius p s k x ≠ x := by
  classical
  by_contra hn
  push Not at hn
  let e : KummerAuxiliaryField p s k ≃
      (kummerAuxiliaryFrobenius p s k).eqLocusField (RingHom.id _) :=
    { toFun := fun x => ⟨x, hn x⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc := Nat.card_congr e
  rw [kummerAuxiliaryField_card, kummerAuxiliaryFixed_card] at hc
  exact h (Nat.pow_right_injective (Fact.out : p.Prime).one_lt hc)

/-- The number of roots of unity in a finite field is a gcd of multiplicative orders. -/
theorem finiteField_rootsOfUnity_card (K : Type*) [Field K] [Finite K] (n : ℕ) :
    Nat.card (rootsOfUnity n K) = Nat.gcd (Nat.card K - 1) n := by
  change Nat.card (powMonoidHom n : Kˣ →* Kˣ).ker = _
  rw [IsCyclic.card_powMonoidHom_ker, Nat.card_units]

/-- The scalar family has an exact cardinality even when the small field is not contained in the middle field. -/
theorem kummerTraceScalars_card (s d : ℕ) :
    Nat.card (KummerTraceScalars p s d) = p ^ Nat.gcd (s + 1) (d + 1) - 1 := by
  rw [KummerTraceScalars, finiteField_rootsOfUnity_card, squareFrobeniusFixedField_card,
    Nat.pow_sub_one_gcd_pow_sub_one]

/-- When `q` is a subfield size of `Q`, there are exactly `q-1` scalar parameters. -/
theorem kummerTraceScalars_card_of_dvd (s d : ℕ) (hd : d + 1 ∣ s + 1) :
    Nat.card (KummerTraceScalars p s d) = p ^ (d + 1) - 1 := by
  rw [kummerTraceScalars_card, Nat.gcd_eq_right hd]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
