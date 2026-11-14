import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerTraceIntersection
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerConstructedPointCount

/-!
# Evaluated parameter counts for rational Kummer fibers

The geometric exponent has the same sign as its number of terms in the
constant field. Thus the small field meets the signed Frobenius family in
all `q` elements when the characteristic is two or the exponent length is
even, and only in zero otherwise. Together with the trace intersection,
this evaluates the affine point-count lower bound explicitly.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open GaloisForLFunctions.ArithmeticHarmonicAnalysis
open GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open scoped Classical

variable (p : ℕ) [Fact p.Prime]

/-- The geometric exponent has the same sign as its number of terms in characteristic `p`. -/
theorem kummerExponent_neg_one_pow (s d n : ℕ) :
    (-1 : SquareConstantField p s) ^ kummerExponent (p ^ (d + 1)) n = (-1) ^ n := by
  induction n with
  | zero => simp only [kummerExponent, Finset.range_zero, Finset.sum_empty, pow_zero]
  | succ n ih =>
    have hs : kummerExponent (p ^ (d + 1)) (n + 1) =
        kummerExponent (p ^ (d + 1)) n + (p ^ (d + 1)) ^ n := by
      simp only [kummerExponent, Finset.sum_range_succ]
    rw [hs, pow_add, ih, pow_succ (-1 : SquareConstantField p s) n]
    congr 1
    rw [← pow_mul p]
    exact neg_one_pow_expChar_pow (SquareConstantField p s) p ((d + 1) * n)

/-- The sign correction depends only on characteristic two and parity of the exponent length. -/
theorem kummerExponent_sign_eq_one_iff (s d r : ℕ) :
    (-1 : SquareConstantField p s) ^ kummerExponent (p ^ (d + 1)) (r + 1) = 1 ↔
      p = 2 ∨ Even (r + 1) := by
  rw [kummerExponent_neg_one_pow]
  have h2 : (2 : SquareConstantField p s) = 0 ↔ p = 2 :=
    (CharP.cast_eq_zero_iff (SquareConstantField p s) p 2).trans
      ((Nat.prime_two.dvd_iff_eq (Fact.out : p.Prime).ne_one).trans eq_comm)
  have hn : (-1 : SquareConstantField p s) = 1 ↔ p = 2 := by
    constructor
    · intro h
      apply h2.mp
      linear_combination -1 * h
    · intro h
      have he := h2.mpr h
      linear_combination -1 * he
  by_cases hp : p = 2
  · rw [hn.mpr hp, one_pow]
    exact ⟨fun _ => Or.inl hp, fun _ => rfl⟩
  · rw [neg_one_pow_eq_one_iff_even (fun h => hp (hn.mp h))]
    exact ⟨Or.inr, fun h => h.resolve_left hp⟩

/-- The small field's intersection with the signed family has either `q` elements or only zero. -/
theorem kummerSigned_smallField_intersection_card (s d r : ℕ) (hd : d + 1 ∣ s + 1) :
    Nat.card {b : SquareConstantField p s //
      b ^ p ^ (s + 1) = (-1) ^ kummerExponent (p ^ (d + 1)) (r + 1) * b ∧
        b ^ p ^ (d + 1) = b} =
      if p = 2 ∨ Even (r + 1) then p ^ (d + 1) else 1 := by
  let R := kummerExponent (p ^ (d + 1)) (r + 1)
  by_cases hs : p = 2 ∨ Even (r + 1)
  · rw [if_pos hs]
    have hsign := (kummerExponent_sign_eq_one_iff p s d r).mpr hs
    let e : {b : SquareConstantField p s //
        b ^ p ^ (s + 1) = (-1) ^ R * b ∧ b ^ p ^ (d + 1) = b} ≃
        KummerAuxiliaryField p s (d + 1) :=
      { toFun := fun b => ⟨b.val, b.property.2⟩
        invFun := fun b => ⟨b.val, by
          rw [hsign, one_mul]
          exact frobenius_fixed_of_dvd p hd b.property, b.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e, kummerAuxiliaryField_card,
      Nat.gcd_eq_right (hd.trans (dvd_mul_left _ _))]
  · rw [if_neg hs]
    have hsign : (-1 : SquareConstantField p s) ^ R ≠ 1 :=
      fun h => hs ((kummerExponent_sign_eq_one_iff p s d r).mp h)
    have hz (b : SquareConstantField p s)
        (hb : b ^ p ^ (s + 1) = (-1) ^ R * b ∧ b ^ p ^ (d + 1) = b) : b = 0 := by
      have hfixed := frobenius_fixed_of_dvd p hd hb.2
      have he : (1 - (-1 : SquareConstantField p s) ^ R) * b = 0 := by
        rw [hfixed] at hb
        linear_combination hb.1
      exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr (Ne.symm hsign))
    letI : Nonempty {b : SquareConstantField p s //
        b ^ p ^ (s + 1) = (-1) ^ R * b ∧ b ^ p ^ (d + 1) = b} := ⟨⟨0, by
          simp only [zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero), mul_zero, and_self]⟩⟩
    letI : Subsingleton {b : SquareConstantField p s //
        b ^ p ^ (s + 1) = (-1) ^ R * b ∧ b ^ p ^ (d + 1) = b} :=
      ⟨fun x y => Subtype.ext ((hz x.val x.property).trans (hz y.val y.property).symm)⟩
    exact Nat.card_unique

/-- The signed construction contributes the exact parity-dependent number of ordinates. -/
theorem kummerSignedParameters_card (s d r : ℕ) (hd : d + 1 ∣ s + 1) :
    Nat.card (KummerSignedParameters p s d r) =
      if p = 2 ∨ Even (r + 1) then p ^ (s + 1) - p ^ (d + 1) else p ^ (s + 1) - 1 := by
  change Nat.card {b : SquareConstantField p s //
    b ^ p ^ (s + 1) = (-1) ^ kummerExponent (p ^ (d + 1)) (r + 1) * b ∧
      ¬b ^ p ^ (d + 1) = b} = _
  rw [card_subtype_and_not, kummerSigned_smallField_intersection_card p s d r hd]
  erw [squareField_signedFrobenius_card]
  split_ifs <;> rfl

/-- The rational affine point bound with every parameter cardinality evaluated. -/
theorem normalizedKummer_affine_card_lower_bound_explicit (s d r : ℕ) (hd : d + 1 ∣ s + 1) :
    ((p ^ (d + 1) - 1) *
        (p ^ (s + 1) - kummerTraceIntersectionNumber p s ((d + 1) * (r + 1))) +
      (if p = 2 ∨ Even (r + 1) then p ^ (s + 1) - p ^ (d + 1) else p ^ (s + 1) - 1)) *
        (p ^ (s + 1) + 1) ≤ Nat.card (NormalizedKummerAffinePoints p s d r) := by
  have h := normalizedKummer_affine_card_lower_bound p s d r
  rwa [kummerTraceScalars_card_of_dvd p s d hd, kummerTraceParameters_card,
    kummerSignedParameters_card p s d r hd] at h

/-- A square-field index for the prime-power parameters `q=p^(d+1)` and `Q=q^(n+1)`. -/
def kummerSquareIndex (d n : ℕ) : ℕ := d + (d + 1) * n

/-- The index realizes the product of the base-field and relative degrees. -/
theorem kummerSquareIndex_succ (d n : ℕ) :
    kummerSquareIndex d n + 1 = (d + 1) * (n + 1) := by
  unfold kummerSquareIndex
  ring

/-- The explicit point-count bound holds for every constructed prime-power Kummer family. -/
theorem normalizedKummer_primePower_affine_card_lower_bound (d n r : ℕ) :
    ((p ^ (d + 1) - 1) *
        (p ^ (kummerSquareIndex d n + 1) -
          kummerTraceIntersectionNumber p (kummerSquareIndex d n) ((d + 1) * (r + 1))) +
      (if p = 2 ∨ Even (r + 1) then p ^ (kummerSquareIndex d n + 1) - p ^ (d + 1)
        else p ^ (kummerSquareIndex d n + 1) - 1)) *
      (p ^ (kummerSquareIndex d n + 1) + 1) ≤
        Nat.card (NormalizedKummerAffinePoints p (kummerSquareIndex d n) d r) :=
  normalizedKummer_affine_card_lower_bound_explicit p _ d r
    (by rw [kummerSquareIndex_succ]; exact dvd_mul_right _ _)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
