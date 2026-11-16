import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.RationalQuotientSubfields
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Linarith

/-!
# Degree of the Dickson quotient invariant

The polynomials `A=X^q-X` and `B=1+A^(q-1)` are coprime.
Their degrees are `q` and `q(q-1)`, so the reduced quotient
`c B^(q+1)/A^(q(q-1))` has rational-function degree `q(q²-1)`.
This is the index of the invariant field in the rational coordinate field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
open scoped IntermediateField
variable {K : Type*} [Field K]

/-- The first additive Frobenius polynomial. -/
def frobeniusAdditivePolynomial (q : ℕ) : K[X] := X ^ q - X

/-- The quotient of the second Frobenius difference by the first. -/
def frobeniusDicksonPolynomial (q : ℕ) : K[X] :=
  1 + (frobeniusAdditivePolynomial q : K[X]) ^ (q - 1)

/-- The two branch factors have their expected exact polynomial degrees. -/
theorem frobeniusDicksonPolynomial_degrees (q : ℕ) (hq : 2 ≤ q) :
    (frobeniusAdditivePolynomial q : K[X]).natDegree = q ∧
    (frobeniusDicksonPolynomial q : K[X]).natDegree = q * (q - 1) := by
  have hA : (frobeniusAdditivePolynomial q : K[X]).natDegree = q := by
    rw [frobeniusAdditivePolynomial, natDegree_sub_eq_left_of_natDegree_lt]
    · exact natDegree_X_pow q
    · simp only [natDegree_X, natDegree_X_pow]
      omega
  have hpow : 0 < ((frobeniusAdditivePolynomial q : K[X]) ^ (q - 1)).natDegree := by
    rw [natDegree_pow, hA]
    exact Nat.mul_pos (by omega) (by omega)
  refine ⟨hA, ?_⟩
  rw [frobeniusDicksonPolynomial, natDegree_add_eq_right_of_natDegree_lt]
  · rw [natDegree_pow, hA, Nat.mul_comm]
  · simpa only [natDegree_one] using hpow

/-- The identity `B-A^(q-1)=1` gives explicit coprimality of the branch factors. -/
theorem frobeniusDicksonPolynomial_isCoprime (q : ℕ) (hq : 2 ≤ q) :
    IsCoprime (frobeniusDicksonPolynomial q : K[X]) (frobeniusAdditivePolynomial q) := by
  refine ⟨1, -(frobeniusAdditivePolynomial q) ^ (q - 2), ?_⟩
  rw [one_mul, neg_mul, ← pow_succ, show q - 2 + 1 = q - 1 by omega,
    frobeniusDicksonPolynomial]
  ring

/-- The Dickson quotient generates a rational subfield of exact index `q(q²-1)`. -/
theorem frobeniusDicksonQuotient_finrank (q : ℕ) (hq : 2 ≤ q) (c : Kˣ) :
    Module.finrank K⟮
      algebraMap K[X] (RatFunc K) (C (c : K) * (frobeniusDicksonPolynomial q) ^ (q + 1)) /
        algebraMap K[X] (RatFunc K) ((frobeniusAdditivePolynomial q) ^ (q * (q - 1)))⟯
      (RatFunc K) = q * (q ^ 2 - 1) := by
  let A : K[X] := frobeniusAdditivePolynomial q
  let B : K[X] := frobeniusDicksonPolynomial q
  obtain ⟨hAdeg, hBdeg⟩ := frobeniusDicksonPolynomial_degrees (K := K) q hq
  have hA : A ≠ 0 := by
    intro h
    rw [show frobeniusAdditivePolynomial q = A from rfl, h, natDegree_zero] at hAdeg
    omega
  have hB : B ≠ 0 := by
    intro h
    have hp : 0 < q * (q - 1) := Nat.mul_pos (by omega) (by omega)
    rw [show frobeniusDicksonPolynomial q = B from rfl, h, natDegree_zero] at hBdeg
    omega
  have hC : (C (c : K) : K[X]) ≠ 0 := C_ne_zero.mpr c.ne_zero
  have hpowcop : IsCoprime (B ^ (q + 1)) (A ^ (q * (q - 1))) :=
    (frobeniusDicksonPolynomial_isCoprime (K := K) q hq).pow_left.pow_right
  have hcop : IsCoprime (C (c : K) * B ^ (q + 1)) (A ^ (q * (q - 1))) := by
    obtain ⟨a, b, hab⟩ := hpowcop
    refine ⟨C ((c : K)⁻¹) * a, b, ?_⟩
    calc
      _ = (C ((c : K)⁻¹) * C (c : K)) * (a * B ^ (q + 1)) +
          b * A ^ (q * (q - 1)) := by ring
      _ = 1 := by rw [← map_mul, inv_mul_cancel₀ c.ne_zero, map_one, one_mul, hab]
  rw [rationalCoprimeQuotientSubfield_finrank _ _
    (mul_ne_zero hC (pow_ne_zero _ hB)) (pow_ne_zero _ hA) hcop,
    natDegree_mul hC (pow_ne_zero _ hB), natDegree_C, zero_add,
    natDegree_pow, natDegree_pow, hAdeg, hBdeg,
    Nat.mul_comm (q + 1) (q * (q - 1)), Nat.mul_comm (q * (q - 1)) q]
  have hle : q * (q * (q - 1)) ≤ q * (q - 1) * (q + 1) := by
    calc
      _ = (q * (q - 1)) * q := by ring
      _ ≤ (q * (q - 1)) * (q + 1) := Nat.mul_le_mul_left _ (Nat.le_succ q)
  rw [max_eq_left hle]
  let t := q - 1
  have hqt : q = t + 1 := (Nat.sub_add_cancel (by omega : 1 ≤ q)).symm
  rw [hqt, Nat.add_sub_cancel]
  have hs : (t + 1) ^ 2 - 1 = t ^ 2 + 2 * t := by
    rw [show (t + 1) ^ 2 = t ^ 2 + 2 * t + 1 by ring, Nat.add_sub_cancel]
  rw [hs]
  ring

/-- The exact quotient index applies to the cardinality of every finite constant field. -/
theorem finiteField_frobeniusDicksonQuotient_finrank [Fintype K] (c : Kˣ) :
    Module.finrank K⟮
      algebraMap K[X] (RatFunc K) (C (c : K) *
        (frobeniusDicksonPolynomial (Fintype.card K)) ^ (Fintype.card K + 1)) /
        algebraMap K[X] (RatFunc K)
          ((frobeniusAdditivePolynomial (Fintype.card K)) ^
            (Fintype.card K * (Fintype.card K - 1)))⟯
      (RatFunc K) = Fintype.card K * ((Fintype.card K) ^ 2 - 1) :=
  frobeniusDicksonQuotient_finrank _ Fintype.one_lt_card c

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
