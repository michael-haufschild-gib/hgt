import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.MobiusFrobenius

/-!
# Higher Frobenius forms under projective substitutions

Every iterate of the finite-field Frobenius fixes the matrix entries.
The binary form of each Frobenius degree therefore transforms by the
same determinant, giving its exact affine denominator under a Möbius map.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
variable {K : Type*} [Field K] [Fintype K]
variable {A : Type*} [CommRing A] [Algebra K A]

/-- Every iterated Frobenius fixes finite-field coefficients of a binary linear form. -/
theorem finiteField_linear_pow_card_pow (a b : K) (U V : A) (n : ℕ) :
    (algebraMap K A a * U + algebraMap K A b * V) ^ (Fintype.card K) ^ n =
      algebraMap K A a * U ^ (Fintype.card K) ^ n +
        algebraMap K A b * V ^ (Fintype.card K) ^ n := by
  induction n with
  | zero => simp only [pow_zero, pow_one]
  | succ n ih =>
    calc
      _ = (algebraMap K A a * U ^ (Fintype.card K) ^ n +
          algebraMap K A b * V ^ (Fintype.card K) ^ n) ^ Fintype.card K := by
        rw [pow_succ (Fintype.card K) n, pow_mul, ih]
      _ = algebraMap K A a * (U ^ (Fintype.card K) ^ n) ^ Fintype.card K +
          algebraMap K A b * (V ^ (Fintype.card K) ^ n) ^ Fintype.card K :=
        finiteField_linear_pow_card a b _ _
      _ = _ := by simp only [pow_succ, pow_mul]

/-- The binary form of every Frobenius degree has determinant weight one. -/
theorem finiteField_frobeniusForm_pow_transform (a b c d : K) (U V : A) (n : ℕ) :
    (algebraMap K A a * U + algebraMap K A b * V) ^ (Fintype.card K) ^ n *
        (algebraMap K A c * U + algebraMap K A d * V) -
      (algebraMap K A a * U + algebraMap K A b * V) *
        (algebraMap K A c * U + algebraMap K A d * V) ^ (Fintype.card K) ^ n =
      algebraMap K A (a * d - b * c) *
        (U ^ (Fintype.card K) ^ n * V - U * V ^ (Fintype.card K) ^ n) := by
  rw [finiteField_linear_pow_card_pow, finiteField_linear_pow_card_pow]
  simp only [map_sub, map_mul]
  ring

/-- Over any extension field, a Möbius substitution has the exact higher-Frobenius denominator. -/
theorem finiteField_mobius_frobenius_pow
    {L : Type*} [Field L] [Algebra K L] (a b c d : K) (x : L) (n : ℕ) :
    ((algebraMap K L a * x + algebraMap K L b) /
        (algebraMap K L c * x + algebraMap K L d)) ^ (Fintype.card K) ^ n -
      (algebraMap K L a * x + algebraMap K L b) /
        (algebraMap K L c * x + algebraMap K L d) =
      algebraMap K L (a * d - b * c) * (x ^ (Fintype.card K) ^ n - x) /
        (algebraMap K L c * x + algebraMap K L d) ^ ((Fintype.card K) ^ n + 1) := by
  have hcross :
      (algebraMap K L a * x + algebraMap K L b) ^ (Fintype.card K) ^ n *
        (algebraMap K L c * x + algebraMap K L d) -
      (algebraMap K L a * x + algebraMap K L b) *
        (algebraMap K L c * x + algebraMap K L d) ^ (Fintype.card K) ^ n =
      algebraMap K L (a * d - b * c) * (x ^ (Fintype.card K) ^ n - x) := by
    simpa only [mul_one, one_pow] using finiteField_frobeniusForm_pow_transform a b c d x 1 n
  by_cases hd : algebraMap K L c * x + algebraMap K L d = 0
  · simp only [hd, div_zero, zero_pow (pow_ne_zero n Fintype.card_ne_zero), sub_self,
      zero_pow (Nat.succ_ne_zero _)]
  · generalize hu : algebraMap K L a * x + algebraMap K L b = u at hcross ⊢
    generalize hv : algebraMap K L c * x + algebraMap K L d = v at hcross hd ⊢
    simp only [div_pow, pow_succ]
    field_simp [hd]
    linear_combination hcross

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
