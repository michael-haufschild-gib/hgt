import GaloisForLFunctions.HTGeometry.RatFuncProjectiveAutomorphism
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Tactic.LinearCombination

/-!
# Frobenius forms under projective substitutions

Over a field with `q` elements, the homogeneous form `U^q V - U V^q`
transforms by the determinant. In the affine chart this gives the exact
transformation law of `X^q-X` under a rational Möbius substitution.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
variable {K : Type*} [Field K] [Fintype K]
variable {A : Type*} [CommRing A] [Algebra K A]

/-- Frobenius fixes the coefficients of every binary linear combination. -/
theorem finiteField_linear_pow_card (a b : K) (U V : A) :
    (algebraMap K A a * U + algebraMap K A b * V) ^ Fintype.card K =
      algebraMap K A a * U ^ Fintype.card K +
        algebraMap K A b * V ^ Fintype.card K := by
  nontriviality A
  obtain ⟨p, hp, e, hprime, hcard⟩ := FiniteField.card' (K := K)
  letI : CharP K p := hp
  letI : Fact p.Prime := ⟨hprime⟩
  letI : CharP A p := charP_of_injective_ringHom (algebraMap K A).injective p
  rw [hcard, add_pow_char_pow, mul_pow, mul_pow, ← map_pow, ← map_pow,
    ← hcard, FiniteField.pow_card, FiniteField.pow_card]

/-- The binary Frobenius form is a relative invariant of determinant weight one. -/
theorem finiteField_frobeniusForm_transform (a b c d : K) (U V : A) :
    (algebraMap K A a * U + algebraMap K A b * V) ^ Fintype.card K *
        (algebraMap K A c * U + algebraMap K A d * V) -
      (algebraMap K A a * U + algebraMap K A b * V) *
        (algebraMap K A c * U + algebraMap K A d * V) ^ Fintype.card K =
      algebraMap K A (a * d - b * c) *
        (U ^ Fintype.card K * V - U * V ^ Fintype.card K) := by
  rw [finiteField_linear_pow_card, finiteField_linear_pow_card]
  simp only [map_sub, map_mul]
  ring

/-- The affine Frobenius branch polynomial transforms with its exact denominator.
The identity includes singular coefficient matrices and a zero denominator. -/
theorem mobius_frobenius_difference (a b c d : K) :
    RatFunc.mobius a b c d ^ Fintype.card K - RatFunc.mobius a b c d =
      algebraMap K (RatFunc K) (a * d - b * c) *
        (RatFunc.X ^ Fintype.card K - RatFunc.X) /
          (algebraMap K (RatFunc K) c * RatFunc.X +
            algebraMap K (RatFunc K) d) ^ (Fintype.card K + 1) := by
  have hcross :
      (algebraMap K (RatFunc K) a * RatFunc.X + algebraMap K (RatFunc K) b) ^
          Fintype.card K *
        (algebraMap K (RatFunc K) c * RatFunc.X + algebraMap K (RatFunc K) d) -
      (algebraMap K (RatFunc K) a * RatFunc.X + algebraMap K (RatFunc K) b) *
        (algebraMap K (RatFunc K) c * RatFunc.X + algebraMap K (RatFunc K) d) ^
          Fintype.card K =
      algebraMap K (RatFunc K) (a * d - b * c) *
        (RatFunc.X ^ Fintype.card K - RatFunc.X) := by
    simpa only [mul_one, one_pow] using
      finiteField_frobeniusForm_transform a b c d (RatFunc.X : RatFunc K) 1
  by_cases hd : algebraMap K (RatFunc K) c * RatFunc.X + algebraMap K (RatFunc K) d = 0
  · simp only [RatFunc.mobius, hd, div_zero,
      zero_pow (Fintype.card_ne_zero), sub_self, zero_pow (Nat.succ_ne_zero _)]
  · generalize hu : algebraMap K (RatFunc K) a * RatFunc.X +
        algebraMap K (RatFunc K) b = u at hcross
    generalize hv : algebraMap K (RatFunc K) c * RatFunc.X +
        algebraMap K (RatFunc K) d = v at hcross hd
    simp only [RatFunc.mobius, hu, hv, div_pow, pow_succ]
    field_simp [hd]
    linear_combination hcross

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
