import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FrobeniusDicksonFactor
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.FrobeniusKummerFields

/-!
# Projective covariance of the Frobenius radical equation

The additive Frobenius factor contributes denominator degree `q+1`,
while each Dickson factor contributes `q²-q`. Their product therefore
has exactly the degree required to lift determinant-one substitutions
by sending the radical to itself divided by the linear denominator.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial ArithmeticHarmonicAnalysis

/-- Evaluation of the branch polynomial gives its additive-coordinate factorization. -/
theorem frobeniusKummerBranch_aeval
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (c : Kˣ) (b R : ℕ) (x : L) :
    aeval x (frobeniusKummerBranch c b R) =
      algebraMap K L c * (x ^ (b + 2) - x) *
        (1 + (x ^ (b + 2) - x) ^ (b + 1)) ^ R := by
  rw [frobeniusKummerBranch_eq]
  simp only [map_mul, map_pow, map_sub, map_add, map_one, aeval_C, aeval_X]

/-- The full branch expression transforms with the sum of its two exact denominator degrees. -/
theorem finiteField_frobeniusBranch_covariance
    {K L : Type*} [Field K] [Fintype K] [Field L] [Algebra K L]
    (a b c d : K) (γ x : L) (R : ℕ) (hdet : a * d - b * c = 1)
    (hx : x ^ Fintype.card K - x ≠ 0)
    (hden : algebraMap K L c * x + algebraMap K L d ≠ 0) :
    let q := Fintype.card K
    let D := algebraMap K L c * x + algebraMap K L d
    let u := (algebraMap K L a * x + algebraMap K L b) / D
    γ * (u ^ q - u) * (1 + (u ^ q - u) ^ (q - 1)) ^ R =
      (γ * (x ^ q - x) * (1 + (x ^ q - x) ^ (q - 1)) ^ R) /
        D ^ (q + 1 + (q ^ 2 - q) * R) := by
  let q := Fintype.card K
  let D := algebraMap K L c * x + algebraMap K L d
  let u := (algebraMap K L a * x + algebraMap K L b) / D
  have h1 : u ^ q - u = (x ^ q - x) / D ^ (q + 1) := by
    simpa only [q, D, u, pow_one, hdet, map_one, one_mul] using
      finiteField_mobius_frobenius_pow a b c d x 1
  have h2 : 1 + (u ^ q - u) ^ (q - 1) =
      (1 + (x ^ q - x) ^ (q - 1)) / D ^ (q ^ 2 - q) :=
    finiteField_mobius_dicksonFactor a b c d x (by rw [hdet]; exact one_ne_zero) hx hden
  change γ * (u ^ q - u) * (1 + (u ^ q - u) ^ (q - 1)) ^ R =
    (γ * (x ^ q - x) * (1 + (x ^ q - x) ^ (q - 1)) ^ R) /
      D ^ (q + 1 + (q ^ 2 - q) * R)
  rw [h2, h1, div_pow, ← pow_mul, pow_add]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
