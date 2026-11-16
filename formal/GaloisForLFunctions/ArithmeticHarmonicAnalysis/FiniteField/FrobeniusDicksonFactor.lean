import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.MobiusFrobeniusPowers

/-!
# The Dickson branch factor under projective substitutions

The quotient of the second Frobenius difference by the first is
`1+(x^q-x)^(q-1)`. Its determinant factors cancel under a projective
substitution, leaving denominator exponent `q²-q`. This is the second
branch factor in the Frobenius radical family.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
variable {K : Type*} [Field K] [Fintype K]

/-- The second Frobenius difference factors through the first and its Dickson factor. -/
theorem finiteField_frobenius_difference_factor
    {A : Type*} [CommRing A] [Algebra K A] (x : A) :
    (x ^ Fintype.card K - x) * (1 + (x ^ Fintype.card K - x) ^ (Fintype.card K - 1)) =
      x ^ (Fintype.card K) ^ 2 - x := by
  let q := Fintype.card K
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero
  have hF : (x ^ q - x) ^ q = x ^ q ^ 2 - x ^ q := by
    simpa only [map_one, map_neg, one_mul, neg_one_mul, ← sub_eq_add_neg,
      ← pow_mul, pow_two] using finiteField_linear_pow_card (1 : K) (-1) (x ^ q) x
  change (x ^ q - x) * (1 + (x ^ q - x) ^ (q - 1)) = _
  calc
    _ = (x ^ q - x) + (x ^ q - x) ^ q := by
      rw [mul_add, mul_one, ← pow_succ', Nat.sub_add_cancel hq]
    _ = x ^ q ^ 2 - x := by rw [hF]; ring

/-- The Dickson factor has projective denominator exponent `q²-q`.
Nonvanishing of the first Frobenius difference permits cancellation. -/
theorem finiteField_mobius_dicksonFactor
    {L : Type*} [Field L] [Algebra K L] (a b c d : K) (x : L)
    (hdet : a * d - b * c ≠ 0)
    (hx : x ^ Fintype.card K - x ≠ 0)
    (hd : algebraMap K L c * x + algebraMap K L d ≠ 0) :
    let u := (algebraMap K L a * x + algebraMap K L b) /
      (algebraMap K L c * x + algebraMap K L d)
    1 + (u ^ Fintype.card K - u) ^ (Fintype.card K - 1) =
      (1 + (x ^ Fintype.card K - x) ^ (Fintype.card K - 1)) /
        (algebraMap K L c * x + algebraMap K L d) ^ ((Fintype.card K) ^ 2 - Fintype.card K) := by
  let q := Fintype.card K
  let D := algebraMap K L c * x + algebraMap K L d
  let δ := algebraMap K L (a * d - b * c)
  let u := (algebraMap K L a * x + algebraMap K L b) / D
  have hδ : δ ≠ 0 := fun h => hdet ((algebraMap K L).injective (h.trans (map_zero _).symm))
  have h1 : u ^ q - u = δ * (x ^ q - x) / D ^ (q + 1) := by
    simpa only [q, D, δ, u, pow_one] using finiteField_mobius_frobenius_pow a b c d x 1
  have h2 : u ^ q ^ 2 - u = δ * (x ^ q ^ 2 - x) / D ^ (q ^ 2 + 1) :=
    finiteField_mobius_frobenius_pow a b c d x 2
  have hu : u ^ q - u ≠ 0 := by
    rw [h1]
    exact div_ne_zero (mul_ne_zero hδ hx) (pow_ne_zero _ hd)
  have hproduct : (u ^ q - u) * (1 + (u ^ q - u) ^ (q - 1)) =
      δ * ((x ^ q - x) * (1 + (x ^ q - x) ^ (q - 1))) / D ^ (q ^ 2 + 1) := by
    rw [finiteField_frobenius_difference_factor (K := K),
      finiteField_frobenius_difference_factor (K := K)]
    exact h2
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero
  have hqq : q ≤ q ^ 2 := by
    simpa only [mul_one, pow_two] using Nat.mul_le_mul_left q hq
  have he : q ^ 2 + 1 = (q + 1) + (q ^ 2 - q) := by omega
  change 1 + (u ^ q - u) ^ (q - 1) = (1 + (x ^ q - x) ^ (q - 1)) / D ^ (q ^ 2 - q)
  apply mul_left_cancel₀ hu
  rw [hproduct, h1, he, pow_add]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
